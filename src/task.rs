//! Tasks and Continuations for executing and chaining Futures.
//!
//! # Overview
//!
//! Tasks and Continuations are used to "glue" futures together and execute them on the Vortex
//! in an abstract fashion. Since every continuation is different the Vortex just executes Tasks
//! as they come in (by calling its `run` method).

use future::FutureState;
use std::mem;

/// The Task is a generic abstraction over a closure to run inside the event loop.
pub trait Task {
    /// Run the Task.
    #[inline]
    fn run(&mut self);
}

/// A specific Task which takes a closure and runs it, passing the `FutureState` to it.
pub struct Continuation<T: 'static, E: 'static, F> {
    state: Option<FutureState<T, E>>,
    func: F,
}

impl<T, E, F> Continuation<T, E, F>
    where F: FnMut(FutureState<T, E>)
{
    /// Creates a continuation with both the state and the closure.
    ///
    /// If this method is used, no further information is needed to run the continuation.
    #[inline]
    pub fn complete(state: FutureState<T, E>, func: F) -> Continuation<T, E, F> {
        Continuation {
            state: Some(state),
            func: func,
        }
    }

    /// Creates a deferred continuation with just the closure, the state needs to be set
    /// separately before running it.
    #[inline]
    pub fn deferred(func: F) -> Continuation<T, E, F> {
        Continuation {
            state: None,
            func: func,
        }
    }

    /// Returns a mutable borrow of the internal future state so it can be modified when a
    /// deferred continuation is created.
    #[inline]
    pub fn state_as_mut(&mut self) -> &mut Option<FutureState<T, E>> {
        &mut self.state
    }
}

impl<T, E, F> Task for Continuation<T, E, F>
    where F: FnMut(FutureState<T, E>)
{
    #[inline]
    fn run(&mut self) {
        let state = mem::replace(&mut self.state, None);
        (self.func)(state.expect("State not set when Continuation is run."));
    }
}

#[cfg(test)]
mod tests {

    use future::FutureState;
    use super::{Task, Continuation};

    #[test]
    fn should_run_continuation_with_ok() {
        let mut cont = Continuation::<_, i32, _>::complete(FutureState::Ok(1), |state| {
            match state {
                FutureState::Ok(v) => assert_eq!(v, 1),
                _ => assert!(false),
            }
        });

        cont.run();
    }

    #[test]
    fn should_run_continuation_with_err() {
        let mut cont = Continuation::<i32, _, _>::complete(FutureState::Err(-1), |state| {
            match state {
                FutureState::Err(e) => assert_eq!(e, -1),
                _ => assert!(false),
            }
        });

        cont.run();
    }

}
