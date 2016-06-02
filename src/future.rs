//! Basic concurrency building blocks (Futures and Promises).
//!
//! # Overview
//!
//! Futures and Promises form the basic building blocks of concurrency in reef. A `Future`
//! represents a result which may have been computed yet (and it may be computed with an error
//! eventually). The `Promise` is responsible for completing the Future and filling its state
//! with either the successful value or the error.
//!
//! A callback (typically a closure) can be attached to a `Future` which will be executed when it
//! completes. Internally this is called a `Continuation`. Reef will make sure to schedule their
//! callbacks and execute them when needed, so this is hidden from the user.
//!
//! If a value is known already, a `Future` can also be created directly without an associated
//! `Promise`, in this case it will immediately be set into a completed state. Please see the
//! individual documentations for Promises and Futures on their respective usage and more info
//! on their inner workings.

use std::ptr;
use std::mem;

use task::Continuation;
use task::Task;
use vortex::Vortex;

/// Contains the current state of a `Future`, `Promise` or `Continuation`.
///
/// Since state can be hold in various places (Futures, Promises and Continuations) this enum
/// abstracts their different representations. See the variants for more information on the
/// possible states.
#[derive(Debug,PartialEq)]
pub enum FutureState<T: 'static, E: 'static> {
    /// This state is invalid, most likely because the previous state has been moved somewhere
    /// else already.
    Invalid,
    /// The state is not yet known, most likely the `Promise` is not completed yet.
    Pending,
    /// The state is known and it completed with a successful value `T`.
    Ok(T),
    /// The state is known and it completed with an error `E`.
    Err(E),
}

impl<T, E> FutureState<T, E> {
    /// Returns `true` if the state is `Ok`.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::FutureState;
    ///
    /// let state = FutureState::Pending::<i32, i32>;
    /// assert_eq!(false, state.is_ok());
    ///
    /// let state = FutureState::Ok::<_, i32>(1);
    /// assert_eq!(true, state.is_ok());
    /// ```
    #[inline]
    pub fn is_ok(&self) -> bool {
        match *self {
            FutureState::Ok(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if the state is `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::FutureState;
    ///
    /// let state = FutureState::Pending::<i32, i32>;
    /// assert_eq!(false, state.is_err());
    ///
    /// let state = FutureState::Err::<i32, _>(-1);
    /// assert_eq!(true, state.is_err());
    /// ```
    #[inline]
    pub fn is_err(&self) -> bool {
        match *self {
            FutureState::Err(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if the state is either `Ok` or `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::FutureState;
    ///
    /// let state = FutureState::Pending::<i32, i32>;
    /// assert_eq!(false, state.is_available());
    ///
    /// let state = FutureState::Err::<i32, _>(-1);
    /// assert_eq!(true, state.is_available());
    ///
    /// let state = FutureState::Ok::<_, i32>(1);
    /// assert_eq!(true, state.is_available());
    /// ```
    #[inline]
    pub fn is_available(&self) -> bool {
        self.is_ok() || self.is_err()
    }
}

/// Allows a `Future` to be completed at a later point in time.
///
/// When a new `Promise` is created through `Promise::new()` it does not reference a `Future`
/// right away. Only once `future` is called then a `Future` is returned and (unsafe) pointer
/// relationships are established between them.
///
/// If a `Task` (a `Continuation`) has been attached already then all state which is set through
/// either the `set_ok` or the `set_err` methods is delivered into the task. If no task has been
/// set yet the state is carried over properly and executed.
///
/// **Note:** The unsafe code is there since, frankly, I don't right now how to get it done in a
/// straightforward way with stable rust. This might change in the future but does not change
/// the semantics of the Future/Promise relationship by any means.
pub struct Promise<T: 'static, E: 'static> {
    future: Option<*mut Future<T, E>>,
    state: FutureState<T, E>,
    task: Option<Box<Task>>,
    task_state: Option<*mut Option<FutureState<T, E>>>,
}

impl<T, E> Promise<T, E> {
    #[inline]
    pub fn new() -> Promise<T, E> {
        Promise {
            future: None,
            state: FutureState::Pending,
            task: None,
            task_state: None,
        }
    }

    #[inline]
    pub fn future(&mut self) -> Future<T, E> {
        Future::deferred(self)
    }

    #[inline]
    pub fn state(&self) -> &FutureState<T, E> {
        match self.task_state {
            Some(ptr) => unsafe { (*ptr).as_ref().unwrap() },
            None => &self.state,
        }
    }

    #[inline]
    pub fn state_mut(&mut self) -> &mut FutureState<T, E> {
        match self.task_state {
            Some(ptr) => unsafe { (*ptr).as_mut().unwrap() },
            None => &mut self.state,
        }
    }

    #[inline]
    pub fn set_ok(&mut self, value: T) {
        match self.task_state {
            Some(ptr) => unsafe { *ptr = Some(FutureState::Ok(value)) },
            None => self.state = FutureState::Ok(value),
        };
        self.make_ready();
    }

    #[inline]
    pub fn set_err(&mut self, err: E) {
        match self.task_state {
            Some(ptr) => unsafe { *ptr = Some(FutureState::Err(err)) },
            None => self.state = FutureState::Err(err),
        };
        self.make_ready();
    }

    #[inline]
    fn schedule<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        let mut boxed = Box::new(Continuation::deferred(f));
        self.task_state = Some(boxed.state_as_mut());
        self.task = Some(boxed);
    }

    #[inline]
    fn make_ready(&mut self) {
        if self.task.is_some() {
            let task = mem::replace(&mut self.task, None).unwrap();
            Vortex::schedule(task);
        }
    }
}

pub enum Future<T: 'static, E: 'static> {
    Deferred(*mut Promise<T, E>),
    Ready(FutureState<T, E>),
}

impl<T, E> Future<T, E> {
    #[inline]
    pub fn deferred(promise: &mut Promise<T, E>) -> Future<T, E> {
        let mut future = Future::Deferred(promise as *mut Promise<T, E>);
        promise.future = Some(&mut future as *mut Future<T, E>);
        future
    }

    #[inline]
    pub fn from_ok(value: T) -> Future<T, E> {
        Future::Ready(FutureState::Ok(value))
    }

    #[inline]
    pub fn from_err(error: E) -> Future<T, E> {
        Future::Ready(FutureState::Err(error))
    }

    #[inline]
    fn state_as_ref(&self) -> &FutureState<T, E> {
        match *self {
            Future::Ready(ref state) => &state,
            Future::Deferred(promise) => unsafe {
                if promise.is_null() {
                    panic!("Trying to get FutureState out of Promise where *mut is null!");
                }
                (*promise).state()
            },
        }
    }

    #[inline]
    fn state(&mut self) -> FutureState<T, E> {
        match *self {
            Future::Ready(ref mut state) => unsafe { ptr::replace(state, FutureState::Invalid) },
            Future::Deferred(promise) => unsafe {
                if promise.is_null() {
                    panic!("Trying to get FutureState out of Promise where *mut is null!");
                }
                mem::replace((*promise).state_mut(), FutureState::Invalid)
            },
        }
    }

    #[inline]
    pub fn is_available(&self) -> bool {
        self.state_as_ref().is_available()
    }

    #[inline]
    pub fn is_err(&self) -> bool {
        self.state_as_ref().is_err()
    }

    #[inline]
    pub fn is_ok(&self) -> bool {
        self.state_as_ref().is_ok()
    }

    #[inline]
    pub fn then<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(T) -> Future<TRES, E> + 'static
    {
        if self.is_available() {
            match self.state() {
                FutureState::Ok(v) => return f(v),
                FutureState::Err(e) => return Future::from_err(e),
                _ => panic!("This should not happen since we checked the state before."),
            }
        }

        let mut promise = Box::new(Promise::<TRES, E>::new());
        let future = promise.future();

        self.schedule(move |state| {
            match state {
                FutureState::Ok(v) => {
                    match f(v).state() {
                        FutureState::Ok(iv) => promise.set_ok(iv),
                        FutureState::Err(ie) => promise.set_err(ie),
                        _ => panic!("This should not happen since we checked the state before."),
                    }
                }
                FutureState::Err(e) => promise.set_err(e),
                _ => panic!("This should not happen since we checked the state before."),
            }
        });

        future
    }

    #[inline]
    pub fn then_wrapped<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(FutureState<T, E>) -> Future<TRES, E> + 'static
    {
        if self.is_available() {
            return f(self.state());
        }


        let mut promise = Box::new(Promise::<TRES, E>::new());
        let future = promise.future();

        self.schedule(move |state| {
            match f(state).state() {
                FutureState::Ok(iv) => promise.set_ok(iv),
                FutureState::Err(ie) => promise.set_err(ie),
                _ => panic!("This should not happen since we checked the state before."),
            }
        });

        future
    }

    #[inline]
    fn schedule<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        match *self {
            Future::Ready(_) => Vortex::schedule(Box::new(Continuation::complete(self.state(), f))),
            Future::Deferred(promise) => unsafe { (*promise).schedule(f) },
        }
    }
}

/// Helper method to create a successful, completed `Future`.
///
/// This function is identical to calling `Future::from_ok(value)`, it's just nicer to read and
/// write in a `Continuation`.
///
/// # Examples
///
/// ```
/// use reef::future::ok;
///
/// let future = ok::<_, i32>(42);
/// assert_eq!(true, future.is_available());
/// assert_eq!(true, future.is_ok());
/// assert_eq!(false, future.is_err());
/// ```
#[inline]
pub fn ok<T, E>(value: T) -> Future<T, E> {
    Future::from_ok(value)
}

/// Helper method to create a failed, completed `Future`.
///
/// This function is identical to calling `Future::from_err(err)`, it's just nicer to read and
/// write in a `Continuation`.
///
/// # Examples
///
/// ```
/// use reef::future::err;
///
/// let future = err::<i32, _>(-1);
/// assert_eq!(true, future.is_available());
/// assert_eq!(false, future.is_ok());
/// assert_eq!(true, future.is_err());
/// ```
#[inline]
pub fn err<T, E>(err: E) -> Future<T, E> {
    Future::from_err(err)
}

#[cfg(test)]
mod tests {

    use super::{FutureState, Future, Promise};

    #[test]
    fn test_future_from_ok() {
        let future = Future::<i32, i32>::from_ok(42);
        assert_eq!(true, future.is_available());
        assert_eq!(false, future.is_err());
    }

    #[test]
    fn test_future_from_err() {
        let future = Future::<i32, i32>::from_err(-1);
        assert_eq!(true, future.is_available());
        assert_eq!(true, future.is_err());
    }

    #[test]
    fn test_set_promise_state_after_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());

        {
            let future = promise.future();
            assert_eq!(FutureState::Pending, *future.state_as_ref());
            assert_eq!(false, future.is_available());
            assert_eq!(false, future.is_err());
        }

        promise.set_ok(42);
        assert_eq!(FutureState::Ok(42), *promise.state());

        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_as_ref());
            assert_eq!(true, future.is_available());
            assert_eq!(false, future.is_err());
        }

    }

    #[test]
    fn test_future_raw_pointer_when_promise_moved() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());
        promise.set_ok(42);
        move_promise_here(promise);
    }

    fn move_promise_here(mut promise: Promise<i32, i32>) {
        assert_eq!(FutureState::Ok(42), *promise.state());

        let future = promise.future();
        assert_eq!(FutureState::Ok(42), *future.state_as_ref());
        assert_eq!(true, future.is_available());
        assert_eq!(false, future.is_err());
    }

    #[test]
    fn test_set_promise_state_before_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());
        promise.set_ok(42);
        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_as_ref());
            assert_eq!(true, future.is_available());
            assert_eq!(false, future.is_err());
        }
    }

    #[test]
    fn test_correct_states_on_pending() {
        let state = FutureState::Pending::<i32, i32>;
        assert_eq!(false, state.is_ok());
        assert_eq!(false, state.is_err());
        assert_eq!(false, state.is_available());
    }

    #[test]
    fn test_correct_states_on_ok() {
        let state = FutureState::Ok::<_, i32>(1);
        assert_eq!(true, state.is_ok());
        assert_eq!(false, state.is_err());
        assert_eq!(true, state.is_available());
    }

    #[test]
    fn test_correct_states_on_err() {
        let state = FutureState::Err::<i32, _>(-1);
        assert_eq!(false, state.is_ok());
        assert_eq!(true, state.is_err());
        assert_eq!(true, state.is_available());
    }

    #[test]
    fn test_extracting_state_from_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        assert_eq!(true, future.is_available());
        assert_eq!(false, future.is_err());

        let state = future.state();
        assert_eq!(FutureState::Ok(42), state);
    }

    #[test]
    fn test_extracting_state_from_deferred_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());

        promise.set_ok(42);
        assert_eq!(FutureState::Ok(42), *promise.state());

        {
            let mut future = promise.future();
            let state = future.state();
            assert_eq!(FutureState::Ok(42), state);
            assert_eq!(FutureState::Invalid, *future.state_as_ref());
        }

        assert_eq!(FutureState::Invalid, *promise.state());
    }

    #[test]
    fn test_then_on_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        future.then(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_ok(22)
            })
            .then(|val| {
                assert_eq!(22, val);
                Future::<(), i32>::from_ok(())
            });
    }

    #[test]
    fn test_then_wrapped_on_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        future.then(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_err(-1)
            })
            .then_wrapped(|state| {
                match state {
                    FutureState::Ok(_) => assert!(false),
                    FutureState::Err(e) => assert_eq!(-1, e),
                    _ => assert!(false),
                }
                Future::<(), i32>::from_ok(())
            });
    }

    #[test]
    fn test_ignore_then_on_err() {
        let mut future = Future::<i32, i32>::from_ok(42);
        future.then(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_err(-1)
            })
            .then(|_| {
                assert!(false);
                Future::<(), i32>::from_ok(())
            })
            .then_wrapped(|state| {
                match state {
                    FutureState::Ok(_) => assert!(false),
                    FutureState::Err(e) => assert_eq!(-1, e),
                    _ => assert!(false),
                }
                Future::<(), i32>::from_ok(())
            });
    }

}
