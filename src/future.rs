//! Main concurrency building blocks (Futures and Promises).
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
    /// assert_eq!(false, state.is_ready());
    ///
    /// let state = FutureState::Err::<i32, _>(-1);
    /// assert_eq!(true, state.is_ready());
    ///
    /// let state = FutureState::Ok::<_, i32>(1);
    /// assert_eq!(true, state.is_ready());
    /// ```
    #[inline]
    pub fn is_ready(&self) -> bool {
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
/// either the `set_ok` or the `set_err` methods is delivered into the task.
pub struct Promise<T: 'static, E: 'static> {
    future: Option<*mut Future<T, E>>,
    state: FutureState<T, E>,
    task: Option<Box<Task>>,
    task_state: Option<*mut Option<FutureState<T, E>>>,
}

impl<T, E> Promise<T, E> {
    /// Create a new `Promise`.
    ///
    /// **Important:** If you want to move out the future later on, keep in mind to Box it before
    /// calling `future()`, otherwise the unsafe pointers will move and you'll get a segfault. Once
    /// all the unsafe code is removed hopefully this will be handled better.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_ref());
    /// ```
    #[inline]
    pub fn new() -> Promise<T, E> {
        Promise {
            future: None,
            state: FutureState::Pending,
            task: None,
            task_state: None,
        }
    }

    /// Creates a `Future` and links it with this `Promise`.
    ///
    /// **Important:** Make sure that the promise is boxed before calling `future` if you want
    /// to move the promise out of the stack, otherwise the unsafe pointers get screwed and
    /// you end up with a segfaults.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let mut promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_ref());
    ///
    /// let future = promise.future();
    /// assert_eq!(false, future.is_ready());
    /// ```
    #[inline]
    pub fn future(&mut self) -> Future<T, E> {
        Future::deferred(self)
    }

    /// Returns the current state of the `Promise` (which mirrors the state of the `Future`) as a
    /// immutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let mut promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_ref());
    /// ```
    #[inline]
    pub fn state_ref(&self) -> &FutureState<T, E> {
        self.task_state.map_or(&self.state, |ptr| {
            unsafe { (*ptr).as_ref().expect("Task State Pointer is null!") }
        })
    }

    /// Returns the current state of the `Promise` (which mirrors the state of the `Future`) as a
    /// mutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let mut promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_mut());
    /// ```
    #[inline]
    pub fn state_mut(&mut self) -> &mut FutureState<T, E> {
        self.task_state.map_or(&mut self.state, |ptr| {
            unsafe { (*ptr).as_mut().expect("Task State Pointer is null!") }
        })
    }

    /// Sets the value on the Promise (completing the Future), scheduling the stored task as a
    /// side-effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let mut promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_ref());
    ///
    /// let future = promise.future();
    /// assert_eq!(false, future.is_ready());
    ///
    /// promise.set_ok(42);
    /// assert_eq!(FutureState::Ok(42), *promise.state_ref());
    /// assert_eq!(true, future.is_ready());
    /// assert_eq!(false, future.is_err());
    /// ```
    #[inline]
    pub fn set_ok(&mut self, value: T) {
        match self.task_state {
            Some(ptr) => unsafe { *ptr = Some(FutureState::Ok(value)) },
            None => self.state = FutureState::Ok(value),
        };
        self.schedule();
    }

    /// Sets the error on the Promise (completing the Future), scheduling the stored task as a
    /// side-effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{FutureState, Promise};
    ///
    /// let mut promise = Box::new(Promise::<i32, i32>::new());
    /// assert_eq!(FutureState::Pending, *promise.state_ref());
    ///
    /// let future = promise.future();
    /// assert_eq!(false, future.is_ready());
    ///
    /// promise.set_err(-1);
    /// assert_eq!(FutureState::Err(-1), *promise.state_ref());
    /// assert_eq!(true, future.is_ready());
    /// assert_eq!(true, future.is_err());
    /// ```
    #[inline]
    pub fn set_err(&mut self, err: E) {
        match self.task_state {
            Some(ptr) => unsafe { *ptr = Some(FutureState::Err(err)) },
            None => self.state = FutureState::Err(err),
        };
        self.schedule();
    }

    /// Stores the closure in a Task for later scheduling.
    #[inline]
    fn store_task<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        let mut continuation = Box::new(Continuation::deferred(f));
        self.task_state = Some(continuation.state_as_mut());
        self.task = Some(continuation);
    }

    /// If the Task is set on this `Promise` it will be scheduled to run on the Vortex.
    #[inline]
    fn schedule(&mut self) {
        if self.task.is_some() {
            let task = mem::replace(&mut self.task, None)
                .expect("Task is None even if checked right before.");
            Vortex::schedule(task);
        }
    }
}

/// Represents a result which may be completed at some point (or is already).
///
/// If a `Future` is initialized with a `Promise` it starts in a Deferred state. If it is
/// initialized from either a value or an error it immediately goes into `Ready` state. A
/// `Ready` future maintains its own `FutureState` while a `Deferred` one keeps the state
/// inside the linked `Promise`.
pub enum Future<T: 'static, E: 'static> {
    /// The Future is not yet completed and depends on a Promise for state.
    Deferred(*mut Promise<T, E>),
    /// The Future is already completed and carries its own state.
    Ready(FutureState<T, E>),
}

impl<T, E> Future<T, E> {
    /// Create a deferred Future, depending on a Promise.
    ///
    /// This method should not be called directly by the user but instead it is used when
    /// `future()` on the `Promise` is called.
    #[inline]
    fn deferred(promise: &mut Promise<T, E>) -> Future<T, E> {
        let mut future = Future::Deferred(promise as *mut Promise<T, E>);
        promise.future = Some(&mut future as *mut Future<T, E>);
        future
    }

    /// Creates a `Future` which is ready and has been completed with a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::Future;
    ///
    /// let future = Future::<i32, i32>::from_ok(42);
    /// assert_eq!(true, future.is_ready());
    /// assert_eq!(true, future.is_ok());
    /// assert_eq!(false, future.is_err());
    /// ```
    #[inline]
    pub fn from_ok(value: T) -> Future<T, E> {
        Future::Ready(FutureState::Ok(value))
    }

    /// Creates a `Future` which is ready and has been completed with an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::Future;
    ///
    /// let future = Future::<i32, i32>::from_err(-1);
    /// assert_eq!(true, future.is_ready());
    /// assert_eq!(false, future.is_ok());
    /// assert_eq!(true, future.is_err());
    /// ```
    #[inline]
    pub fn from_err(error: E) -> Future<T, E> {
        Future::Ready(FutureState::Err(error))
    }

    /// Returns the underlying `FutureState` as a immutable reference.
    ///
    /// **Note:** depending on if deferred or ready the state is either extracted from the
    /// linked promise or directly from the locally stored state.
    #[inline]
    fn state_ref(&self) -> &FutureState<T, E> {
        match *self {
            Future::Ready(ref state) => &state,
            Future::Deferred(promise) => unsafe {
                promise.as_ref().expect("State in deferred Future is null").state_ref()
            },
        }
    }

    /// Returns the underlying `FutureState` with ownership and invalidates the state on the
    /// called instance.
    ///
    /// **Note:** depending on if deferred or ready the state is either extracted from the
    /// linked promise or directly from the locally stored state.
    #[inline]
    fn state(&mut self) -> FutureState<T, E> {
        match *self {
            Future::Ready(ref mut state) => unsafe { ptr::replace(state, FutureState::Invalid) },
            Future::Deferred(promise) => unsafe {
                let state = promise.as_mut()
                    .expect("State in deferred Future is null")
                    .state_mut();
                mem::replace(state, FutureState::Invalid)
            },
        }
    }

    /// Returns true if this `Future` is ready (either errored or successful).
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::Future;
    ///
    /// let future = Future::<i32, i32>::from_err(-1);
    /// assert_eq!(true, future.is_ready());
    /// ```
    #[inline]
    pub fn is_ready(&self) -> bool {
        self.state_ref().is_ready()
    }

    /// Returns true if this `Future` is ready and has failed.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::Future;
    ///
    /// let future = Future::<i32, i32>::from_err(-1);
    /// assert_eq!(true, future.is_err());
    /// ```
    #[inline]
    pub fn is_err(&self) -> bool {
        self.state_ref().is_err()
    }

    /// Returns true if this `Future` is ready and is successful.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::Future;
    ///
    /// let future = Future::<i32, i32>::from_ok(42);
    /// assert_eq!(true, future.is_ok());
    /// ```
    #[inline]
    pub fn is_ok(&self) -> bool {
        self.state_ref().is_ok()
    }

    /// Attaches a closure to run when the `Future` completes.
    ///
    /// This method is one of the most important ones on the Future. A closure needs to be passed
    /// in that will be called with the result of current Future. It can then perform all kinds
    /// of operations in it but it must return another `Future` where yet another closure can
    /// be attached.
    ///
    /// **Important:** This method will only be called if the Future is successful. If the Future
    /// fails, the error handling closures will be called instead. If your closure needs to react
    /// to both successful and failed results, use `map_state`.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{Future, ok};
    ///
    /// let mut future = ok::<i32, i32>(42);
    /// future
    ///     .map(|val| {
    ///         assert_eq!(42, val);
    ///         ok::<String, i32>(format!("I am {} years old!", val))
    ///     })
    ///     .map(|val| {
    ///         assert_eq!("I am 42 years old!", val);
    ///         ok::<(), i32>(())
    ///     });
    /// ```
    #[inline]
    pub fn map<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(T) -> Future<TRES, E> + 'static
    {
        if self.is_ready() {
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

    /// Attaches a closure to run when the `Future` completes.
    ///
    /// This method is one of the most important ones on the Future. A closure needs to be passed
    /// in that will be called with the resulting state of current Future. It can then perform all
    /// kinds of operations in it but it must return another `Future` where yet another closure can
    /// be attached.
    ///
    /// This method will be called with the `FutureState` in both the successful and failed case.
    /// The methods on the `FutureState` are available to extract the value and check the outcome.
    ///
    /// # Examples
    ///
    /// ```
    /// use reef::future::{Future, ok, err, FutureState};
    ///
    /// let mut future = ok::<i32, i32>(42);
    /// future.map(|val| {
    ///         assert_eq!(42, val);
    ///         err::<i32, i32>(-1)
    ///     })
    ///     .map(|_| {
    ///         // This will never be called!
    ///         assert!(false);
    ///         ok::<(), i32>(())
    ///     })
    ///     .map_state(|state| {
    ///         match state {
    ///             FutureState::Ok(_) => assert!(false),
    ///             FutureState::Err(e) => assert_eq!(-1, e),
    ///             _ => assert!(false),
    ///         }
    ///         ok::<(), i32>(())
    ///     });
    /// ```
    #[inline]
    pub fn map_state<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(FutureState<T, E>) -> Future<TRES, E> + 'static
    {
        if self.is_ready() {
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

    /// Schedules the Future if `Ready` or stores the Closure in the Promise if `Deferred`.
    #[inline]
    fn schedule<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        match *self {
            Future::Ready(_) => Vortex::schedule(Box::new(Continuation::complete(self.state(), f))),
            Future::Deferred(promise) => unsafe { (*promise).store_task(f) },
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
/// assert_eq!(true, future.is_ready());
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
/// assert_eq!(true, future.is_ready());
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
        assert_eq!(true, future.is_ready());
        assert_eq!(false, future.is_err());
    }

    #[test]
    fn test_future_from_err() {
        let future = Future::<i32, i32>::from_err(-1);
        assert_eq!(true, future.is_ready());
        assert_eq!(true, future.is_err());
    }

    #[test]
    fn test_set_promise_state_after_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state_ref());

        {
            let future = promise.future();
            assert_eq!(FutureState::Pending, *future.state_ref());
            assert_eq!(false, future.is_ready());
            assert_eq!(false, future.is_err());
        }

        promise.set_ok(42);
        assert_eq!(FutureState::Ok(42), *promise.state_ref());

        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_ref());
            assert_eq!(true, future.is_ready());
            assert_eq!(false, future.is_err());
        }

    }

    #[test]
    fn test_future_raw_pointer_when_promise_moved() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state_ref());
        promise.set_ok(42);
        move_promise_here(promise);
    }

    fn move_promise_here(mut promise: Promise<i32, i32>) {
        assert_eq!(FutureState::Ok(42), *promise.state_ref());

        let future = promise.future();
        assert_eq!(FutureState::Ok(42), *future.state_ref());
        assert_eq!(true, future.is_ready());
        assert_eq!(false, future.is_err());
    }

    #[test]
    fn test_set_promise_state_before_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state_ref());
        promise.set_ok(42);
        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_ref());
            assert_eq!(true, future.is_ready());
            assert_eq!(false, future.is_err());
        }
    }

    #[test]
    fn test_correct_states_on_pending() {
        let state = FutureState::Pending::<i32, i32>;
        assert_eq!(false, state.is_ok());
        assert_eq!(false, state.is_err());
        assert_eq!(false, state.is_ready());
    }

    #[test]
    fn test_correct_states_on_ok() {
        let state = FutureState::Ok::<_, i32>(1);
        assert_eq!(true, state.is_ok());
        assert_eq!(false, state.is_err());
        assert_eq!(true, state.is_ready());
    }

    #[test]
    fn test_correct_states_on_err() {
        let state = FutureState::Err::<i32, _>(-1);
        assert_eq!(false, state.is_ok());
        assert_eq!(true, state.is_err());
        assert_eq!(true, state.is_ready());
    }

    #[test]
    fn test_extracting_state_from_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        assert_eq!(true, future.is_ready());
        assert_eq!(false, future.is_err());

        let state = future.state();
        assert_eq!(FutureState::Ok(42), state);
    }

    #[test]
    fn test_extracting_state_from_deferred_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state_ref());

        promise.set_ok(42);
        assert_eq!(FutureState::Ok(42), *promise.state_ref());

        {
            let mut future = promise.future();
            let state = future.state();
            assert_eq!(FutureState::Ok(42), state);
            assert_eq!(FutureState::Invalid, *future.state_ref());
        }

        assert_eq!(FutureState::Invalid, *promise.state_ref());
    }

    #[test]
    fn test_then_on_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        future.map(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_ok(22)
            })
            .map(|val| {
                assert_eq!(22, val);
                Future::<(), i32>::from_ok(())
            });
    }

    #[test]
    fn test_then_wrapped_on_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        future.map(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_err(-1)
            })
            .map_state(|state| {
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
        future.map(|val| {
                assert_eq!(42, val);
                Future::<i32, i32>::from_err(-1)
            })
            .map(|_| {
                assert!(false);
                Future::<(), i32>::from_ok(())
            })
            .map_state(|state| {
                match state {
                    FutureState::Ok(_) => assert!(false),
                    FutureState::Err(e) => assert_eq!(-1, e),
                    _ => assert!(false),
                }
                Future::<(), i32>::from_ok(())
            });
    }

}
