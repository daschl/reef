use std::ptr;
use std::mem;

use task::Continuation;
use task::Task;
use vortex::Vortex;

// Baustellen:
// 1) in der promise schedule implementieren, inklusive speichern des callbacks
// bis der state da ist?


#[derive(Debug,PartialEq)]
pub enum FutureState<T: 'static, E: 'static> {
    Invalid,
    Pending,
    Ok(T),
    Err(E),
}

impl<T, E> FutureState<T, E> {
    pub fn available(&self) -> bool {
        match *self {
            FutureState::Pending => false,
            _ => true,
        }
    }

    pub fn failed(&self) -> bool {
        match *self {
            FutureState::Err(_) => true,
            _ => false,
        }
    }
}

pub struct Promise<T: 'static, E: 'static> {
    future: Option<*mut Future<T, E>>,
    state: FutureState<T, E>,
}

impl<T, E> Promise<T, E> {
    pub fn new() -> Promise<T, E> {
        Promise {
            future: None,
            state: FutureState::Pending,
        }
    }

    pub fn future(&mut self) -> Future<T, E> {
        Future::deferred(self)
    }

    pub fn state(&self) -> &FutureState<T, E> {
        &self.state
    }

    pub fn state_mut(&mut self) -> &mut FutureState<T, E> {
        &mut self.state
    }

    pub fn set_ok(&mut self, value: T) {
        self.state = FutureState::Ok(value);
        self.make_ready();
    }

    pub fn set_err(&mut self, err: E) {
        self.state = FutureState::Err(err);
        self.make_ready();
    }

    fn schedule<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        // self.task = Some(Box::new(f));
    }

    fn make_ready(&mut self) {
        // let f = mem::replace(&mut self.task, None).unwrap();
        // let state = mem::replace(&mut self.state, FutureState::Invalid);
        // Vortex::schedule(Box::new(Continuation::complete(state, f)))
    }
}

pub enum Future<T: 'static, E: 'static> {
    Deferred(*mut Promise<T, E>),
    Ready(FutureState<T, E>),
}

impl<T, E> Future<T, E> {
    pub fn deferred(promise: &mut Promise<T, E>) -> Future<T, E> {
        let mut future = Future::Deferred(promise as *mut Promise<T, E>);
        promise.future = Some(&mut future as *mut Future<T, E>);
        future
    }

    pub fn from_ok(value: T) -> Future<T, E> {
        Future::Ready(FutureState::Ok(value))
    }

    pub fn from_err(error: E) -> Future<T, E> {
        Future::Ready(FutureState::Err(error))
    }

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

    pub fn available(&self) -> bool {
        self.state_as_ref().available()
    }

    pub fn failed(&self) -> bool {
        self.state_as_ref().failed()
    }

    pub fn then<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(T) -> Future<TRES, E> + 'static
    {
        if self.available() {
            match self.state() {
                FutureState::Ok(v) => return f(v),
                FutureState::Err(e) => return Future::from_err(e),
                _ => panic!("This should not happen since we checked the state before."),
            }
        }

        let mut promise = Promise::<TRES, E>::new();
        let mut future = promise.future();

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

    pub fn then_wrapped<F, TRES>(&mut self, f: F) -> Future<TRES, E>
        where F: Fn(FutureState<T, E>) -> Future<TRES, E> + 'static
    {
        if self.available() {
            return f(self.state());
        }


        let mut promise = Promise::<TRES, E>::new();
        let mut future = promise.future();

        self.schedule(move |state| {
            match f(state).state() {
                FutureState::Ok(iv) => promise.set_ok(iv),
                FutureState::Err(ie) => promise.set_err(ie),
                _ => panic!("This should not happen since we checked the state before."),
            }
        });

        future
    }

    fn schedule<F>(&mut self, f: F)
        where F: FnMut(FutureState<T, E>) + 'static
    {
        match *self {
            Future::Ready(_) => Vortex::schedule(Box::new(Continuation::complete(self.state(), f))),
            Future::Deferred(promise) => unsafe { (*promise).schedule(f) },
        }
    }
}

#[cfg(test)]
mod tests {

    use super::{FutureState, Future, Promise};

    #[test]
    fn test_future_from_ok() {
        let future = Future::<i32, i32>::from_ok(42);
        assert_eq!(true, future.available());
        assert_eq!(false, future.failed());
    }

    #[test]
    fn test_future_from_err() {
        let future = Future::<i32, i32>::from_err(-1);
        assert_eq!(true, future.available());
        assert_eq!(true, future.failed());
    }

    #[test]
    fn test_set_promise_state_after_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());

        {
            let future = promise.future();
            assert_eq!(FutureState::Pending, *future.state_as_ref());
            assert_eq!(false, future.available());
            assert_eq!(false, future.failed());
        }

        promise.set_ok(42);
        assert_eq!(FutureState::Ok(42), *promise.state());

        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_as_ref());
            assert_eq!(true, future.available());
            assert_eq!(false, future.failed());
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
        assert_eq!(true, future.available());
        assert_eq!(false, future.failed());
    }

    #[test]
    fn test_set_promise_state_before_future() {
        let mut promise = Promise::<i32, i32>::new();
        assert_eq!(FutureState::Pending, *promise.state());
        promise.set_ok(42);
        {
            let future = promise.future();
            assert_eq!(FutureState::Ok(42), *future.state_as_ref());
            assert_eq!(true, future.available());
            assert_eq!(false, future.failed());
        }
    }

    #[test]
    fn test_correct_states_on_pending() {
        let state = FutureState::Pending::<i32, i32>;
        assert_eq!(false, state.available());
        assert_eq!(false, state.failed());
    }

    #[test]
    fn test_correct_states_on_ok() {
        let state = FutureState::Ok::<_, i32>(1);
        assert_eq!(true, state.available());
        assert_eq!(false, state.failed());
    }

    #[test]
    fn test_correct_states_on_err() {
        let state = FutureState::Err::<i32, _>(-1);
        assert_eq!(true, state.available());
        assert_eq!(true, state.failed());
    }

    #[test]
    fn test_extracting_state_from_ready_future() {
        let mut future = Future::<i32, i32>::from_ok(42);
        assert_eq!(true, future.available());
        assert_eq!(false, future.failed());

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
            .then(|val| {
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
