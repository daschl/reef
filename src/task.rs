use future::FutureState;
use std::mem;

pub trait Task {
    fn run(&mut self);
}

pub struct Continuation<T: 'static, E: 'static, F> {
    state: Option<FutureState<T, E>>,
    func: F,
}

impl<T, E, F> Continuation<T, E, F>
    where F: FnMut(FutureState<T, E>)
{
    pub fn complete(state: FutureState<T, E>, func: F) -> Continuation<T, E, F> {
        Continuation {
            state: Some(state),
            func: func,
        }
    }
}

impl<T, E, F> Task for Continuation<T, E, F>
    where F: FnMut(FutureState<T, E>)
{
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
