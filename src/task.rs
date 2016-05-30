use future::FutureState;

trait Task {
    fn run(self);
}

struct Continuation<T, E, F> {
    state: FutureState<T, E>,
    func: F,
}

impl<T, E, F> Continuation<T, E, F>
    where F: Fn(FutureState<T, E>)
{
    pub fn new(state: FutureState<T, E>, func: F) -> Continuation<T, E, F> {
        Continuation {
            state: state,
            func: func,
        }
    }
}

impl<T, E, F> Task for Continuation<T, E, F>
    where F: Fn(FutureState<T, E>)
{
    fn run(self) {
        (self.func)(self.state);
    }
}

#[cfg(test)]
mod tests {

    use future::FutureState;
    use super::{Task, Continuation};

    #[test]
    fn should_run_continuation_with_ok() {
        let cont = Continuation::<_, i32, _>::new(FutureState::Ok(1), |state| {
            match state {
                FutureState::Ok(v) => assert_eq!(v, 1),
                _ => assert!(false),
            }
        });

        cont.run();
    }

    #[test]
    fn should_run_continuation_with_err() {
        let cont = Continuation::<i32, _, _>::new(FutureState::Err(-1), |state| {
            match state {
                FutureState::Err(e) => assert_eq!(e, -1),
                _ => assert!(false),
            }
        });

        cont.run();
    }

}
