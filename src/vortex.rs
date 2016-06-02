use std::collections::vec_deque::VecDeque;
use std::cell::RefCell;
use std::sync::mpsc::Receiver;
use task::Task;
use future::Promise;

thread_local! { static TL_VT: RefCell<Option<Vortex>> = RefCell::new(None) }

pub enum ControlMsg {
    Stop,
}

pub struct Vortex {
    control: RefCell<Receiver<ControlMsg>>,
    task_queue: RefCell<VecDeque<Box<Task>>>,
    start_promise: RefCell<Promise<(), ()>>,
}

impl Vortex {
    pub fn init(control: Receiver<ControlMsg>, start_promise: Promise<(), ()>) {
        let vortex = Vortex {
            control: RefCell::new(control),
            task_queue: RefCell::new(VecDeque::new()),
            start_promise: RefCell::new(start_promise),
        };

        TL_VT.with(|s| {
            let mut s = s.borrow_mut();
            assert!(s.is_none());
            *s = Some(vortex);
        });
    }

    pub fn start() {
        TL_VT.with(|s| {
            let s = s.borrow();
            let v = (*s).as_ref().unwrap();
            v.run();
        });
    }

    #[inline]
    pub fn schedule(task: Box<Task>) {
        TL_VT.with(|s| s.borrow().as_ref().unwrap().push_task(task));
    }

    fn run(&self) {
        // Additional Start logic goes here.

        self.start_promise.borrow_mut().set_ok(());

        loop {
            let control_msg = self.control.borrow().try_recv();
            if control_msg.is_ok() {
                match control_msg.unwrap() {
                    ControlMsg::Stop => break,
                }
            }

            while let Some(mut task) = self.pop_task() {
                task.run();
            }
        }
    }

    #[inline]
    fn pop_task(&self) -> Option<Box<Task>> {
        self.task_queue.borrow_mut().pop_back()
    }

    #[inline]
    fn push_task(&self, task: Box<Task>) {
        self.task_queue.borrow_mut().push_front(task);
    }
}
