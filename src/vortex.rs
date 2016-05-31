use std::collections::vec_deque::VecDeque;
use std::cell::RefCell;
use std::sync::mpsc::Receiver;
use task::Task;

thread_local! { pub static TL_VT: RefCell<Option<Vortex>> = RefCell::new(None) }

pub enum ControlMsg {
    Stop,
}

pub struct Vortex {
    control: RefCell<Receiver<ControlMsg>>,
    task_queue: RefCell<VecDeque<Box<Task>>>,
}

impl Vortex {
    pub fn init(control: Receiver<ControlMsg>) {
        let vortex = Vortex {
            control: RefCell::new(control),
            task_queue: RefCell::new(VecDeque::new()),
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

    fn run(&self) {
        loop {
            let control_msg = self.control.borrow().try_recv();
            if control_msg.is_ok() {
                match control_msg.unwrap() {
                    ControlMsg::Stop => break,
                }
            }

            while let Some(mut task) = self.task_queue.borrow_mut().pop_back() {
                task.run();
            }
        }
    }

    fn add_task<T>(&self, task: Box<T>)
        where T: Task + 'static
    {
        self.task_queue.borrow_mut().push_front(task);
    }

    pub fn schedule<T>(task: Box<T>)
        where T: Task + 'static
    {
        TL_VT.with(|s| s.borrow().as_ref().unwrap().add_task(task));
    }
}
