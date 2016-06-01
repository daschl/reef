extern crate reef;

use reef::vortex::{Vortex, ControlMsg};
use reef::future::{Promise, ok};

use std::thread;
use std::thread::sleep;
use std::time::Duration;
use std::sync::mpsc::channel;

#[derive(Debug)]
struct User {
    name: &'static str,
    age: i32,
}

fn main() {
    let (tx, rx) = channel();

    let child = thread::spawn(move || {

        // Create the Promise which will be completed when the vortex is loaded!
        let mut start_promise = Promise::<(), ()>::new();

        start_promise.future()
            .then(|_| {
                println!("Connected :)");
                ok(42)
            })
            .then(|age| {
                ok(User {
                    name: "Michael",
                    age: age,
                })
            })
            .then(|user| {
                println!("{:?}", user);
                ok(())
            });


        // Initialize the Vortex
        Vortex::init(rx, start_promise);

        // Start the Vortex (run the event loop)
        Vortex::start();
    });

    sleep(Duration::from_millis(1000));
    tx.send(ControlMsg::Stop).unwrap();
    child.join().unwrap();
}
