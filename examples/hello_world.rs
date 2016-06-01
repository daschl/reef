extern crate reef;

use reef::vortex::Vortex;
use reef::vortex::ControlMsg;
use reef::future::Promise;
use reef::future::Future;

use std::thread;
use std::thread::sleep;
use std::time::Duration;
use std::sync::mpsc::channel;

fn main() {
    let (tx, rx) = channel();

    let child = thread::spawn(move || {
        // Initialize the Vortex
        Vortex::init(rx);

        // This needs to go into the vortex and run the continuation once connected
        let mut promise = Promise::<i32, i32>::new();

        promise.future()
            .then(|val| {
                println!("First cb");
                Future::from_ok(format!("My Age is: {}", val))
            })
            .then(|val| {
                println!("Second cb: {}", val);
                Future::from_ok(())
            });

        promise.set_ok(42);

        // Start the Vortex (run the event loop)
        Vortex::start();
    });

    sleep(Duration::from_millis(1000));
    tx.send(ControlMsg::Stop).unwrap();
    child.join().unwrap();
}
