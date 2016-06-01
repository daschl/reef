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

        // Create the Promise which will be completed when the vortex is loaded!
        let mut start_promise = Promise::<(), ()>::new();

        start_promise.future()
            .then(|()| {
                println!("CONNECTED!");
                let val = 42;
                Future::from_ok(format!("My Age is: {}", val))
            })
            .then(|val| {
                println!("Second cb: {}", val);
                Future::from_ok(())
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
