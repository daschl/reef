#![feature(test)]

extern crate reef;
extern crate test;
extern crate chrono;

use reef::timer::wheel::TimerWheel;
use reef::timer::Timer;
use chrono::{Duration, NaiveDateTime};

#[derive(Debug,PartialEq)]
struct SimpleTimer {
    expires: Duration,
}

impl Timer for SimpleTimer {
    fn expires(&self) -> NaiveDateTime {
        NaiveDateTime::from_timestamp(self.expires.num_seconds(), 0)
    }
}

#[bench]
fn insert_one_timer(b: &mut test::Bencher) {
    let timer = SimpleTimer { expires: Duration::days(2) };
    let mut wheel = TimerWheel::new();
    b.iter(|| {
        wheel.insert(&timer);
    });
}

#[bench]
fn remove_one_timer(b: &mut test::Bencher) {
    let timer = SimpleTimer { expires: Duration::days(2) };
    let mut wheel = TimerWheel::new();
    wheel.insert(&timer);
    b.iter(|| {
        wheel.remove(&timer);
    });
}
