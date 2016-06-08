use chrono::{NaiveDateTime, Duration};
use linked_list::LinkedList;
use bit_vec::BitVec;
use timer::Timer;
use std::cmp;

// todo: get it working one way or another
// add tests to cover all kinds of stuff on insert, remove and expire
// add benchmarks
// refactor until happy

pub struct TimerWheel<'a, T: 'a> {
    last: Duration,
    next: Duration,
    num_buckets: u32,
    buckets: Vec<LinkedList<&'a T>>,
    non_empty_buckets: BitVec,
}

enum RemoveAction {
    Remove,
    SeekForward,
}

impl<'a, T: 'a> TimerWheel<'a, T>
    where T: Timer
{
    pub fn new() -> TimerWheel<'a, T> {
        let last = Duration::seconds(0);
        let next = Duration::max_value();
        let num_buckets = next.num_seconds().count_ones() + next.num_seconds().count_zeros() + 1;
        let mut buckets = Vec::with_capacity(num_buckets as usize);
        for _ in 0..num_buckets {
            buckets.push(LinkedList::new());
        }
        let non_empty_buckets = BitVec::from_elem(num_buckets as usize, false);

        TimerWheel {
            last: last,
            next: next,
            num_buckets: num_buckets,
            buckets: buckets,
            non_empty_buckets: non_empty_buckets,
        }
    }

    /// Inserts a `Timer` into the `TimerWheel`.
    pub fn insert(&mut self, timer: &'a T) -> bool {
        let timestamp = TimerWheel::<T>::duration_since_epoch(timer.expires());
        let index = self.get_index(timestamp) as usize;

        self.buckets.get_mut(index).expect("Index out of bounds!").push_back(timer);
        self.non_empty_buckets.set(index, true);

        if timestamp < self.next {
            self.next = timestamp;
            true
        } else {
            false
        }
    }

    /// Removes the timer from the `TimerWheel`.
    pub fn remove(&mut self, timer: &'a T) {
        let timestamp = TimerWheel::<T>::duration_since_epoch(timer.expires());
        let index = self.get_index(timestamp) as usize;

        let list = self.buckets.get_mut(index).expect("Index out of bounds!");
        {
            let mut cursor = list.cursor();
            loop {
                let action = match cursor.peek_next() {
                    Some(t) => {
                        if *t as *const T == timer as *const T {
                            RemoveAction::Remove
                        } else {
                            RemoveAction::SeekForward
                        }
                    }
                    None => break,
                };

                match action {
                    RemoveAction::Remove => {
                        cursor.remove();
                        break;
                    }
                    RemoveAction::SeekForward => cursor.seek_forward(1),
                }
            }
        }

        if list.is_empty() {
            self.non_empty_buckets.set(index, false);
        }
    }

    pub fn expire(&mut self, now: NaiveDateTime) -> LinkedList<&'a T> {
        let timestamp = TimerWheel::<T>::duration_since_epoch(now);
        if timestamp < self.last {
            panic!("The timestamp to expire is smaller than last!");
        }

        let mut expired = LinkedList::new();
        let index = self.get_index(timestamp) as usize;

        let skipped = self.non_empty_buckets
            .iter()
            .enumerate()
            .skip(index + 1)
            .collect::<Vec<(usize, bool)>>();
        for (i, _) in skipped {
            let length = expired.len();
            expired.splice(length, self.buckets.get_mut(i).expect("Expected list"));
            self.non_empty_buckets.set(i, false);
        }

        self.last = timestamp;
        self.next = Duration::max_value();

        let mut reinsert = vec![];
        {
            let mut list = self.buckets.get_mut(index).unwrap();
            while !list.is_empty() {
                let timer = list.pop_front().unwrap();
                if timer.expires() <= now {
                    list.push_back(timer);
                } else {
                    reinsert.push(timer);
                }
            }
        }

        for t in &mut reinsert {
            self.insert(t);
        }

        self.non_empty_buckets.set(index, !self.buckets.get(index).unwrap().is_empty());

        if self.next == Duration::max_value() && self.non_empty_buckets.any() {
            let list = self.buckets.get(self.last_non_empty_bucket()).unwrap();
            for t in list.iter() {
                self.next = cmp::min(self.next,
                                     TimerWheel::<T>::duration_since_epoch(t.expires()));
            }
        }

        expired
    }

    /// Returns the `index` for the bucket vector where the given `Duration` is located.
    fn get_index(&self, timestamp: Duration) -> u32 {
        if timestamp <= self.last {
            self.num_buckets - 1
        } else {
            let index = (timestamp.num_seconds() ^ self.last.num_seconds()).leading_zeros();
            debug_assert!(index < self.num_buckets - 1);
            index
        }
    }

    #[inline]
    fn last_non_empty_bucket(&self) -> usize {
        let (idx, _) = self.non_empty_buckets
            .iter()
            .filter(|b| *b == true)
            .enumerate()
            .last()
            .expect("No non-empty bucket found!");
        idx
    }

    /// Returns a `Duration` since epoch for the given time point.
    #[inline]
    fn duration_since_epoch(time_point: NaiveDateTime) -> Duration {
        Duration::seconds(time_point.timestamp())
    }
}

#[cfg(test)]
mod tests {

    use super::TimerWheel;
    use timer::Timer;
    use chrono::{NaiveDateTime, Duration, UTC, TimeZone};

    #[derive(Debug,PartialEq)]
    struct MyTimer {
        expires: Duration,
    }

    impl Timer for MyTimer {
        fn expires(&self) -> NaiveDateTime {
            NaiveDateTime::from_timestamp(self.expires.num_seconds(), 0)
        }
    }

    #[test]
    fn test_insert_and_remove() {
        let timer = MyTimer { expires: Duration::days(3) };
        let mut wheel = TimerWheel::<MyTimer>::new();
        let index = wheel.get_index(Duration::days(3));

        assert_eq!(Some(false), wheel.non_empty_buckets.get(index as usize));
        wheel.insert(&timer);
        assert_eq!(Some(true), wheel.non_empty_buckets.get(index as usize));
        wheel.remove(&timer);
        assert_eq!(Some(false), wheel.non_empty_buckets.get(index as usize));
    }

    #[test]
    fn test_expire() {
        let timer = MyTimer { expires: Duration::days(2) };
        let mut wheel = TimerWheel::<MyTimer>::new();


        wheel.insert(&timer);

        let expired =
            wheel.expire(NaiveDateTime::from_timestamp(Duration::days(1).num_seconds(), 0));

        assert_eq!(true, expired.is_empty());

        let mut expired =
            wheel.expire(NaiveDateTime::from_timestamp(Duration::days(4).num_seconds(), 0));

        assert_eq!(false, expired.is_empty());
        assert_eq!(1, expired.len());
        assert_eq!(timer, *expired.pop_front().unwrap());
    }

    #[test]
    fn test_get_index() {
        let wheel = TimerWheel::<MyTimer>::new();
        let index = wheel.get_index(Duration::seconds(1));
        assert_eq!(63, index);
    }

    #[test]
    fn test_since_epoch() {
        let dt = UTC.ymd(2014, 7, 8).and_hms(9, 10, 11);
        let duration = TimerWheel::<MyTimer>::duration_since_epoch(dt.naive_utc());
        assert_eq!(1404810611, duration.num_seconds());
    }
}
