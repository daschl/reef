use chrono::{NaiveDateTime, Duration};
use linked_list::LinkedList;
use bit_set::BitSet;
use timer::Timer;

struct TimerWheel<'a, T: 'a> {
    last: Duration,
    next: Duration,
    num_buckets: u32,
    buckets: Vec<LinkedList<&'a T>>,
    non_empty_buckets: BitSet,
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
        let non_empty_buckets = BitSet::with_capacity(num_buckets as usize);

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
        self.non_empty_buckets.insert(index);

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
        let pos = list.iter()
            .position(|t| *t as *const T == timer as *const T)
            .expect("Position not found!");
        list.remove(pos);
        if list.is_empty() {
            self.non_empty_buckets.remove(index);
        }
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

    #[derive(Debug)]
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

        assert!(!wheel.non_empty_buckets.contains(index as usize));
        wheel.insert(&timer);
        assert!(wheel.non_empty_buckets.contains(index as usize));

        wheel.remove(&timer);
        assert!(!wheel.non_empty_buckets.contains(index as usize));
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
