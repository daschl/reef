pub mod wheel;

use chrono::NaiveDateTime;

pub trait Timer {
    /// Denotes when the timer expires.
    fn expires(&self) -> NaiveDateTime;
}
