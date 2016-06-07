mod wheel;

use chrono::NaiveDateTime;

trait Timer {
    /// Denotes when the timer expires.
    fn expires(&self) -> NaiveDateTime;
}
