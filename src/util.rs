use std::ops::Add;

use chrono::{DateTime, Datelike, Duration, NaiveDate, NaiveTime, TimeZone, Timelike, Utc};

use crate::TimeRange;

/** Round a [`DateTime`] or [`NaiveDateTime`] to the nearest Nth minute.

## Examples

### Round to the nearest 5 minutes

```
# use chrono::{DateTime, NaiveDateTime, Utc};
# use time_range::util::round_down_to_minute;
# use anyhow::Result;
# fn main() -> Result<()> {
let date_time = DateTime::parse_from_rfc3339("2024-03-24T01:02:03Z")?;
let rounded = round_down_to_minute(date_time, 5).unwrap();
assert_eq!(rounded, DateTime::parse_from_rfc3339("2024-03-24T01:00:00Z")?);
# Ok(())
# }
```

### Round to the nearest 15 minutes

```
# use chrono::{DateTime, NaiveDateTime, Utc};
# use time_range::util::round_down_to_minute;
# use anyhow::Result;
# fn main() -> Result<()> {
let date_time = DateTime::parse_from_rfc3339("2024-03-24T01:02:03Z")?;
let rounded = round_down_to_minute(date_time, 15).unwrap();
assert_eq!(rounded, DateTime::parse_from_rfc3339("2024-03-24T01:00:00Z")?);
# Ok(())
# }
```
*/
pub fn round_down_to_minute<T>(dt: T, n: u32) -> Option<T>
where
    T: Datelike + Timelike,
{
    let rounded_minute = (dt.minute() / n) * n;

    dt.with_year(dt.year())?
        .with_month(dt.month())?
        .with_day(dt.day())?
        .with_hour(dt.hour())?
        .with_minute(rounded_minute)?
        .with_second(0)
}

/** Round a [`DateTime`] or [`NaiveDateTime`] to the up Nth minute.

## Examples

### Round to the nearest 5 minutes

```
# use chrono::{DateTime, NaiveDateTime, Utc};
# use time_range::util::round_up_to_minute;
# use anyhow::Result;
# fn main() -> Result<()> {
let date_time = DateTime::parse_from_rfc3339("2024-03-24T01:02:03Z")?;
let rounded = round_up_to_minute(date_time, 5).unwrap();
assert_eq!(rounded, DateTime::parse_from_rfc3339("2024-03-24T01:05:00Z")?);
# Ok(())
# }
```

### Round to the nearest 15 minutes

```
# use chrono::{DateTime, NaiveDateTime, Utc};
# use time_range::util::round_up_to_minute;
# use anyhow::Result;
# fn main() -> Result<()> {
let date_time = DateTime::parse_from_rfc3339("2024-03-24T01:02:03Z")?;
let rounded = round_up_to_minute(date_time, 15).unwrap();
assert_eq!(rounded, DateTime::parse_from_rfc3339("2024-03-24T01:15:00Z")?);
# Ok(())
# }
 ```
*/
pub fn round_up_to_minute<T>(dt: T, n: u32) -> Option<T>
where
    T: Datelike + Timelike + PartialEq + Eq + Clone + Add<Duration, Output = T>,
{
    // when T is NaiveDateTime or DateTime<Utc>, the clone is an inexpensive copy
    let down = match round_down_to_minute(dt.clone(), n) {
        Some(d) => d,
        None => return None,
    };

    if dt != down {
        if let Some(up) = Duration::try_minutes(n as i64) {
            return Some(down + up);
        }

        return None;
    }

    Some(down)
}

/// Convert a [`NaiveDate`] to a [`DateTime`] with a time of 00:00:00 in the UTC timezone.
pub fn naive_date_to_utc(date: NaiveDate) -> DateTime<Utc> {
    let time = NaiveTime::from_hms_opt(0, 0, 0)
        .expect("00:00:00 is a considered by some civilizations to be a valid naive  time.");
    Utc.from_utc_datetime(&date.and_time(time))
}

/// Get the relative age of a [`DateTime`] in milliseconds, as measured from the current UTC time
/// at invocation.  If `originated_at` is in the future, the returned age will be 0.
pub fn calculate_age_ms(dt: DateTime<Utc>) -> u64 {
    match (Utc::now() - dt).to_std() {
        Ok(flight_time) => flight_time.as_millis() as u64,
        Err(_) => 0_u64,
    }
}

/// Determine if a timestamp falls between a range defined by `start` and `end`, where `end` can
/// be None. `timestamp` is considered to be within the range if it is greater than or equal to
/// `start` and less than `end` (if `end` is Some). If `end` is None, then the range is considered
/// to be unbounded.  In other words, `start` is inclusive and `end` is exclusive (if defined).
///
pub fn timestamp_in_range_opt(
    timestamp: DateTime<Utc>,
    start: DateTime<Utc>,
    end: Option<DateTime<Utc>>,
) -> bool {
    let end = end.unwrap_or(DateTime::<Utc>::MAX_UTC);
    TimeRange::new(start, end).contains_end_exclusive(&timestamp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use chrono::DateTime;

    #[test]
    fn test_calculate_age_ms() -> Result<()> {
        let originated_at = Utc::now();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let age_ms = calculate_age_ms(originated_at);

        assert!(age_ms >= 10);
        assert!(age_ms < 20);

        Ok(())
    }

    #[test]
    fn test_calculate_age_ms_originated_at_in_future() -> Result<()> {
        let originated_at = Utc::now() + Duration::try_days(1).unwrap();
        let age_ms = calculate_age_ms(originated_at);

        assert_eq!(age_ms, 0);

        Ok(())
    }

    #[test]
    fn test_round_down_to_minute_end_of_hour() -> Result<()> {
        let date_time = DateTime::parse_from_rfc3339("2024-06-21T10:59:59.000000Z")?;
        let result = round_down_to_minute(date_time.naive_utc(), 5).unwrap();
        assert_eq!("2024-06-21 10:55:00", result.to_string());
        Ok(())
    }

    #[test]
    fn test_round_up_to_minute_end_of_hour() -> Result<()> {
        let date_time = DateTime::parse_from_rfc3339("2024-06-21T10:59:59.000000Z")?;
        let result = round_up_to_minute(date_time.naive_utc(), 5).unwrap();
        assert_eq!("2024-06-21 11:00:00", result.to_string());
        Ok(())
    }

    #[test]
    fn test_round_down_to_minute_start_of_hour() -> Result<()> {
        let date_time = DateTime::parse_from_rfc3339("2024-06-21T10:02:02.000000Z")?;
        let result = round_down_to_minute(date_time.naive_utc(), 5).unwrap();
        assert_eq!("2024-06-21 10:00:00", result.to_string());
        Ok(())
    }

    #[test]
    fn test_round_up_to_minute_start_of_hour() -> Result<()> {
        let date_time = DateTime::parse_from_rfc3339("2024-06-21T10:02:02.000000Z")?;
        let result = round_up_to_minute(date_time.naive_utc(), 5).unwrap();
        assert_eq!("2024-06-21 10:05:00", result.to_string());
        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns true if `start` is before
    /// the timestamp and `end` is after the timestamp.
    #[test]
    fn test_timestamp_in_range_opt_positive() -> Result<()> {
        let timestamp = "2024-06-28T01:30:00Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;
        let end = "2024-06-28T02:00:00Z".parse()?;

        assert!(timestamp_in_range_opt(timestamp, start, Some(end)));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns true if `start` is before
    /// the timestamp and `end` is None.
    #[test]
    fn test_timestamp_in_range_opt_positive_no_end() -> Result<()> {
        let timestamp = "2024-06-28T01:30:00Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;

        assert!(timestamp_in_range_opt(timestamp, start, None));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns true if `start` is before
    /// the timestamp and `end` is after the timestamp when timestamp is equal to `start`.
    #[test]
    fn test_timestamp_in_range_opt_positive_equal_to_start() -> Result<()> {
        let timestamp = "2024-06-28T01:00:00Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;

        assert!(timestamp_in_range_opt(timestamp, start, None));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns false if the timestmamp
    /// is equal to `end`.
    #[test]
    fn test_timestamp_in_range_opt_negative_equal_to_end() -> Result<()> {
        let timestamp = "2024-06-28T02:00:00Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;
        let end = "2024-06-28T02:00:00Z".parse()?;

        assert!(!timestamp_in_range_opt(timestamp, start, Some(end)));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns false if the timestamp is
    /// before `start`.
    #[test]
    fn test_timestamp_in_range_opt_negative_before_start() -> Result<()> {
        let timestamp = "2024-06-28T00:59:59Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;

        assert!(!timestamp_in_range_opt(timestamp, start, None));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns false if the timestamp is
    /// before `start` and `end` is not None.
    #[test]
    fn test_timestamp_in_range_opt_negative_before_start_with_end() -> Result<()> {
        let timestamp = "2024-06-28T00:59:59Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;
        let end = "2024-06-28T02:00:00Z".parse()?;

        assert!(!timestamp_in_range_opt(timestamp, start, Some(end)));

        Ok(())
    }

    /// Given a timestamp, test that [`timestamp_in_range_opt`] returns false if the timestamp is
    /// after `end`.
    #[test]
    fn test_timestamp_in_range_opt_negative_after_end() -> Result<()> {
        let timestamp = "2024-06-28T02:00:01Z".parse()?;
        let start = "2024-06-28T01:00:00Z".parse()?;
        let end = "2024-06-28T02:00:00Z".parse()?;

        assert!(!timestamp_in_range_opt(timestamp, start, Some(end)));

        Ok(())
    }
}
