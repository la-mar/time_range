use std::fmt::Debug;

use chrono::{DateTime, Datelike, Duration, NaiveDateTime, TimeZone, Timelike, Utc};

use crate::{convert, error::Error, util, DateRange};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// The start_at and end_at bounds of the TimeRange are both inclusive.
///
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct TimeRange {
    start_at: DateTime<Utc>,
    end_at: DateTime<Utc>,
}

impl Debug for TimeRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TimeRange[{} -> {}]", self.start_at, self.end_at)
    }
}

impl TimeRange {
    /// Create a new TimeRange from a start and end datetime.
    ///
    /// Args:
    ///     start_at: The start of the time range (inclusive).
    ///     end_at: The end of the time range (inclusive).
    ///
    /// **Examples:**
    ///
    /// ```rust
    /// use time_range::{TimeRange, Utc, TimeZone};
    ///
    /// let start_at = Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap();
    /// let end_at = Utc.ymd(2024, 6, 13).and_hms(11, 59, 59);
    /// let time_range = TimeRange::new(start_at, end_at);
    /// println!("{:#?}", time_range);
    /// // TimeRange[2024-06-01T12:00:00+00:00 -> 2024-06-13T11:59:59+00:00]
    /// ```
    ///
    pub fn new(start_at: impl Into<DateTime<Utc>>, end_at: impl Into<DateTime<Utc>>) -> Self {
        TimeRange {
            start_at: start_at.into(),
            end_at: end_at.into(),
        }
    }

    /// Parse the given ISO-8601 formatted string into a TimeRange. The start and end
    /// time should be delimited by a forward slash ("/"). Start/end must be formatted as
    /// datetime.  Date-only formats and naive datetimes are not supported.
    ///
    /// Args:
    ///     ranges (str): delimited date ranges (e.g. `"2024-07-01T12:00:00+00:00/2024-07-02T11:59:59+00:00"`)
    ///
    /// Returns:
    ///     TimeRange: parsed time range
    ///
    /// **Examples:**
    ///
    /// ```rust
    /// use time_range::TimeRange;
    ///
    /// let time_range = TimeRange::parse("2024-07-01T12:00:00+00:00/2024-07-02T11:59:59+00:00").unwrap();
    /// println!("{:#?}", time_range);
    /// // TimeRange[2024-07-01T12:00:00+00:00 -> 2024-07-02T11:59:59+00:00]
    /// ```
    ///
    pub fn parse(s: &str) -> Result<TimeRange, Error> {
        let mut elements = s.split('/');

        let start_at = match elements.next() {
            Some(s) => match DateTime::parse_from_rfc3339(s) {
                Ok(dt) => dt,
                Err(err) => {
                    return Err(Error::ParseFieldError {
                        field_name: "start_at",
                        value: s.into(),
                        source: err,
                    })
                }
            },
            None => {
                return Err(Error::MissingValue {
                    field_name: "start_at",
                })
            }
        };
        let end_at = match elements.next() {
            Some(s) => match DateTime::parse_from_rfc3339(s) {
                Ok(dt) => dt,
                Err(err) => {
                    return Err(Error::ParseFieldError {
                        field_name: "end_at",
                        value: s.into(),
                        source: err,
                    })
                }
            },
            None => {
                return Err(Error::MissingValue {
                    field_name: "end_at",
                })
            }
        };

        Ok(TimeRange::new(start_at, end_at))
    }

    pub fn start_at(&self) -> &DateTime<Utc> {
        &self.start_at
    }

    /// Get the start of the time range as a number of seconds since the UNIX epoch.
    pub fn start_timestamp(&self) -> i64 {
        self.start_at.timestamp()
    }

    pub fn start_year(&self) -> u32 {
        // These component accessors are defined here in the struct to avoid callers needing to
        // import the chrono DateLike and TimeLike traits.
        self.start_at.year() as u32
    }

    pub fn start_month(&self) -> u32 {
        self.start_at.month()
    }

    pub fn start_day(&self) -> u32 {
        self.start_at.day()
    }

    pub fn start_hour(&self) -> u32 {
        self.start_at.hour()
    }

    pub fn start_minute(&self) -> u32 {
        self.start_at.minute()
    }

    pub fn end_at(&self) -> &DateTime<Utc> {
        &self.end_at
    }

    /// Get the end of the time range as a number of seconds since the UNIX epoch.
    pub fn end_timestamp(&self) -> i64 {
        self.end_at.timestamp()
    }

    pub fn end_year(&self) -> u32 {
        self.end_at.year() as u32
    }

    pub fn end_month(&self) -> u32 {
        self.end_at.month()
    }

    pub fn end_day(&self) -> u32 {
        self.end_at.day()
    }

    pub fn end_hour(&self) -> u32 {
        self.end_at.hour()
    }

    pub fn end_minute(&self) -> u32 {
        self.end_at.minute()
    }

    pub fn to_tuple(self) -> (DateTime<Utc>, DateTime<Utc>) {
        (self.start_at, self.end_at)
    }

    pub fn start_at_string(&self) -> String {
        convert::dt_to_string(&self.start_at)
    }

    pub fn end_at_string(&self) -> String {
        convert::dt_to_string(&self.end_at)
    }

    /// Check if the given datetime falls within the time_range. Both ends are inclusive.
    pub fn contains(&self, dt: &DateTime<Utc>) -> bool {
        self.start_at() <= dt && dt <= self.end_at()
    }

    /// Check if the given datetime falls within the time_range. Start is inclusive, end is exclusive.
    pub fn contains_end_exclusive(&self, dt: &DateTime<Utc>) -> bool {
        self.start_at() <= dt && dt < self.end_at()
    }

    /// Check if the time_range encapsulates `other`. Both ends are inclusive.
    ///
    ///```ignore
    /// Example (encapsulating):
    ///
    ///     +---------+--------+
    ///     |         A        |
    ///     +---------+--------+
    ///          +----+----+
    ///          |    B    |
    ///          +----+----+
    ///
    ///      A.encapsulates(B) => true
    ///
    ///
    /// Example (overlapping):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                  +--------+--------+
    ///                  |        B        |
    ///                  +--------+--------+
    ///
    ///      A.encapsulates(B) => false
    ///
    ///
    /// Example (equal):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///     +--------+--------+
    ///     |        B        |
    ///     +--------+--------+
    ///
    ///      A.encapsulates(B) => true
    ///
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     A.encapsulates(B) => false
    ///```
    pub fn encapsulates(&self, other: &TimeRange) -> bool {
        self.start_at() <= other.start_at() && self.end_at() >= other.end_at()
    }

    /// Check if any part of the time_range overlaps with `other`. Both ends are inclusive.
    ///
    /// Example (overlapping):
    ///```ignore
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                 +--------+--------+
    ///                 |        B        |
    ///                 +--------+--------+
    ///
    ///     A.intersects(B) => true
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     A.intersects(B) => false
    ///```
    pub fn intersects(&self, other: &TimeRange) -> bool {
        // (StartA <= EndB) and (EndA >= StartB)
        self.start_at() <= other.end_at() && self.end_at() >= other.start_at()
    }

    /// Check if any part of the time_range overlaps with `other`. Both ends are exclusive.
    ///```ignore
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                 +--------+--------+
    ///                 |        B        |
    ///                 +--------+--------+
    ///
    ///     A.intersects(B) => true
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     A.intersects(B) => false
    ///
    ///     +---------+--------+
    ///     |         A        |
    ///     +---------+--------+
    ///                        +----+----+
    ///                        |    B    |
    ///                        +----+----+
    ///     A.intersects(B) => false
    ///
    ///               +---------+--------+
    ///               |         A        |
    ///               +---------+--------+
    ///     +----+----+
    ///     |    B    |
    ///     +----+----+
    ///
    ///      A.intersects(B) => false
    /// ```
    pub fn intersects_exclusive(&self, other: &TimeRange) -> bool {
        // (StartA < EndB) and (EndA > StartB)
        self.start_at() < other.end_at() && self.end_at() > other.start_at()
    }

    /// Return the region where time_range overlaps with `other` if the two ranges have
    /// any overlap. Both ends are inclusive.  Returns `None` if the two ranges are disjoint.
    ///
    ///```ignore
    /// Example (overlapping):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                 +--------+--------+
    ///                 |        B        |
    ///                 +--------+--------+
    ///
    ///     C = A.intersection(B)
    ///
    ///                 +--+--+
    ///                 |  C  |
    ///                 +--+--+
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     C = A.intersection(B)
    ///
    ///     None
    ///```
    pub fn intersection(&self, other: &TimeRange) -> Option<TimeRange> {
        if self.intersects(other) {
            Some(TimeRange::new(
                *self.start_at().max(other.start_at()),
                *self.end_at().min(other.end_at()),
            ))
        } else {
            None
        }
    }

    /// Merge the time_range with `other` if the two ranges have any overlap.
    /// Both ends are inclusive.  Returns `None` if the two ranges are disjoint.
    ///
    ///```ignore
    /// Example (overlapping):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                 +--------+--------+
    ///                 |        B        |
    ///                 +--------+--------+
    ///
    ///     C = A.union(B)
    ///
    ///     +--------------+--------------+
    ///     |              C              |
    ///     +--------------+--------------+
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     C = A.union(B)
    ///
    ///     None
    ///```
    pub fn union(&self, other: &TimeRange) -> Option<TimeRange> {
        if self.intersects(other) {
            Some(TimeRange::new(
                *self.start_at().min(other.start_at()),
                *self.end_at().max(other.end_at()),
            ))
        } else {
            None
        }
    }

    /// Return the regions where time_range and `other` do not overlap, if the two ranges
    /// have any overlap. Both ends are inclusive.
    ///
    /// Returns `None` if the two ranges are disjoint or if the ranges are equal.
    ///
    ///```ignore
    /// Example (overlapping):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                  +--------+--------+
    ///                  |        B        |
    ///                  +--------+--------+
    ///
    ///      A.difference(B)
    ///
    ///     +-----+-----+
    ///     |     C     |
    ///     +-----+-----+
    ///
    ///
    /// Example (encapsulating):
    ///
    ///     +---------+--------+
    ///     |         A        |
    ///     +---------+--------+
    ///          +----+----+
    ///          |    B    |
    ///          +----+----+
    ///
    ///
    ///      A.difference(B)
    ///
    ///     +-+-+           +-+-+
    ///     | C |           | D |
    ///     +-+-+           +-+-+
    ///
    ///
    /// Example (adjacent):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                       +--------+--------+
    ///                       |        B        |
    ///                       +--------+--------+
    ///
    ///      A.difference(B)
    ///
    ///     +--------+-------+
    ///     |        A       |
    ///     +--------+-------+
    ///
    ///
    /// Example (equal):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///     +--------+--------+
    ///     |        B        |
    ///     +--------+--------+
    ///
    ///      A.difference(B)
    ///
    ///     None
    ///
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     A.difference(B)
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///```
    pub fn difference(&self, other: &TimeRange) -> Option<Vec<TimeRange>> {
        if self.intersects(other) {
            let mut result = Vec::new();
            if self.start_at() < other.start_at() {
                result.push(TimeRange::new(*self.start_at(), *other.start_at()));
            }
            if self.end_at() > other.end_at() {
                result.push(TimeRange::new(*other.end_at(), *self.end_at()));
            }

            match result.is_empty() {
                true => None, // return None no results (happens when ranges are equal)
                false => Some(result),
            }
        } else {
            None
        }
    }

    /// Return the regions where time_range and `other` do not overlap, if the two ranges
    /// have any overlap. Both ends are inclusive.
    ///
    /// Returns `None` if the two ranges are disjoint or if the ranges are equal.
    ///```ignore
    /// Example (overlapping):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                  +--------+--------+
    ///                  |        B        |
    ///                  +--------+--------+
    ///
    ///      A.symmetric_difference(B)
    ///
    ///     +-----+-----+      +-----+-----+
    ///     |     C     |      |     D     |
    ///     +-----+-----+      +-----+-----+
    ///
    ///
    /// Example (encapsulating):
    ///
    ///     +---------+--------+
    ///     |         A        |
    ///     +---------+--------+
    ///          +----+----+
    ///          |    B    |
    ///          +----+----+
    ///
    ///
    ///      A.symmetric_difference(B)
    ///
    ///     +-+-+           +-+-+
    ///     | C |           | D |
    ///     +-+-+           +-+-+
    ///
    ///
    /// Example (a end equal to b start):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                       +--------+--------+
    ///                       |        B        |
    ///                       +--------+--------+
    ///
    ///      A.symmetric_difference(B)
    ///
    ///     +--------+-------+ +--------+--------+
    ///     |        C       | |        D        |
    ///     +--------+-------+ +--------+--------+
    ///
    ///
    /// Example (equal):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///     +--------+--------+
    ///     |        B        |
    ///     +--------+--------+
    ///
    ///      A.symmetric_difference(B)
    ///
    ///     None
    ///
    ///
    /// Example (disjoint):
    ///
    ///     +--------+--------+
    ///     |        A        |
    ///     +--------+--------+
    ///                            +--------+--------+
    ///                            |        B        |
    ///                            +--------+--------+
    ///
    ///     A.symmetric_difference(B)
    ///
    ///     None
    ///```
    pub fn symmetric_difference(&self, other: &TimeRange) -> Option<Vec<TimeRange>> {
        if self.intersects(other) {
            let mut result = Vec::new();
            if let Some(mut v) = self.difference(other) {
                result.append(&mut v);
            }
            if let Some(mut v) = other.difference(self) {
                result.append(&mut v);
            }

            match result.is_empty() {
                true => None, // return None no results (happens when ranges are equal)
                false => {
                    // sort diffs into ascending order by start_at
                    result.sort_by(|a, b| a.start_at().cmp(b.start_at()));
                    Some(result)
                }
            }
        } else {
            None
        }
    }

    /// Checks if the range is valid.  A range is valid if its start_at is before its end_at.
    pub fn is_valid(&self) -> bool {
        self.start_at() <= self.end_at()
    }

    /// Get the width of the range as a `chrono::Duration`.
    pub fn duration(&self) -> Duration {
        *self.end_at() - *self.start_at()
    }

    /// Returns an iterator with step width equal to provided `chrono::Duration`. If `TimeRange`
    /// is not evenly divisible by the given `chrono::Duration` and `return_partial` is set to false,
    /// the last element returned by the iterator will be the last full step fully contained within
    /// the time range.  If `return_partial` is set to true, the last element returned by the iterator
    /// will be a partial time range with a width that is less than the specified step size.  If the
    /// specified step size is greater than or equal to the width of the time range, the iterator will
    /// return a single element with the entire time range if `return_partial` is set to true,
    /// otherwise the iterator will return no elements.
    ///
    /// ### Examples
    ///
    /// TimeRange evenly divisible by the step size:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{TimeRange, Duration};
    /// let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z")?;
    ///
    /// let iter = range.iter(Duration::minutes(5), true);
    /// let items = iter.collect::<Vec<TimeRange>>();
    ///
    /// let expected = vec![
    ///     TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z")?,
    /// ];
    ///
    /// assert_eq!(items, expected);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// TimerRange not evenly divisible by the step size, `return_partial` is set to false:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{TimeRange, Duration};
    /// let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:17:00Z")?;
    ///
    /// let iter = range.iter(Duration::minutes(5), false);
    /// let items = iter.collect::<Vec<TimeRange>>();
    ///
    /// let expected = vec![
    ///     TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z")?,
    /// ];
    ///
    /// assert_eq!(items, expected);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// TimerRange not evenly divisible by the step size, `return_partial` is set to true:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{TimeRange, Duration};
    /// let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:17:00Z")?;
    ///
    /// let iter = range.iter(Duration::minutes(5), true);
    /// let items = iter.collect::<Vec<TimeRange>>();
    ///
    /// let expected = vec![
    ///     TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z")?,
    ///     TimeRange::parse("2024-07-23T10:15:00Z/2024-07-23T10:17:00Z")?,
    /// ];
    ///
    /// assert_eq!(items, expected);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Step size is >= to TimeRange width, `return_partial` is set to false:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{TimeRange, Duration};
    /// let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z")?;
    ///
    /// let iter = range.iter(Duration::minutes(20), false);
    /// let items = iter.collect::<Vec<TimeRange>>();
    ///
    /// let expected = vec![];
    ///
    /// assert_eq!(items, expected);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Step size is >= to TimeRange width, `return_partial` is set to true:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{TimeRange, Duration};
    /// let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z")?;
    ///
    /// let iter = range.iter(Duration::minutes(20), true);
    /// let items = iter.collect::<Vec<TimeRange>>();
    ///
    /// let expected = vec![
    ///     TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z")?,
    /// ];
    ///
    /// assert_eq!(items, expected);
    /// # Ok(())
    /// # }
    /// ```
    pub fn iter(&self, step: Duration, return_partial: bool) -> TimeRangeIter<'_> {
        TimeRangeIter::new(self, step, return_partial)
    }

    /// Create a TimeRange from two epoch timestamps in nanoseconds.
    pub fn from_nanos(start_at: i64, end_at: i64) -> TimeRange {
        TimeRange::new(Utc.timestamp_nanos(start_at), Utc.timestamp_nanos(end_at))
    }

    pub fn into_nanos(self) -> Result<(i64, i64), Error> {
        let start = match self.start_at.timestamp_nanos_opt() {
            Some(n) => n,
            None => return Err(Error::NanosOutOfRange(self.start_at.to_string())),
        };

        let end = match self.end_at.timestamp_nanos_opt() {
            Some(n) => n,
            None => return Err(Error::NanosOutOfRange(self.end_at.to_string())),
        };

        Ok((start, end))
    }
}

impl std::fmt::Display for TimeRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.start_at_string(), self.end_at_string())
    }
}

impl From<(DateTime<Utc>, DateTime<Utc>)> for TimeRange {
    fn from(t: (DateTime<Utc>, DateTime<Utc>)) -> Self {
        TimeRange::new(t.0, t.1)
    }
}

impl From<TimeRange> for (DateTime<Utc>, DateTime<Utc>) {
    fn from(t: TimeRange) -> Self {
        t.to_tuple()
    }
}

impl From<(NaiveDateTime, NaiveDateTime)> for TimeRange {
    fn from(t: (NaiveDateTime, NaiveDateTime)) -> Self {
        TimeRange::new(Utc.from_utc_datetime(&t.0), Utc.from_utc_datetime(&t.1))
    }
}

impl From<TimeRange> for (NaiveDateTime, NaiveDateTime) {
    fn from(t: TimeRange) -> Self {
        (t.start_at().naive_utc(), t.end_at().naive_utc())
    }
}

impl From<DateRange> for TimeRange {
    fn from(t: DateRange) -> Self {
        let start = util::naive_date_to_utc(*t.start_at());
        let end = util::naive_date_to_utc(*t.end_at());

        TimeRange::new(start, end)
    }
}

pub struct TimeRangeIter<'a> {
    range: &'a TimeRange,
    step: Duration,
    last: DateTime<Utc>,
    return_partial: bool,
}

impl<'a> TimeRangeIter<'a> {
    fn new(range: &'a TimeRange, step: Duration, return_partial: bool) -> TimeRangeIter<'a> {
        TimeRangeIter {
            range,
            step,
            last: range.start_at,
            return_partial,
        }
    }
}

impl<'a> Iterator for TimeRangeIter<'a> {
    type Item = TimeRange;

    fn next(&mut self) -> Option<Self::Item> {
        let end = self.last + self.step;
        if self.range.contains(&end) {
            let range = TimeRange::new(self.last, end);
            self.last = end;
            return Some(range);
        } else if self.return_partial && (end - self.range.end_at) < self.step {
            // if the current step caused end to be past the end of the range, return the last element
            // as a partial range, meaning the width of the range is less than the step width.
            let range = TimeRange::new(self.last, self.range.end_at);
            self.last = end;
            return Some(range);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::{NaiveDate, TimeZone, Timelike};
    use pretty_assertions::assert_eq;
    use test_log::test;
    use tracing::debug;

    #[test]
    fn test_parse() {
        let ranges = [
            // "2024-06-01/2024-06-02", // dates (not supported)
            // "2024-06-01T00:00:00/2024-06-02T00:00:02", // naive (not supported)
            "2024-06-01T00:00:00Z/2024-06-02T00:00:02Z", // utc use_z
            "2024-06-01T00:00:00+00:00/2024-06-02T00:00:02+00:00", // utc
            "2024-05-31T19:00:00-05:00/2024-06-01T19:00:02-05:00", // same local timezone
            "2024-05-31T19:00:00-05:00/2024-06-02T00:00:02+00:00", // mixed timezones
        ];

        for s in ranges {
            debug!("Parsing: {}", s);
            let time_range = TimeRange::parse(s).unwrap();

            debug!("time_range= {}", time_range);
            assert_eq!(
                time_range.start_at,
                Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
                "start_at mismatch"
            );
            assert_eq!(
                time_range.end_at,
                Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2).unwrap(),
                "end_at mismatch"
            );
        }
    }

    #[test]
    fn test_display() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2).unwrap(),
        );
        assert_eq!(
            format!("{time_range}"),
            "2024-06-01T00:00:00Z/2024-06-02T00:00:02Z",
            "display mismatch"
        );
    }

    #[test]
    fn test_display_microseconds() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0)
                .unwrap()
                .with_nanosecond(1000)
                .unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2)
                .unwrap()
                .with_nanosecond(1000)
                .unwrap(),
        );
        debug!("time_range= {}", time_range);

        assert_eq!(
            format!("{time_range}"),
            "2024-06-01T00:00:00.000001Z/2024-06-02T00:00:02.000001Z",
            "display mismatch"
        );
    }

    #[test]
    fn test_display_milliseconds() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0)
                .unwrap()
                .with_nanosecond(1000000)
                .unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2)
                .unwrap()
                .with_nanosecond(1000000)
                .unwrap(),
        );
        debug!("time_range= {}", time_range);

        assert_eq!(
            format!("{time_range}"),
            "2024-06-01T00:00:00.001Z/2024-06-02T00:00:02.001Z",
            "display mismatch"
        );
    }

    #[test]
    fn test_display_nanos() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0)
                .unwrap()
                .with_nanosecond(1)
                .unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2)
                .unwrap()
                .with_nanosecond(1)
                .unwrap(),
        );
        debug!("time_range= {}", time_range);

        assert_eq!(
            format!("{time_range}"),
            "2024-06-01T00:00:00.000000001Z/2024-06-02T00:00:02.000000001Z",
            "display mismatch"
        );
    }

    #[test]
    fn test_is_valid() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2).unwrap(),
        );

        assert!(time_range.is_valid());
    }

    #[test]
    fn test_not_valid() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 2).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
        );

        assert!(!time_range.is_valid());
    }

    #[test]
    fn test_duration() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap(),
        );

        assert!(time_range.duration() == Duration::try_seconds(2).unwrap());
    }

    #[test]
    fn test_duration_invalid_order() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
        );

        assert!(time_range.duration() == Duration::try_seconds(-2).unwrap());
    }

    #[test]
    fn test_from_tuple() {
        let time_range = TimeRange::from((
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap(),
        ));

        assert!(time_range.start_at == Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap());
        assert!(time_range.end_at == Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap());
    }

    #[test]
    fn test_into_tuple() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap(),
        );

        let (start_at, end_at): (DateTime<Utc>, DateTime<Utc>) = time_range.into();

        assert!(start_at == Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap());
        assert!(end_at == Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap());
    }

    #[test]
    fn test_into_naive_tuple() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 2).unwrap(),
        );

        let (start_at, end_at): (NaiveDateTime, NaiveDateTime) = time_range.into();

        assert!(
            start_at
                == NaiveDate::from_ymd_opt(2024, 6, 1)
                    .unwrap()
                    .and_hms_opt(0, 0, 0)
                    .unwrap()
        );
        assert!(
            end_at
                == NaiveDate::from_ymd_opt(2024, 6, 1)
                    .unwrap()
                    .and_hms_opt(0, 0, 2)
                    .unwrap()
        );
    }

    #[test]
    fn test_from_nanos() {
        let time_range = TimeRange::from_nanos(
            1648083600000000000_i64, // 2022-03-24 01:00:00
            1648085400000000000_i64, // 2022-03-24 01:30:00
        );

        assert!(
            time_range.start_at == Utc.with_ymd_and_hms(2022, 3, 24, 1, 0, 0).unwrap(),
            "start_at mismatch"
        );
        assert!(
            time_range.end_at == Utc.with_ymd_and_hms(2022, 3, 24, 1, 30, 0).unwrap(),
            "end_at mismatch"
        );
    }

    #[test]
    fn test_into_nanos() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2022, 3, 24, 1, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2022, 3, 24, 1, 30, 0).unwrap(),
        );

        let (start_at, end_at) = time_range.into_nanos().unwrap();
        assert!(
            start_at == 1648083600000000000_i64,
            "start_at nanos must match"
        );
        assert!(end_at == 1648085400000000000_i64, "end_at nanos must match");
    }

    #[test]
    fn test_from_secs() {
        let date_range = DateRange::from_secs(
            1648083600_i64, // 2022-03-24 01:00:00
            1648085400_i64, // 2022-03-24 01:30:00
        )
        .unwrap();

        assert!(date_range.start_at() == &NaiveDate::from_ymd_opt(2022, 3, 24).unwrap());
        assert!(date_range.end_at() == &NaiveDate::from_ymd_opt(2022, 3, 24).unwrap());
    }

    #[test]
    fn test_from_date_range() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2024, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2024, 6, 2).unwrap(),
        );

        let time_range = TimeRange::from(date_range);

        assert!(time_range.start_at == Utc.with_ymd_and_hms(2024, 6, 1, 0, 0, 0).unwrap());
        assert!(time_range.end_at == Utc.with_ymd_and_hms(2024, 6, 2, 0, 0, 0).unwrap());
    }

    #[test]
    fn test_to_timestamps() {
        let date_range = TimeRange::new(
            Utc.with_ymd_and_hms(2022, 11, 21, 1, 1, 1).unwrap(),
            Utc.with_ymd_and_hms(2022, 11, 22, 2, 2, 2).unwrap(),
        );

        assert_eq!(date_range.start_timestamp(), 1668992461_i64);
        assert_eq!(date_range.end_timestamp(), 1669082522_i64);
    }
}

#[cfg(test)]
mod test_pairwise_ops {
    use super::*;
    use chrono::TimeZone;
    use pretty_assertions::assert_eq;
    use test_log::test;
    use tracing::trace;

    fn time_range_a() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )
    }

    // A is disjoint from B
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //                             +--------+--------+
    //                             |        B        |
    //                             +--------+--------+
    //
    fn time_range_a_disjoint_b() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 14, 0, 0, 1).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 16, 0, 0, 0).unwrap(),
        )
    }

    // A is adjacent to B
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //                        +--------+--------+
    //                        |        B        |
    //                        +--------+--------+
    //
    fn time_range_a_adjacent_b() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 1).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 14, 0, 0, 0).unwrap(),
        )
    }

    // B is adjacent to A
    //
    //                        +--------+--------+
    //                        |        A        |
    //                        +--------+--------+
    //     +--------+--------+
    //     |        B        |
    //     +--------+--------+
    //
    fn time_range_b_adjacent_a() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 8, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 9, 23, 59, 59).unwrap(),
        )
    }

    // A end == B start
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //                       +--------+--------+
    //                       |        B        |
    //                       +--------+--------+
    //
    fn time_range_a_end_eq_b_start() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 14, 0, 0, 0).unwrap(),
        )
    }

    // B end == A start
    //
    //                       +--------+--------+
    //                       |        A        |
    //                       +--------+--------+
    //     +--------+--------+
    //     |        B        |
    //     +--------+--------+
    //
    fn time_range_b_end_eq_a_start() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 8, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
        )
    }

    // A partially overlaps B
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //                  +--------+--------+
    //                  |        B        |
    //                  +--------+--------+
    //
    fn time_range_a_partially_overlaps_b() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        )
    }

    // B partially overlaps A
    //
    //                  +--------+--------+
    //                  |        A        |
    //                  +--------+--------+
    //     +--------+--------+
    //     |        B        |
    //     +--------+--------+
    //
    fn time_range_b_partially_overlaps_a() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
        )
    }

    // A encapsulates B
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //       +------+------+
    //       |      B      |
    //       +------+------+
    //
    fn time_range_a_encapsulates_b() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            // Utc.with_ymd_and_hms(2024, 6, 11, 12, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 12, 0, 0).unwrap(),
        )
    }

    // B encapsulates A
    //
    //       +------+------+
    //       |      A      |
    //       +------+------+
    //     +--------+--------+
    //     |        B        |
    //     +--------+--------+
    //
    fn time_range_b_encapsulates_a() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        )
    }

    // A encapsulates B, starts are equal
    //
    //     +-----------+-----------+
    //     |           A           |
    //     +-----------+-----------+
    //     +--------+--------+
    //     |        B        |
    //     +--------+--------+
    //
    fn time_range_a_encapsulates_b_starts_equal() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
        )
    }

    // B encapsulates A, starts are equal
    //
    //     +--------+--------+
    //     |        A        |
    //     +--------+--------+
    //     +-----------+-----------+
    //     |           B           |
    //     +-----------+-----------+
    //
    fn time_range_b_encapsulates_a_starts_equal() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        )
    }

    // A encapsulates B, ends are equal
    //
    //     +-----------+-----------+
    //     |           A           |
    //     +-----------+-----------+
    //           +--------+--------+
    //           |        B        |
    //           +--------+--------+
    //
    fn time_range_a_encapsulates_b_ends_equal() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )
    }

    // B encapsulates A, ends are equal
    //
    //           +--------+--------+
    //           |        A        |
    //           +--------+--------+
    //     +-----------+-----------+
    //     |           B           |
    //     +-----------+-----------+
    //
    fn time_range_b_encapsulates_a_ends_equal() -> TimeRange {
        TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )
    }

    // All scenarios:
    //
    // time_range_a_adjacent_b
    // time_range_b_adjacent_a
    // time_range_a_end_eq_b_start
    // time_range_b_end_eq_a_start
    // time_range_a_partially_overlaps_b
    // time_range_b_partially_overlaps_a
    // time_range_a_encapsulates_b
    // time_range_b_encapsulates_a
    // time_range_a_encapsulates_b_starts_equal
    // time_range_b_encapsulates_a_starts_equal
    // time_range_a_encapsulates_b_ends_equal
    // time_range_b_encapsulates_a_ends_equal
    //

    // ---- test_contains_range --------------------------------------------------------------

    #[test]
    fn test_contains_range_a_disjoint_b() {
        assert!(!time_range_a().encapsulates(&time_range_a_disjoint_b()));
    }

    #[test]
    fn test_contains_range_a_adjacent_b() {
        assert!(!time_range_a().encapsulates(&time_range_a_adjacent_b()));
    }

    #[test]
    fn test_contains_range_b_adjacent_a() {
        assert!(!time_range_a().encapsulates(&time_range_b_adjacent_a()));
    }

    #[test]
    fn test_contains_range_a_end_eq_b_start() {
        assert!(!time_range_a().encapsulates(&time_range_a_end_eq_b_start()));
    }

    #[test]
    fn test_contains_range_b_end_eq_a_start() {
        assert!(!time_range_a().encapsulates(&time_range_b_end_eq_a_start()));
    }

    #[test]
    fn test_contains_range_a_partially_overlaps_b() {
        assert!(!time_range_a().encapsulates(&time_range_a_partially_overlaps_b()));
    }

    #[test]
    fn test_contains_range_b_partially_overlaps_a() {
        assert!(!time_range_a().encapsulates(&time_range_b_partially_overlaps_a()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b() {
        assert!(time_range_a().encapsulates(&time_range_a_encapsulates_b()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a() {
        assert!(!time_range_a().encapsulates(&time_range_b_encapsulates_a()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b_starts_equal() {
        assert!(time_range_a().encapsulates(&time_range_a_encapsulates_b_starts_equal()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a_starts_equal() {
        assert!(!time_range_a().encapsulates(&time_range_b_encapsulates_a_starts_equal()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b_ends_equal() {
        assert!(time_range_a().encapsulates(&time_range_a_encapsulates_b_ends_equal()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a_ends_equal() {
        assert!(!time_range_a().encapsulates(&time_range_b_encapsulates_a_ends_equal()));
    }

    // ---- test_intersects ------------------------------------------------------------

    #[test]
    fn test_intersects_range_a_disjoint_b() {
        assert!(!time_range_a().intersects(&time_range_a_disjoint_b()));
    }

    #[test]
    fn test_intersects_range_a_adjacent_b() {
        assert!(!time_range_a().intersects(&time_range_a_adjacent_b()));
    }

    #[test]
    fn test_intersects_range_b_adjacent_a() {
        assert!(!time_range_a().intersects(&time_range_b_adjacent_a()));
    }

    #[test]
    fn test_intersects_range_a_end_eq_b_start() {
        assert!(time_range_a().intersects(&time_range_a_end_eq_b_start()));
    }

    #[test]
    fn test_intersects_range_b_end_eq_a_start() {
        assert!(time_range_a().intersects(&time_range_b_end_eq_a_start()));
    }

    #[test]
    fn test_intersects_range_a_partially_overlaps_b() {
        assert!(time_range_a().intersects(&time_range_a_partially_overlaps_b()));
    }

    #[test]
    fn test_intersects_range_b_partially_overlaps_a() {
        assert!(time_range_a().intersects(&time_range_b_partially_overlaps_a()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b() {
        assert!(time_range_a().intersects(&time_range_a_encapsulates_b()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a() {
        assert!(time_range_a().intersects(&time_range_b_encapsulates_a()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b_starts_equal() {
        assert!(time_range_a().intersects(&time_range_a_encapsulates_b_starts_equal()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a_starts_equal() {
        assert!(time_range_a().intersects(&time_range_b_encapsulates_a_starts_equal()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b_ends_equal() {
        assert!(time_range_a().intersects(&time_range_a_encapsulates_b_ends_equal()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a_ends_equal() {
        assert!(time_range_a().intersects(&time_range_b_encapsulates_a_ends_equal()));
    }

    // ---- test_intersects ------------------------------------------------------------

    #[test]
    fn test_intersects_excluded_range_a_disjoint_b() {
        assert!(!time_range_a().intersects_exclusive(&time_range_a_disjoint_b()));
    }

    #[test]
    fn test_intersects_excluded_range_a_adjacent_b() {
        assert!(!time_range_a().intersects_exclusive(&time_range_a_adjacent_b()));
    }

    #[test]
    fn test_intersects_excluded_range_b_adjacent_a() {
        assert!(!time_range_a().intersects_exclusive(&time_range_b_adjacent_a()));
    }

    #[test]
    fn test_intersects_excluded_range_a_end_eq_b_start() {
        assert!(!time_range_a().intersects_exclusive(&time_range_a_end_eq_b_start()));
    }

    #[test]
    fn test_intersects_excluded_range_b_end_eq_a_start() {
        assert!(!time_range_a().intersects_exclusive(&time_range_b_end_eq_a_start()));
    }

    #[test]
    fn test_intersects_excluded_range_a_partially_overlaps_b() {
        assert!(time_range_a().intersects_exclusive(&time_range_a_partially_overlaps_b()));
    }

    #[test]
    fn test_intersects_excluded_range_b_partially_overlaps_a() {
        assert!(time_range_a().intersects_exclusive(&time_range_b_partially_overlaps_a()));
    }

    #[test]
    fn test_intersects_excluded_range_a_encapsulates_b() {
        assert!(time_range_a().intersects_exclusive(&time_range_a_encapsulates_b()));
    }

    #[test]
    fn test_intersects_excluded_range_b_encapsulates_a() {
        assert!(time_range_a().intersects_exclusive(&time_range_b_encapsulates_a()));
    }

    #[test]
    fn test_intersects_excluded_range_a_encapsulates_b_starts_equal() {
        assert!(time_range_a().intersects_exclusive(&time_range_a_encapsulates_b_starts_equal()));
    }

    #[test]
    fn test_intersects_excluded_range_b_encapsulates_a_starts_equal() {
        assert!(time_range_a().intersects_exclusive(&time_range_b_encapsulates_a_starts_equal()));
    }

    #[test]
    fn test_intersects_excluded_range_a_encapsulates_b_ends_equal() {
        assert!(time_range_a().intersects_exclusive(&time_range_a_encapsulates_b_ends_equal()));
    }

    #[test]
    fn test_intersects_excluded_range_b_encapsulates_a_ends_equal() {
        assert!(time_range_a().intersects_exclusive(&time_range_b_encapsulates_a_ends_equal()));
    }

    // ---- test_contains --------------------------------------------------------------

    #[test]
    fn test_contains_dt_precedes_range() {
        // dt < start_at => false
        assert!(!time_range_a().contains(&Utc.with_ymd_and_hms(2024, 6, 9, 23, 59, 59).unwrap()));
    }
    #[test]
    fn test_contains_dt_eq_range_start() {
        // dt == start_at => true
        assert!(time_range_a().contains(&Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap()));
    }

    #[test]
    fn test_contains_dt_within_range() {
        // dt between start_at and end_at => true
        assert!(time_range_a().contains(&Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 1).unwrap()));
    }

    #[test]
    fn test_contains_dt_eq_range_end() {
        // dt == end_at => true
        assert!(time_range_a().contains(&Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap()));
    }

    #[test]
    fn test_contains_dt_follows_range() {
        // dt > end_at => false
        assert!(!time_range_a().contains(&Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 1).unwrap()));
    }

    // ---- test_contains_end_exclusive ------------------------------------------------

    #[test]
    fn test_contains_end_exclusive_dt_precedes_range() {
        // dt < start_at => false
        assert!(!time_range_a()
            .contains_end_exclusive(&Utc.with_ymd_and_hms(2024, 6, 9, 23, 59, 59).unwrap()));
    }
    #[test]
    fn test_contains_end_exclusive_dt_eq_range_start() {
        // dt == start_at => true
        assert!(time_range_a()
            .contains_end_exclusive(&Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap()));
    }

    #[test]
    fn test_contains_end_exclusive_dt_within_range() {
        // dt between start_at and end_at => true
        assert!(time_range_a()
            .contains_end_exclusive(&Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 1).unwrap()));
    }

    #[test]
    fn test_contains_end_exclusive_dt_eq_range_end() {
        // dt == end_at => false
        assert!(!time_range_a()
            .contains_end_exclusive(&Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap()));
    }

    #[test]
    fn test_contains_end_exclusive_dt_follows_range() {
        // dt > end_at => false
        assert!(!time_range_a()
            .contains_end_exclusive(&Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 1).unwrap()));
    }

    // ---- test_union ------------------------------------------------------------

    #[test]
    fn test_union_range_a_disjoint_b() {
        let result = time_range_a().union(&time_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_a_adjacent_b() {
        let result = time_range_a().union(&time_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_b_adjacent_a() {
        let result = time_range_a().union(&time_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_a_end_eq_b_start() {
        let result = time_range_a().union(&time_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 14, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_end_eq_a_start() {
        let result = time_range_a().union(&time_range_b_end_eq_a_start());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 8, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_partially_overlaps_b() {
        let result = time_range_a().union(&time_range_a_partially_overlaps_b());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_partially_overlaps_a() {
        let result = time_range_a().union(&time_range_b_partially_overlaps_a());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b() {
        let result = time_range_a().union(&time_range_a_encapsulates_b());

        let actual = result.expect("Expected result to be Some");
        let expected = time_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a() {
        let result = time_range_a().union(&time_range_b_encapsulates_a());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b_starts_equal() {
        let result = time_range_a().union(&time_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = time_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a_starts_equal() {
        let result = time_range_a().union(&time_range_b_encapsulates_a_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b_ends_equal() {
        let result = time_range_a().union(&time_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = time_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a_ends_equal() {
        let result = time_range_a().union(&time_range_b_encapsulates_a_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    // ---- test_difference ------------------------------------------------------------

    #[test]
    fn test_difference_range_a_disjoint_b() {
        let result = time_range_a().difference(&time_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_adjacent_b() {
        let result = time_range_a().difference(&time_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_b_adjacent_a() {
        let result = time_range_a().difference(&time_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_end_eq_b_start() {
        let result = time_range_a().difference(&time_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![time_range_a()];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_end_eq_a_start() {
        let result = time_range_a().difference(&time_range_b_end_eq_a_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_a_partially_overlaps_b() {
        let result = time_range_a().difference(&time_range_a_partially_overlaps_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_partially_overlaps_a() {
        let result = time_range_a().difference(&time_range_b_partially_overlaps_a());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b() {
        let result = time_range_a().difference(&time_range_a_encapsulates_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 11, 12, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a() {
        let result = time_range_a().difference(&time_range_b_encapsulates_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b_starts_equal() {
        let result = time_range_a().difference(&time_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a_starts_equal() {
        let result = time_range_a().difference(&time_range_b_encapsulates_a_starts_equal());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b_ends_equal() {
        let result = time_range_a().difference(&time_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a_ends_equal() {
        let result = time_range_a().difference(&time_range_b_encapsulates_a_ends_equal());

        assert_eq!(result, None);
    }

    // ---- test_symmetric_difference --------------------------------------------------

    #[test]
    fn test_symmetric_difference_range_a_disjoint_b() {
        let result = time_range_a().symmetric_difference(&time_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_a_adjacent_b() {
        let result = time_range_a().symmetric_difference(&time_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_b_adjacent_a() {
        let result = time_range_a().symmetric_difference(&time_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_a_end_eq_b_start() {
        let result = time_range_a().symmetric_difference(&time_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 14, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_end_eq_a_start() {
        let result = time_range_a().symmetric_difference(&time_range_b_end_eq_a_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 8, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_partially_overlaps_b() {
        let result = time_range_a().symmetric_difference(&time_range_a_partially_overlaps_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_partially_overlaps_a() {
        let result = time_range_a().symmetric_difference(&time_range_b_partially_overlaps_a());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b() {
        let result = time_range_a().symmetric_difference(&time_range_a_encapsulates_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 11, 12, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a() {
        let result = time_range_a().symmetric_difference(&time_range_b_encapsulates_a());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            ),
            TimeRange::new(
                Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
                Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b_starts_equal() {
        let result =
            time_range_a().symmetric_difference(&time_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a_starts_equal() {
        let result =
            time_range_a().symmetric_difference(&time_range_b_encapsulates_a_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 12, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 13, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b_ends_equal() {
        let result = time_range_a().symmetric_difference(&time_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 11, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a_ends_equal() {
        let result = time_range_a().symmetric_difference(&time_range_b_encapsulates_a_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![TimeRange::new(
            Utc.with_ymd_and_hms(2024, 6, 9, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2024, 6, 10, 0, 0, 0).unwrap(),
        )];
        assert_eq!(expected, actual);
    }
}

#[cfg(test)]
mod test_time_range_iter {
    use super::*;
    use pretty_assertions::assert_eq;
    use test_log::test;

    #[test]
    fn test_evenly_divisible_keep_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(5).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_evenly_divisible_drop_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(5).unwrap(), false);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_return_partial_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:17:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(5).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:15:00Z/2024-07-23T10:17:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_drop_partial_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:17:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(5).unwrap(), false);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:05:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:05:00Z/2024-07-23T10:10:00Z").unwrap(),
            TimeRange::parse("2024-07-23T10:10:00Z/2024-07-23T10:15:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_evenly_divisible_step_size_eq_range_width_keep_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(15).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap()];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_evenly_divisible_step_size_gt_range_width_keep_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(30).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap()];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_evenly_divisible_step_size_eq_range_width_drop_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(15).unwrap(), false);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap()];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_evenly_divisible_step_size_gt_range_width_drop_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:15:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(30).unwrap(), false);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![];

        assert_eq!(items, expected);
    }
}

#[cfg(test)]
mod test_iterator {
    use super::*;
    use pretty_assertions::assert_eq;
    use test_log::test;

    #[test]
    fn test_empty() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T10:00:00Z").unwrap();

        let iter = range.iter(Duration::try_minutes(5).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_daily_same_day() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T20:00:00Z").unwrap();

        let iter = range.iter(Duration::try_days(1).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![TimeRange::parse("2024-07-23T10:00:00Z/2024-07-23T20:00:00Z").unwrap()];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_daily_intra_day_with_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-25T20:00:00Z").unwrap();

        let iter = range.iter(Duration::try_days(1).unwrap(), true);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-24T10:00:00Z").unwrap(),
            TimeRange::parse("2024-07-24T10:00:00Z/2024-07-25T10:00:00Z").unwrap(),
            TimeRange::parse("2024-07-25T10:00:00Z/2024-07-25T20:00:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }

    #[test]
    fn test_daily_intra_day_no_remainder() {
        let range = TimeRange::parse("2024-07-23T10:00:00Z/2024-07-25T20:00:00Z").unwrap();

        let iter = range.iter(Duration::try_days(1).unwrap(), false);
        let items = iter.collect::<Vec<TimeRange>>();

        let expected = vec![
            TimeRange::parse("2024-07-23T10:00:00Z/2024-07-24T10:00:00Z").unwrap(),
            TimeRange::parse("2024-07-24T10:00:00Z/2024-07-25T10:00:00Z").unwrap(),
        ];

        assert_eq!(items, expected);
    }
}
