use chrono::{DateTime, Datelike, Duration, NaiveDate, TimeZone, Utc};

use crate::{error::Error, util, TimeRange};

/** A DateRange represents a range of dates.  The range is inclusive of both the start and end dates.
*/
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DateRange {
    start_at: NaiveDate,
    end_at: NaiveDate,
}

impl std::fmt::Debug for DateRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DateRange[{} -> {}]", self.start_at, self.end_at)
    }
}

impl DateRange {
    /// Create a new DateRange from a start and end datetime.
    ///
    /// Args:
    ///     start_at: The start of the time range (inclusive).
    ///     end_at: The end of the time range (inclusive).
    ///
    /// **Examples:**
    ///
    /// ```rust
    /// use time_range::{DateRange, NaiveDate};
    ///
    /// let start_at = NaiveDate::from_ymd_opt(2022, 6, 1).unwrap();
    /// let end_at = NaiveDate::from_ymd_opt(2022, 6, 13).unwrap();
    /// let date_range = DateRange::new(start_at, end_at);
    /// println!("{:#?}", date_range);
    /// // DateRange[2021-06-01 -> 2021-06-13]
    /// ```
    ///
    pub fn new(start_at: impl Into<NaiveDate>, end_at: impl Into<NaiveDate>) -> Self {
        DateRange {
            start_at: start_at.into(),
            end_at: end_at.into(),
        }
    }

    /// Parse the given ISO-8601 formatted string into a DateRange. The start and end
    /// time should be delimited by a forward slash ("/"). Start/end must be formatted as
    /// datetime.  Date-only formats and naive datetimes are not supported.
    ///
    /// Args:
    ///     ranges (str): delimited date ranges (e.g. `"2021-07-01/2021-07-02"`)
    ///
    /// Returns:
    ///     DateRange: parsed time range
    ///
    /// **Examples:**
    ///
    /// ```rust
    /// use time_range::DateRange;
    ///
    /// let date_range = DateRange::parse("2021-07-01/2021-07-02").unwrap();
    /// println!("{:#?}", date_range);
    /// // DateRange[2021-07-01 -> 2021-07-02]
    /// ```
    ///
    pub fn parse(s: &str) -> Result<DateRange, Error> {
        let mut elements = s.split('/');
        let start_at = match elements.next() {
            Some(s) => match s.parse::<NaiveDate>() {
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
            Some(s) => match s.parse::<NaiveDate>() {
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

        Ok(DateRange::new(start_at, end_at))
    }

    pub fn start_at(&self) -> &NaiveDate {
        &self.start_at
    }

    /// Get the start of the date range as a number of seconds since the UNIX epoch.
    pub fn start_timestamp(&self) -> i64 {
        util::naive_date_to_utc(self.start_at).timestamp()
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

    pub fn end_at(&self) -> &NaiveDate {
        &self.end_at
    }

    /// Get the end of the date range as a number of seconds since the UNIX epoch.
    pub fn end_timestamp(&self) -> i64 {
        util::naive_date_to_utc(self.end_at).timestamp()
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

    pub fn to_tuple(self) -> (NaiveDate, NaiveDate) {
        (self.start_at, self.end_at)
    }

    pub fn start_at_string(&self) -> String {
        self.start_at.to_string()
    }

    pub fn end_at_string(&self) -> String {
        self.end_at.to_string()
    }

    /// Check if the given date falls within the date_range. Both ends are inclusive.
    pub fn contains(&self, dt: &NaiveDate) -> bool {
        self.start_at() <= dt && dt <= self.end_at()
    }

    /// Check if the given date falls within the time_range. Start is inclusive, end is exclusive.
    pub fn contains_end_exclusive(&self, dt: &NaiveDate) -> bool {
        self.start_at() <= dt && dt < self.end_at()
    }

    /// Check if the date_range encapsulates `other`. Both ends are inclusive.
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
    pub fn encapsulates(&self, other: &DateRange) -> bool {
        self.start_at() <= other.start_at() && self.end_at() >= other.end_at()
    }

    /// Check if any part of the date_range overlaps with `other`. Both ends are inclusive.
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
    pub fn intersects(&self, other: &DateRange) -> bool {
        // (StartA <= EndB) and (EndA >= StartB)
        self.start_at() <= other.end_at() && self.end_at() >= other.start_at()
    }

    /// Return the region where date_range overlaps with `other` if the two ranges have
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
    pub fn intersection(&self, other: &DateRange) -> Option<DateRange> {
        if self.intersects(other) {
            Some(DateRange::new(
                *self.start_at().max(other.start_at()),
                *self.end_at().min(other.end_at()),
            ))
        } else {
            None
        }
    }

    /// Merge the date_range with `other` if the two ranges have any overlap.
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
    pub fn union(&self, other: &DateRange) -> Option<DateRange> {
        if self.intersects(other) {
            Some(DateRange::new(
                *self.start_at().min(other.start_at()),
                *self.end_at().max(other.end_at()),
            ))
        } else {
            None
        }
    }

    /// Return the regions where date_range and `other` do not overlap, if the two ranges
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
    pub fn difference(&self, other: &DateRange) -> Option<Vec<DateRange>> {
        if self.intersects(other) {
            let mut result = Vec::new();
            if self.start_at() < other.start_at() {
                result.push(DateRange::new(*self.start_at(), *other.start_at()));
            }
            if self.end_at() > other.end_at() {
                result.push(DateRange::new(*other.end_at(), *self.end_at()));
            }

            match result.is_empty() {
                true => None, // return None no results (happens when ranges are equal)
                false => Some(result),
            }
        } else {
            None
        }
    }

    /// Return the regions where date_range and `other` do not overlap, if the two ranges
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
    pub fn symmetric_difference(&self, other: &DateRange) -> Option<Vec<DateRange>> {
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

    /// Returns an iterator with step width equal to provided `chrono::Duration`. If `DateRange`
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
    /// DateRange evenly divisible by the step size:
    /// ```
    /// # fn main() -> anyhow::Result<()> {
    /// # use time_range::{DateRange, Duration};
    /// let range = DateRange::parse("2022-07-23/2022-07-25")?;
    ///
    /// let iter = range.iter();
    /// let actual = iter.collect::<Vec<DateRange>>();
    ///
    /// let expected = vec![
    ///     DateRange::parse("2022-07-23/2022-07-24")?,
    ///     DateRange::parse("2022-07-24/2022-07-25")?,
    /// ];
    ///
    /// assert_eq!(actual, expected);
    /// # Ok(())
    /// # }
    /// ```
    pub fn iter(&self) -> DateRangeIter<'_> {
        DateRangeIter::new(self)
    }

    /// Create a DateRange from two epoch timestamps in nanoseconds.
    pub fn from_nanos(start_at: i64, end_at: i64) -> DateRange {
        DateRange::new(
            Utc.timestamp_nanos(start_at).naive_utc().date(),
            Utc.timestamp_nanos(end_at).naive_utc().date(),
        )
    }

    /// Create a DateRange from two epoch timestamps in seconds.  Returns `None` if the timestamp(s)
    /// cannot be converted to a `DateTime<Utc>`.
    pub fn from_secs(start_at: i64, end_at: i64) -> Option<DateRange> {
        let start = match Utc.timestamp_opt(start_at, 0).single() {
            Some(s) => s.naive_utc().date(),
            None => return None,
        };

        let end = match Utc.timestamp_opt(end_at, 0).single() {
            Some(e) => e.naive_utc().date(),
            None => return None,
        };

        Some(DateRange::new(start, end))
    }
}

impl std::fmt::Display for DateRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.start_at_string(), self.end_at_string())
    }
}

impl From<(NaiveDate, NaiveDate)> for DateRange {
    fn from(t: (NaiveDate, NaiveDate)) -> Self {
        DateRange::new(t.0, t.1)
    }
}

impl From<DateRange> for (NaiveDate, NaiveDate) {
    fn from(t: DateRange) -> Self {
        t.to_tuple()
    }
}

impl From<(DateTime<Utc>, DateTime<Utc>)> for DateRange {
    fn from(t: (DateTime<Utc>, DateTime<Utc>)) -> Self {
        DateRange::new(t.0.naive_utc().date(), t.1.naive_utc().date())
    }
}

impl From<DateRange> for (DateTime<Utc>, DateTime<Utc>) {
    fn from(t: DateRange) -> Self {
        (
            util::naive_date_to_utc(t.start_at),
            util::naive_date_to_utc(t.end_at),
        )
    }
}

impl From<TimeRange> for DateRange {
    fn from(t: TimeRange) -> Self {
        // datetimes are always truncated DOWN to the nearest day so that behvaior is always predictable,
        // rather than getting different results when the time of a bounary crosses noon.
        DateRange::new(
            t.start_at().naive_utc().date(),
            t.end_at().naive_utc().date(),
        )
    }
}

pub struct DateRangeIter<'a> {
    range: &'a DateRange,
    step: Duration,
    last: NaiveDate,
}

impl<'a> DateRangeIter<'a> {
    fn new(range: &'a DateRange) -> DateRangeIter<'a> {
        DateRangeIter {
            range,
            step: Duration::try_days(1).expect("1 day is a valid duration"),
            last: range.start_at,
        }
    }
}

impl<'a> Iterator for DateRangeIter<'a> {
    type Item = DateRange;

    fn next(&mut self) -> Option<Self::Item> {
        let end = self.last + self.step;
        if self.range.contains(&end) {
            let range = DateRange::new(self.last, end);
            self.last = end;
            return Some(range);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use test_log::test;
    use tracing::debug;

    use super::*;

    #[test]
    fn test_parse() {
        let ranges = ["2022-06-01/2022-06-02"];

        for s in ranges {
            debug!("Parsing: {}", s);
            let date_range = DateRange::parse(s).unwrap();

            debug!("date_range= {}", date_range);

            assert_eq!(
                date_range.start_at,
                NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
                "start_at mismatch"
            );
            assert_eq!(
                date_range.end_at,
                NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
                "end_at mismatch"
            );
        }
    }

    #[test]
    fn test_display() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
        );
        assert_eq!(
            format!("{date_range}"),
            "2022-06-01/2022-06-02",
            "display mismatch"
        );
    }

    #[test]
    fn test_is_valid() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
        );

        assert!(date_range.is_valid());
    }

    #[test]
    fn test_not_valid() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
        );

        assert!(!date_range.is_valid());
    }

    #[test]
    fn test_duration() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 6).unwrap(),
        );

        assert!(date_range.duration() == Duration::try_days(5).unwrap());
    }

    #[test]
    fn test_duration_invalid_order() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 3).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
        );

        assert!(date_range.duration() == Duration::try_days(-2).unwrap());
    }

    #[test]
    fn test_from_tuple() {
        let date_range = DateRange::from((
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
        ));

        assert!(date_range.start_at == NaiveDate::from_ymd_opt(2022, 6, 1).unwrap());
        assert!(date_range.end_at == NaiveDate::from_ymd_opt(2022, 6, 2).unwrap());
    }

    #[test]
    fn test_from_datetime_tuple() {
        let date_range = DateRange::from((
            Utc.with_ymd_and_hms(2022, 6, 1, 0, 0, 0).unwrap(),
            Utc.with_ymd_and_hms(2022, 6, 2, 0, 0, 0).unwrap(),
        ));

        assert!(date_range.start_at == NaiveDate::from_ymd_opt(2022, 6, 1).unwrap());
        assert!(date_range.end_at == NaiveDate::from_ymd_opt(2022, 6, 2).unwrap());
    }

    #[test]
    fn test_into_tuple() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
        );

        let (start_at, end_at): (DateTime<Utc>, DateTime<Utc>) = date_range.into();

        assert!(start_at == Utc.with_ymd_and_hms(2022, 6, 1, 0, 0, 0).unwrap());
        assert!(end_at == Utc.with_ymd_and_hms(2022, 6, 2, 0, 0, 0).unwrap());
    }

    #[test]
    fn test_into_datetime_tuple() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 1).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 2).unwrap(),
        );

        let (start_at, end_at): (DateTime<Utc>, DateTime<Utc>) = date_range.into();

        assert!(start_at == Utc.with_ymd_and_hms(2022, 6, 1, 0, 0, 0).unwrap());
        assert!(end_at == Utc.with_ymd_and_hms(2022, 6, 2, 0, 0, 0).unwrap());
    }

    #[test]
    fn test_from_nanos() {
        let date_range = DateRange::from_nanos(
            1648083600000000000_i64, // 2022-03-24 01:00:00
            1648085400000000000_i64, // 2022-03-24 01:30:00
        );

        assert!(date_range.start_at == NaiveDate::from_ymd_opt(2022, 3, 24).unwrap());
        assert!(date_range.end_at == NaiveDate::from_ymd_opt(2022, 3, 24).unwrap());
    }

    #[test]
    fn test_from_secs() {
        let date_range = DateRange::from_secs(1668988800_i64, 1669075200_i64).unwrap();

        assert!(date_range.start_at == NaiveDate::from_ymd_opt(2022, 11, 21).unwrap());
        assert!(date_range.end_at == NaiveDate::from_ymd_opt(2022, 11, 22).unwrap());
    }

    #[test]
    fn test_from_time_range() {
        let time_range = TimeRange::new(
            Utc.with_ymd_and_hms(2022, 6, 1, 1, 1, 1).unwrap(),
            Utc.with_ymd_and_hms(2022, 6, 2, 23, 59, 59).unwrap(),
        );

        let date_range = DateRange::from(time_range);

        assert!(date_range.start_at() == &NaiveDate::from_ymd_opt(2022, 6, 1).unwrap());
        assert!(date_range.end_at() == &NaiveDate::from_ymd_opt(2022, 6, 2).unwrap());
    }

    #[test]
    fn test_to_timestamps() {
        let date_range = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 11, 21).unwrap(),
            NaiveDate::from_ymd_opt(2022, 11, 22).unwrap(),
        );

        assert_eq!(date_range.start_timestamp(), 1668988800_i64);
        assert_eq!(date_range.end_timestamp(), 1669075200_i64);
    }
}

#[cfg(test)]
mod test_pairwise_ops {
    use super::*;
    use pretty_assertions::assert_eq;
    use test_log::test;
    use tracing::trace;

    fn date_range_a() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
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
    fn date_range_a_disjoint_b() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 14).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 16).unwrap(),
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
    fn date_range_a_adjacent_b() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 14).unwrap(),
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
    fn date_range_b_adjacent_a() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 8).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
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
    fn date_range_a_end_eq_b_start() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 14).unwrap(),
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
    fn date_range_b_end_eq_a_start() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 8).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
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
    fn date_range_a_partially_overlaps_b() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
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
    fn date_range_b_partially_overlaps_a() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
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
    fn date_range_a_encapsulates_b() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
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
    fn date_range_b_encapsulates_a() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
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
    fn date_range_a_encapsulates_b_starts_equal() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
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
    fn date_range_b_encapsulates_a_starts_equal() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
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
    fn date_range_a_encapsulates_b_ends_equal() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
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
    fn date_range_b_encapsulates_a_ends_equal() -> DateRange {
        DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        )
    }

    // All scenarios:
    //
    // date_range_a_adjacent_b
    // date_range_b_adjacent_a
    // date_range_a_end_eq_b_start
    // date_range_b_end_eq_a_start
    // date_range_a_partially_overlaps_b
    // date_range_b_partially_overlaps_a
    // date_range_a_encapsulates_b
    // date_range_b_encapsulates_a
    // date_range_a_encapsulates_b_starts_equal
    // date_range_b_encapsulates_a_starts_equal
    // date_range_a_encapsulates_b_ends_equal
    // date_range_b_encapsulates_a_ends_equal
    //

    // ---- test_contains_range --------------------------------------------------------------

    #[test]
    fn test_contains_range_a_disjoint_b() {
        assert!(!date_range_a().encapsulates(&date_range_a_disjoint_b()));
    }

    #[test]
    fn test_contains_range_a_adjacent_b() {
        assert!(!date_range_a().encapsulates(&date_range_a_adjacent_b()));
    }

    #[test]
    fn test_contains_range_b_adjacent_a() {
        assert!(!date_range_a().encapsulates(&date_range_b_adjacent_a()));
    }

    #[test]
    fn test_contains_range_a_end_eq_b_start() {
        assert!(!date_range_a().encapsulates(&date_range_a_end_eq_b_start()));
    }

    #[test]
    fn test_contains_range_b_end_eq_a_start() {
        assert!(!date_range_a().encapsulates(&date_range_b_end_eq_a_start()));
    }

    #[test]
    fn test_contains_range_a_partially_overlaps_b() {
        assert!(!date_range_a().encapsulates(&date_range_a_partially_overlaps_b()));
    }

    #[test]
    fn test_contains_range_b_partially_overlaps_a() {
        assert!(!date_range_a().encapsulates(&date_range_b_partially_overlaps_a()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b() {
        assert!(date_range_a().encapsulates(&date_range_a_encapsulates_b()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a() {
        assert!(!date_range_a().encapsulates(&date_range_b_encapsulates_a()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b_starts_equal() {
        assert!(date_range_a().encapsulates(&date_range_a_encapsulates_b_starts_equal()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a_starts_equal() {
        assert!(!date_range_a().encapsulates(&date_range_b_encapsulates_a_starts_equal()));
    }

    #[test]
    fn test_contains_range_a_encapsulates_b_ends_equal() {
        assert!(date_range_a().encapsulates(&date_range_a_encapsulates_b_ends_equal()));
    }

    #[test]
    fn test_contains_range_b_encapsulates_a_ends_equal() {
        assert!(!date_range_a().encapsulates(&date_range_b_encapsulates_a_ends_equal()));
    }

    // ---- test_intersects ------------------------------------------------------------

    #[test]
    fn test_intersects_range_a_disjoint_b() {
        assert!(!date_range_a().intersects(&date_range_a_disjoint_b()));
    }

    #[test]
    fn test_intersects_range_a_adjacent_b() {
        assert!(!date_range_a().intersects(&date_range_a_adjacent_b()));
    }

    #[test]
    fn test_intersects_range_b_adjacent_a() {
        assert!(!date_range_a().intersects(&date_range_b_adjacent_a()));
    }

    #[test]
    fn test_intersects_range_a_end_eq_b_start() {
        assert!(date_range_a().intersects(&date_range_a_end_eq_b_start()));
    }

    #[test]
    fn test_intersects_range_b_end_eq_a_start() {
        assert!(date_range_a().intersects(&date_range_b_end_eq_a_start()));
    }

    #[test]
    fn test_intersects_range_a_partially_overlaps_b() {
        assert!(date_range_a().intersects(&date_range_a_partially_overlaps_b()));
    }

    #[test]
    fn test_intersects_range_b_partially_overlaps_a() {
        assert!(date_range_a().intersects(&date_range_b_partially_overlaps_a()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b() {
        assert!(date_range_a().intersects(&date_range_a_encapsulates_b()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a() {
        assert!(date_range_a().intersects(&date_range_b_encapsulates_a()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b_starts_equal() {
        assert!(date_range_a().intersects(&date_range_a_encapsulates_b_starts_equal()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a_starts_equal() {
        assert!(date_range_a().intersects(&date_range_b_encapsulates_a_starts_equal()));
    }

    #[test]
    fn test_intersects_range_a_encapsulates_b_ends_equal() {
        assert!(date_range_a().intersects(&date_range_a_encapsulates_b_ends_equal()));
    }

    #[test]
    fn test_intersects_range_b_encapsulates_a_ends_equal() {
        assert!(date_range_a().intersects(&date_range_b_encapsulates_a_ends_equal()));
    }

    // ---- test_contains --------------------------------------------------------------

    #[test]
    fn test_contains_dt_precedes_range() {
        // dt < start_at => false
        assert!(!date_range_a().contains(&NaiveDate::from_ymd_opt(2022, 6, 9).unwrap()));
    }

    #[test]
    fn test_contains_dt_eq_range_start() {
        // dt == start_at => true
        assert!(date_range_a().contains(&NaiveDate::from_ymd_opt(2022, 6, 10).unwrap()));
    }

    #[test]
    fn test_contains_dt_within_range() {
        // dt between start_at and end_at => true
        assert!(date_range_a().contains(&NaiveDate::from_ymd_opt(2022, 6, 10).unwrap()));
    }

    #[test]
    fn test_contains_dt_eq_range_end() {
        // dt == end_at => true
        assert!(date_range_a().contains(&NaiveDate::from_ymd_opt(2022, 6, 11).unwrap()));
    }

    #[test]
    fn test_contains_dt_follows_range() {
        // dt > end_at => false
        assert!(!date_range_a().contains(&NaiveDate::from_ymd_opt(2022, 6, 13).unwrap()));
    }

    // ---- test_contains_end_exclusive --------------------------------------------------------------

    #[test]
    fn test_contains_end_exclusive_dt_precedes_range() {
        // dt < start_at => false
        assert!(
            !date_range_a().contains_end_exclusive(&NaiveDate::from_ymd_opt(2022, 6, 9).unwrap())
        );
    }

    #[test]
    fn test_contains_end_exclusive_dt_eq_range_start() {
        // dt == start_at => true
        assert!(
            date_range_a().contains_end_exclusive(&NaiveDate::from_ymd_opt(2022, 6, 10).unwrap())
        );
    }

    #[test]
    fn test_contains_end_exclusive_dt_within_range() {
        // dt between start_at and end_at => true
        assert!(
            date_range_a().contains_end_exclusive(&NaiveDate::from_ymd_opt(2022, 6, 11).unwrap())
        );
    }

    #[test]
    fn test_contains_end_exclusive_dt_eq_range_end() {
        // dt == end_at => false
        assert!(
            !date_range_a().contains_end_exclusive(&NaiveDate::from_ymd_opt(2022, 6, 12).unwrap())
        );
    }

    #[test]
    fn test_contains_end_exclusive_dt_follows_range() {
        // dt > end_at => false
        assert!(
            !date_range_a().contains_end_exclusive(&NaiveDate::from_ymd_opt(2022, 6, 13).unwrap())
        );
    }

    // ---- test_union ------------------------------------------------------------

    #[test]
    fn test_union_range_a_disjoint_b() {
        let result = date_range_a().union(&date_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_a_adjacent_b() {
        let result = date_range_a().union(&date_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_b_adjacent_a() {
        let result = date_range_a().union(&date_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_union_range_a_end_eq_b_start() {
        let result = date_range_a().union(&date_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 14).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_end_eq_a_start() {
        let result = date_range_a().union(&date_range_b_end_eq_a_start());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 8).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_partially_overlaps_b() {
        let result = date_range_a().union(&date_range_a_partially_overlaps_b());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_partially_overlaps_a() {
        let result = date_range_a().union(&date_range_b_partially_overlaps_a());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b() {
        let result = date_range_a().union(&date_range_a_encapsulates_b());

        let actual = result.expect("Expected result to be Some");
        let expected = date_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a() {
        let result = date_range_a().union(&date_range_b_encapsulates_a());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b_starts_equal() {
        let result = date_range_a().union(&date_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = date_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a_starts_equal() {
        let result = date_range_a().union(&date_range_b_encapsulates_a_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_a_encapsulates_b_ends_equal() {
        let result = date_range_a().union(&date_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = date_range_a();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_union_range_b_encapsulates_a_ends_equal() {
        let result = date_range_a().union(&date_range_b_encapsulates_a_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        );
        assert_eq!(expected, actual);
    }

    // ---- test_difference ------------------------------------------------------------

    #[test]
    fn test_difference_range_a_disjoint_b() {
        let result = date_range_a().difference(&date_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_adjacent_b() {
        let result = date_range_a().difference(&date_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_b_adjacent_a() {
        let result = date_range_a().difference(&date_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_end_eq_b_start() {
        let result = date_range_a().difference(&date_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![date_range_a()];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_end_eq_a_start() {
        let result = date_range_a().difference(&date_range_b_end_eq_a_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_a_partially_overlaps_b() {
        let result = date_range_a().difference(&date_range_a_partially_overlaps_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_partially_overlaps_a() {
        let result = date_range_a().difference(&date_range_b_partially_overlaps_a());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b() {
        let result = date_range_a().difference(&date_range_a_encapsulates_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a() {
        let result = date_range_a().difference(&date_range_b_encapsulates_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b_starts_equal() {
        let result = date_range_a().difference(&date_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a_starts_equal() {
        let result = date_range_a().difference(&date_range_b_encapsulates_a_starts_equal());

        assert_eq!(result, None);
    }

    #[test]
    fn test_difference_range_a_encapsulates_b_ends_equal() {
        let result = date_range_a().difference(&date_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_difference_range_b_encapsulates_a_ends_equal() {
        let result = date_range_a().difference(&date_range_b_encapsulates_a_ends_equal());

        assert_eq!(result, None);
    }

    // ---- test_symmetric_difference --------------------------------------------------

    #[test]
    fn test_symmetric_difference_range_a_disjoint_b() {
        let result = date_range_a().symmetric_difference(&date_range_a_disjoint_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_a_adjacent_b() {
        let result = date_range_a().symmetric_difference(&date_range_a_adjacent_b());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_b_adjacent_a() {
        let result = date_range_a().symmetric_difference(&date_range_b_adjacent_a());

        assert_eq!(result, None);
    }

    #[test]
    fn test_symmetric_difference_range_a_end_eq_b_start() {
        let result = date_range_a().symmetric_difference(&date_range_a_end_eq_b_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 14).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_end_eq_a_start() {
        let result = date_range_a().symmetric_difference(&date_range_b_end_eq_a_start());
        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 8).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_partially_overlaps_b() {
        let result = date_range_a().symmetric_difference(&date_range_a_partially_overlaps_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_partially_overlaps_a() {
        let result = date_range_a().symmetric_difference(&date_range_b_partially_overlaps_a());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b() {
        let result = date_range_a().symmetric_difference(&date_range_a_encapsulates_b());

        trace!("result={:?}", result);

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a() {
        let result = date_range_a().symmetric_difference(&date_range_b_encapsulates_a());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            ),
            DateRange::new(
                NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
                NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
            ),
        ];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b_starts_equal() {
        let result =
            date_range_a().symmetric_difference(&date_range_a_encapsulates_b_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a_starts_equal() {
        let result =
            date_range_a().symmetric_difference(&date_range_b_encapsulates_a_starts_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 12).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 13).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_a_encapsulates_b_ends_equal() {
        let result = date_range_a().symmetric_difference(&date_range_a_encapsulates_b_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 11).unwrap(),
        )];
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_symmetric_difference_range_b_encapsulates_a_ends_equal() {
        let result = date_range_a().symmetric_difference(&date_range_b_encapsulates_a_ends_equal());

        let actual = result.expect("Expected result to be Some");
        let expected = vec![DateRange::new(
            NaiveDate::from_ymd_opt(2022, 6, 9).unwrap(),
            NaiveDate::from_ymd_opt(2022, 6, 10).unwrap(),
        )];
        assert_eq!(expected, actual);
    }
}

#[cfg(test)]
mod test_iterator {
    use super::*;
    use pretty_assertions::assert_eq;
    use test_log::test;
    use tracing::debug;

    #[test]
    fn test_range() {
        let range = DateRange::parse("2022-07-23/2022-07-25").unwrap();

        let iter = range.iter();
        let actual = iter.collect::<Vec<DateRange>>();

        let expected = vec![
            DateRange::parse("2022-07-23/2022-07-24").unwrap(),
            DateRange::parse("2022-07-24/2022-07-25").unwrap(),
        ];

        debug!("actual={:?}", actual);
        debug!("expected={:?}", expected);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_same_day() {
        let range = DateRange::parse("2022-07-23/2022-07-23").unwrap();

        let iter = range.iter();
        let items = iter.collect::<Vec<DateRange>>();

        let expected = vec![];

        assert_eq!(items, expected);
    }
}
