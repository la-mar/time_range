use chrono::{DateTime, SecondsFormat, Utc};

/// Convert a [`DateTime`] into an RFC3339 string representation.
///
/// Example:
///     ```ignore
///      time_range::to_rfc3339(Utc.ymd(2022, 7, 8).and_hms(18, 16, 3)); // "2022-07-08T18:16:03Z"
///     ```
pub fn dt_to_string(dt: &DateTime<Utc>) -> String {
    dt.to_rfc3339_opts(SecondsFormat::AutoSi, true)
}

#[cfg(test)]
mod tests {

    use chrono::TimeZone;
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_dt_to_string() {
        let dt = Utc
            .with_ymd_and_hms(2022, 7, 8, 18, 16, 3)
            .single()
            .unwrap();
        assert_eq!(dt_to_string(&dt), "2022-07-08T18:16:03Z");
    }
}
