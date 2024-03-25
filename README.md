# time_range

time_range extends [chrono](https://docs.rs/chrono/latest/chrono/) to provide two range types: DateRange and TimeRange. They are used to represent a range of dates or datetimes and encapsulate related functionality, such as iteration, intersection, unioning, etc.

## Usage

#### TimeRange

```rust

use time_range::{TimeRange, Utc, Datelike, Timelike};

// create from start and end bounds
let start_at = Utc.ymd(2024, 3, 1).and_hms(0, 0, 0)
let end_at = Utc.ymd(2024, 3, 13).and_hms(11, 59, 59);
let time_range = TimeRange::new(start_at, end_at);

println!("{:#?}", time_range); // TimeRange[2024-03-01T12:00:00+00:00 -> 2024-03-13T11:59:59+00:00]

// parse from a string
let time_range = TimeRange::parse("2024-03-24T12:00:00+00:00/2024-03-25T11:59:59+00:00")?;

// export back into a string
println!("{}", time_range.to_string()); // 2024-03-24T12:00:00+00:00/2024-03-25T11:59:59+00:00

```

#### DateRange

```rust

use time_range::{DateRange, Utc, Datelike, Timelike};

// create from start and end bounds
let start_at = NaiveDate::from_ymd(2024, 3, 1);
let end_at = NaiveDate::from_ymd(2024, 3, 13);
let date_range = DateRange::new(start_at, end_at);
println!("{:#?}", date_range); // DateRange[2024-03-01 -> 2024-03-13]

// parse from a string
let date_range = DateRange::parse("2024-03-20/2024-03-24").unwrap();
println!("{:#?}", date_range); // DateRange[2024-03-20 -> 2024-03-24]

// export back into a string
println!("{}", date_range.to_string()); // 2024-03-20/2024-03-24

```

#### Operations

Pairwise operations are available on both types:
    - `contains`
    - `encapsulates`
    - `intersects`
    - `intersection`
    - `union`
    - `difference`
    - `symmetric_difference`

