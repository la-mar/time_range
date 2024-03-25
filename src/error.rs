use thiserror;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("failed to parse field {field_name:?}: {value:?}")]
    ParseFieldError {
        field_name: &'static str,
        value: String,
        #[source]
        source: chrono::ParseError,
    },
    #[error("Failed to convert datetime to nanoseconds -- out of range: {0}")]
    NanosOutOfRange(String),
    #[error("expected value for {field_name:?}")]
    MissingValue { field_name: &'static str },
    #[error("unknown error parsing datetime")]
    Unknown,
}
