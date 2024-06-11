#[macro_export]
macro_rules! input_file_lines {
    ($filename:expr) => {
        include_str!(concat!("../inputs/", $filename)).lines()
    };
}
