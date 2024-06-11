pub fn parse_digit(byte: u8) -> Option<u8> {
    byte.checked_sub(b'0').and_then(|c| (c < 10).then(|| c))
}