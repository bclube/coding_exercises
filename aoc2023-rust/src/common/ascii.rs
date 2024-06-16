pub fn parse_digit(byte: u8) -> Option<u8> {
    byte.checked_sub(b'0').and_then(|c| (c < 10).then(|| c))
}

pub fn parse_int<T>(bytes: &[u8]) -> Option<T>
where
    T: From<u8> + std::ops::Mul<Output = T>,
    <T as std::ops::Mul>::Output: From<u8> + std::ops::Add<Output = T> + From<u8>,
{
    bytes.iter().try_fold(T::from(0), |acc, &c| {
        parse_digit(c).map(|d| acc * T::from(10) + T::from(d))
    })
}
