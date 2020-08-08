use ascii::AsciiStr;
use std::borrow::Cow;
use std::slice;

#[derive(Debug)]
pub enum StrData {
    OwnedU8(Box<[u8]>),
    StaticU8(&'static [u8]),
    OwnedU16(Box<[u16]>),
    OwnedU32(Box<[u32]>),
}

impl StrData {
    pub fn len(&self) -> usize {
        match self {
            Self::OwnedU8(s) => s.len(),
            Self::StaticU8(s) => s.len(),
            Self::OwnedU16(s) => s.len(),
            Self::OwnedU32(s) => s.len(),
        }
    }
    pub fn iter(&self) -> Chars {
        match self {
            Self::OwnedU8(s) => Chars {
                inner: CharsInner::U8(s.iter()),
            },
            Self::StaticU8(s) => Chars {
                inner: CharsInner::U8(s.iter()),
            },
            Self::OwnedU16(s) => Chars {
                inner: CharsInner::U16(s.iter()),
            },
            Self::OwnedU32(s) => Chars {
                inner: CharsInner::U32(s.iter()),
            },
        }
    }
    pub fn as_ascii(&self) -> Option<&AsciiStr> {
        let s: &[u8] = match self {
            Self::OwnedU8(s) => s,
            Self::StaticU8(s) => s,
            _ => return None,
        };
        AsciiStr::from_ascii(s).ok()
    }
    pub fn to_utf8(&self) -> Result<Cow<str>, Utf8Error> {
        if let Some(s) = self.as_ascii() {
            return Ok(s.as_str().into());
        }
        self.iter()
            .enumerate()
            .map(|(i, ucs)| std::char::from_u32(ucs).ok_or(Utf8Error { position: i }))
            .collect::<Result<_, _>>()
            .map(Cow::Owned)
    }
    pub fn to_utf8_lossy(&self) -> (Cow<str>, Option<Utf8Error>) {
        if let Some(s) = self.as_ascii() {
            return (s.as_str().into(), None);
        }
        let mut err = None;
        let s = self
            .iter()
            .enumerate()
            .map(|(i, ucs)| {
                std::char::from_u32(ucs).unwrap_or_else(|| {
                    if err.is_none() {
                        err = Some(Utf8Error { position: i });
                    }
                    std::char::REPLACEMENT_CHARACTER
                })
            })
            .collect::<String>();
        (s.into(), err)
    }
    pub fn from_static(s: &'static str) -> Self {
        if s.is_ascii() {
            Self::StaticU8(s.as_bytes())
        } else {
            s.into()
        }
    }
}

impl From<Cow<'_, str>> for StrData {
    fn from(s: Cow<'_, str>) -> Self {
        if s.is_ascii() {
            return Self::OwnedU8(s.into_owned().into_bytes().into_boxed_slice());
        }
        let mut width = None;
        for c in s.chars() {
            let c = c as u32;
            if width.is_none() && c <= u32::from(u8::MAX) {
                continue;
            }
            if c > u32::from(u16::MAX) {
                width = Some(true);
                // no point continuing
                break;
            } else {
                width = Some(false)
            }
        }
        match width {
            None => Self::OwnedU8(s.chars().map(|c| c as u32 as u8).collect()),
            Some(false) => Self::OwnedU16(s.chars().map(|c| c as u32 as u16).collect()),
            Some(true) => Self::OwnedU32(s.chars().map(|c| c as u32).collect()),
        }
    }
}
impl From<&str> for StrData {
    fn from(s: &str) -> Self {
        Cow::from(s).into()
    }
}
impl From<String> for StrData {
    fn from(s: String) -> Self {
        Cow::from(s).into()
    }
}

#[derive(Debug, Clone)]
pub struct Utf8Error {
    position: usize,
}

#[derive(Debug, Clone)]
pub struct Chars<'a> {
    inner: CharsInner<'a>,
}
#[derive(Debug, Clone)]
enum CharsInner<'a> {
    U8(slice::Iter<'a, u8>),
    U16(slice::Iter<'a, u16>),
    U32(slice::Iter<'a, u32>),
}
macro_rules! delegate_iter {
    ($inner:expr, $it:ident, $result:expr) => {{
        match $inner {
            CharsInner::U8($it) => $result,
            CharsInner::U16($it) => $result,
            CharsInner::U32($it) => $result,
        }
    }};
}
impl Iterator for Chars<'_> {
    type Item = u32;
    fn size_hint(&self) -> (usize, Option<usize>) {
        delegate_iter!(&self.inner, i, i.size_hint())
    }
    fn next(&mut self) -> Option<Self::Item> {
        delegate_iter!(&mut self.inner, i, i.next().copied().map(Into::into))
    }
}
impl DoubleEndedIterator for Chars<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        delegate_iter!(&mut self.inner, i, i.next_back().copied().map(Into::into))
    }
}
impl ExactSizeIterator for Chars<'_> {
    fn len(&self) -> usize {
        delegate_iter!(&self.inner, i, i.len())
    }
}

pub fn get_chars(s: &str, range: std::ops::Range<usize>) -> &str {
    let mut chars = s.chars();
    for _ in 0..range.start {
        let _ = chars.next();
    }
    let start = chars.as_str();
    for _ in range {
        let _ = chars.next();
    }
    let end = chars.as_str();
    &start[..start.len() - end.len()]
}

pub fn zfill(bytes: &[u8], width: usize) -> Vec<u8> {
    if width <= bytes.len() {
        bytes.to_vec()
    } else {
        let (sign, s) = match bytes.first() {
            Some(_sign @ b'+') | Some(_sign @ b'-') => {
                (unsafe { bytes.get_unchecked(..1) }, &bytes[1..])
            }
            _ => (&b""[..], bytes),
        };
        let mut filled = Vec::new();
        filled.extend_from_slice(sign);
        filled.extend(std::iter::repeat(b'0').take(width - bytes.len()));
        filled.extend_from_slice(s);
        filled
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_chars() {
        let s = "0123456789";
        assert_eq!(get_chars(s, 3..7), "3456");
        assert_eq!(get_chars(s, 3..7), &s[3..7]);

        let s = "0유니코드 문자열9";
        assert_eq!(get_chars(s, 3..7), "코드 문");

        let s = "0😀😃😄😁😆😅😂🤣9";
        assert_eq!(get_chars(s, 3..7), "😄😁😆😅");
    }
}
