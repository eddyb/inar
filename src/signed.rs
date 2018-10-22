use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Shl, Shr, Sub};

pub use self::Sign::*;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sign {
    Minus,
    Plus,
}

impl fmt::Debug for Sign {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Minus => write!(f, "-"),
            Plus => write!(f, "+"),
        }
    }
}

impl Neg for Sign {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Minus => Plus,
            Plus => Minus,
        }
    }
}

impl<T: Neg<Output = O>, O: From<T>> Mul<T> for Sign {
    type Output = O;
    fn mul(self, x: T) -> O {
        match self {
            Minus => -x,
            Plus => O::from(x),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Signed<T> {
    pub sign: Sign,
    pub abs: T,
}

impl<T> From<T> for Signed<T> {
    fn from(abs: T) -> Self {
        Signed { sign: Plus, abs }
    }
}

impl<T: fmt::Debug> fmt::Debug for Signed<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:?}", self.sign, self.abs)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Signed<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{:x}", self.sign, self.abs)
    }
}

impl<T: PartialOrd> PartialOrd for Signed<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.sign.cmp(&other.sign) {
            Ordering::Equal => self.abs.partial_cmp(&other.abs).map(|ord| match self.sign {
                Minus => ord.reverse(),
                Plus => ord,
            }),
            ord => Some(ord),
        }
    }
}

impl<T: Ord> Ord for Signed<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.sign.cmp(&other.sign).then_with(|| {
            let ord = self.abs.cmp(&other.abs);
            match self.sign {
                Minus => ord.reverse(),
                Plus => ord,
            }
        })
    }
}

impl<T> Neg for Signed<T> {
    type Output = Self;
    fn neg(mut self) -> Self {
        self.sign = -self.sign;
        self
    }
}

impl<T: Add<U, Output = O> + Sub<U, Output = O>, U, O: Neg<Output = O>> Add<Signed<U>>
    for Signed<T> {
    type Output = O;
    fn add(self, other: Signed<U>) -> O {
        let abs = if self.sign == other.sign {
            self.abs + other.abs
        } else {
            self.abs - other.abs
        };
        self.sign * abs
    }
}

impl<T: Add<U, Output = O> + Sub<U, Output = O>, U, O: Neg<Output = O>> Sub<Signed<U>>
    for Signed<T> {
    type Output = O;
    fn sub(self, other: Signed<U>) -> O {
        self + (-other)
    }
}

impl<T: Mul<Output = O>, O: Neg<Output = O>> Mul for Signed<T> {
    type Output = O;
    fn mul(self, other: Self) -> O {
        self.sign * other.sign * (self.abs * other.abs)
    }
}

impl<T: Div<Output = O>, O: Neg<Output = O>> Div for Signed<T> {
    type Output = O;
    fn div(self, other: Self) -> O {
        self.sign * other.sign * (self.abs / other.abs)
    }
}

impl<T: Shl<U, Output = O>, U, O: Neg<Output = O>> Shl<U> for Signed<T> {
    type Output = O;
    fn shl(self, n: U) -> O {
        self.sign * (self.abs << n)
    }
}

impl<T: Shr<U, Output = O>, U, O: Neg<Output = O>> Shr<U> for Signed<T> {
    type Output = O;
    fn shr(self, n: U) -> O {
        self.sign * (self.abs >> n)
    }
}
