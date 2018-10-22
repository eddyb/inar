use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Shl, Shr, Sub};
use signed::{Plus, Sign, Signed};

pub trait Zero: Sized {
    const ZERO: Self;
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Zeroid<T> {
    /// The zero value.
    At,

    /// Any other value than zero (whether positive or negative).
    Apart(T),
}

impl<T> Zero for Zeroid<T> {
    const ZERO: Self = Zeroid::At;
}

impl<T> Zeroid<T> {
    pub fn as_ref<'a>(&'a self) -> Zeroid<&'a T> {
        match *self {
            Zeroid::At => Zeroid::At,
            Zeroid::Apart(ref x) => Zeroid::Apart(x),
        }
    }

    pub fn map<F: FnOnce(T) -> U, U>(self, f: F) -> Zeroid<U> {
        match self {
            Zeroid::At => Zeroid::At,
            Zeroid::Apart(x) => Zeroid::Apart(f(x)),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Zeroid<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Zeroid::At => write!(f, "0"),
            Zeroid::Apart(ref x) => write!(f, "{:?}", x),
        }
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Zeroid<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Zeroid::At => write!(f, "0"),
            Zeroid::Apart(ref x) => write!(f, "{:x}", x),
        }
    }
}

impl PartialOrd for Zeroid<Sign> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Zeroid<Sign> {
    fn cmp(&self, other: &Self) -> Ordering {
        let (a, b) = match (*self, *other) {
            (Zeroid::At, Zeroid::At) => (Plus, Plus),

            // Use the opposite sign as 0.
            (Zeroid::Apart(x), Zeroid::At) => (x, -x),
            (Zeroid::At, Zeroid::Apart(x)) => (-x, x),

            (Zeroid::Apart(a), Zeroid::Apart(b)) => (a, b),
        };
        a.cmp(&b)
    }
}

impl<T: PartialOrd> PartialOrd for Zeroid<Signed<T>> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (&Zeroid::Apart(ref a), &Zeroid::Apart(ref b)) => a.partial_cmp(b),
            (a, b) => a.as_ref()
                .map(|s| s.sign)
                .partial_cmp(&b.as_ref().map(|s| s.sign)),
        }
    }
}

impl<T: Ord> Ord for Zeroid<Signed<T>> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (&Zeroid::Apart(ref a), &Zeroid::Apart(ref b)) => a.cmp(b),
            (a, b) => a.as_ref().map(|s| s.sign).cmp(&b.as_ref().map(|s| s.sign)),
        }
    }
}

impl<T: Neg<Output = O>, O> Neg for Zeroid<T> {
    type Output = Zeroid<O>;
    fn neg(self) -> Zeroid<O> {
        self.map(|x| -x)
    }
}

impl<T: Add<U, Output = O>, U, O: From<Self> + From<Zeroid<U>>> Add<Zeroid<U>> for Zeroid<T> {
    type Output = O;
    fn add(self, other: Zeroid<U>) -> O {
        match (self, other) {
            (x, Zeroid::At) => O::from(x),
            (Zeroid::At, x) => O::from(x),
            (Zeroid::Apart(a), Zeroid::Apart(b)) => a + b,
        }
    }
}

impl<T: Sub<U, Output = O>, U: Neg<Output = U>, O: From<Self> + From<Zeroid<U>>> Sub<Zeroid<U>>
    for Zeroid<T> {
    type Output = O;
    fn sub(self, other: Zeroid<U>) -> O {
        match (self, other) {
            (x, Zeroid::At) => O::from(x),
            (Zeroid::At, x) => O::from(-x),
            (Zeroid::Apart(a), Zeroid::Apart(b)) => a - b,
        }
    }
}

impl<T: Mul<Output = O>, O: From<Self>> Mul for Zeroid<T> {
    type Output = O;
    fn mul(self, other: Self) -> O {
        match (self, other) {
            (_, Zeroid::At) | (Zeroid::At, _) => O::from(Zeroid::At),
            (Zeroid::Apart(a), Zeroid::Apart(b)) => a * b,
        }
    }
}

pub struct ZeroDivZero;
pub struct DivZero;

impl<T: Div<Output = O>, O: From<Self> + From<ZeroDivZero> + From<DivZero>> Div for Zeroid<T> {
    type Output = O;
    fn div(self, other: Self) -> O {
        match (self, other) {
            (Zeroid::At, Zeroid::At) => O::from(ZeroDivZero),
            (_, Zeroid::At) => O::from(DivZero),
            (Zeroid::At, _) => O::from(Zeroid::At),
            (Zeroid::Apart(a), Zeroid::Apart(b)) => a / b,
        }
    }
}

impl<T: Shl<U, Output = O>, U, O: From<Self>> Shl<U> for Zeroid<T> {
    type Output = O;
    fn shl(self, n: U) -> O {
        match self {
            Zeroid::At => O::from(Zeroid::At),
            Zeroid::Apart(x) => x << n,
        }
    }
}

impl<T: Shr<U, Output = O>, U, O: From<Self>> Shr<U> for Zeroid<T> {
    type Output = O;
    fn shr(self, n: U) -> O {
        match self {
            Zeroid::At => O::from(Zeroid::At),
            Zeroid::Apart(x) => x >> n,
        }
    }
}
