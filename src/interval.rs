use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, BitOr, Div, Mul, Neg, Shl, Shr, Sub};
use zeroid::{DivZero, ZeroDivZero, Zeroid};

pub trait Side: Sized {
    type Other: Side;
    const OTHER: Self::Other;
    fn get_from_interval<T>(x: Interval<T>) -> Bound<T, Self>;
}

#[derive(Copy, Clone)]
pub struct Lo;

impl Side for Lo {
    type Other = Hi;
    const OTHER: Hi = Hi;
    fn get_from_interval<T>(x: Interval<T>) -> Bound<T, Self> {
        x.lo
    }
}

#[derive(Copy, Clone)]
pub struct Hi;

impl Side for Hi {
    type Other = Lo;
    const OTHER: Lo = Lo;
    fn get_from_interval<T>(x: Interval<T>) -> Bound<T, Self> {
        x.hi
    }
}

#[derive(Copy, Clone)]
pub struct Bound<T, S: Side> {
    pub end: T,
    pub closed: bool,
    pub side: S,
}

impl<T: fmt::Debug> fmt::Debug for Bound<T, Lo> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{:?}", if self.closed { '[' } else { '(' }, self.end)
    }
}

impl<T: fmt::Debug> fmt::Debug for Bound<T, Hi> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}{}", self.end, if self.closed { ']' } else { ')' })
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Bound<T, Lo> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{:x}", if self.closed { '[' } else { '(' }, self.end)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Bound<T, Hi> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}{}", self.end, if self.closed { ']' } else { ')' })
    }
}

impl<T: Neg, S: Side> Neg for Bound<T, S> {
    type Output = Bound<T::Output, S::Other>;
    fn neg(self) -> Self::Output {
        Bound {
            end: -self.end,
            closed: self.closed,
            side: S::OTHER,
        }
    }
}

impl<T: Add<Output = Interval<T>>, S: Side> Add for Bound<T, S> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut r = (self.end + other.end).get(self.side);
        r.closed &= self.closed & other.closed;
        r
    }
}

impl<T: Sub<Output = Interval<T>>, S: Side> Sub<Bound<T, S::Other>> for Bound<T, S> {
    type Output = Self;
    fn sub(self, other: Bound<T, S::Other>) -> Self {
        let mut r = (self.end - other.end).get(self.side);
        r.closed &= self.closed & other.closed;
        r
    }
}

impl<T: Mul<Output = Interval<T>>, S: Side, S2: Side> Mul<Bound<T, S2>> for Bound<T, S> {
    type Output = Interval<T>;
    fn mul(self, other: Bound<T, S2>) -> Interval<T> {
        let closed = self.closed & other.closed;
        let mut r = self.end * other.end;
        r.lo.closed &= closed;
        r.hi.closed &= closed;
        r
    }
}

impl<T: Div<Output = Interval<T>>, S: Side, S2: Side> Div<Bound<T, S2>> for Bound<T, S> {
    type Output = Interval<T>;
    fn div(self, other: Bound<T, S2>) -> Interval<T> {
        let closed = self.closed & other.closed;
        let mut r = self.end / other.end;
        r.lo.closed &= closed;
        r.hi.closed &= closed;
        r
    }
}

impl<T: Shl<U, Output = Interval<T>>, U, S: Side> Shl<U> for Bound<T, S> {
    type Output = Self;
    fn shl(self, n: U) -> Self {
        let mut r = (self.end << n).get(self.side);
        r.closed &= self.closed;
        r
    }
}

impl<T: Shr<U, Output = Interval<T>>, U, S: Side> Shr<U> for Bound<T, S> {
    type Output = Self;
    fn shr(self, n: U) -> Self {
        let mut r = (self.end >> n).get(self.side);
        r.closed &= self.closed;
        r
    }
}

#[derive(Copy, Clone)]
pub struct Interval<T> {
    pub lo: Bound<T, Lo>,
    pub hi: Bound<T, Hi>,
}

impl<T> Interval<T> {
    fn get<S: Side>(self, _: S) -> Bound<T, S> {
        S::get_from_interval(self)
    }
}

impl<T: Copy> From<T> for Interval<T> {
    fn from(value: T) -> Interval<T> {
        Interval {
            lo: Bound {
                end: value,
                closed: true,
                side: Lo,
            },
            hi: Bound {
                end: value,
                closed: true,
                side: Hi,
            },
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Interval<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}, {:?}", self.lo, self.hi)
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Interval<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}, {:x}", self.lo, self.hi)
    }
}

impl<T: Neg<Output = T>> Neg for Interval<T> {
    type Output = Self;
    fn neg(self) -> Self {
        Interval {
            lo: -self.hi,
            hi: -self.lo,
        }
    }
}

impl<T: Ord> BitOr for Interval<T> {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        let lo = {
            let (a, b) = (self.lo, other.lo);
            match a.end.cmp(&b.end) {
                Ordering::Less => a,
                Ordering::Greater => b,
                Ordering::Equal => Bound {
                    end: a.end,
                    closed: a.closed | b.closed,
                    side: Lo,
                },
            }
        };
        let hi = {
            let (a, b) = (self.hi, other.hi);
            match a.end.cmp(&b.end) {
                Ordering::Less => b,
                Ordering::Greater => a,
                Ordering::Equal => Bound {
                    end: a.end,
                    closed: a.closed | b.closed,
                    side: Hi,
                },
            }
        };
        Interval { lo, hi }
    }
}

impl<T: Add<Output = Self>> Add for Interval<T> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Interval {
            lo: self.lo + other.lo,
            hi: self.hi + other.hi,
        }
    }
}

impl<T: Sub<Output = Self>> Sub for Interval<T> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Interval {
            lo: self.lo - other.hi,
            hi: self.hi - other.lo,
        }
    }
}

impl<T: Mul<Output = Self> + Copy + Ord> Mul for Interval<T> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        (self.lo * other.lo) | (self.lo * other.hi) | (self.hi * other.lo) | (self.hi * other.hi)
    }
}

impl<T: Mul<Output = Self> + Copy + Ord> Interval<T> {
    pub fn square(self) -> Self {
        (self.lo * self.lo) | (self.hi * self.hi)
    }
}

impl<T> From<ZeroDivZero> for Interval<T> {
    fn from(_: ZeroDivZero) -> Self {
        panic!("0 / 0")
    }
}

impl<T> From<DivZero> for Interval<T> {
    fn from(_: DivZero) -> Self {
        panic!("x / 0")
    }
}

impl<T: Copy> Div for Interval<Zeroid<T>>
where
    Zeroid<T>: Ord + Div<Output = Self>,
{
    type Output = Self;
    fn div(self, other: Self) -> Self {
        // Division by an interval containing zero ends up diverging,
        // and can only be represented as the same interval as 0 / 0.
        let zero = Zeroid::At;
        if other.lo.end < zero && zero < other.hi.end {
            return zero / zero;
        }

        (self.lo / other.lo) | (self.lo / other.hi) | (self.hi / other.lo) | (self.hi / other.hi)
    }
}

impl<T: Shl<U, Output = Self>, U: Copy> Shl<U> for Interval<T> {
    type Output = Self;
    fn shl(self, n: U) -> Self {
        Interval {
            lo: self.lo << n,
            hi: self.hi << n,
        }
    }
}

impl<T: Shr<U, Output = Self>, U: Copy> Shr<U> for Interval<T> {
    type Output = Self;
    fn shr(self, n: U) -> Self {
        Interval {
            lo: self.lo >> n,
            hi: self.hi >> n,
        }
    }
}
