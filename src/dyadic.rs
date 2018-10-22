use std::cmp::Ordering;
use std::fmt;
use std::convert::TryFrom;
use std::ops::{Add, BitOr, Div, Mul, Shl, Shr, Sub};
use zeroid::{Zero, Zeroid};
use interval::Interval;
use signed::{Minus, Plus, Signed};
use ramp::int::Int;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Epsilon;

type Residue = Zeroid<Signed<Epsilon>>;

impl BitOr for Residue {
    type Output = Self;
    fn bitor(self, other: Self) -> Self {
        match (self, other) {
            (Zeroid::At, Zeroid::At) => Zeroid::At,
            (Zeroid::At, Zeroid::Apart(x)) | (Zeroid::Apart(x), Zeroid::At) => Zeroid::Apart(x),
            (Zeroid::Apart(a), Zeroid::Apart(b)) => {
                assert_eq!(a, b);
                self
            }
        }
    }
}

/// Marker for a fraction in "normal form", i.e. 1.0 <= x < 2.0.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Normal<T>(T);

impl<T: fmt::LowerHex> fmt::LowerHex for Normal<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}", self.0)
    }
}

pub trait Frac: Sized {
    const ONE: Self;
    fn is_normal(&self) -> bool;
    fn increment(x: Dyadic<Self>) -> Dyadic<Self>;
    fn decrement(x: Dyadic<Self>) -> Dyadic<Self>;
}

pub trait ExtraBit: Frac {
    type ExtraBit: Frac + From<Self>;
}

impl<T: Frac> Normal<T> {
    pub fn unwrap(self) -> T {
        assert!(self.0.is_normal());
        self.0
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dyadic<T> {
    exp: i8,
    frac: Normal<T>,
}

type IZSD<T> = Interval<Zeroid<Signed<Dyadic<T>>>>;

impl<T: Frac> From<T> for Dyadic<T> {
    fn from(x: T) -> Self {
        assert!(x.is_normal());
        Dyadic {
            exp: 0,
            frac: Normal(x),
        }
    }
}

impl From<u64> for IZSD<Frac63<u64>> {
    fn from(x: u64) -> Self {
        if x == 0 {
            return IZSD::from(Zeroid::At::<Signed<Dyadic<Frac63<u64>>>>);
        }

        let (x, r) = Frac64((x as u128) << 64).into();
        Zeroid::Apart(Signed::from(x)) + r
    }
}

impl<T: fmt::LowerHex> fmt::Debug for Dyadic<T> {
    default fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::LowerHex::fmt(self, f)
    }
}

impl fmt::Debug for Dyadic<Frac63<u64>> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let unit_bit = 63 - self.exp as i32;
        let mut frac = Int::from(self.frac.unwrap().0);
        let unit_bit = if unit_bit < 0 {
            frac <<= -unit_bit as usize;
            0
        } else {
            unit_bit as usize
        };
        let mask = (Int::one() << unit_bit) - 1;
        write!(f, "{}.", &frac >> unit_bit)?;
        frac &= &mask;
        loop {
            frac *= 10;
            write!(f, "{}", &frac >> unit_bit)?;
            frac &= &mask;
            if frac == 0 {
                break;
            }
        }
        Ok(())
    }
}

impl<T: fmt::LowerHex> fmt::LowerHex for Dyadic<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:x}p{:+}", self.frac, self.exp)
    }
}

impl<T: Copy + Frac> From<Residue> for IZSD<T> {
    fn from(_: Residue) -> Self {
        let mut result = Interval::from(Zeroid::At::<Signed<Dyadic<T>>>);
        result.hi.closed = false;
        result.hi.end = Zeroid::Apart(Signed::from(Dyadic {
            exp: i8::min_value(),
            frac: Normal(Frac::ONE),
        }));
        result
    }
}

impl<T: Copy + Frac> Add<Epsilon> for Dyadic<T> {
    type Output = IZSD<T>;
    fn add(self, _: Epsilon) -> IZSD<T> {
        let mut result = Interval::from(Zeroid::Apart(Signed::from(self)));
        result.hi.closed = false;
        result.hi.end = Zeroid::Apart(Signed::from(Frac::increment(self)));
        result
    }
}

impl<T: Copy + Frac> Sub<Epsilon> for Dyadic<T> {
    type Output = IZSD<T>;
    fn sub(self, _: Epsilon) -> IZSD<T> {
        let mut result = Interval::from(Zeroid::Apart(Signed::from(self)));
        result.lo.closed = false;
        result.lo.end = Zeroid::Apart(Signed::from(Frac::decrement(self)));
        result
    }
}

impl<T: Frac + Ord + Copy, U> Add for Dyadic<T>
where
    T: Shr<u32, Output = (T, Residue)> + Add<Output = U>,
    U: Into<(Self, Residue)>,
{
    type Output = IZSD<T>;
    fn add(self, other: Self) -> IZSD<T> {
        let (a_exp, b_exp) = (self.exp as i32, other.exp as i32);
        let (a, b, r, exp) = match a_exp.cmp(&b_exp) {
            Ordering::Equal => (
                self.frac.unwrap(),
                other.frac.unwrap(),
                Residue::ZERO,
                a_exp,
            ),
            Ordering::Less => {
                let (a, r) = self.frac.unwrap() >> ((b_exp - a_exp) as u32);
                (a, other.frac.unwrap(), r, b_exp)
            }
            Ordering::Greater => {
                let (b, r) = other.frac.unwrap() >> ((a_exp - b_exp) as u32);
                (self.frac.unwrap(), b, r, a_exp)
            }
        };
        let (x, r2) = (a + b).into();
        (Zeroid::Apart(Signed::from(x)) + (r | r2)) << exp
    }
}

impl<T: ExtraBit + Ord + Copy, U> Sub for Dyadic<T>
where
    T: Shr<u32, Output = (T, Residue)>,
    Normal<T>: Sub<T::ExtraBit, Output = Zeroid<Signed<U>>>,
    U: Into<(Self, Residue)>,
{
    type Output = IZSD<T>;
    fn sub(self, other: Self) -> IZSD<T> {
        let (a_exp, b_exp) = (self.exp as i32, other.exp as i32);
        let (a, b, r, sign, exp) = match a_exp.cmp(&b_exp) {
            Ordering::Equal => (self.frac, other.frac.unwrap(), Residue::ZERO, Plus, a_exp),
            Ordering::Less => {
                let (a, r) = self.frac.unwrap() >> ((b_exp - a_exp) as u32);
                (other.frac, a, r, Minus, b_exp)
            }
            Ordering::Greater => {
                let (b, r) = other.frac.unwrap() >> ((a_exp - b_exp) as u32);
                (self.frac, b, -r, Plus, a_exp)
            }
        };
        let mut r2 = Residue::ZERO;
        let x = (sign * (a - b.into())).map(|Signed { sign, abs }| {
            let (x, r3) = abs.into();
            r2 = sign * r3;
            Signed { sign, abs: x }
        });

        // r2 has a strictly higher "value" than r.
        let x = match r2 {
            Residue::ZERO => x + r,
            _ => x + r2,
        };
        x << exp
    }
}

// impl<T: Shr<i32, Output = U>, U: Sub<Output = V>, V: Shl<i32, Output = O>, O> Sub for Dyadic<T> {
//     type Output = O;
//     fn sub(self, other: Self) -> O {
//         let (a_exp, b_exp) = (self.exp as i32, other.exp as i32);
//         if a_exp > b_exp {
//             ((self.frac >> 0) - (other.frac >> (a_exp - b_exp))) << a_exp
//         } else {
//             ((self.frac >> (b_exp - a_exp)) - (other.frac >> 0)) << b_exp
//         }
//     }
// }

impl<T: Mul<Output = U> + Frac + Ord + Copy, U: Into<(Self, Residue)>> Mul for Dyadic<T> {
    type Output = IZSD<T>;
    fn mul(self, other: Self) -> IZSD<T> {
        let (x, r) = (self.frac.unwrap() * other.frac.unwrap()).into();
        (Zeroid::Apart(Signed::from(x)) + r) << (self.exp as i32 + other.exp as i32)
    }
}

impl<T: Ord + Copy + Frac, U: Into<(Self, Residue)>> Div for Dyadic<T>
where
    Normal<T>: Div<Output = U>,
{
    type Output = IZSD<T>;
    fn div(self, other: Self) -> IZSD<T> {
        let (x, r) = (self.frac / other.frac).into();
        (Zeroid::Apart(Signed::from(x)) + r) << (self.exp as i32 - other.exp as i32)
    }
}

impl<T: Copy> Shl<i32> for Dyadic<T> {
    type Output = IZSD<T>;
    fn shl(mut self, n: i32) -> IZSD<T> {
        // FIXME implement under/overflow.
        self.exp = TryFrom::try_from((self.exp as i32).checked_add(n).unwrap()).unwrap();
        Interval::from(Zeroid::Apart(Signed::from(self)))
    }
}

macro_rules! frac {
    ($($(#[$attr:meta])+ $name:ident, $unit:expr, [$($uint:ty),+];)+) => {
        $(
            $(#[$attr])*
            #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
            pub struct $name<T>(pub T);

            $(
                impl fmt::LowerHex for $name<$uint> {
                    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                        let bits = <$uint>::leading_zeros(0) as usize;
                        let units = self.0 >> $unit;
                        let frac = (self.0 & ((1 << $unit) - 1)) << (bits - $unit);
                        write!(f, "{:x}.{:02$x}", units, frac, bits / 4)
                    }
                }

                impl Frac for $name<$uint> {
                    const ONE: Self = $name(1 << $unit);
                    fn is_normal(&self) -> bool {
                        (self.0 >> $unit) == 1
                    }
                    fn increment(mut x: Dyadic<Self>) -> Dyadic<Self> {
                        match x.frac.unwrap().0.checked_add(1).map($name) {
                            Some(next) if next.is_normal() => {
                                x.frac = Normal(next);
                                x
                            }
                            _ => {
                                x.frac = Normal(Self::ONE);
                                let x = x << 1;
                                assert_eq!(x.lo.end, x.hi.end);
                                assert!(x.lo.closed && x.hi.closed);
                                match x.lo.end {
                                    Zeroid::At => unreachable!(),
                                    Zeroid::Apart(x) => {
                                        assert_eq!(x.sign, Plus);
                                        x.abs
                                    }
                                }
                            }
                        }
                    }
                    fn decrement(mut x: Dyadic<Self>) -> Dyadic<Self> {
                        match x.frac.unwrap().0.checked_sub(1).map($name) {
                            Some(next) if next.is_normal() => {
                                x.frac = Normal(next);
                                x
                            }
                            _ => {
                                x.frac = Normal(Self::ONE);
                                let x = x << -1;
                                assert_eq!(x.lo.end, x.hi.end);
                                assert!(x.lo.closed && x.hi.closed);
                                match x.lo.end {
                                    Zeroid::At => unreachable!(),
                                    Zeroid::Apart(x) => {
                                        assert_eq!(x.sign, Plus);
                                        x.abs
                                    }
                                }
                            }
                        }
                    }
                }

                impl Shr<u32> for $name<$uint> {
                    type Output = (Self, Residue);
                    fn shr(self, n: u32) -> (Self, Residue) {
                        let bits = <$uint>::leading_zeros(0);
                        // FIXME deduplicate.
                        if n >= bits {
                            let r = if self.0 == 0 {
                                Residue::ZERO
                            } else {
                                Zeroid::Apart(Signed::from(Epsilon))
                            };
                            return ($name(0), r);
                        }
                        let r = if self.0 & ((1 << n) - 1) == 0 {
                            Residue::ZERO
                        } else {
                            Zeroid::Apart(Signed::from(Epsilon))
                        };
                        ($name(self.0 >> n), r)
                    }
                }
            )+

            impl Into<(Dyadic<Frac63<u64>>, Residue)> for $name<u128> {
                fn into(self) -> (Dyadic<Frac63<u64>>, Residue) {
                    assert_ne!(self.0, 0);
                    let exp = (128 - self.0.leading_zeros() - 1) as i8 - 63;
                    let (normal, r) = if exp > 0 {
                        self >> exp as u32
                    } else {
                        ($name(self.0 << -exp), Residue::ZERO)
                    };
                    (
                        Dyadic {
                            exp: exp - ($unit - 63),
                            frac: Normal(Frac63(normal.0 as u64)),
                        },
                        r,
                    )
                }
            }
        )+
    }
}

frac! {
    /// Fixed-point binary fraction where 1.0 is represented as 2^63.
    Frac63, 63, [u64, u128];
    /// Fixed-point binary fraction where 1.0 is represented as 2^64.
    Frac64, 64, [u128];
    /// Fixed-point binary fraction where 1.0 is represented as 2^126.
    Frac126, 126, [u128];
}

impl From<Frac63<u64>> for Frac64<u128> {
    fn from(f: Frac63<u64>) -> Frac64<u128> {
        Frac64((f.0 as u128) << 1)
    }
}

impl ExtraBit for Frac63<u64> {
    type ExtraBit = Frac64<u128>;
}

impl Add for Frac63<u64> {
    type Output = Frac63<u128>;
    fn add(self, other: Self) -> Frac63<u128> {
        let (a, b) = (self.0 as u128, other.0 as u128);
        Frac63(a + b)
    }
}

impl Sub<Frac64<u128>> for Normal<Frac63<u64>> {
    type Output = Zeroid<Signed<Frac64<u128>>>;
    fn sub(self, other: Frac64<u128>) -> Zeroid<Signed<Frac64<u128>>> {
        let (a, b) = (Frac64::from(self.unwrap()).0, other.0);

        match a.cmp(&b) {
            Ordering::Equal => Zeroid::At,
            Ordering::Less => Zeroid::Apart(Signed {
                sign: Minus,
                abs: Frac64(b - a),
            }),
            Ordering::Greater => Zeroid::Apart(Signed {
                sign: Plus,
                abs: Frac64(a - b),
            }),
        }
    }
}

impl Mul for Frac63<u64> {
    type Output = Frac126<u128>;
    fn mul(self, other: Self) -> Frac126<u128> {
        let (a, b) = (self.0 as u128, other.0 as u128);
        Frac126(a * b)
    }
}

impl Div for Normal<Frac63<u64>> {
    type Output = Frac64<u128>;
    fn div(self, other: Self) -> Frac64<u128> {
        let (a, b) = (self.unwrap().0 as u128, other.unwrap().0 as u128);

        // `a / b` can "lose" its remainder when a and b are close,
        // so it suffices to consider `(x + 1) / x = 1 + 1 / x`,
        // where `x` is the largest possible value (`2^64 - 2` here).
        // That gives `1 + 1 / (2^64 - 2)` as the worst case, which
        // is countered here by shifting left to get the final result
        // of `2^64 + 2^64 / (2^64 - 2) = 2^64 + 1 + 2 / (2^64 - 2)`.
        // The `1` in the result is enough for the user to be able
        // to tell whether the division was imprecise in all cases.
        let mut x = (a << 64) / b;
        // HACK(eddyb) figure out why the above comment is actually wrong.
        if (a << 64) % b != 0 {
            // For imprecise divisions, set the lowest bit.
            x |= 1;
        }
        Frac64(x)
    }
}
