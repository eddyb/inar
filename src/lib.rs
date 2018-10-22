#![feature(i128_type, specialization, try_from)]

extern crate ramp;

pub mod dyadic;
pub mod interval;
pub mod signed;
pub mod zeroid;

pub type Inar =
    interval::Interval<zeroid::Zeroid<signed::Signed<dyadic::Dyadic<dyadic::Frac63<u64>>>>>;

#[test]
fn test() {
    let one = Inar::from(1);
    let two = one + one;
    let half = one / two;
    println!("{:<12} = {:x}", "1", one);
    println!("{:<12} = {:x}", "2", two);
    println!("{:<12} = {:x}", "1/2", half);
    println!("{:<12} = {:x}", "2*(1/2)", two * half);
    let tiny = one << -40;
    let huge = one << 40;
    println!("{:<12} = {:x}", "2^-40 + 2^40", tiny + huge);

    let mut u0 = Inar::from(2);
    let mut u1 = -Inar::from(4);
    for _ in 0..50 {
        let u2 = (Inar::from(111) - (Inar::from(1130) / u1)) + (Inar::from(3000) / (u1 * u0));
        println!("{:?}", u2);
        u0 = u1;
        u1 = u2;
    }

    let x = Inar::from(77617);
    let y = Inar::from(33096);
    let x2 = x.square();
    let y2 = y.square();
    let y4 = y2.square();
    let y6 = y2 * y4;
    let y8 = y4.square();
    let rump = ((Inar::from(33375) / Inar::from(100)) * y6)
        + (x2 * ((Inar::from(11) * x2 * y2) - y6 - (Inar::from(121) * y4) - Inar::from(2)))
        + ((Inar::from(55) / Inar::from(10)) * y8) + (x / (Inar::from(2) * y));
    println!("{:?}", rump);
}
