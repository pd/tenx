use rand::{thread_rng, Rng};
use std::fmt;
use std::slice::Iter;
use itertools::Itertools;

pub type Points = u64;

pub fn all() -> Iter<'static, Piece> {
    ALL.iter()
}

pub fn by_name(name: &str) -> &'static Piece {
    all().find(|pc| pc.name == name).expect("no such piece")
}

pub fn by_id(id: usize) -> &'static Piece {
    &ALL[id - 1]
}

pub fn offsets_of(pc: &'static Piece) -> &'static Vec<(isize, isize)> {
    &OFFSETS[pc.id]
}

#[derive(Clone, Copy)]
pub struct Piece {
    pub id: usize,
    pub name: &'static str,
    pub value: Points,
    pub occ: u32,
}

impl fmt::Debug for Piece {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Piece {
    pub fn random() -> &'static Piece {
        let n = thread_rng().gen_range(0, ALL.len());
        by_id(n + 1)
    }

    pub fn offsets(&self) -> Vec<(isize, isize)> {
        let bits = self.occ;
        let x1 = bits.trailing_zeros() as isize;

        (0..5).cartesian_product(0..5).fold(vec![], |mut offsets, (x, y)| {
            if self.is_bit_set(x, y) {
                offsets.push((x as isize - x1, y as isize));
            }
            offsets
        })
    }

    fn is_bit_set(&self, x: usize, y: usize) -> bool {
        self.occ & (1 << (y * 5 + x)) != 0
    }
}

macro_rules! define_piece {
    ($id:expr, $name:expr, $bits:expr) => {
        Piece {
            id:    $id,
            name:  $name,
            occ:   $bits,
            value: ($bits as u32).count_ones() as u64,
        }
    }
}

lazy_static! {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    static ref ALL: [Piece; 19] = [
        define_piece!( 1, "Uni",     0b1),
        define_piece!( 2, "DuoUD",   0b100001),
        define_piece!( 3, "DuoLR",   0b11),
        define_piece!( 4, "TriUD",   0b10000100001),
        define_piece!( 5, "TriLR",   0b111),
        define_piece!( 6, "TriNW",   0b1000011),
        define_piece!( 7, "TriNE",   0b100011),
        define_piece!( 8, "TriSW",   0b1100010),
        define_piece!( 9, "TriSE",   0b1100001),
        define_piece!(10, "QuadUD",  0b1000010000100001),
        define_piece!(11, "QuadLR",  0b1111),
        define_piece!(12, "Square2", 0b1100011),
        define_piece!(13, "Square3", 0b1110011100111),
        define_piece!(14, "EllNW",   0b001000010000111),
        define_piece!(15, "EllNE",   0b000010000100111),
        define_piece!(16, "EllSE",   0b1110000100001),
        define_piece!(17, "EllSW",   0b1110010000100),
        define_piece!(18, "PentUD",  0b100001000010000100001),
        define_piece!(19, "PentLR",  0b11111),
    ];

    static ref OFFSETS: [Vec<(isize, isize)>; 20] = [
        vec![],
        by_id(1).offsets(),
        by_id(2).offsets(),
        by_id(3).offsets(),
        by_id(4).offsets(),
        by_id(5).offsets(),
        by_id(6).offsets(),
        by_id(7).offsets(),
        by_id(8).offsets(),
        by_id(9).offsets(),
        by_id(10).offsets(),
        by_id(11).offsets(),
        by_id(12).offsets(),
        by_id(13).offsets(),
        by_id(14).offsets(),
        by_id(15).offsets(),
        by_id(16).offsets(),
        by_id(17).offsets(),
        by_id(18).offsets(),
        by_id(19).offsets(),
    ];
}
