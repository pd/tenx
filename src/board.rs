use std::fmt;
use std::u64;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not};

use piece;
use piece::Piece;

#[derive(Debug)]
pub enum PlacementError {
    OutOfBounds(usize, usize),
    Occupied(Piece, usize, usize),
}

#[inline]
pub fn index(x: usize, y: usize) -> usize {
    y * 10 + x
}

#[inline]
fn dxy(x: usize, dx: isize, y: usize, dy: isize) -> (isize, isize) {
    (x as isize + dx, y as isize + dy)
}

#[inline]
fn in_bounds(x: isize, y: isize) -> bool {
    x >= 0 && x < 10 && y >= 0 && y < 10
}

#[derive(Debug, Clone, Copy)]
pub enum Line {
    Col(usize),
    Row(usize),
}

macro_rules! line_mask {
    (x: $col:expr) => {
        (0..10).fold(Bitboard::new(), |board, y| board.fill_square($col, y))
    };

    (y: $row:expr) => {
        (0..10).fold(Bitboard::new(), |board, x| board.fill_square(x, $row))
    }
}

lazy_static! {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    pub static ref MASKS_COL: [Bitboard; 10] = [
        line_mask!(x: 0), line_mask!(x: 1), line_mask!(x: 2), line_mask!(x: 3), line_mask!(x: 4),
        line_mask!(x: 5), line_mask!(x: 6), line_mask!(x: 7), line_mask!(x: 8), line_mask!(x: 9),
    ];

    #[cfg_attr(rustfmt, rustfmt_skip)]
    pub static ref MASKS_ROW: [Bitboard; 10] = [
        line_mask!(y: 0), line_mask!(y: 1), line_mask!(y: 2), line_mask!(y: 3), line_mask!(y: 4),
        line_mask!(y: 5), line_mask!(y: 6), line_mask!(y: 7), line_mask!(y: 8), line_mask!(y: 9),
    ];
}

/// Bitboard represents the state of the board and the pieces
/// available to play. The 100 least significant bits, starting in the
/// first element of the backing tuple, are used to represent the
/// occupancy of a given square, with `(0,0)` being the LSB. The next
/// 15 bits represent the pieces available to play, using 5 bits each.
#[derive(Debug, Copy, Clone)]
pub struct Bitboard(pub u64, pub u64);

const MASK_BOARD_HIGH_BITS: u64 = 0xfffffffff;
const MASK_PIECES: u64 = 0x7fff << 36;

// #[allow(dead_code)]
// const MASK_BOARD: Bitboard = Bitboard(u64::MAX, MASK_BOARD_HIGH_BITS);
// const MASK_PIECE0: u64 = 0xf << 36;
// const MASK_PIECE1: u64 = 0xf << 41;
// const MASK_PIECE2: u64 = 0xf << 46;

impl Bitboard {
    pub fn new() -> Bitboard {
        Bitboard(0, 0)
    }

    fn lower_bits(&self)  -> u64 { self.0 }
    fn higher_bits(&self) -> u64 { self.1 & MASK_BOARD_HIGH_BITS }

    pub fn is_empty(&self) -> bool {
        self.lower_bits() == 0 && self.higher_bits() == 0
    }

    pub fn is_occupied(&self, x: usize, y: usize) -> bool {
        self.is_bit_set(index(x, y))
    }

    pub fn occupancy(&self) -> usize {
        self.lower_bits().count_ones() as usize + self.higher_bits().count_ones() as usize
    }

    pub fn can_fit(&self, pc: &'static Piece, x: usize, y: usize) -> bool {
        if self.is_occupied(x, y) {
            return false;
        }

        piece::offsets_of(pc).iter().all(|&(dx, dy)| {
            let (nx, ny) = dxy(x, dx, y, dy);
            in_bounds(nx, ny) && !self.is_occupied(nx as usize, ny as usize)
        })
    }

    pub fn place(&self,
                 pc: &'static Piece,
                 x: usize,
                 y: usize)
                 -> Result<Bitboard, PlacementError> {
        if !in_bounds(x as isize, y as isize) {
            return Err(PlacementError::OutOfBounds(x, y));
        }

        if !self.can_fit(pc, x, y) {
            return Err(PlacementError::Occupied(*pc, x, y));
        }

        let mut board = self.clone();
        for &(dx, dy) in piece::offsets_of(pc).iter() {
            let (nx, ny) = dxy(x, dx, y, dy);
            board.set_bit(index(nx as usize, ny as usize));
        }

        Ok(board)
    }

    pub fn filled(&self) -> Vec<Line> {
        let cols = MASKS_COL.iter()
            .enumerate()
            .filter(|&(_, &mask)| (*self & mask).occupancy() == 10)
            .map(|(x, _)| Line::Col(x));

        let rows = MASKS_ROW.iter()
            .enumerate()
            .filter(|&(_, &mask)| (*self & mask).occupancy() == 10)
            .map(|(y, _)| Line::Row(y));

        cols.chain(rows).collect()
    }

    pub fn fill_square(&self, x: usize, y: usize) -> Bitboard {
        let mut new = self.clone();
        new.set_bit(index(x, y));
        new
    }

    pub fn empty_square(&self, x: usize, y: usize) -> Bitboard {
        let mut new = self.clone();
        new.clear_bit(index(x, y));
        new
    }

    pub fn clear(&self, line: Line) -> Bitboard {
        match line {
            Line::Col(x) => *self & !MASKS_COL[x],
            Line::Row(y) => *self & !MASKS_ROW[y],
        }
    }

    pub fn with_pieces(&self, pieces: [&'static Piece; 3]) -> Bitboard {
        let mut new = self.clone();
        new.1 &= !MASK_PIECES;
        new.1 |= (pieces[0].id as u64) << 36 | (pieces[1].id as u64) << 41 |
                 (pieces[2].id as u64) << 46;
        new
    }

    pub fn without_piece(&self, n: usize) -> Bitboard {
        let mut new = self.clone();
        let mask = (0x1f as u64) << (36 + 5 * n);
        new.1 &= !mask;
        new
    }

    pub fn no_remaining_pieces(&self) -> bool {
        (self.1 & MASK_PIECES) >> 36 == 0
    }

    pub fn pieces(&self) -> [Option<&'static Piece>; 3] {
        [self.piece(0), self.piece(1), self.piece(2)]
    }

    pub fn piece(&self, n: usize) -> Option<&'static Piece> {
        let id = (self.1 >> 36 + 5 * n) as usize & 0x1f;
        if id == 0 { None } else { Some(piece::by_id(id)) }
    }

    fn is_bit_set(&self, n: usize) -> bool {
        if n <= 63 { self.0 & (1 << n) != 0 } else { self.1 & (1 << (n - 64)) != 0 }
    }

    fn clear_bit(&mut self, n: usize) {
        if n <= 63 {
            self.0 &= !(1 << n);
        } else {
            self.1 &= !(1 << (n - 64));
        }
    }

    fn set_bit(&mut self, n: usize) {
        if n <= 63 {
            self.0 |= 1 << n;
        } else {
            self.1 |= 1 << (n - 64);
        }
    }
}

impl BitAnd for Bitboard {
    type Output = Bitboard;

    fn bitand(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 & rhs.0, self.1 & rhs.1)
    }
}

impl BitOr for Bitboard {
    type Output = Bitboard;

    fn bitor(self, rhs: Bitboard) -> Bitboard {
        Bitboard(self.0 | rhs.0, self.1 | rhs.1)
    }
}

impl BitAndAssign for Bitboard {
    fn bitand_assign(&mut self, rhs: Bitboard) {
        self.0 &= rhs.0;
        self.1 &= rhs.1;
    }
}

impl BitOrAssign for Bitboard {
    fn bitor_assign(&mut self, rhs: Bitboard) {
        self.0 |= rhs.0;
        self.1 |= rhs.1;
    }
}

impl Not for Bitboard {
    type Output = Bitboard;

    fn not(self) -> Bitboard {
        Bitboard(!self.0, !self.1)
    }
}

impl fmt::Display for Bitboard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::new();
        for y in 0..10 {
            for x in 0..10 {
                s.push(if self.is_occupied(x, y) { 'X' } else { ' ' });
            }
            s.push('\n');
        }
        write!(f, "{}", s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use piece;
    use itertools::Itertools;

    #[test]
    fn test_place_piece() {
        let board = Bitboard::new();
        assert!(board.is_empty());
        assert_eq!(board.occupancy(), 0);

        for (x, y) in (0..10).cartesian_product(0..10) {
            match board.place(piece::by_name("Uni"), x, y) {
                Ok(new) => {
                    assert_eq!(new.occupancy(), 1);
                    assert!(new.is_occupied(x, y));
                },
                Err(e) => panic!("Could not place piece: {:?}", e),
            }
        }
    }

    #[test]
    fn test_fit_obvious() {
        let empty_board = Bitboard::new();
        assert_eq!(empty_board.occupancy(), 0);

        // every piece can fit at (3, 0). this is a dumb test,
        // but establishes a baseline.
        for pc in piece::all() {
            assert!(empty_board.can_fit(pc, 3, 0),
                    "Piece {} should fit at (3, 0)",
                    pc.name);
        }

        // but only pieces filled at (0, 0) can fit at the board's (0, 0)
        for pc in piece::all() {
            if pc.occ.trailing_zeros() == 0 {
                assert!(empty_board.can_fit(pc, 0, 0),
                        "Piece {} should fit at (0, 0)",
                        pc.name);
            } else {
                assert!(!empty_board.can_fit(pc, 0, 0),
                        "Piece {} should not fit at (0, 0)",
                        pc.name);
            }
        }

        // and no piece will fit anywhere on a full board
        let full = (0..10).cartesian_product(0..10)
            .fold(Bitboard::new(), |b, (x, y)| {
                let mut new = b.clone();
                new.set_bit(index(x, y));
                new
            });
        assert_eq!(full.occupancy(), 100);
        for pc in piece::all() {
            for (x, y) in (0..10).cartesian_product(0..10) {
                assert!(!full.can_fit(pc, x, y));
            }
        }

        // clear a few squares, ensure only the correct pieces fit.
        let nearly_full = full.empty_square(0, 0).empty_square(0, 1).empty_square(1, 1);

        macro_rules! assert_fit {
            ($board:expr, $pc:expr, ($x:expr, $y:expr)) => {
                assert!($board.can_fit($pc, $x, $y), "Piece {} should fit at ({}, {})", $pc.name, $x, $y);
            }
        }

        macro_rules! assert_no_fit {
            ($board:expr, $pc:expr, ($x:expr, $y:expr)) => {
                assert!(!$board.can_fit($pc, $x, $y), "Piece {} should not fit at ({}, {})", $pc.name, $x, $y);
            }
        }

        for pc in piece::all() {
            match pc.name {
                "Uni" => {
                    assert_fit!(nearly_full, pc, (0, 0));
                    assert_fit!(nearly_full, pc, (0, 1));
                    assert_fit!(nearly_full, pc, (1, 1));
                }
                "DuoUD" | "TriSE" => {
                    assert_fit!(nearly_full, pc, (0, 0));
                    assert_no_fit!(nearly_full, pc, (0, 1));
                    assert_no_fit!(nearly_full, pc, (1, 1));
                }
                "DuoLR" => {
                    assert_fit!(nearly_full, pc, (0, 1));
                    assert_no_fit!(nearly_full, pc, (0, 0));
                    assert_no_fit!(nearly_full, pc, (1, 1));
                }
                _ => {
                    assert_no_fit!(nearly_full, pc, (0, 0));
                    assert_no_fit!(nearly_full, pc, (0, 1));
                    assert_no_fit!(nearly_full, pc, (1, 1));
                }
            }
        }
    }

    #[test]
    fn test_clear() {
        let board = (0..10).cartesian_product(0..10)
            .fold(Bitboard::new(), |b, (x, y)| {
                let mut new = b.clone();
                new.set_bit(index(x, y));
                new
            }).with_pieces([piece::by_name("Uni"),
                            piece::by_name("Uni"),
                            piece::by_name("Uni")]);

        for x in 0..10 {
            let new = board.clear(Line::Col(x));
            assert_eq!(new.occupancy(), 90);
            assert_eq!(new.filled().len(), 9);

            for y in 0..10 {
                assert!(!new.is_occupied(x, y));
            }

            assert!(new.pieces().iter().all(|pc| pc.is_some()));
        }

        for y in 0..10 {
            let new = board.clear(Line::Row(y));
            assert_eq!(new.occupancy(), 90);
            assert_eq!(new.filled().len(), 9);
            for x in 0..10 {
                assert!(!new.is_occupied(x, y));
            }
            assert!(new.pieces().iter().all(|pc| pc.is_some()));
        }
    }

    #[test]
    fn test_pieces() {
        assert!(Bitboard::new().no_remaining_pieces());

        let board = Bitboard::new().with_pieces([piece::by_name("Uni"),
                                                 piece::by_name("DuoUD"),
                                                 piece::by_name("Square3")]);

        assert_eq!(board.piece(0).expect("piece 0 should be present").name, "Uni");
        assert_eq!(board.piece(1).expect("piece 1 should be present").name, "DuoUD");
        assert_eq!(board.piece(2).expect("piece 2 should be present").name, "Square3");

        let fewer = board.without_piece(0);
        assert!(fewer.piece(0).is_none());
        assert_eq!(fewer.piece(1).expect("piece 1 should be present").name, "DuoUD");
        assert_eq!(fewer.piece(2).expect("piece 2 should be present").name, "Square3");

        let to_play = fewer.without_piece(2).pieces();
        assert!(to_play[0].is_none());
        assert!(to_play[1].is_some());
        assert!(to_play[2].is_none());
    }
}
