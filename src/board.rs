use rand::{thread_rng, Rng};
use std::fmt;
use itertools::Itertools;

pub type Points = u64;

#[derive(Debug, Clone, Copy)]
pub enum Line {
    Col(usize),
    Row(usize),
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
        let n = thread_rng().gen_range(0, PIECES.len());
        &PIECES[n]
    }

    #[inline]
    pub fn is_bit_set(&self, x: usize, y: usize) -> bool {
        self.occ & (1 << (y * 5 + x)) != 0
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
    pub static ref PIECES: [Piece; 19] = [
        define_piece!( 0, "Uni",     0b1),
        define_piece!( 1, "DuoUD",   0b100001),
        define_piece!( 2, "DuoLR",   0b11),
        define_piece!( 3, "TriUD",   0b10000100001),
        define_piece!( 4, "TriLR",   0b111),
        define_piece!( 5, "TriNW",   0b1000011),
        define_piece!( 6, "TriNE",   0b100011),
        define_piece!( 7, "TriSW",   0b1100010),
        define_piece!( 8, "TriSE",   0b1100001),
        define_piece!( 9, "QuadUD",  0b1000010000100001),
        define_piece!(10, "QuadLR",  0b1111),
        define_piece!(11, "Square2", 0b1100011),
        define_piece!(12, "Square3", 0b1110011100111),
        define_piece!(13, "EllNW",   0b001000010000111),
        define_piece!(14, "EllNE",   0b000010000100111),
        define_piece!(15, "EllSE",   0b1110000100001),
        define_piece!(16, "EllSW",   0b1110010000100),
        define_piece!(17, "PentUD",  0b100001000010000100001),
        define_piece!(18, "PentLR",  0b11111),
    ];

    pub static ref OFFSETS: [Vec<(isize, isize)>; 19] = [
        PIECES[0].offsets(),
        PIECES[1].offsets(),
        PIECES[2].offsets(),
        PIECES[3].offsets(),
        PIECES[4].offsets(),
        PIECES[5].offsets(),
        PIECES[6].offsets(),
        PIECES[7].offsets(),
        PIECES[8].offsets(),
        PIECES[9].offsets(),
        PIECES[10].offsets(),
        PIECES[11].offsets(),
        PIECES[12].offsets(),
        PIECES[13].offsets(),
        PIECES[14].offsets(),
        PIECES[15].offsets(),
        PIECES[16].offsets(),
        PIECES[17].offsets(),
        PIECES[18].offsets(),
    ];
}

#[inline]
fn index(x: usize, y: usize) -> usize {
    y * 10 + x
}

#[inline]
fn to_pos(i: usize) -> (usize, usize) {
    (i % 10, i / 10)
}

#[inline]
fn dxy(x: usize, dx: isize, y: usize, dy: isize) -> (isize, isize) {
    (x as isize + dx, y as isize + dy)
}

#[inline]
fn in_bounds(x: isize, y: isize) -> bool {
    x >= 0 && x < 10 && y >= 0 && y < 10
}

pub enum PlacementError {
    OutOfBounds(usize, usize),
    Occupied(Piece, usize, usize),
}

#[derive(Debug, Clone)]
pub struct Board {
    squares: Vec<Option<&'static Piece>>,
}

impl Board {
    pub fn new() -> Board {
        let mut squares = vec![];
        squares.resize(100, None);
        Board { squares: squares }
    }

    pub fn is_empty(&self) -> bool {
        self.occupancy() == 0
    }

    pub fn is_occupied(&self, x: usize, y: usize) -> bool {
        self.squares[index(x, y)].is_some()
    }

    pub fn occupancy(&self) -> usize {
        self.squares.iter().filter(|x| x.is_some()).count()
    }

    pub fn unoccupied_squares(&self) -> Vec<(usize, usize)> {
        self.squares
            .iter()
            .enumerate()
            .filter_map(|(i, pc)| if pc.is_none() { Some(to_pos(i)) } else { None })
            .collect()
    }

    pub fn filled(&self) -> Vec<Line> {
        let cols = (0..10)
            .filter_map(|x| match (0..10).all(|y| self.is_occupied(x, y)) {
                true => Some(Line::Col(x)),
                false => None,
            });

        let rows = (0..10)
            .filter_map(|y| match (0..10).all(|x| self.is_occupied(x, y)) {
                true => Some(Line::Row(y)),
                false => None,
            });

        cols.chain(rows).collect()
    }

    pub fn can_fit(&self, pc: &'static Piece, x: usize, y: usize) -> bool {
        if self.is_occupied(x, y) {
            return false;
        }

        OFFSETS[pc.id].iter().all(|&(dx, dy)| {
            let (nx, ny) = dxy(x, dx, y, dy);
            in_bounds(nx, ny) && !self.is_occupied(nx as usize, ny as usize)
        })
    }

    // Place pc at (x, y).
    pub fn place(&self, pc: &'static Piece, x: usize, y: usize) -> Result<Board, PlacementError> {
        if !in_bounds(x as isize, y as isize) {
            return Err(PlacementError::OutOfBounds(x, y));
        }

        if !self.can_fit(pc, x, y) {
            return Err(PlacementError::Occupied(*pc, x, y));
        }

        let mut squares = self.squares.clone();
        for &(dx, dy) in OFFSETS[pc.id].iter() {
            let (nx, ny) = dxy(x, dx, y, dy);
            squares[index(nx as usize, ny as usize)] = Some(pc)
        }

        Ok(Board { squares: squares })
    }

    pub fn clear(&self, line: Line) -> Board {
        let mut squares = self.squares.clone();

        match line {
            Line::Row(y) => {
                for x in 0..10 {
                    squares[index(x, y)] = None;
                }
            }
            Line::Col(x) => {
                for y in 0..10 {
                    squares[index(x, y)] = None;
                }
            }
        }

        Board { squares: squares }
    }

    // Unconditionally fill only (x, y) with pc.
    pub fn put_square(&self, pc: &'static Piece, x: usize, y: usize) -> Board {
        let mut squares = self.squares.clone();
        squares[index(x, y)] = Some(pc);
        Board { squares: squares }
    }

    pub fn remove(&self, x: usize, y: usize) -> Board {
        let mut squares = self.squares.clone();
        squares[index(x, y)] = None;
        Board { squares: squares }
    }
}

impl fmt::Display for Board {
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
    use super::{PIECES, Piece, Board, Line};
    use itertools::Itertools;

    fn piece_by_name(name: &str) -> &'static Piece {
        PIECES.iter().find(|pc| pc.name == name).expect("no such piece")
    }

    fn filled_board() -> Board {
        let uni = piece_by_name("Uni");
        let all_squares = (0..10).cartesian_product(0..10);
        all_squares.fold(Board::new(), |b, (x, y)| b.put_square(uni, x, y))
    }

    #[test]
    fn test_clear() {
        let mut board = filled_board().clear(Line::Col(0));
        assert_eq!(board.occupancy(), 90);
        for y in 0..10 {
            assert!(!board.is_occupied(0, y));
        }

        board = board.clear(Line::Row(3));
        assert_eq!(board.occupancy(), 81);
        for x in 0..10 {
            assert!(!board.is_occupied(x, 3));
        }
    }

    #[test]
    fn test_fit_obvious() {
        let empty_board = Board::new();
        assert_eq!(empty_board.occupancy(), 0);

        // every piece can fit at (3, 0). this is a dumb test,
        // but establishes a baseline.
        for pc in PIECES.iter() {
            assert!(empty_board.can_fit(pc, 3, 0),
                    "Piece {} should fit at (3, 0)",
                    pc.name);
        }

        // but only pieces filled at (0, 0) can fit at the board's (0, 0)
        for pc in PIECES.iter() {
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
        let full = filled_board();
        assert_eq!(full.occupancy(), 100);
        for pc in PIECES.iter() {
            for (x, y) in (0..10).cartesian_product(0..10) {
                assert!(!full.can_fit(pc, x, y));
            }
        }

        // clear a few squares, ensure only the correct pieces fit.
        let nearly_full = full.remove(0, 0).remove(0, 1).remove(1, 1);

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

        for pc in PIECES.iter() {
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
}
