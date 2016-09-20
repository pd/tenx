use rand::{thread_rng, Rng};
use std::fmt;

pub type Points = u64;

#[derive(Debug, Clone, Copy)]
pub enum Line {
    Col(usize),
    Row(usize),
}

#[derive(Clone)]
pub struct Piece {
    pub name: &'static str,
    pub size: [usize; 2],
    pub squares: Vec<Vec<bool>>,
}

impl fmt::Debug for Piece {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Piece {
    pub fn random() -> Piece {
        let n = thread_rng().gen_range(0, PIECES.len());
        PIECES[n].clone()
    }

    pub fn value(&self) -> Points {
        self.squares
            .iter()
            .flat_map(|row| row.iter().filter(|&&sq| sq))
            .count() as Points
    }

    pub fn offsets(&self) -> Vec<(isize, isize)> {
        let x1 = self.squares[0]
            .iter()
            .enumerate()
            .find(|&(_, &v)| v)
            .expect("No occupied square on top row?")
            .0 as isize;

        let mut offsets = vec![];

        for (y, ref row) in self.squares.iter().enumerate() {
            for (x, &sq) in row.iter().enumerate() {
                if sq {
                    offsets.push((x as isize - x1, y as isize));
                }
            }
        }

        offsets
    }
}

lazy_static! {
    #[cfg_attr(rustfmt, rustfmt_skip)]
    pub static ref PIECES: [Piece; 19] = [
        Piece {
            name: "Uni",
            size: [1, 1],
            squares: vec![vec![true]]
        },

        Piece {
            name: "DuoUD",
            size: [1, 2],
            squares: vec![
                vec![true],
                vec![true]
            ],
        },

        Piece {
            name: "DuoLR",
            size: [2, 1],
            squares: vec![vec![true, true]],
        },

        Piece {
            name: "TriUD",
            size: [1, 3],
            squares: vec![
                vec![true],
                vec![true],
                vec![true]
            ],
        },

        Piece {
            name: "TriLR",
            size: [3, 1],
            squares: vec![vec![true, true, true]],
        },

        Piece {
            name: "TriNW",
            size: [2, 2],
            squares: vec![
                vec![true,  true],
                vec![false, true],
            ],
        },

        Piece {
            name: "TriNE",
            size: [2, 2],
            squares: vec![
                vec![true, true],
                vec![true, false],
            ],
        },

        Piece {
            name: "TriSW",
            size: [2, 2],
            squares: vec![
                vec![false, true],
                vec![true,  true],
            ],
        },

        Piece {
            name: "TriSE",
            size: [2, 2],
            squares: vec![
                vec![true, false],
                vec![true, true],
            ],
        },

        Piece {
            name: "QuadUD",
            size: [1, 4],
            squares: vec![
                vec![true],
                vec![true],
                vec![true],
                vec![true],
            ],
        },

        Piece {
            name: "QuadLR",
            size: [4, 1],
            squares: vec![vec![true, true, true, true]]
        },

        Piece {
            name: "Square2",
            size: [2, 2],
            squares: vec![
                vec![true, true],
                vec![true, true],
            ],
        },

        Piece {
            name: "Square3",
            size: [3, 3],
            squares: vec![
                vec![true, true, true],
                vec![true, true, true],
                vec![true, true, true],
            ],
        },

        Piece {
            name: "EllNW",
            size: [3, 3],
            squares: vec![
                vec![true,  true,  true],
                vec![false, false, true],
                vec![false, false, true],
            ],
        },

        Piece {
            name: "EllNE",
            size: [3, 3],
            squares: vec![
                vec![true, true,  true],
                vec![true, false, false],
                vec![true, false, false],
            ],
        },

        Piece {
            name: "EllSW",
            size: [3, 3],
            squares: vec![
                vec![false, false, true],
                vec![false, false, true],
                vec![true,  true,  true],
            ],
        },

        Piece {
            name: "EllSE",
            size: [3, 3],
            squares: vec![
                vec![true, false, false],
                vec![true, false, false],
                vec![true, true,  true],
            ],
        },

        Piece {
            name: "PentUD",
            size: [1, 5],
            squares: vec![
                vec![true],
                vec![true],
                vec![true],
                vec![true],
                vec![true],
            ],
        },

        Piece {
            name: "PentLR",
            size: [5, 1],
            squares: vec![vec![true, true, true, true, true]]
        },
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

#[derive(Debug)]
pub struct Board {
    squares: Vec<Option<Piece>>,
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
            .map(|(i, opt_pc)| {
                let (x, y) = to_pos(i);
                if opt_pc.is_none() { Some((x, y)) } else { None }
            })
            .filter(|x| x.is_some())
            .map(|x| x.unwrap())
            .collect()
    }

    pub fn filled(&self) -> Vec<Line> {
        let cols = (0..10)
            .filter_map(|x| match (0..10).into_iter().all(|y| self.is_occupied(x, y)) {
                true => Some(Line::Col(x)),
                false => None,
            });

        let rows = (0..10)
            .filter_map(|y| match (0..10).into_iter().all(|x| self.is_occupied(x, y)) {
                true => Some(Line::Row(y)),
                false => None,
            });

        cols.chain(rows).collect()
    }

    pub fn can_fit(&self, pc: &Piece, x: usize, y: usize) -> bool {
        pc.offsets().iter().all(|&(dx, dy)| {
            let (nx, ny) = dxy(x, dx, y, dy);
            in_bounds(nx, ny) && !self.is_occupied(nx as usize, ny as usize)
        })
    }

    // Place pc at (x, y).
    pub fn place(&self, pc: &Piece, x: usize, y: usize) -> Result<Board, PlacementError> {
        if !in_bounds(x as isize, y as isize) {
            return Err(PlacementError::OutOfBounds(x, y));
        }

        if !self.can_fit(pc, x, y) {
            return Err(PlacementError::Occupied(pc.clone(), x, y));
        }

        // TODO: I don't _really_ grok why I have to explicitly re-construct the board
        // here. So many `clone()`s.
        let base = Board { squares: self.squares.clone() };
        let board: Board = pc.offsets().iter().fold(base, |b, &(dx, dy)| {
            let (nx, ny) = dxy(x, dx, y, dy);
            b.put_square(pc.clone(), nx as usize, ny as usize)
        });

        Ok(board)
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
    pub fn put_square(&self, pc: Piece, x: usize, y: usize) -> Board {
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

#[cfg(test)]
mod tests {
    use super::{PIECES, Piece, Board, Line};

    fn piece_by_name(name: &str) -> Piece {
        let pc = PIECES.iter().find(|pc| pc.name == name).expect("no such piece");
        pc.clone()
    }

    fn filled_board() -> Board {
        use itertools::Itertools;

        let uni = piece_by_name("Uni");
        let all_squares = (0..10).cartesian_product(0..10);
        all_squares.fold(Board::new(),
                         |board, (x, y)| board.put_square(uni.clone(), x, y))
    }

    #[test]
    fn test_piece() {
        for pc in PIECES.iter() {
            let (w, h) = (pc.size[0], pc.size[1]);
            assert_eq!(pc.squares.len(), h, "height mismatch: {}", pc.name);
            for row in pc.squares.iter() {
                assert_eq!(row.len(), w, "width mismatch: {}", pc.name);
            }

            let expected_value = match pc.name {
                "Uni" => 1,
                "DuoUD" | "DuoLR" => 2,
                "TriUD" | "TriLR" | "TriNW" | "TriNE" | "TriSW" | "TriSE" => 3,
                "QuadUD" | "QuadLR" => 4,
                "PentUD" | "PentLR" => 5,
                "EllNW" | "EllNE" | "EllSW" | "EllSE" => 5,
                "Square2" => 4,
                "Square3" => 9,
                _ => unreachable!(),
            };

            assert_eq!(pc.value(), expected_value);
        }
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
        use itertools::Itertools;

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
            if pc.squares[0][0] {
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
