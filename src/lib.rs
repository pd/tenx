extern crate rand;
#[macro_use(lazy_static)]
extern crate lazy_static;
extern crate itertools;

pub mod board;
pub mod piece;

use itertools::Itertools;
use std::ops::Not;
use board::{Bitboard, Line, PlacementError};
use piece::{Piece, Points};

pub type PlayResult = Result<(GameState, History), PlayError>;

#[derive(Debug)]
pub enum PlayError {
    PieceOutOfBounds(usize),
    SquareOutOfBounds(usize, usize),
    PiecePlayed(usize),
    PieceDoesNotFit(Piece, usize, usize),
}

impl From<PlacementError> for PlayError {
    fn from(err: PlacementError) -> PlayError {
        use PlayError::*;
        match err {
            PlacementError::OutOfBounds(x, y) => SquareOutOfBounds(x, y),
            PlacementError::Occupied(pc, x, y) => PieceDoesNotFit(pc, x, y),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum GameStateChange {
    Gen { pieces: [&'static Piece; 3] },
    Play {
        piece: &'static Piece,
        x: usize,
        y: usize,
        points: Points,
    },
    Clear { line: Line, points: Points },
    GameOver,
}

impl GameStateChange {
    pub fn score(&self) -> Points {
        match self {
            &GameStateChange::Play { points, .. } |
            &GameStateChange::Clear { points, .. } => points,
            _ => 0,
        }
    }
}

pub type History = Vec<GameStateChange>;

#[derive(Debug, Copy, Clone)]
pub struct Move {
    pub piece_number: usize,
    pub x: usize,
    pub y: usize,
}

pub fn possible_moves(board: &Bitboard) -> Vec<Move> {
    let mut moves: Vec<Move> = vec![];
    let pieces = board.pieces();

    for (x, y) in (0..10).cartesian_product(0..10) {
        for n in 0..3 {
            let opt = pieces[n];
            if opt.is_none() {
                continue;
            }

            if board.can_fit(opt.unwrap(), x, y) {
                moves.push(Move {
                    piece_number: n,
                    x: x,
                    y: y,
                });
            }
        }
    }

    moves
}

fn generate_pieces() -> ([&'static Piece; 3], GameStateChange) {
    let pieces = [Piece::random(), Piece::random(), Piece::random()];
    let change = GameStateChange::Gen { pieces: pieces };
    (pieces, change)
}

fn clear_filled(board: Bitboard) -> (Bitboard, History) {
    // kinda guessing at the scoring values right now:
    // I *think* the first cleared line is worth 10, all extras are worth 20.
    // But it's tedious to play through the game and validate that reliably...
    let mut cleared = board;
    let mut history: History = vec![];

    for (i, &line) in cleared.filled().iter().enumerate() {
        cleared = cleared.clear(line);
        history.push(GameStateChange::Clear {
            line: line,
            points: 10 * (i as Points + 1),
        });
    }

    (cleared, history)
}

#[derive(Debug, Copy, Clone)]
pub struct GameState {
    pub board: Bitboard,
    pub score: Points,
}

impl GameState {
    pub fn new() -> GameState {
        GameState {
            board: Bitboard::new().with_pieces([Piece::random(), Piece::random(), Piece::random()]),
            score: 0,
        }
    }

    pub fn play(&self, pc_number: usize, x: usize, y: usize) -> PlayResult {
        use PlayError::*;

        if pc_number > 2 {
            return Err(PieceOutOfBounds(pc_number));
        }

        match self.board.piece(pc_number) {
            None => Err(PiecePlayed(pc_number)),
            Some(pc) => {
                let board = try!(self.board.place(pc, x, y)).without_piece(pc_number);

                let mut history: History = vec![GameStateChange::Play {
                                                    piece: pc,
                                                    x: x,
                                                    y: y,
                                                    points: pc.value,
                                                }];

                let board = if board.no_remaining_pieces() {
                    let (pieces, gen) = generate_pieces();
                    history.push(gen);
                    board.with_pieces(pieces)
                } else {
                    board
                };

                let (cleared, changes) = clear_filled(board);
                history.extend(changes);

                let points_scored: u64 = history.iter().map(|change| change.score()).sum();

                let next_state = GameState {
                    board: cleared,
                    score: self.score + points_scored,
                };

                if next_state.is_game_over() {
                    history.push(GameStateChange::GameOver);
                }

                Ok((next_state, history))
            }
        }
    }

    pub fn is_game_over(&self) -> bool {
        let remaining: Vec<&'static Piece> =
            self.board.pieces().iter().filter(|x| x.is_some()).map(|x| x.unwrap()).collect();

        (0..10)
            .cartesian_product(0..10)
            .any(|(x, y)| remaining.iter().any(|pc| self.board.can_fit(pc, x, y)))
            .not()
    }
}

#[cfg(test)]
mod tests {
    use super::{GameState, GameStateChange};
    use itertools::Itertools;
    use board::Bitboard;
    use piece;

    #[test]
    fn test_new_game() {
        let state = GameState::new();
        assert_eq!(state.score, 0);
        assert!(state.board.is_empty());
        assert!(state.board.pieces().iter().all(|s| s.is_some()));
    }

    #[test]
    fn test_play_first_piece() {
        let initial_state = GameState::new();
        let result = initial_state.play(0, 3, 0);
        assert!(result.is_ok(),
                "Move failed! Err: {:?}\n\nStarting state: {:?}",
                result.err().unwrap(),
                initial_state);
    }

    #[test]
    fn test_clear_three_lines() {
        let board = (0..9)
            .cartesian_product(0..3)
            .fold(Bitboard::new(), |board, (x, y)| board.fill_square(x, y));

        let state = GameState {
            board: board.with_pieces([piece::by_name("TriUD"),
                                      piece::by_name("Uni"),
                                      piece::by_name("Uni")]),
            score: 0,
        };

        // play TriUD at the NE edge
        let result = state.play(0, 9, 0);
        assert!(result.is_ok());

        let (new_state, history) = result.unwrap();
        assert_eq!(new_state.score, 63);
        assert_eq!(history.len(), 4);
    }

    #[test]
    fn test_losing() {
        let board = {
            let mut b = Bitboard::new();

            for y in 0..9 {
                for x in 0..9 {
                    b = b.fill_square(x, y);
                }
            }

            b
        };

        assert_eq!(board.filled().len(), 0);

        let state = GameState {
            board: board.with_pieces([piece::by_name("Uni"),
                                      piece::by_name("Square3"),
                                      piece::by_name("Square3")]),
            score: 0,
        };

        // Clear one line, but not enough to make space for the 3x3s. Game over.
        let result = state.play(0, 9, 0);
        assert!(result.is_ok());

        let (new_state, history) = result.unwrap();
        assert_eq!(new_state.score, 11);

        if let Some(change) = history.last() {
            match *change {
                GameStateChange::GameOver => (),
                _ => panic!("Should be game over, but isn't"),
            }
        }
    }
}
