extern crate rand;
#[macro_use(lazy_static)]
extern crate lazy_static;
extern crate itertools;

mod board;
use board::{Board, Line, Piece, Points, PlacementError};

type PlayResult = Result<(GameState, History), PlayError>;

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

#[derive(Debug)]
pub enum GameStateChange {
    Gen { pieces: [Piece; 3] },
    Play { piece: Piece, points: Points },
    Clear { line: Line, points: Points },
    GameOver,
}

impl GameStateChange {
    pub fn score(&self) -> Points {
        match self {
            &GameStateChange::Play { piece: _, points } |
            &GameStateChange::Clear { line: _, points } => points,
            _ => 0,
        }
    }
}

type History = Vec<GameStateChange>;

#[derive(Debug)]
pub struct GameState {
    pub board: Board,
    pub score: Points,
    pub to_play: [Option<Piece>; 3],
}

fn generate_pieces() -> ([Option<Piece>; 3], GameStateChange) {
    let pieces = [Piece::random(), Piece::random(), Piece::random()];
    let change =
        GameStateChange::Gen { pieces: [pieces[0].clone(), pieces[1].clone(), pieces[2].clone()] };

    ([Some(pieces[0].clone()), Some(pieces[1].clone()), Some(pieces[2].clone())], change)
}

fn played_piece(to_play: &[Option<Piece>; 3], index: usize) -> [Option<Piece>; 3] {
    [if index == 0 { None } else { to_play[0].clone() },
     if index == 1 { None } else { to_play[1].clone() },
     if index == 2 { None } else { to_play[2].clone() }]
}

fn clear_filled(board: Board) -> (Board, History) {
    // kinda guessing at the scoring values right now:
    // I *think* the first cleared line is worth 10, all extras are worth 20.
    // But it's tedious to play through the game and validate that reliably...
    let mut cleared = board;
    let mut history: History = vec![];

    let filled = cleared.filled();
    for (i, &line) in filled.iter().enumerate() {
        let points: Points = if i == 0 { 10 } else { 20 };
        cleared = cleared.clear(line);
        history.push(GameStateChange::Clear {
            line: line,
            points: points,
        });
    }

    (cleared, history)
}

impl GameState {
    pub fn new() -> GameState {
        GameState {
            board: Board::new(),
            score: 0,
            to_play: [Some(Piece::random()), Some(Piece::random()), Some(Piece::random())],
        }
    }

    pub fn play(&self, pc_number: usize, x: usize, y: usize) -> PlayResult {
        use PlayError::*;

        if pc_number > 2 {
            return Err(PieceOutOfBounds(pc_number));
        }

        match self.to_play[pc_number] {
            None => Err(PiecePlayed(pc_number)),
            Some(ref pc) => {
                let board = try!(self.board.place(pc, x, y));

                let mut history: History = vec![GameStateChange::Play {
                                                    piece: pc.clone(),
                                                    points: pc.value(),
                                                }];

                let to_play = {
                    let remaining = played_piece(&self.to_play, pc_number);
                    if remaining.iter().all(|o| o.is_none()) {
                        let (pieces, gen) = generate_pieces();
                        history.push(gen);
                        pieces
                    } else {
                        remaining
                    }
                };

                let (cleared, changes) = clear_filled(board);
                history.extend(changes);

                let points_scored: u64 = history.iter().map(|change| change.score()).sum();

                let next_state = GameState {
                    board: cleared,
                    score: self.score + points_scored,
                    to_play: to_play,
                };

                Ok((next_state, history))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::GameState;
    use board::{Board, PIECES};

    #[test]
    fn test_new_game() {
        let state = GameState::new();
        assert_eq!(state.score, 0);
        assert!(state.board.is_empty());
        assert!(state.to_play.iter().all(|s| s.is_some()));
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
    fn test_clear_two_lines() {
        let board = {
            let mut b = Board::new();
            let uni = PIECES[0].clone();

            for y in 0..2 {
                for x in 0..9 {
                    b = b.put_square(uni.clone(), x, y);
                }
            }

            b
        };

        let state = GameState {
            board: board,
            score: 0,
            to_play: [Some(PIECES[3].clone()), Some(PIECES[0].clone()), Some(PIECES[0].clone())],
        };

        // play TriUD at the NE edge
        let result = state.play(0, 9, 0);
        assert!(result.is_ok());

        let (new_state, history) = result.unwrap();
        assert_eq!(new_state.score, 33);
        assert_eq!(history.len(), 3);
        assert_eq!(new_state.board.occupancy(), 1);
    }
}
