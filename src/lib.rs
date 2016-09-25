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

#[derive(Debug, Clone)]
pub enum GameStateChange {
    Gen { pieces: [Piece; 3] },
    Play {
        piece: Piece,
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

type History = Vec<GameStateChange>;

#[derive(Debug)]
pub struct GameState {
    pub board: Board,
    pub score: Points,
    pub to_play: [Option<Piece>; 3],
}

fn generate_pieces() -> ([Option<Piece>; 3], GameStateChange) {
    let pieces = [Piece::random(), Piece::random(), Piece::random()];
    let change = GameStateChange::Gen { pieces: pieces };
    ([Some(pieces[0]), Some(pieces[1]), Some(pieces[2])], change)
}

fn played_piece(to_play: &[Option<Piece>; 3], index: usize) -> [Option<Piece>; 3] {
    [if index == 0 { None } else { to_play[0] },
     if index == 1 { None } else { to_play[1] },
     if index == 2 { None } else { to_play[2] }]
}

fn clear_filled(board: Board) -> (Board, History) {
    // kinda guessing at the scoring values right now:
    // I *think* the first cleared line is worth 10, all extras are worth 20.
    // But it's tedious to play through the game and validate that reliably...
    let mut cleared = board;
    let mut history: History = vec![];

    let filled = cleared.filled();
    for (i, &line) in filled.iter().enumerate() {
        cleared = cleared.clear(line);
        history.push(GameStateChange::Clear {
            line: line,
            points: 10 * (i as Points + 1),
        });
    }

    (cleared, history)
}

#[derive(Debug, Copy, Clone)]
pub struct Move {
    pub piece_number: usize,
    pub x: usize,
    pub y: usize,
}

pub fn possible_moves(board: &Board, pieces: [Option<Piece>; 3]) -> Vec<Move> {
    use itertools::Itertools;

    let mut moves: Vec<Move> = vec![];

    for (x, y) in (0..10).cartesian_product(0..10) {
        for n in 0..3 {
            let opt = pieces[n];
            if opt.is_none() {
                continue;
            }

            if board.can_fit(&opt.unwrap(), x, y) {
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
                                                    piece: *pc,
                                                    x: x,
                                                    y: y,
                                                    points: pc.value,
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

                if next_state.is_game_over() {
                    history.push(GameStateChange::GameOver);
                }

                Ok((next_state, history))
            }
        }
    }

    pub fn is_game_over(&self) -> bool {
        use itertools::Itertools;
        use std::ops::Not;

        let remaining: Vec<Piece> =
            self.to_play.iter().filter(|x| x.is_some()).map(|x| x.unwrap()).collect();

        (0..10)
            .cartesian_product(0..10)
            .any(|(x, y)| remaining.iter().any(|pc| self.board.can_fit(pc, x, y)))
            .not()
    }
}

#[cfg(test)]
mod tests {
    use super::{GameState, GameStateChange, History, Move, possible_moves};
    use board::{Board, Piece, Points, PIECES};

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
    fn test_clear_three_lines() {
        let board = {
            let mut b = Board::new();
            let uni = PIECES[0];

            for y in 0..3 {
                for x in 0..9 {
                    b = b.put_square(uni, x, y);
                }
            }

            b
        };

        let state = GameState {
            board: board,
            score: 0,
            to_play: [Some(PIECES[3]), Some(PIECES[0]), Some(PIECES[0])],
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
            let mut b = Board::new();
            let uni = PIECES[0];

            for y in 0..9 {
                for x in 0..9 {
                    b = b.put_square(uni, x, y);
                }
            }

            b
        };

        assert_eq!(board.filled().len(), 0);

        let state = GameState {
            board: board,
            score: 0,
            to_play: [Some(PIECES[0]), Some(PIECES[12]), Some(PIECES[12])],
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

    fn play_random_game<F>(mut pick_move: F) -> (GameState, History)
        where F: FnMut(&[Move], &Board, [Option<Piece>; 3]) -> Move
    {
        let mut state = GameState::new();
        let mut history: History = vec![];

        while !state.is_game_over() {
            let moves = possible_moves(&state.board, state.to_play);
            let mv = pick_move(&moves, &state.board, state.to_play);

            match state.play(mv.piece_number, mv.x, mv.y) {
                Ok((next_state, changes)) => {
                    state = next_state;
                    history.extend(changes);
                }
                Err(e) => panic!("Move {:?} failed: {:?}", mv, e),
            }
        }

        (state, history)
    }

    fn play_many_games<F>(n: usize, mut pick_move: F) -> (Points, usize)
        where F: FnMut(&[Move], &Board, [Option<Piece>; 3]) -> Move
    {
        let (state, history) = (0..n)
            .map(|_| play_random_game(|moves, board, pieces| pick_move(moves, board, pieces)))
            .max_by_key(|&(ref s, _)| s.score)
            .unwrap();

        let score = state.score;
        let cleared = history.iter()
            .filter(|c| {
                match *c {
                    &GameStateChange::Clear { .. } => true,
                    _ => false,
                }
            })
            .count();

        (score, cleared)
    }

    #[test]
    fn test_random_game() {
        use rand::{thread_rng, Rng};
        let mut rng = thread_rng();

        let (score, cleared) = play_many_games(200, |moves, _, _| *rng.choose(&moves).unwrap());
        println!("Best of 200, max score = {}", score);
        println!("Cleared {} lines", cleared);
    }

    #[test]
    fn test_slightly_less_stupid_game() {
        let resulting_score = move |mv: &Move, board: &Board, pieces: [Option<Piece>; 3]| -> i64 {
            let (state, _) = GameState {
                    board: board.clone(),
                    score: 0,
                    to_play: pieces,
                }
                .play(mv.piece_number, mv.x, mv.y)
                .unwrap();
            if state.is_game_over() { -1000 } else { state.score as i64 }
        };

        let pick = |moves: &[Move], board: &Board, pieces: [Option<Piece>; 3]| -> Move {
            let best_move = moves.iter()
                .max_by_key(|mv| resulting_score(mv, board, pieces))
                .unwrap();

            *best_move
        };

        let (score, cleared) = play_many_games(200, pick);
        println!("Best of 200, max score = {}", score);
        println!("Cleared {} lines", cleared);
    }
}
