extern crate tenx;
extern crate rayon;
extern crate rand;
extern crate itertools;

use tenx::board::*;
use tenx::*;

fn play_game<F: Sync>(pick_move: F) -> (GameState, History)
    where F: Fn(&[Move], &Board, [Option<&'static Piece>; 3]) -> Move
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

fn play_many<F: Sync>(n: usize, pick_move: F)
    where F: Fn(&[Move], &Board, [Option<&'static Piece>; 3]) -> Move
{
    let mut results: Vec<(GameState, History)> = vec![];

    for _ in 0..n {
        results.push(play_game(|moves, board, pieces| pick_move(moves, board, pieces)));
    }
}

fn play_many_par<F: Sync>(n: usize, pick_move: F)
    where F: Fn(&[Move], &Board, [Option<&'static Piece>; 3]) -> Move
{
    use rayon::prelude::*;
    let mut results: Vec<(GameState, History)> = vec![];

    (0..n)
        .into_par_iter()
        .map(|_| play_game(|moves, board, pieces| pick_move(moves, board, pieces)))
        .collect_into(&mut results);
}

fn main() {
    let resulting_score = |mv: &Move, board: &Board, pieces: [Option<&'static Piece>; 3]| -> i64 {
        let (state, _) = GameState {
                board: board.clone(),
                score: 0,
                to_play: pieces,
            }
            .play(mv.piece_number, mv.x, mv.y)
            .unwrap();
        if state.is_game_over() { -1000 } else { state.score as i64 }
    };

    let pick = |moves: &[Move], board: &Board, pieces: [Option<&'static Piece>; 3]| -> Move {
        let best_move = moves.iter()
            .max_by_key(|mv| resulting_score(mv, board, pieces))
            .unwrap();

        *best_move
    };

    let n = std::env::var("N")
        .unwrap_or("200".into())
        .parse::<usize>()
        .expect("expected $N to be an int");

    let par = match std::env::var("PAR") {
        Ok(s) => s == "true" || s == "1",
        Err(_) => false,
    };

    println!("Playing {} games, {}in parallel",
             n,
             if par { "" } else { "not " });

    if par {
        play_many_par(n, pick);
    } else {
        play_many(n, pick);
    }
}
