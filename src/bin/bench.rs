extern crate tenx;
extern crate futures;
extern crate futures_cpupool;
extern crate rand;
extern crate itertools;

use tenx::board::*;
use tenx::*;

fn play_game() -> (GameState, History) {
    let mut state = GameState::new();
    let mut history: History = vec![];

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

    loop {
        let moves = possible_moves(&state.board, state.to_play);
        let mv = pick(&moves, &state.board, state.to_play);

        match state.play(mv.piece_number, mv.x, mv.y) {
            Ok((next_state, changes)) => {
                let done = {
                    match changes[changes.len() - 1] {
                        GameStateChange::GameOver => true,
                        _ => false,
                    }
                };

                state = next_state;
                history.extend(changes);

                if done {
                    break;
                }
            }
            Err(e) => panic!("Move {:?} failed: {:?}", mv, e),
        }
    }

    (state, history)
}

fn play_many(n: usize) {
    let mut results: Vec<Points> = vec![];

    for _ in 0..n {
        results.push(play_game().0.score);
    }

    println!("Best score: {}", results.iter().max().unwrap());
}

fn play_many_par(n: usize) {
    use futures::{Future, finished, lazy};

    let pool = futures_cpupool::CpuPool::new(4);
    let mut futs = vec![];
    for _ in 0..n {
        futs.push(pool.spawn(lazy(|| finished::<Points, ()>(play_game().0.score))));
    }

    let mut scores = vec![];
    for fut in futs {
        scores.push(fut.wait().unwrap());
    }

    println!("Best score: {}", scores.iter().max().unwrap());
}

fn main() {

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
        play_many_par(n);
    } else {
        play_many(n);
    }
}
