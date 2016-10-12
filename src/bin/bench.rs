extern crate tenx;
extern crate futures;
extern crate futures_cpupool;
extern crate rand;
extern crate itertools;

use tenx::board::Bitboard;
use tenx::*;

fn play_game() -> (GameState, History) {
    let mut state = GameState::new();
    let mut history: History = vec![];

    let resulting_score = |mv: &Move, board: &Bitboard| -> i64 {
        let (state, _) = GameState {
                board: board.clone(),
                score: 0,
            }
            .play(mv.piece_number, mv.x, mv.y)
            .expect("received invalid move");
        if state.is_game_over() { -1000 } else { state.score as i64 }
    };

    let pick = |moves: &[Move], board: &Bitboard| -> Move {
        let best_move = moves.iter()
            .max_by_key(|mv| resulting_score(mv, board))
            .expect("no best move found");

        *best_move
    };

    loop {
        let mv = pick(&possible_moves(&state.board), &state.board);

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

fn show_best_game(games: Vec<(GameState, History)>) {
    let (state, ref history) = *games.iter()
        .max_by_key(|&&(ref gs, _)| gs.score)
        .expect("no best game?");

    println!("Best score: {} in {} moves", state.score, history.len());
}

fn play_many(n: usize) {
    show_best_game((0..n).map(|_| play_game()).collect());
}

fn play_many_par(n: usize) {
    use futures::{Future, finished, lazy};

    let pool = futures_cpupool::CpuPool::new(4);
    let mut futs = vec![];
    for _ in 0..n {
        futs.push(pool.spawn(lazy(|| finished::<(GameState, History), ()>(play_game()))));
    }

    let mut results = vec![];
    for fut in futs {
        results.push(fut.wait().unwrap());
    }

    show_best_game(results);
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
