extern crate tenx;
extern crate futures;
extern crate futures_cpupool;
extern crate rand;
extern crate itertools;

use tenx::*;

fn game_over(history: &History) -> bool {
    if history.is_empty() {
        return false;
    }
    match history[history.len() - 1] {
        GameStateChange::GameOver => true,
        _ => false,
    }
}

fn pick_best_move(state: &GameState) -> Move {
    let moves = state.moves();
    let best = moves.iter()
        .max_by_key(|mv| {
            let (next, history) = state.play(&mv)
                .expect("move generation produced invalid move");
            if game_over(&history) { 0 } else { next.score }
        })
        .unwrap();

    *best
}

fn play_game() -> (GameState, History) {
    let mut state = GameState::new();
    let mut history: History = vec![];

    loop {
        let mv = pick_best_move(&state);

        match state.play(&mv) {
            Ok((next_state, changes)) => {
                state = next_state;
                history.extend(changes);

                if game_over(&history) {
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
    println!("Final board:\n{}\n\n{:?}",
             state.board,
             state.board.pieces());
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
