//! Phase 6-4: 31-path symbolic solc E2E verification.
//!
//! Each test loads a fixture produced by `tests/zk-symbolic-solc.test.js`
//! (one per exploration leaf of MultisigNoCall.sol) and proves it via STARK.
//!
//! Run all: `cargo test --test p6_symbolic_e2e --release`
//! Run one: `cargo test --test p6_symbolic_e2e p6_symbolic_000 --release`

use sequent_certifier::bridge::prove_json;

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

macro_rules! symbolic_test {
    ($name:ident, $idx:expr) => {
        #[test]
        fn $name() {
            let fixture = format!("solc_symbolic_{:03}", $idx);
            let t0 = std::time::Instant::now();
            prove_json(&load_fixture(&fixture))
                .unwrap_or_else(|e| panic!("{fixture} failed: {e}"));
            eprintln!("  {} proved in {:.2}s", fixture, t0.elapsed().as_secs_f64());
        }
    };
}

symbolic_test!(p6_symbolic_000, 0);
symbolic_test!(p6_symbolic_001, 1);
symbolic_test!(p6_symbolic_002, 2);
symbolic_test!(p6_symbolic_003, 3);
symbolic_test!(p6_symbolic_004, 4);
symbolic_test!(p6_symbolic_005, 5);
symbolic_test!(p6_symbolic_006, 6);
symbolic_test!(p6_symbolic_007, 7);
symbolic_test!(p6_symbolic_008, 8);
symbolic_test!(p6_symbolic_009, 9);
symbolic_test!(p6_symbolic_010, 10);
symbolic_test!(p6_symbolic_011, 11);
symbolic_test!(p6_symbolic_012, 12);
symbolic_test!(p6_symbolic_013, 13);
symbolic_test!(p6_symbolic_014, 14);
symbolic_test!(p6_symbolic_015, 15);
symbolic_test!(p6_symbolic_016, 16);
symbolic_test!(p6_symbolic_017, 17);
symbolic_test!(p6_symbolic_018, 18);
symbolic_test!(p6_symbolic_019, 19);
symbolic_test!(p6_symbolic_020, 20);
symbolic_test!(p6_symbolic_021, 21);
symbolic_test!(p6_symbolic_022, 22);
symbolic_test!(p6_symbolic_023, 23);
symbolic_test!(p6_symbolic_024, 24);
symbolic_test!(p6_symbolic_025, 25);
symbolic_test!(p6_symbolic_026, 26);
symbolic_test!(p6_symbolic_027, 27);
symbolic_test!(p6_symbolic_028, 28);
symbolic_test!(p6_symbolic_029, 29);
symbolic_test!(p6_symbolic_030, 30);
