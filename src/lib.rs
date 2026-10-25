//! vyges-lec — combinational **logic equivalence** check.
//!
//! Two gate-level **netlists** (golden + revised) and a **Liberty** in, a verdict
//! out: do they compute the same function? It builds a canonical **ROBDD** for every
//! endpoint of both designs over one shared variable order and compares — equal
//! functions share a node, so the check is exact, not a sample. When two endpoints
//! differ, the miter yields a concrete input **counter-example**.
//!
//! This is the formal sibling of simulation: a simulator shows two designs agree on
//! the vectors you ran; `vyges-lec` proves they agree on *all* of them (or hands you
//! the input where they don't). Sequential designs are cut at the registers — flop
//! outputs are free inputs, flop data pins are endpoints — the standard combinational
//! equivalence model with registers matched by instance name.
//!
//! Gate functions come from the Liberty `function` attribute of each output pin (a
//! built-in standard-cell primitive map stands in for libraries without one); the
//! Liberty also supplies pin directions and the combinational/sequential split. Pure std beyond
//! the shared parsers.

// The crate's own name inside it: the command-line entry ([`cli_main`]) is built into the
// library too, and its `vyges_lec::…` paths resolve here.
extern crate self as vyges_lec;

pub use vyges_loom::{liberty, netlist};

pub mod bdd;
pub mod lec;

/// The same check through ABC (`--features abc`): a second, SAT-based engine over the same model.
#[cfg(feature = "abc")]
pub mod abc;

/// Sequential equivalence through ABC (`--features abc`): the registers kept as state.
#[cfg(feature = "abc")]
pub mod sec;

/// Property checking through ABC (`--features abc`): a net that must never be 1.
#[cfg(feature = "abc")]
pub mod prop;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const COPYRIGHT: &str = "© 2026 Vyges. All Rights Reserved.  https://vyges.com";

/// The `vyges-lec` command-line entry (the binary's `main`), built into the library too so a
/// suite binary can link every engine and run the one it is invoked as.
#[cfg(feature = "suite")]
#[doc(hidden)]
#[path = "main.rs"]
pub mod cli_main;
