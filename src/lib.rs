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
//! Q nets are free inputs, flop D nets are endpoints — the standard combinational
//! equivalence model with registers matched by name.
//!
//! Gate functions come from the Liberty `function` attribute of each output pin (a
//! built-in standard-cell primitive map stands in for libraries without one); the
//! Liberty also supplies pin directions and the combinational/sequential split. Pure std beyond
//! the shared parsers.

pub use vyges_loom::{liberty, netlist};

pub mod bdd;
pub mod lec;

/// The same check through ABC (`--features abc`): a second, SAT-based engine over the same model.
#[cfg(feature = "abc")]
pub mod abc;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const COPYRIGHT: &str = "© 2026 Vyges. All Rights Reserved.  https://vyges.com";
