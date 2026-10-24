# vyges-lec

Combinational **logic equivalence** check: two gate-level **netlists** (golden and
revised) and a **Liberty** in, a verdict out — *do they compute the same function?*
— with a concrete input **counter-example** when they don't.

> **Vyges open EDA tools.** Commercial-grade silicon sign-off capability, built on
> open standards and plain file formats — and meant to be accessible to everyone,
> not only teams who can license a six-figure tool. `vyges-lec` opens up formal
> equivalence.

> **Stability: experimental (v0.1.0).** A real, canonical-BDD combinational
> equivalence check with counter-examples; the standard-cell primitive map and the
> sequential model have honest bounds — see **Current state**.

## Why this exists

Every synthesis, ECO, hand-edit, and clock-gating insertion is a *promise* that the
logic still means the same thing. Simulation can only spot-check that promise on the
vectors you happened to run. Equivalence checking **proves** it across all
2ⁿ inputs at once — or hands you the one input where the promise broke. It is the
formal sibling of simulation, and a pure decision-procedure problem: deterministic,
exhaustive, exactly the work an open Rust engine can own.

## How this is solved today

LEC is a **commercial** sign-off tool (Conformal, Formality, …) behind major
licenses; the open ecosystem is thin and mostly research code. `vyges-lec` is a
clean-room Rust engine with an **in-tree ROBDD** package — no external SAT/BDD
dependency — reading the **same Liberty / Verilog** the rest of the Vyges flow uses.
Because a reduced, ordered BDD over a fixed variable order is **canonical**, two
functions are equal *iff* they are the same node: the equivalence test is a pointer
compare, and a mismatch's miter walks straight to a counter-example.

## Use it

```sh
cargo build --release            # std-only; the BDD package is in-tree

vyges-lec check golden.v revised.v --lib cells.lib                  # -> verdict
vyges-lec check golden.v revised.v --lib cells.lib --json
vyges-lec check golden.v revised.v --lib cells.lib --fail-on-diff   # exit 3 if differ
# flags: --lib FILE · --engine bdd|abc|both · -o FILE · --json · --fail-on-diff · -h · -V
```

```text
vyges-lec — NOT EQUIVALENT ✗  (1 compared, 1 differ)
  differ at `f`   when a=1 b=0
```

## Two engines

| `--engine` | how | reports |
| --- | --- | --- |
| `bdd` (default) | the in-tree ROBDD: exact, canonical | every differing endpoint, each with a counter-example |
| `abc` | ABC's SAT-based prover over the same model, through [`vyges-abc-lib`](https://github.com/vyges-tools/abc-lib) | the first differing endpoint and its counter-example; scales to datapaths where BDDs grow too large |
| `both` | runs both and fails if they disagree | the `bdd` report |

Both engines read the same model, so on every design both finish they must give the same verdict:
two independent provers checking each other. `abc` and `both` need the optional feature:

```sh
cargo build --release --features abc   # links the prebuilt ABC archive (see vyges-abc-lib)
```

With `--fail-on-diff`, an `abc` run that gives up within its limits exits 4 (undecided).

## How it works

- Each design's endpoints — primary outputs and flop data pins — are built into a
  **ROBDD** in *one shared package over one shared variable order* (primary inputs
  by name).
- Gate functions come from a built-in standard-cell **primitive map**, keyed on the
  cell name's logic prefix: INV/BUF, AND/NAND, OR/NOR, XOR/XNOR (any fan-in), and
  MUX (`S ? B : A`). The Liberty gives pin directions and splits combinational from
  sequential cells.
- Matching endpoints are compared by node identity. Equal → proven equivalent.
  Different → the miter `golden ⊕ revised` is solved for one satisfying assignment,
  reported as the input cube under which the designs disagree.
- **Sequential** designs are cut at the registers — flop Q nets become free inputs,
  flop D nets become endpoints — so the check proves the combinational logic between
  registers (registers matched by name).

## Current state (v0.1.0)

**Working & tested:** canonical-ROBDD equivalence of two netlists, De-Morgan / logic
re-write equivalence, real-bug detection with a concrete counter-example,
register-boundary (sequential) cutting, and reporting of endpoints present in only
one design. Text + `--json`, a `--fail-on-diff` CI exit code. The ROBDD package
(ite-based, memoized, with `sat_one`) is unit-tested in its own right.

**Depth reserved (honest):**

- a gate's logic is its output pin's Liberty `function` (so AOI/OAI, multi-output cells
  such as half and full adders, and tie cells are covered); a library with no
  `function` attributes falls back to a **name-prefix primitive map**. A function that
  does not parse, an unrecognized cell, or a cell missing from the Liberty that touches a
  compared cone is a hard error (never a silent wrong answer). UDPs are not read;
- sequential equivalence assumes **matched registers by name** (no retiming, no
  state re-encoding) — sequential/retiming LEC is a separate, larger problem;
- the `bdd` engine is a single **monolithic BDD** with a static variable order:
  correct for any size, but wide datapaths (multipliers) can blow up memory; the
  `abc` engine (SAT-based) is the path for those;
- a pin tied to a literal (`.B(1'b0)`) and a `supply0`/`supply1` net are constants, in both
  engines;
- an input pin left unconnected is an error where its gate lies in a compared cone: it floats.

**Validation roadmap:** cross-check verdicts against an established equivalence
checker (or against exhaustive simulation for small cones) on open-PDK synthesis
before/after pairs — the same oracle-backed discipline the rest of Loom uses.
