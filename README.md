# vyges-lec

Formal checks on gate-level **netlists**, with a **Liberty** for the cell functions:
**logic equivalence** of two netlists — combinational (`check`) and sequential (`sec`) —
and **property checking** of one (`prove`). Every failure comes with a concrete
**counter-example**.

> **Vyges open EDA tools.** Commercial-grade silicon sign-off capability, built on
> open standards and plain file formats — and meant to be accessible to everyone,
> not only teams who can license a six-figure tool. `vyges-lec` opens up formal
> equivalence.

> **Stability: stable, actively developed.** Combinational and sequential equivalence and
> safety-property proofs, each with a replayed counter-example, from two independent engines
> (an exact in-tree BDD and ABC's SAT-based prover). The modelled scope is stated exactly — see
> **Current state**.

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

Through the Vyges CLI, installed with the physical engines:

```sh
vyges install physical
vyges physical lec check golden.v revised.v --lib cells.lib
```

Or the standalone binary:

```sh
cargo build --release --features abc   # as released: links the prebuilt ABC archive
cargo build --release                  # std-only: the in-tree BDD engine, `check` only

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
| `abc` (default, as released) | ABC's SAT-based prover over the same model, through [`vyges-abc-lib`](https://github.com/vyges-tools/abc-lib) | the first differing endpoint and its counter-example; scales to real netlists and datapaths where BDDs grow too large |
| `bdd` (default without ABC) | the in-tree ROBDD: exact, canonical | every differing endpoint, each with a counter-example |
| `both` | runs both and fails if they disagree | the `bdd` report |

Both engines read the same model, so on every design both finish they must give the same verdict:
two independent provers checking each other. The released binary carries ABC; a source build needs
the optional feature for `abc`, `both`, `sec` and `prove` (without it `check` uses `bdd`):

```sh
cargo build --release --features abc   # links the prebuilt ABC archive (see vyges-abc-lib)
```

With `--fail-on-diff`, an `abc` run that gives up within its limits exits 4 (undecided).

## Sequential equivalence (`sec`)

`check` cuts both designs at the registers, so it needs them to correspond one to one.
`sec` keeps the registers as state and asks a stronger question: *do the two designs
produce the same primary outputs on every input sequence, from the same starting
state?* It still holds when registers do not line up: one duplicated, two merged, one
removed because it never changes.

```sh
vyges-lec sec golden.v revised.v --lib cells.lib     # needs --features abc
```

```text
vyges-lec sec — NOT EQUIVALENT ✗  (1 output(s) compared; 1 vs 2 register(s))
  `y` differs in cycle 3 (cycle 0 is before the first clock edge), under:
    cycle 0: en=1
    cycle 1: en=1
    cycle 2: en=1
    cycle 3: en=0
```

- Each register is its cell's Liberty `ff` group: `next_state` is loaded on the rising edge
  of `clocked_on`, and the output pins read the state through their `function`
  (so scan registers and inverted outputs are covered). `next_state` may read the stored
  value through the group's own variables, as an enable register's `(D&DE) | (IQ&!DE)` does.
- An asynchronous `clear` / `preset` acts at the clock edge: while active, the output shows
  the forced value and the edge loads it (`clear_preset_var1`/`_var2` when both are active).
- Every register starts at 0 and is clocked by one primary input, reached through buffers.
  An inverted, gated or generated clock, a second clock, a latch or a register bank is a
  hard error, never a guess.
- ABC proves it (a multi-output sequential miter, register correspondence, then
  interpolation and PDR). A difference comes with the inputs of every cycle up to it, and is
  replayed on both designs before it is reported.

## Property checking (`prove`)

The same sequential model answers a safety question about one netlist: *can this net ever
be 1?* An error flag, a "two grants at once" net, an assertion synthesized into gates.

```sh
vyges-lec prove design.v --lib cells.lib --never err --never both_grants   # a proof (PDR)
vyges-lec prove design.v --lib cells.lib --never err --bound 20            # cycles 0..20 only
```

```text
vyges-lec prove — FAILS ✗  `c3` is 1 in cycle 3 (2 register(s)), under:
    cycle 0: en=1
    cycle 1: en=1
    cycle 2: en=1
    cycle 3: en=0
```

Without `--bound` the answer is a proof (every net stays 0 on every input sequence from the
all-zero register state) or the first net driven to 1, with its cycle and the inputs of every
cycle up to it, replayed before it is reported. With `--bound N` it is a bounded search:
finding nothing in cycles 0 to N is reported as exactly that, not as a proof. A net that is 0
in every state (a constant tie, say), and any net whose logic reads no register, is decided
exactly from one cycle's logic before ABC is asked. `--fail-on-diff` exits 3 when a net can be
1 and 4 when the answer is undecided; without it every verdict exits 0.

In every command an `assign a = b;` is a wire: the name that is not driven reads the net that is.

## How it works

- Each design's endpoints — primary outputs and flop data pins — are built into a
  **ROBDD** in *one shared package over one shared variable order* (primary inputs
  by name).
- Gate functions come from each output pin's Liberty `function`; for a library
  without one, from a built-in standard-cell **primitive map** keyed on the cell
  name's logic prefix: INV/BUF, AND/NAND, OR/NOR, XOR/XNOR (any fan-in), and MUX
  (`S ? B : A`). The Liberty also gives pin directions and splits combinational from
  sequential cells.
- Matching endpoints are compared by node identity. Equal → proven equivalent.
  Different → the miter `golden ⊕ revised` is solved for one satisfying assignment,
  reported as the input cube under which the designs disagree.
- **Sequential** designs are cut at the registers — flop outputs become free inputs,
  flop data pins become endpoints — so the check proves the combinational logic
  between registers. Registers are matched by **instance name** (`inst/Q`, `inst/D`),
  not by the nets on their pins, so a netlist whose nets were renamed by buffering or
  resizing still lines up with its source.

## Current state

**Working & tested:**
- `check`: canonical-ROBDD equivalence of two netlists (De-Morgan / logic re-write
  equivalence, real-bug detection with a concrete counter-example), register-boundary
  cutting, and reporting of endpoints present in only one design;
- `--engine abc|bdd|both`: ABC's SAT-based prover for netlists and datapaths too large for a
  BDD, and `both` to have the two engines check each other;
- `sec`: sequential equivalence through register correspondence, interpolation and PDR,
  with a counter-example covering every cycle up to the difference, replayed before it is
  reported;
- `prove`: safety properties (`--never NET`) as a PDR proof or a bounded search, with a
  BDD pre-pass that decides constant and register-free nets exactly;
- a node budget that the BDD enforces inside every operation, so a cone that would blow up
  hands over to ABC instead of exhausting memory;
- text + `--json` output, and `--fail-on-diff` CI exit codes (3 = differs, 4 = undecided).

The ROBDD package (ite-based, memoized, with `sat_one`) is unit-tested in its own right.
`vyges-lec prove` is also the proof engine behind
[`vyges-formal`](https://github.com/vyges-tools/formal)'s property campaigns.

**Scope (what is modelled, and what is refused):**

- a gate's logic is its output pin's Liberty `function` (so AOI/OAI, multi-output cells
  such as half and full adders, and tie cells are covered); a library with no
  `function` attributes falls back to a **name-prefix primitive map**. A function that
  does not parse, an unrecognized cell, or a cell missing from the Liberty that touches a
  compared cone is a hard error (never a silent wrong answer). UDPs are not read;
- `check` matches **registers by instance name** (no retiming, no state re-encoding); `sec`
  does not need them to match, and models one rising-edge clock from an all-zero state;
- the `bdd` engine is a single **monolithic BDD** with a static variable order:
  correct for any size, but wide datapaths (multipliers) can blow up memory; the
  `abc` engine (SAT-based) is the path for those;
- a pin tied to a literal (`.B(1'b0)`) and a `supply0`/`supply1` net are constants, in both
  engines;
- an input pin left unconnected is an error where its gate lies in a compared cone: it floats.

**Validation roadmap:** cross-check verdicts against an established equivalence
checker (or against exhaustive simulation for small cones) on open-PDK synthesis
before/after pairs — the same oracle-backed discipline the rest of Loom uses.
