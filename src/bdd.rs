//! A small **reduced, ordered binary decision diagram** (ROBDD) package — the
//! decision procedure behind the equivalence check.
//!
//! No complement edges; canonicity comes from the reduction rule (`mk` collapses a
//! node whose branches match and shares structurally-equal nodes through a unique
//! table). Because a ROBDD over a fixed variable order is **canonical**, two boolean
//! functions are equal *iff* they are the same node index — which is exactly what
//! makes equivalence checking a pointer compare, not a search.
//!
//! `ite` (if-then-else) is the one primitive; `and`/`or`/`xor`/`not` are thin
//! wrappers, all memoized. `sat_one` extracts a satisfying assignment (a
//! counter-example) when two functions differ.

use std::collections::HashMap;

const FALSE: u32 = 0;
const TRUE: u32 = 1;
const TERM_VAR: u32 = u32::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Node {
    var: u32,
    lo: u32,
    hi: u32,
}

pub struct Bdd {
    nodes: Vec<Node>,
    unique: HashMap<Node, u32>,
    ite_memo: HashMap<(u32, u32, u32), u32>,
}

impl Default for Bdd {
    fn default() -> Self {
        Bdd::new()
    }
}

impl Bdd {
    pub fn new() -> Bdd {
        // index 0 = FALSE terminal, 1 = TRUE terminal
        let nodes = vec![
            Node { var: TERM_VAR, lo: 0, hi: 0 },
            Node { var: TERM_VAR, lo: 1, hi: 1 },
        ];
        Bdd { nodes, unique: HashMap::new(), ite_memo: HashMap::new() }
    }

    pub fn one(&self) -> u32 {
        TRUE
    }
    pub fn zero(&self) -> u32 {
        FALSE
    }

    fn var_of(&self, f: u32) -> u32 {
        self.nodes[f as usize].var
    }

    /// The canonical node for `(var, lo, hi)` — applies the reduction rule and
    /// shares through the unique table.
    fn mk(&mut self, var: u32, lo: u32, hi: u32) -> u32 {
        if lo == hi {
            return lo; // redundant test
        }
        let n = Node { var, lo, hi };
        if let Some(&i) = self.unique.get(&n) {
            return i;
        }
        let i = self.nodes.len() as u32;
        self.nodes.push(n);
        self.unique.insert(n, i);
        i
    }

    /// A decision variable as a function (var index = position in the order; lower
    /// index sits nearer the top of every diagram).
    pub fn var(&mut self, index: u32) -> u32 {
        self.mk(index, FALSE, TRUE)
    }

    fn is_term(f: u32) -> bool {
        f == FALSE || f == TRUE
    }

    /// `ite(f, g, h)` = (f ? g : h). The single core operation.
    pub fn ite(&mut self, f: u32, g: u32, h: u32) -> u32 {
        // terminal / trivial reductions
        if f == TRUE {
            return g;
        }
        if f == FALSE {
            return h;
        }
        if g == h {
            return g;
        }
        if g == TRUE && h == FALSE {
            return f;
        }
        if let Some(&r) = self.ite_memo.get(&(f, g, h)) {
            return r;
        }
        // split on the top-most variable among f, g, h
        let v = {
            let mut v = self.var_of(f);
            let vg = self.var_of(g);
            let vh = self.var_of(h);
            if !Self::is_term(g) {
                v = v.min(vg);
            }
            if !Self::is_term(h) {
                v = v.min(vh);
            }
            v
        };
        let (flo, fhi) = self.cof(f, v);
        let (glo, ghi) = self.cof(g, v);
        let (hlo, hhi) = self.cof(h, v);
        let lo = self.ite(flo, glo, hlo);
        let hi = self.ite(fhi, ghi, hhi);
        let r = self.mk(v, lo, hi);
        self.ite_memo.insert((f, g, h), r);
        r
    }

    /// Cofactors `(f|v=0, f|v=1)` for the split variable `v`. A node whose top var
    /// is deeper than `v` (or a terminal) doesn't depend on `v` here.
    fn cof(&self, f: u32, v: u32) -> (u32, u32) {
        let n = self.nodes[f as usize];
        if n.var == v {
            (n.lo, n.hi)
        } else {
            (f, f)
        }
    }

    pub fn not(&mut self, f: u32) -> u32 {
        self.ite(f, FALSE, TRUE)
    }
    pub fn and(&mut self, f: u32, g: u32) -> u32 {
        self.ite(f, g, FALSE)
    }
    pub fn or(&mut self, f: u32, g: u32) -> u32 {
        self.ite(f, TRUE, g)
    }
    pub fn xor(&mut self, f: u32, g: u32) -> u32 {
        let ng = self.not(g);
        self.ite(f, ng, g)
    }
    pub fn xnor(&mut self, f: u32, g: u32) -> u32 {
        let x = self.xor(f, g);
        self.not(x)
    }

    /// One satisfying assignment of `f` (a path to TRUE), as `(var, value)` pairs
    /// for the variables actually tested; unlisted variables are don't-cares.
    /// `None` iff `f` is the constant FALSE.
    pub fn sat_one(&self, f: u32) -> Option<Vec<(u32, bool)>> {
        if f == FALSE {
            return None;
        }
        let mut out = Vec::new();
        let mut cur = f;
        while cur != TRUE {
            let n = self.nodes[cur as usize];
            if n.hi != FALSE {
                out.push((n.var, true));
                cur = n.hi;
            } else {
                out.push((n.var, false));
                cur = n.lo;
            }
        }
        Some(out)
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn de_morgan_holds_by_canonicity() {
        let mut b = Bdd::new();
        let a = b.var(0);
        let c = b.var(1);
        // a & c  ==  !(!a | !c)
        let left = b.and(a, c);
        let na = b.not(a);
        let nc = b.not(c);
        let or = b.or(na, nc);
        let right = b.not(or);
        assert_eq!(left, right, "ROBDD is canonical -> equal functions share a node");
    }

    #[test]
    fn xor_is_not_xnor_and_constants_fold() {
        let mut b = Bdd::new();
        let a = b.var(0);
        let c = b.var(1);
        let x = b.xor(a, c);
        let xn = b.xnor(a, c);
        assert_ne!(x, xn);
        // a ^ a = 0, a | !a = 1
        let z = b.xor(a, a);
        assert_eq!(z, b.zero());
        let na = b.not(a);
        let t = b.or(a, na);
        assert_eq!(t, b.one());
    }

    #[test]
    fn sat_one_finds_a_difference() {
        let mut b = Bdd::new();
        let a = b.var(0);
        let c = b.var(1);
        // miter of (a) vs (a|c): differs exactly when a=0, c=1
        let f = a;
        let g = b.or(a, c);
        let m = b.xor(f, g);
        let asn = b.sat_one(m).expect("they differ");
        // reconstruct: a must be 0, c must be 1
        let a_val = asn.iter().find(|(v, _)| *v == 0).map(|(_, x)| *x);
        let c_val = asn.iter().find(|(v, _)| *v == 1).map(|(_, x)| *x);
        assert_eq!(a_val, Some(false));
        assert_eq!(c_val, Some(true));
    }

    #[test]
    fn identical_functions_have_no_counterexample() {
        let mut b = Bdd::new();
        let a = b.var(0);
        let c = b.var(1);
        let f = b.and(a, c);
        let g = b.and(c, a); // commutative -> same node
        assert_eq!(f, g);
        let m = b.xor(f, g);
        assert!(b.sat_one(m).is_none(), "miter is FALSE -> equivalent");
    }
}
