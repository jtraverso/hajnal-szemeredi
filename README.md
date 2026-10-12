# The Hajnal–Szemerédi theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

**Theorem (Hajnal–Szemerédi 1970; conjectured by Erdős 1964).** Every finite graph with maximum
degree at most `r` has an *equitable* proper colouring with `r + 1` colours: any two colour classes
differ in size by at most one. If the number of vertices is `s (r + 1)`, every class has exactly
`s` vertices (the colouring form of Erdős Problem #914).

The audited statements are in [`Challenge.lean`](Challenge.lean) (Mathlib imports only, Mathlib's
`SimpleGraph.Coloring` and `SimpleGraph.degree`); the proofs are in [`Solution.lean`](Solution.lean)
and the library [`HajnalSzemeredi/`](HajnalSzemeredi). [`comparator.json`](comparator.json) lists
the compared theorems and [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md) reproduces verbatim the Mathlib definitions
used by the statements (at the pinned Mathlib revision), and
[`formalization.yaml`](formalization.yaml) records provenance and process.

## How the proof goes (Kierstead–Kostochka 2008)

Colourings are functions `V → ℕ` restricted to a finite vertex set `S` with a palette `P`, so that
the induction can pass to induced subgraphs and sub-palettes without changing types.

* `Shift.lean` — **Lemma 2.1**: if the large class of a nearly equitable colouring reaches the
  small class in the auxiliary digraph (`V → W` if some vertex of `V` has no neighbour in `W`),
  moving one vertex along each arc gives an equitable colouring.
* `Structure.lean` — accessible classes, inequality (2.1), sizes of `A` and `B`, `|𝒜| ≥ 2`,
  terminal classes and the family `𝒜' = T_U` (with `U` non-terminal minimising `|T_U|`), and
  inequality (2.2).
* `Count.lean` — **Lemmas 2.2–2.3**: solo edges, inequality (2.3), and the discharging count with
  weights `q/|S_z|`.
* `Cases.lean` — the two recolouring cases of **Theorem 2.4**.
* `Main.lean` — primary induction on the number of edges (delete an edge, move one endpoint) and
  secondary induction on the number of inaccessible classes.
* `Final.lean` — reduction to `|V|` divisible by `r + 1` (add a disjoint `K_p`) and the statements
  with Mathlib colourings.

## Scope

Finite simple graphs, vertex types in any universe. No `sorry`, no custom axioms; the compared
theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The algorithmic part of
Kierstead–Kostochka (Section 3) is not formalized.

## Sources

* H. A. Kierstead, A. V. Kostochka, *A short proof of the Hajnal–Szemerédi theorem on equitable
  colouring*, Combin. Probab. Comput. 17 (2008) 265–270.
* A. Hajnal, E. Szemerédi, *Proof of a conjecture of P. Erdős*, in Combinatorial Theory and its
  Applications II, North-Holland, 1970, 601–623.
* P. Erdős, Problem 9, in Theory of Graphs and its Applications, Prague, 1964, p. 159.
* Erdős Problem #914, https://www.erdosproblems.com/914 (its Lean statement, without proof, is in
  google-deepmind/formal-conjectures).

We are not aware of a prior formal proof of the Hajnal–Szemerédi theorem; this was checked against
Mathlib, the Lean Pool collection, the Palomar registry and a web search, not exhaustively.

## Authorship and use of AI

The choice of result and proof route are by the author. The Lean code was written with an AI agent
(Claude Opus 5.5 in Claude Code); the proofs of Lemmas 2.2–2.3 and of the two recolouring cases were
produced by Harmonic's Aristotle from formal statements and audited. Every result was checked
mechanically with Lean. See `formalization.yaml` for details.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

Submissions to the Palomar registry go through https://submit.palomar-registry.org/.
