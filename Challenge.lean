/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The Hajnal–Szemerédi theorem on equitable colourings

A proper colouring is *equitable* if the sizes of any two colour classes differ by at most one.

**Theorem (Hajnal–Szemerédi 1970, conjectured by Erdős in 1964).** Every finite graph with
maximum degree at most `r` has an equitable proper colouring with `r + 1` colours.

We use Mathlib's notions: `G.Coloring (Fin (r + 1))` is a proper colouring with colours
`0, …, r`, `G.degree v` is the degree of `v`, and the colour class of `i` is
`Finset.univ.filter fun v => C v = i`.

* `HajnalSzemeredi.hajnal_szemeredi`: the theorem.
* `HajnalSzemeredi.hajnal_szemeredi_exact`: the exact form when `|V| = s (r + 1)`: every colour
  class has exactly `s` vertices (this is the colouring form of Erdős Problem #914).
-/

public section

namespace HajnalSzemeredi

/-- **Hajnal–Szemerédi theorem.** A finite graph with maximum degree at most `r` has a proper
`(r + 1)`-colouring in which any two colour classes differ in size by at most one. -/
theorem hajnal_szemeredi {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by
  sorry

/-- **Hajnal–Szemerédi, exact form.** If moreover `|V| = s (r + 1)`, there is a proper
`(r + 1)`-colouring all of whose colour classes have exactly `s` vertices. -/
theorem hajnal_szemeredi_exact {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card = s := by
  sorry

end HajnalSzemeredi
