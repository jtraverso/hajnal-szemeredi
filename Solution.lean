/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import HajnalSzemeredi

/-!
# Proofs of the statements in `Challenge.lean`

The statements are restated verbatim and proved from the `HajnalSzemeredi` library, which
follows Kierstead–Kostochka's short proof (`HajnalSzemeredi.Final`). The library works with
classical decidability instances; `convert` identifies the colour-class cardinalities.
-/

public section

namespace HajnalSzemeredi

theorem hajnal_szemeredi {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by
  obtain ⟨C, hC⟩ := hajnalSzemeredi G r h
  exact ⟨C, fun i j => by convert hC i j⟩

theorem hajnal_szemeredi_exact {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card = s := by
  obtain ⟨C, hC⟩ := hajnalSzemeredi_exact G r s hcard h
  exact ⟨C, fun i => by convert hC i⟩

end HajnalSzemeredi
