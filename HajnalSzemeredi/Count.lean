module

public import HajnalSzemeredi.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Lemas de conteo 2.2 y 2.3 de Kierstead–Kostochka

Abstraemos la situación del artículo en `CountHyp`:

* `PA` (clases accesibles) y `PB` (inaccesibles) son paletas disjuntas que cubren los colores de
  `S`; `A`, `B` son los vértices con color en `PA`, `PB`;
* `TU ⊆ PA` es la familia `𝒜'`, con `t = |TU|` clases, todas de tamaño `s`;
* `q = |PB|`, `|B| = q s + 1`, grado máximo `r` con `r + 1 = |PA| + |PB|`;
* (2.1): todo `y ∈ B` tiene un vecino en cada clase de `PA`;
* (2.2): todo `x` con color en `TU` tiene al menos `|PA| - 1 - t` vecinos en `A`.

Una arista `zy` (`z` con color `W ∈ TU`, `y ∈ B`) es *solo* si `z` es el único vecino de `y` en
la clase `W`. `Sz z` son los vecinos especiales de `z` (en `B`) y `Sy y` los de `y` (en `A'`).
-/

@[expose] public section

noncomputable section

open Classical Finset

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

/-- Vértices de `S` con color en la paleta `Q`. -/
def part (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) : Finset V := S.filter fun v => c v ∈ Q

/-- Vecinos de `y` en la clase `W`. -/
def nIn (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (y : V) (W : ℕ) : Finset V :=
  nbr G S y ∩ cls S c W

/-- `zy` es una arista solo (respecto a la familia `TU` y al conjunto `B`). -/
def IsSolo (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V)
    (z y : V) : Prop :=
  z ∈ S ∧ c z ∈ TU ∧ y ∈ B ∧ nIn G S c y (c z) = {z}

/-- Vecinos especiales de `z`. -/
def Sz (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (z : V) :
    Finset V := B.filter fun y => IsSolo G S c TU B z y

/-- Vecinos especiales de `y`. -/
def Sy (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (y : V) :
    Finset V := S.filter fun z => IsSolo G S c TU B z y

/-- Hipótesis de la parte de conteo. -/
structure CountHyp (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (PA PB TU : Finset ℕ)
    (r s : ℕ) : Prop where
  disj : Disjoint PA PB
  cover : ∀ v ∈ S, c v ∈ PA ∪ PB
  sub : TU ⊆ PA
  ne : TU.Nonempty
  card_r : r + 1 = PA.card + PB.card
  deg : DegLe G S r
  size : ∀ W ∈ TU, (cls S c W).card = s
  card_B : (part S c PB).card = PB.card * s + 1
  /-- (2.1) -/
  h21 : ∀ y ∈ part S c PB, ∀ X ∈ PA, (nIn G S c y X).Nonempty
  /-- (2.2) -/
  h22 : ∀ x ∈ S, c x ∈ TU → PA.card ≤ (nbr G (part S c PA) x).card + TU.card + 1

namespace CountHyp

variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}

/-- Desigualdad (2.3): `|S^y| ≥ t - q + 1 + d_B(y)`. -/
theorem card_Sy (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    TU.card + 1 + (nbr G (part S c PB) y).card ≤
      (Sy G S c TU (part S c PB) y).card + PB.card := by
  sorry

/-- (2.1), forma de grado: `d_B(y) ≤ q - 1` para `y ∈ B`. -/
theorem deg_B (h : CountHyp G S c PA PB TU r s) {y : V} (hy : y ∈ part S c PB) :
    (nbr G (part S c PB) y).card + 1 ≤ PB.card := by
  sorry

/-- **Lema 2.2.** Si ningún vértice solo de `W ∈ TU` es movible a otra clase de `PA`, entonces
`q + 1 ≤ t` y todo `y ∈ B` es solo. -/
theorem lemma_2_2 (h : CountHyp G S c PA PB TU r s) {W : ℕ} (hW : W ∈ TU)
    (hW' : ∀ z ∈ cls S c W, (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ W → ¬ Movable G S c z X) :
    PB.card + 1 ≤ TU.card ∧ ∀ y ∈ part S c PB, (Sy G S c TU (part S c PB) y).Nonempty := by
  sorry

/-- **Lema 2.3.** Existe un vértice solo `z` (con color en `TU`) que es movible a otra clase de
`PA`, o que tiene dos vecinos especiales distintos no adyacentes. -/
theorem lemma_2_3 (h : CountHyp G S c PA PB TU r s) :
    ∃ z ∈ S, c z ∈ TU ∧ (Sz G S c TU (part S c PB) z).Nonempty ∧
      ((∃ X ∈ PA, X ≠ c z ∧ Movable G S c z X) ∨
        ∃ y₁ ∈ Sz G S c TU (part S c PB) z, ∃ y₂ ∈ Sz G S c TU (part S c PB) z,
          y₁ ≠ y₂ ∧ ¬ G.Adj y₁ y₂) := by
  sorry

end CountHyp

end HajnalSzemeredi
