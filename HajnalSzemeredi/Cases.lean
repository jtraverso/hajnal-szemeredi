module

public import HajnalSzemeredi.Shift
public import HajnalSzemeredi.Structure

/-!
# Los dos casos de recoloreo del Teorema 2.4 de Kierstead–Kostochka

Contexto: `Ctx G S P c r s lo hi` (clase grande inaccesible), `U` y `𝒜' = T_U` como en
`Ctx.exists_TU`, un vértice solo `z` con color `W = c z ∈ 𝒜'`, un vecino especial
`y₁ ∈ S_z ⊆ B`, y una coloración equitativa `g` de `B⁻ = B \ {y₁}` con la paleta `ℬ = P \ 𝒜`
(dada por la hipótesis de inducción primaria).

* **Caso 1** (`case1`): `z` es movible a una clase `X ∈ 𝒜 \ {W}`. Se mueve `z` a `X` y `y₁` a
  `W`; la coloración de `A⁺ = A ∪ {y₁}` es equitativa o casi equitativa con clase grande
  `X ∪ {z}` accesible (porque `W` es terminal), y por el Lema 2.1 se vuelve equitativa; junto con
  `g` da una coloración equitativa de `S`.
* **Caso 2** (`case2`): `z` no es movible a ninguna clase de `𝒜` y tiene dos vecinos especiales
  `y₁ ≠ y₂` no adyacentes. Se mueve `y₁` a `W` y `z` a una clase `Y` de `g` sin vecinos de `z`;
  se obtiene una coloración casi equitativa con estrictamente más clases accesibles.
-/

@[expose] public section

noncomputable section

open Classical Finset Relation

namespace HajnalSzemeredi

variable {V : Type*} {G : SimpleGraph V}

/-- Pegado de dos coloraciones equitativas de partes disjuntas con paletas disjuntas. -/
theorem isEq_combine {S SA SB : Finset V} {P PA PB : Finset ℕ} {cA cB : V → ℕ} {s : ℕ}
    (hA : IsEq G SA PA cA s) (hB : IsEq G SB PB cB s) (hS : SA ∪ SB = S)
    (hdisj : Disjoint SA SB) (hP : PA ∪ PB = P) (hPdisj : Disjoint PA PB) :
    IsEq G S P (fun v => if v ∈ SA then cA v else cB v) s := by
  sorry

theorem case1 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hX : ∃ X ∈ acc G S P c lo, X ≠ c z ∧ Movable G S c z X)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c', IsEq G S P c' s := by
  sorry

theorem case2 {S : Finset V} {P : Finset ℕ} {c g : V → ℕ} {r s lo hi U : ℕ} {z y₁ y₂ : V}
    (h : Ctx G S P c r s lo hi)
    (hterm : ∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
      ReflTransGen (avoid G S c W) X lo)
    (hzS : z ∈ S) (hzT : c z ∈ T G S P c lo U)
    (hnot : ∀ X ∈ acc G S P c lo, X ≠ c z → ¬ Movable G S c z X)
    (hy₁ : y₁ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hy₂ : y₂ ∈ Sz G S c (T G S P c lo U) (part S c (P \ acc G S P c lo)) z)
    (hne : y₁ ≠ y₂) (hnadj : ¬ G.Adj y₁ y₂)
    (hg : IsEq G ((part S c (P \ acc G S P c lo)).erase y₁) (P \ acc G S P c lo) g s) :
    ∃ c' hi', IsNear G S P c' s lo hi' ∧
      (acc G S P c lo).card < (acc G S P c' lo).card := by
  sorry

end HajnalSzemeredi
