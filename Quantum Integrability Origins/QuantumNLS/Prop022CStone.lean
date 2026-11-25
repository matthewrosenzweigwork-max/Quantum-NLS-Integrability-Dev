import Mathlib

/-! PROP-022 route A, round 4, stage C4: uniqueness of a strongly continuous unitary group with a
prescribed (closed-graph) generator.

For a complex Hilbert space `X`, a set `S ⊆ X × X` (the graph of a closed operator) and a family
`G : ℝ → X ≃ₗᵢ X`, `IsStoneGroup G S` says: `G` is a strongly continuous one-parameter unitary group
whose generator is exactly `S`: `t ↦ G t x` is differentiable at `0` with derivative `y` iff `(x,y) ∈ S`.

`stone_unique`: if `S` is skew-symmetric (`⟪y,x'⟫ + ⟪x,y'⟫ = 0` on `S × S`) and has dense domain, two groups
with generator `S` coincide.  (Proof: for `x, x'` in the domain, `s ↦ ⟪G₁(s) x, G₂(s) x'⟫` has derivative zero
because `G_i(s)` preserve the graph; density and unitarity then give `G₁ = G₂`.)  This is the generic form of
`Ext006SourceStoneR44a.family_unique`, used to characterize `exp(t(a*(v) - a(v)))` on Fock space. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace Topology
open Filter
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022CStone

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- `G` is a strongly continuous unitary group with generator exactly `S`. -/
structure IsStoneGroup (G : ℝ → X ≃ₗᵢ[ℂ] X) (S : Set (X × X)) : Prop where
  zero : ∀ x, G 0 x = x
  add : ∀ s t x, G s (G t x) = G (s + t) x
  cont : ∀ x, Continuous fun t : ℝ => G t x
  gen : ∀ x y, HasDerivAt (fun t : ℝ => G t x) y 0 ↔ (x, y) ∈ S

variable {G : ℝ → X ≃ₗᵢ[ℂ] X} {S : Set (X × X)}

lemma IsStoneGroup.deriv_at (h : IsStoneGroup G S) {x y : X} (hxy : (x, y) ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => G s x) (G t y) t := by
  have hd0 := (h.gen x y).mpr hxy
  have hshift := hd0.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have hd := ((G t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hshift
  have he : (fun s : ℝ => G t (G (s - t) x)) = (fun s : ℝ => G s x) := by
    funext s
    rw [h.add]
    congr 1
    ring
  change HasDerivAt (fun s : ℝ => G t (G (s - t) x)) (G t ((1 : ℝ) • y)) t at hd
  rw [he, one_smul] at hd
  exact hd

lemma IsStoneGroup.preserves (h : IsStoneGroup G S) {x y : X} (hxy : (x, y) ∈ S) (t : ℝ) :
    (G t x, G t y) ∈ S := by
  have hd0 := (h.gen x y).mpr hxy
  have hd := ((G t).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd0
  have he : (fun s : ℝ => G t (G s x)) = (fun s : ℝ => G s (G t x)) := by
    funext s
    rw [h.add, h.add, add_comm]
  change HasDerivAt (fun s : ℝ => G t (G s x)) (G t y) 0 at hd
  rw [he] at hd
  exact (h.gen _ _).mp hd

lemma dense_ind {s : Set X} (hs : Dense s) {p : X → Prop} (hp : IsClosed {x | p x})
    (h : ∀ a ∈ s, p a) (x : X) : p x :=
  (closure_minimal h hp) (hs x)

/-- **Uniqueness of the unitary group with a given skew-symmetric densely defined generator.** -/
theorem stone_unique {G₁ G₂ : ℝ → X ≃ₗᵢ[ℂ] X}
    (hskew : ∀ p ∈ S, ∀ q ∈ S, ⟪p.2, q.1⟫_ℂ + ⟪p.1, q.2⟫_ℂ = 0)
    (hdense : Dense {x | ∃ y, (x, y) ∈ S})
    (h₁ : IsStoneGroup G₁ S) (h₂ : IsStoneGroup G₂ S) (t : ℝ) (x : X) : G₁ t x = G₂ t x := by
  have hp : ∀ x x' : X, (∃ y, (x, y) ∈ S) → (∃ y', (x', y') ∈ S) →
      ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ := by
    rintro x x' ⟨y, hxy⟩ ⟨y', hxy'⟩
    have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => ⟪G₁ u x, G₂ u x'⟫_ℂ) 0 s := by
      intro s
      have d1 := h₁.deriv_at hxy s
      have d2 := h₂.deriv_at hxy' s
      have hs := hskew _ (h₁.preserves hxy s) _ (h₂.preserves hxy' s)
      have d := d1.inner ℂ d2
      have hs' : ⟪G₁ s x, G₂ s y'⟫_ℂ + ⟪G₁ s y, G₂ s x'⟫_ℂ = 0 := by
        rw [add_comm]
        exact hs
      convert d using 1
      exact hs'.symm
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [h₁.zero, h₂.zero] using he
  have h1 : ∀ x : X, (∃ y, (x, y) ∈ S) → ∀ x' : X, ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ := by
    intro x hx x'
    exact dense_ind hdense (p := fun x' : X => ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ)
      (isClosed_eq (continuous_const.inner (G₂ t).continuous) (continuous_const.inner continuous_id))
      (fun x'' hx'' => hp x x'' hx hx'') x'
  have hall : ∀ x x' : X, ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ := by
    intro x x'
    have hcl : IsClosed {x : X | ∀ x' : X, ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ} := by
      have : {x : X | ∀ x' : X, ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ} =
          ⋂ x' : X, {x : X | ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ} := by
        ext x; simp
      rw [this]
      exact isClosed_iInter (fun x' => isClosed_eq ((G₁ t).continuous.inner continuous_const)
        (continuous_id.inner continuous_const))
    exact dense_ind hdense (p := fun x : X => ∀ x' : X, ⟪G₁ t x, G₂ t x'⟫_ℂ = ⟪x, x'⟫_ℂ) hcl
      (fun x'' hx'' => h1 x'' hx'') x x'
  apply ext_inner_right ℂ
  intro w
  have := hall x ((G₂ t).symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  rw [this, ← (G₂ t).inner_map_map x ((G₂ t).symm w), LinearIsometryEquiv.apply_symm_apply]

end QuantumNLS.Prop022CStone

#print axioms QuantumNLS.Prop022CStone.stone_unique
