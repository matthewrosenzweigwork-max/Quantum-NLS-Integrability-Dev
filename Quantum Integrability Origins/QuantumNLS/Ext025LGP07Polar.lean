import Mathlib

/-!
# EXT-025 layer A (GP-07 unconditional route), module 1: bounded polar decomposition

Generic bounded-operator layer (no spectral measure, no unbounded calculus).  For Hilbert spaces
`V`, `E` over `ℂ` and a bounded INJECTIVE operator `i : V →L[ℂ] E` with DENSE range, put
`A := i i†` and `R := CFC.sqrt A` (Mathlib's bounded continuous functional calculus
`CFC.sqrt` on the C*-algebra `E →L[ℂ] E`).  Then

* `R` is nonnegative (hence selfadjoint), `R * R = i i†`, and `‖R x‖ = ‖i† x‖`;
* `R` is injective with dense range;
* (polar decomposition, `polar_exists`) there is a unitary `Z : V ≃ₗᵢ[ℂ] E` with `i v = R (Z v)`;
  `Z` is obtained by extending the isometry `R x ↦ i† x` (`LinearMap.extendOfIsometry`) and
  showing that it is onto;
* (uniqueness, `polar_unique`) any nonnegative `R'` with `i = R' ∘ Z'` for a unitary `Z'` equals `R`.

The route avoids Douglas' lemma: the statement `ran i = ran R` is a consequence of
`i = R ∘ Z` with `Z` onto.  Everything is proved from Mathlib; no unproved goal and no extra axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexConjugate InnerProduct

namespace QuantumNLS.Ext025L.Polar

universe u v

variable {V : Type u} {E : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `A = i i†`. -/
def polarA (i : V →L[ℂ] E) : E →L[ℂ] E := i ∘L (ContinuousLinearMap.adjoint i)

/-- `R = (i i†)^{1/2}` by the bounded continuous functional calculus. -/
def polarR (i : V →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt (polarA i)

theorem polarA_nonneg (i : V →L[ℂ] E) : 0 ≤ polarA i :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_self_comp_adjoint i)

theorem polarR_nonneg (i : V →L[ℂ] E) : 0 ≤ polarR i := CFC.sqrt_nonneg _

theorem polarR_mul_self (i : V →L[ℂ] E) : polarR i * polarR i = polarA i :=
  CFC.sqrt_mul_sqrt_self _ (polarA_nonneg i)

theorem polarR_apply_apply (i : V →L[ℂ] E) (x : E) :
    polarR i (polarR i x) = i (ContinuousLinearMap.adjoint i x) := by
  have h := congrArg (fun T : E →L[ℂ] E => T x) (polarR_mul_self i)
  simpa [polarA] using h

theorem polarR_isPositive (i : V →L[ℂ] E) : (polarR i).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (polarR_nonneg i)

/-- `R` is symmetric. -/
theorem polarR_inner (i : V →L[ℂ] E) (x y : E) : ⟪polarR i x, y⟫_ℂ = ⟪x, polarR i y⟫_ℂ :=
  (polarR_isPositive i).isSymmetric x y

theorem polarR_norm (i : V →L[ℂ] E) (x : E) :
    ‖polarR i x‖ = ‖ContinuousLinearMap.adjoint i x‖ := by
  have h1 : ‖polarR i x‖ ^ 2 = (⟪polarR i x, polarR i x⟫_ℂ).re :=
    norm_sq_eq_re_inner (𝕜 := ℂ) _
  have h2 : ‖ContinuousLinearMap.adjoint i x‖ ^ 2 =
      (⟪ContinuousLinearMap.adjoint i x, ContinuousLinearMap.adjoint i x⟫_ℂ).re :=
    norm_sq_eq_re_inner (𝕜 := ℂ) _
  have h3 : ⟪polarR i x, polarR i x⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint i x, ContinuousLinearMap.adjoint i x⟫_ℂ := by
    rw [polarR_inner, polarR_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  have : ‖polarR i x‖ ^ 2 = ‖ContinuousLinearMap.adjoint i x‖ ^ 2 := by rw [h1, h2, h3]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

/-- A vector orthogonal to a dense range is `0`. -/
theorem eq_zero_of_orthogonal_range {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (f : X → W) (hd : DenseRange f) (z : W) (hz : ∀ x, ⟪f x, z⟫_ℂ = 0) :
    z = 0 := by
  have : ⟪z, z⟫_ℂ = 0 := by
    have h := hd.induction_on (p := fun y : W => ⟪y, z⟫_ℂ = 0) z
      (isClosed_eq (by fun_prop) continuous_const) hz
    exact h
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp this

theorem adjoint_injective (i : V →L[ℂ] E) (hd : DenseRange i) :
    Function.Injective (ContinuousLinearMap.adjoint i) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_orthogonal_range (fun v => i v) hd x (fun v => ?_)
  rw [← ContinuousLinearMap.adjoint_inner_right, hx, inner_zero_right]

theorem polarR_injective (i : V →L[ℂ] E) (hd : DenseRange i) :
    Function.Injective (polarR i) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := polarR_norm i x
  rw [hx, norm_zero] at h
  exact adjoint_injective i hd (by simpa using (norm_eq_zero.mp h.symm))

/-- Dense range from triviality of the orthogonal complement of the range. -/
theorem denseRange_of_orthogonal {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (f : X →L[ℂ] W) (h : ∀ z : W, (∀ x, ⟪f x, z⟫_ℂ = 0) → z = 0) : DenseRange f := by
  have hK : (LinearMap.range (f : X →ₗ[ℂ] W))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact h z (fun x => (Submodule.mem_orthogonal _ z).mp hz (f x)
      (LinearMap.mem_range_self (f : X →ₗ[ℂ] W) x))
  have hc := (Submodule.topologicalClosure_eq_top_iff
    (K := LinearMap.range (f : X →ₗ[ℂ] W))).mpr hK
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr hc
  have hr : ((LinearMap.range (f : X →ₗ[ℂ] W) : Submodule ℂ W) : Set W) = Set.range f := by
    ext w
    simp
  rw [hr] at hd
  exact hd

theorem polarR_denseRange (i : V →L[ℂ] E) (hd : DenseRange i) : DenseRange (polarR i) := by
  refine denseRange_of_orthogonal (polarR i) (fun z hz => ?_)
  have h1 : polarR i z = 0 := by
    refine (inner_self_eq_zero (𝕜 := ℂ)).mp ?_
    have := hz (polarR i z)
    rwa [polarR_inner] at this
  exact polarR_injective i hd (by rw [h1, map_zero])

theorem adjoint_denseRange (i : V →L[ℂ] E) (hinj : Function.Injective i) :
    DenseRange (ContinuousLinearMap.adjoint i) := by
  refine denseRange_of_orthogonal (ContinuousLinearMap.adjoint i) (fun z hz => ?_)
  have h1 : i z = 0 := by
    refine (inner_self_eq_zero (𝕜 := ℂ)).mp ?_
    have := hz (i z)
    rwa [ContinuousLinearMap.adjoint_inner_left] at this
  exact hinj (by rw [h1, map_zero])

/-- The isometry `Y : E → V` with `Y (R x) = i† x`. -/
def polarY (i : V →L[ℂ] E) (hd : DenseRange i) : E →ₗᵢ[ℂ] V :=
  LinearMap.extendOfIsometry (f := (ContinuousLinearMap.adjoint i : E →ₗ[ℂ] V))
    (e := (polarR i : E →ₗ[ℂ] E)) (polarR_denseRange i hd)
    (fun x => (polarR_norm i x).symm)

theorem polarY_apply (i : V →L[ℂ] E) (hd : DenseRange i) (x : E) :
    polarY i hd (polarR i x) = ContinuousLinearMap.adjoint i x :=
  LinearMap.extendOfIsometry_eq (f := (ContinuousLinearMap.adjoint i : E →ₗ[ℂ] V))
    (e := (polarR i : E →ₗ[ℂ] E)) (polarR_denseRange i hd)
    (fun x => (polarR_norm i x).symm) x

theorem polarY_surjective (i : V →L[ℂ] E) (hinj : Function.Injective i) (hd : DenseRange i) :
    Function.Surjective (polarY i hd) := by
  have hcl : IsClosed (Set.range (polarY i hd)) :=
    (polarY i hd).isometry.isClosedEmbedding.isClosed_range
  have hsub : Set.range (ContinuousLinearMap.adjoint i) ⊆ Set.range (polarY i hd) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨polarR i x, polarY_apply i hd x⟩
  have hdense : Dense (Set.range (polarY i hd)) :=
    (adjoint_denseRange i hinj).mono hsub
  have : Set.range (polarY i hd) = Set.univ := by
    rw [← hcl.closure_eq, hdense.closure_eq]
  exact Set.range_eq_univ.mp this

/-- The unitary of the polar decomposition `i = R ∘ Z`. -/
def polarZ (i : V →L[ℂ] E) (hinj : Function.Injective i) (hd : DenseRange i) : V ≃ₗᵢ[ℂ] E :=
  (LinearIsometryEquiv.ofSurjective (polarY i hd) (polarY_surjective i hinj hd)).symm

theorem polarZ_symm_apply (i : V →L[ℂ] E) (hinj : Function.Injective i) (hd : DenseRange i)
    (x : E) : (polarZ i hinj hd).symm x = polarY i hd x := by
  simp [polarZ]

/-- Polar decomposition: `i v = R (Z v)`. -/
theorem polar_decomp (i : V →L[ℂ] E) (hinj : Function.Injective i) (hd : DenseRange i)
    (v : V) : i v = polarR i (polarZ i hinj hd v) := by
  refine ext_inner_right ℂ (fun x => ?_)
  rw [polarR_inner, ← ContinuousLinearMap.adjoint_inner_right]
  have h1 : ContinuousLinearMap.adjoint i x = (polarZ i hinj hd).symm (polarR i x) := by
    rw [polarZ_symm_apply, polarY_apply]
  rw [h1]
  have := (polarZ i hinj hd).inner_map_map v ((polarZ i hinj hd).symm (polarR i x))
  rw [(polarZ i hinj hd).apply_symm_apply] at this
  exact this.symm

theorem polar_exists (i : V →L[ℂ] E) (hinj : Function.Injective i) (hd : DenseRange i) :
    ∃ Z : V ≃ₗᵢ[ℂ] E, ∀ v, i v = polarR i (Z v) :=
  ⟨polarZ i hinj hd, polar_decomp i hinj hd⟩

/-- Uniqueness of the nonnegative factor in `i = R' ∘ Z'` (`Z'` unitary). -/
theorem polar_unique (i : V →L[ℂ] E) (R' : E →L[ℂ] E) (hR' : 0 ≤ R') (Z' : V ≃ₗᵢ[ℂ] E)
    (h : ∀ v, i v = R' (Z' v)) : R' = polarR i := by
  have hpos : R'.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hR'
  have hadj : ∀ x, ContinuousLinearMap.adjoint i x = Z'.symm (R' x) := by
    intro x
    refine ext_inner_left ℂ (fun v => ?_)
    have hsym : ∀ a b : E, ⟪R' a, b⟫_ℂ = ⟪a, R' b⟫_ℂ := fun a b => hpos.isSymmetric a b
    rw [ContinuousLinearMap.adjoint_inner_right, h, hsym]
    have := Z'.inner_map_map v (Z'.symm (R' x))
    rw [Z'.apply_symm_apply] at this
    exact this
  have hmul : R' * R' = polarA i := by
    ext x
    change R' (R' x) = i (ContinuousLinearMap.adjoint i x)
    rw [hadj, h, Z'.apply_symm_apply]
  exact (CFC.sqrt_unique hmul hR').symm

end QuantumNLS.Ext025L.Polar

#print axioms QuantumNLS.Ext025L.Polar.polar_exists
#print axioms QuantumNLS.Ext025L.Polar.polar_unique
#print axioms QuantumNLS.Ext025L.Polar.polarR_injective
