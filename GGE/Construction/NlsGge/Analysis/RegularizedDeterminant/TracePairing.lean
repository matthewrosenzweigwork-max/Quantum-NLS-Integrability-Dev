import NlsGge.Analysis.RegularizedDeterminant.FiniteRank

/-!
The trace pairing `tr(BC)` on real Hilbert-Schmidt operators: a polarized basis
series for the HS inner product, its identification with the ordinary trace of
the product of restrictions to a finite-dimensional subspace containing both
ranges, and joint continuity.
-/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

section Rect

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Polarized basis series for the HS inner product, over an arbitrary Hilbert basis. -/
theorem HilbertSchmidt.hasSum_inner_basis (S T : HilbertSchmidt E F) {ι : Type*}
    (b : HilbertBasis ι ℝ E) :
    HasSum (fun i => inner ℝ (toCLM S (b i)) (toCLM T (b i))) (inner ℝ S T) := by
  have h1 := HilbertSchmidt.hasSum_basis_sq (S + T) b
  have h2 := HilbertSchmidt.hasSum_basis_sq (S - T) b
  have h := (h1.sub h2).div_const 4
  have hpt : ∀ i, (‖toCLM (S + T) (b i)‖ ^ 2 - ‖toCLM (S - T) (b i)‖ ^ 2) / 4 =
      inner ℝ (toCLM S (b i)) (toCLM T (b i)) := by
    intro i
    rw [toCLM_add, toCLM_sub, add_apply, sub_apply,
      norm_add_sq_real, norm_sub_sq_real]
    ring
  have hval : (‖S + T‖ ^ 2 - ‖S - T‖ ^ 2) / 4 = inner ℝ S T := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  simp only [hpt, hval] at h
  exact h

end Rect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The trace pairing `tr(BC) = ⟪B*, C⟫_HS`. -/
def pairTrace (B C : HilbertSchmidt H H) : ℝ := inner ℝ (HilbertSchmidt.adjoint B) C

theorem pairTrace_eq_trace_restrict (B C : HilbertSchmidt H H) (V : Submodule ℝ H)
    [FiniteDimensional ℝ V] (hB : LinearMap.range (toCLM B).toLinearMap ≤ V)
    (hC : LinearMap.range (toCLM C).toLinearMap ≤ V) :
    pairTrace B C = LinearMap.trace ℝ V
      (restrictedEnd (toCLM B).toLinearMap V hB * restrictedEnd (toCLM C).toLinearMap V hC) := by
  classical
  let b := stdOrthonormalBasis ℝ V
  let v : Fin (Module.finrank ℝ V) → H := fun j => (b j : H)
  have hv : Orthonormal ℝ v := by
    have := b.orthonormal
    exact (Submodule.subtypeₗᵢ V).orthonormal_comp_iff.mpr this
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hs : Orthonormal ℝ ((↑) : Set.range v → H) := (orthonormal_subtype_range hinj).mpr hv
  obtain ⟨w, bw, hsw, hbw⟩ := hs.exists_hilbertBasis_extension
  have hsum := HilbertSchmidt.hasSum_inner_basis (HilbertSchmidt.adjoint B) C bw
  let g : Fin (Module.finrank ℝ V) → w := fun j => ⟨v j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hinj (congrArg (fun x : w => (x : H)) hij)
  have hterm : ∀ x : H, inner ℝ (toCLM (HilbertSchmidt.adjoint B) x) (toCLM C x) =
      inner ℝ x (toCLM B (toCLM C x)) := by
    intro x
    rw [toCLM_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hgv : ∀ j, bw (g j) = v j := fun j => by rw [hbw]
  have hzero : ∀ i ∉ Finset.univ.map ⟨g, hg⟩,
      inner ℝ (toCLM (HilbertSchmidt.adjoint B) (bw i)) (toCLM C (bw i)) = 0 := by
    intro i hi
    rw [hterm]
    have hz : toCLM B (toCLM C (bw i)) ∈ V := hB ⟨_, rfl⟩
    have hrep := congrArg (fun y : V => (y : H)) (b.sum_repr' ⟨_, hz⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep, inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [inner_smul_right]
    have hne : i ≠ g j := fun h => hi (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, h.symm⟩)
    have h0 : inner ℝ (bw i) (bw (g j)) = 0 := bw.orthonormal.2 hne
    rw [hgv] at h0
    have : inner ℝ (bw i) ((b j : V) : H) = 0 := h0
    rw [this, mul_zero]
  have hS : HasSum (fun i => inner ℝ (toCLM (HilbertSchmidt.adjoint B) (bw i)) (toCLM C (bw i)))
      (∑ i ∈ Finset.univ.map ⟨g, hg⟩,
        inner ℝ (toCLM (HilbertSchmidt.adjoint B) (bw i)) (toCLM C (bw i))) :=
    hasSum_sum_of_ne_finset_zero hzero
  have heq := hsum.unique hS
  have hpair : pairTrace B C = ∑ j, inner ℝ (v j) (toCLM B (toCLM C (v j))) := by
    unfold pairTrace
    rw [heq, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    rw [hterm]
    simp only [Function.Embedding.coeFn_mk, hgv]
  rw [hpair, LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  rfl

theorem continuous_pairTrace :
    Continuous (fun p : HilbertSchmidt H H × HilbertSchmidt H H => pairTrace p.1 p.2) := by
  have hadj : Continuous (fun B : HilbertSchmidt H H => HilbertSchmidt.adjoint B) := by
    apply (Isometry.of_dist_eq _).continuous
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← HilbertSchmidt.adjoint_sub, HilbertSchmidt.norm_adjoint]
  exact (hadj.comp continuous_fst).inner continuous_snd

end NlsGge.Analysis.RegularizedDeterminant
