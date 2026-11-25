import Mathlib

/-!
# Finite-dimensional Carleman inequality

* `norm_det_le_prod_col` : complex Hadamard inequality `‖det M‖ ≤ ∏_j ‖M e_j‖`.
* `norm_det_one_add_mul_exp_neg_trace_le` : `‖det(1+X) exp(-tr X)‖ ≤ exp(½ ‖X‖_HS²)`,
  the finite-matrix form of Carleman's inequality
  (cf. B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Lemma 9.1 / Thm 9.2;
  here the exact form with constant `1/2` is derived directly from Hadamard's inequality).

Proof of Hadamard: Gram-Schmidt orthonormal basis `b` of the columns `v`; the change of basis
`b → standard basis` is unitary so `‖det M‖ = ‖b.det v‖ = ∏ ‖⟪b i, v i⟫‖ ≤ ∏ ‖v i‖`.
-/

namespace NlsGge.Analysis.RegularizedDeterminant

open scoped Matrix InnerProductSpace

section Hadamard

/-- Hadamard on `Fin n`, in terms of column vectors of `EuclideanSpace`. -/
theorem norm_det_le_prod_norm_fin {n : ℕ} (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    ‖(Matrix.of fun i j => v j i).det‖ ≤ ∏ j, ‖v j‖ := by
  classical
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  set b := InnerProductSpace.gramSchmidtOrthonormalBasis hcard v with hb
  set e := EuclideanSpace.basisFun (Fin n) ℂ with he
  have h1 : b.toBasis.toMatrix v = b.toBasis.toMatrix e.toBasis * e.toBasis.toMatrix v := by
    rw [Module.Basis.toMatrix_mul_toMatrix]
  have h2 : e.toBasis.toMatrix v = Matrix.of fun i j => v j i := by
    ext i j
    simp [Module.Basis.toMatrix_apply, he]
  have h4 : ‖b.toBasis.det e.toBasis‖ = 1 := by
    rw [OrthonormalBasis.coe_toBasis]
    exact OrthonormalBasis.det_to_matrix_orthonormalBasis b e
  have h3 : ‖b.toBasis.det v‖ = ‖(Matrix.of fun i j => v j i).det‖ := by
    rw [Module.Basis.det_apply, h1, Matrix.det_mul, norm_mul, ← Module.Basis.det_apply,
      h4, one_mul, h2]
  rw [← h3, InnerProductSpace.gramSchmidtOrthonormalBasis_det hcard v, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ?_)
  calc ‖⟪b i, v i⟫_ℂ‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.norm_eq_one, one_mul]

/-- **Complex Hadamard inequality** (column version). -/
theorem norm_det_le_prod_col {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) :
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) := by
  set σ : I ≃ Fin (Fintype.card I) := Fintype.equivFin I with hσ
  set M' : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ :=
    M.submatrix σ.symm σ.symm with hM'
  have hdet : M'.det = M.det := Matrix.det_submatrix_equiv_self σ.symm M
  let v : Fin (Fintype.card I) → EuclideanSpace ℂ (Fin (Fintype.card I)) :=
    fun j => WithLp.toLp 2 fun i => M' i j
  have hv : (Matrix.of fun i j => v j i) = M' := by ext i j; rfl
  have key := norm_det_le_prod_norm_fin v
  rw [hv, hdet] at key
  refine key.trans (le_of_eq ?_)
  rw [← Equiv.prod_comp σ.symm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [← Equiv.sum_comp σ.symm]
  simp [v, hM']

end Hadamard

section Carleman

/-- Squared norm of column `j` of `1 + X`. -/
theorem sum_norm_sq_one_add_col {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (j : I) :
    ∑ i, ‖(1 + X) i j‖ ^ 2 = 1 + 2 * (X j j).re + ∑ i, ‖X i j‖ ^ 2 := by
  have : ∀ i, ‖(1 + X) i j‖ ^ 2 =
      ‖X i j‖ ^ 2 + (if i = j then 1 + 2 * (X j j).re else 0) := by
    intro i
    by_cases h : i = j
    · subst h
      simp only [Matrix.add_apply, Matrix.one_apply_eq, ite_true]
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp; ring
    · simp [Matrix.add_apply, Matrix.one_apply_ne h, h]
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j]
  simp; ring

/-- **Finite Carleman inequality.** -/
theorem norm_det_one_add_mul_exp_neg_trace_le {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) :
    ‖(1 + X).det * Complex.exp (-X.trace)‖ ≤
      Real.exp ((1 / 2) * ∑ i, ∑ j, ‖X i j‖ ^ 2) := by
  have hcol : ∀ j : I, Real.sqrt (∑ i, ‖(1 + X) i j‖ ^ 2) ≤
      Real.exp ((X j j).re + (1 / 2) * ∑ i, ‖X i j‖ ^ 2) := by
    intro j
    rw [sum_norm_sq_one_add_col, Real.sqrt_le_iff]
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [sq, ← Real.exp_add]
    have := Real.add_one_le_exp (2 * (X j j).re + ∑ i, ‖X i j‖ ^ 2)
    refine le_trans (by linarith) (le_of_eq ?_)
    congr 1; ring
  have h1 : ‖(1 + X).det‖ ≤ ∏ j : I, Real.exp ((X j j).re + (1 / 2) * ∑ i, ‖X i j‖ ^ 2) :=
    (norm_det_le_prod_col (1 + X)).trans
      (Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _) fun j _ => hcol j)
  rw [← Real.exp_sum] at h1
  have h2 : ‖Complex.exp (-X.trace)‖ = Real.exp (-(∑ j, (X j j).re)) := by
    rw [Complex.norm_exp]
    simp [Matrix.trace, Complex.re_sum]
  rw [norm_mul, h2]
  calc ‖(1 + X).det‖ * Real.exp (-(∑ j, (X j j).re))
      ≤ Real.exp (∑ j : I, ((X j j).re + (1 / 2) * ∑ i, ‖X i j‖ ^ 2)) *
          Real.exp (-(∑ j, (X j j).re)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((1 / 2) * ∑ i, ∑ j, ‖X i j‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
        ring

end Carleman

end NlsGge.Analysis.RegularizedDeterminant
