import NlsGge.Analysis.RegularizedDeterminant.Det2Product

/-!
G5: interface of the infinite-dimensional `det2` with the finite real determinant/trace algebra.
In a finite-dimensional real Hilbert space, `det2 B = det (I+B) exp (-tr B)` and
`pairTrace B C = tr (B C)`; the finite Gaussian trace cancellation identity is then stated for
`det2`.  A regression shows `det2` is signed and not identically `1`.
-/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem finiteRank_of_finiteDimensional [FiniteDimensional ℝ H] (T : HilbertSchmidt H H) :
    HasFiniteRank (toCLM T) := by
  unfold HasFiniteRank; infer_instance

theorem range_le_top' (B : H →ₗ[ℝ] H) : LinearMap.range B ≤ (⊤ : Submodule ℝ H) := le_top

theorem restrictedEnd_top_conj (B : H →ₗ[ℝ] H) :
    (Submodule.topEquiv : (⊤ : Submodule ℝ H) ≃ₗ[ℝ] H).toLinearMap.comp
      ((restrictedEnd B ⊤ (range_le_top' B)).comp
        (Submodule.topEquiv : (⊤ : Submodule ℝ H) ≃ₗ[ℝ] H).symm.toLinearMap) = B := by
  ext x; rfl

/-- In finite dimension `det2` is the plain finite regularized determinant of the operator. -/
theorem det2_eq_finiteDet2 [FiniteDimensional ℝ H] (B : HilbertSchmidt H H) :
    det2 B = finiteDet2 (toCLM B).toLinearMap := by
  rw [det2_of_finiteRank B (finiteRank_of_finiteDimensional B),
    finiteRankDet2_eq_restriction (toCLM B).toLinearMap (finiteRank_of_finiteDimensional B) ⊤
      (range_le_top' _)]
  conv_rhs => rw [← restrictedEnd_top_conj (toCLM B).toLinearMap]
  exact (finiteDet2_conjugate _ _).symm

/-- Explicitly: `det2 B = det (I + B) · exp (-tr B)` in finite dimension. -/
theorem det2_eq_det_mul_exp [FiniteDimensional ℝ H] (B : HilbertSchmidt H H) :
    det2 B = LinearMap.det (1 + (toCLM B).toLinearMap) *
      Real.exp (-(LinearMap.trace ℝ H (toCLM B).toLinearMap)) := by
  rw [det2_eq_finiteDet2]; rfl

/-- In finite dimension the HS pairing is the ordinary trace of the product. -/
theorem pairTrace_eq_trace [FiniteDimensional ℝ H] (B C : HilbertSchmidt H H) :
    pairTrace B C = LinearMap.trace ℝ H ((toCLM B).toLinearMap * (toCLM C).toLinearMap) := by
  rw [pairTrace_eq_trace_restrict B C ⊤ (range_le_top' _) (range_le_top' _)]
  let e : (⊤ : Submodule ℝ H) ≃ₗ[ℝ] H := Submodule.topEquiv
  have h : (toCLM B).toLinearMap * (toCLM C).toLinearMap =
      e.toLinearMap.comp ((restrictedEnd (toCLM B).toLinearMap ⊤ (range_le_top' _) *
        restrictedEnd (toCLM C).toLinearMap ⊤ (range_le_top' _)).comp e.symm.toLinearMap) := by
    ext x; rfl
  rw [h, LinearMap.trace_comp_comm']
  congr 1

/-- Finite real Gaussian trace cancellation, stated for `det2`. -/
theorem det2_trace_cancellation [FiniteDimensional ℝ H] (B : HilbertSchmidt H H) (x k : H) :
    |det2 B| * Real.exp (-(inner ℝ x k - LinearMap.trace ℝ H (toCLM B).toLinearMap) -
        ‖k‖ ^ 2 / 2) =
      |LinearMap.det (1 + (toCLM B).toLinearMap)| * Real.exp (-(‖x + k‖ ^ 2 - ‖x‖ ^ 2) / 2) := by
  rw [det2_eq_finiteDet2]
  exact finiteDet2_trace_cancellation _ x k

/-- Regression: on `ℝ`, `det₂(I + (-2)·I) = -e²`; the HS determinant is signed and not `1`. -/
theorem det2_negative_example :
    det2 (ofCLM ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (isHilbertSchmidt_of_finiteDomain _)) = -Real.exp 2 := by
  rw [det2_eq_finiteDet2, toCLM_ofCLM]
  have : (((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
      (-2 : ℝ) • (1 : ℝ →ₗ[ℝ] ℝ) := by ext; simp
  rw [this]
  exact finiteDet2_negative_example

end NlsGge.Analysis.RegularizedDeterminant
