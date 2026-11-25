import NlsGge.GK38.EigenvalueCompactnessState

/-! # S7: real initial eigenvectors from conjugate-symmetric matrices

The anti-linear involution is realized explicitly; no direction selection is continuous.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def realInvolution38 (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![star (v 1), star (v 0)]

theorem realInvolution_mulVec38 (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : star (M 0 0) = M 1 1) (h1 : star (M 0 1) = M 1 0) (v : Fin 2 → ℂ) :
    M.mulVec (realInvolution38 v) = realInvolution38 (M.mulVec v) := by
  have h2 : star (M 1 1) = M 0 0 := by rw [← h0, star_star]
  have h3 : star (M 1 0) = M 0 1 := by rw [← h1, star_star]
  ext i
  fin_cases i <;> simp [realInvolution38, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1, h2, h3] <;> ring

theorem real_matrix_eigenvector38 (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : star (M 0 0) = M 1 1) (h1 : star (M 0 1) = M 1 0) (σ : ℝ)
    (he : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = (σ : ℂ) • v) :
    ∃ a : ℂ, a ≠ 0 ∧ M.mulVec (realInitial38 a) = (σ : ℂ) • realInitial38 a := by
  obtain ⟨v, hv, he⟩ := he
  have hj : M.mulVec (realInvolution38 v) = (σ : ℂ) • realInvolution38 v := by
    rw [realInvolution_mulVec38 M h0 h1, he]
    ext i
    fin_cases i <;> simp [realInvolution38, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm]
  let b := v 0 + star (v 1)
  have hw : realInitial38 b = v + realInvolution38 v := by
    ext i
    fin_cases i <;> simp [realInitial38, realInvolution38, b, star_add, add_comm]
  by_cases hb : b ≠ 0
  · refine ⟨b, hb, ?_⟩
    rw [hw, Matrix.mulVec_add, he, hj, smul_add]
  · have hb' : v 0 + star (v 1) = 0 := by simpa only [b] using not_ne_iff.mp hb
    have hv0 : v 0 ≠ 0 := by
      intro hz
      have hv1 : v 1 = 0 := star_eq_zero.mp (by simpa only [hz, zero_add] using hb')
      exact hv (by ext i; fin_cases i <;> simp [hz, hv1])
    have hv1 : v 1 = -star (v 0) := by
      have hh := congrArg star hb'
      simp only [star_add, star_star, star_zero] at hh
      linear_combination hh
    have hi : realInitial38 (Complex.I * v 0) = Complex.I • v := by
      ext i
      fin_cases i <;> simp [realInitial38, Pi.smul_apply, smul_eq_mul, star_mul, hv1] <;> ring
    refine ⟨Complex.I * v 0, mul_ne_zero Complex.I_ne_zero hv0, ?_⟩
    rw [hi, Matrix.mulVec_smul, he, smul_smul, smul_smul]
    congr 1
    ring

theorem real_matrix_unit_eigenvector38 (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : star (M 0 0) = M 1 1) (h1 : star (M 0 1) = M 1 0) (σ : ℝ)
    (he : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = (σ : ℂ) • v) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ M.mulVec (realInitial38 a) = (σ : ℂ) • realInitial38 a := by
  obtain ⟨b, hb, he⟩ := real_matrix_eigenvector38 M h0 h1 σ he
  have hshape : realInitial38 (b / (‖b‖ : ℂ)) = (‖b‖ : ℂ)⁻¹ • realInitial38 b := by
    ext i
    fin_cases i <;> simp [realInitial38, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  refine ⟨b / (‖b‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hb)
  · rw [hshape, Matrix.mulVec_smul, he, smul_smul, smul_smul]
    congr 1
    ring

end
end NlsGge.GK38
