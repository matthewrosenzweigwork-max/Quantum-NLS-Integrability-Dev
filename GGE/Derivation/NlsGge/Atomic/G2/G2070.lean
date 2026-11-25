import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace NlsGge.Atomic.G2

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A norm-controlled perturbation of a Banach-space equivalence has a two-sided
continuous-linear inverse with the usual factor-two bound. -/
theorem inverse_perturbation_half (Q : E ≃L[𝕜] E) (δQ : E →L[𝕜] E)
    (h : ‖Q.symm.toContinuousLinearMap‖ * ‖δQ‖ ≤ 1 / 2) :
    ∃ R : E →L[𝕜] E,
      R * (Q.toContinuousLinearMap + δQ) = 1 ∧
      (Q.toContinuousLinearMap + δQ) * R = 1 ∧
      ‖R‖ ≤ 2 * ‖Q.symm.toContinuousLinearMap‖ := by
  let A := E →L[𝕜] E
  let D : A := Q.symm.toContinuousLinearMap.comp δQ
  have hD : ‖D‖ ≤ 1 / 2 := by
    calc
      ‖D‖ = ‖Q.symm.toContinuousLinearMap.comp δQ‖ := rfl
      _ ≤ ‖Q.symm.toContinuousLinearMap‖ * ‖δQ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 / 2 := h
  have hDlt : ‖-D‖ < 1 := by rw [norm_neg]; linarith
  let u : Aˣ := Units.oneSub (-D) hDlt
  have hu : (u : A) = 1 + D := by simp [u, sub_neg_eq_add]
  have hfactor : Q.toContinuousLinearMap + δQ = Q.toContinuousLinearMap * (1 + D) := by
    ext x
    simp [D]
  have hsymmQ : Q.symm.toContinuousLinearMap * Q.toContinuousLinearMap = (1 : A) := by
    ext x
    simp
  have hQsymm : Q.toContinuousLinearMap * Q.symm.toContinuousLinearMap = (1 : A) := by
    ext x
    simp
  let R : A := (↑u⁻¹ : A) * Q.symm.toContinuousLinearMap
  have huLeft : (↑u⁻¹ : A) * (1 + D) = 1 := by
    rw [← hu]
    exact u.inv_mul
  have huRight : (1 + D) * (↑u⁻¹ : A) = 1 := by
    rw [← hu]
    exact u.mul_inv
  have hIdNorm : ‖(1 : A)‖ ≤ 1 := by
    exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by simp)
  have hInvNorm : ‖(↑u⁻¹ : A)‖ ≤ 2 := by
    have hgeom := tsum_geometric_le_of_norm_lt_one (-D) hDlt
    have hdenom : (1 / 2 : ℝ) ≤ 1 - ‖-D‖ := by rw [norm_neg]; linarith
    have hdenomPos : 0 < 1 - ‖-D‖ := lt_of_lt_of_le (by norm_num) hdenom
    have hinv : (1 - ‖-D‖)⁻¹ ≤ 2 := by
      calc
        (1 - ‖-D‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          (inv_le_inv₀ hdenomPos (by norm_num)).2 hdenom
        _ = 2 := by norm_num
    calc
      ‖(↑u⁻¹ : A)‖ = ‖∑' n : ℕ, (-D) ^ n‖ := by simp [u, Units.oneSub]
      _ ≤ ‖(1 : A)‖ - 1 + (1 - ‖-D‖)⁻¹ := hgeom
      _ ≤ 2 := by nlinarith [hIdNorm]
  refine ⟨R, ?_, ?_, ?_⟩
  · dsimp [R]
    rw [hfactor]
    calc
      (↑u⁻¹ : A) * Q.symm.toContinuousLinearMap *
          (Q.toContinuousLinearMap * (1 + D)) =
          (↑u⁻¹ : A) * ((Q.symm.toContinuousLinearMap * Q.toContinuousLinearMap) * (1 + D)) := by
            simp only [mul_assoc]
      _ = (↑u⁻¹ : A) * (1 + D) := by rw [hsymmQ, one_mul]
      _ = 1 := huLeft
  · dsimp [R]
    rw [hfactor]
    calc
      (Q.toContinuousLinearMap * (1 + D)) *
          ((↑u⁻¹ : A) * Q.symm.toContinuousLinearMap) =
          Q.toContinuousLinearMap * ((1 + D) * (↑u⁻¹ : A)) *
            Q.symm.toContinuousLinearMap := by simp only [mul_assoc]
      _ = Q.toContinuousLinearMap * (1 : A) * Q.symm.toContinuousLinearMap := by
        rw [huRight]
      _ = 1 := by simp [hQsymm]
  · dsimp [R]
    calc
      ‖(↑u⁻¹ : A) * Q.symm.toContinuousLinearMap‖ ≤
          ‖(↑u⁻¹ : A)‖ * ‖Q.symm.toContinuousLinearMap‖ := norm_mul_le _ _
      _ ≤ 2 * ‖Q.symm.toContinuousLinearMap‖ := by
        exact mul_le_mul_of_nonneg_right hInvNorm (norm_nonneg _)

/-- Reciprocal-radius form of `inverse_perturbation_half`, including the degenerate
zero-norm case without assuming that the Banach space is nontrivial. -/
theorem inverse_perturbation_half_reciprocal (Q : E ≃L[𝕜] E) (δQ : E →L[𝕜] E)
    (h : ‖δQ‖ ≤ 1 / (2 * ‖Q.symm.toContinuousLinearMap‖)) :
    ∃ R : E →L[𝕜] E,
      R * (Q.toContinuousLinearMap + δQ) = 1 ∧
      (Q.toContinuousLinearMap + δQ) * R = 1 ∧
      ‖R‖ ≤ 2 * ‖Q.symm.toContinuousLinearMap‖ := by
  have hprod : ‖Q.symm.toContinuousLinearMap‖ * ‖δQ‖ ≤ 1 / 2 := by
    by_cases hzero : ‖Q.symm.toContinuousLinearMap‖ = 0
    · simp [hzero]
    · have hnonneg : 0 ≤ ‖Q.symm.toContinuousLinearMap‖ := norm_nonneg _
      calc
        ‖Q.symm.toContinuousLinearMap‖ * ‖δQ‖ ≤ ‖Q.symm.toContinuousLinearMap‖ * (1 / (2 * ‖Q.symm.toContinuousLinearMap‖)) :=
          mul_le_mul_of_nonneg_left h hnonneg
        _ = 1 / 2 := by field_simp [hzero]
  exact inverse_perturbation_half Q δQ hprod

end NlsGge.Atomic.G2
