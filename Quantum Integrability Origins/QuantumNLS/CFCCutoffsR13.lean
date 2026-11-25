import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Tactic

/-! Continuous cutoffs of the bounded inverse, with exact plateaus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology
open scoped InnerProductSpace ComplexOrder
namespace QuantumNLS.CFCCutoffsR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def cut (n : ℕ) (t : ℝ) : ℝ := min 1 (max 0 (2*((n : ℝ)+1)*t-1))

theorem cut_continuous (n : ℕ) : Continuous (cut n) := by unfold cut; fun_prop

theorem cut_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cut n t :=
  le_min zero_le_one (le_max_left _ _)

theorem cut_le_one (n : ℕ) (t : ℝ) : cut n t ≤ 1 := min_le_left _ _

theorem cut_zero (n : ℕ) {t : ℝ} (ht : t ≤ 1/(2*((n : ℝ)+1))) : cut n t = 0 := by
  have hn : 0 < 2*((n : ℝ)+1) := by positivity
  have hh := (le_div_iff₀ hn).mp ht
  unfold cut
  rw [max_eq_left (by nlinarith : 2*((n : ℝ)+1)*t-1 ≤ 0)]
  norm_num

theorem cut_one (n : ℕ) {t : ℝ} (ht : 1/((n : ℝ)+1) ≤ t) : cut n t = 1 := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hh := (div_le_iff₀ hn).mp ht
  unfold cut
  apply min_eq_left
  exact (by nlinarith : 1 ≤ 2*((n : ℝ)+1)*t-1).trans (le_max_right _ _)

theorem cut_monotone {n m : ℕ} (hnm : n ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    cut n t ≤ cut m t := by
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  have hc : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  nlinarith

theorem residual_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(1-cut n t)*t| ≤ 1/((n : ℝ)+1) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (cut_le_one n t)) ht)]
  by_cases hh : 1/((n : ℝ)+1) ≤ t
  · rw [cut_one n hh]; simp; positivity
  · have hlt := le_of_not_ge hh
    have h0 := cut_nonneg n t
    nlinarith

/-- Denominator stays away from zero, so this root cutoff is continuous. -/
def rootCut (n : ℕ) (t : ℝ) : ℝ := cut n t / Real.sqrt (max t (1/(2*((n : ℝ)+1))))

theorem rootCut_continuous (n : ℕ) : Continuous (rootCut n) := by
  unfold rootCut
  apply (cut_continuous n).div (by fun_prop)
  intro t
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  exact (by positivity : 0 < 1/(2*((n : ℝ)+1))).trans_le (le_max_right _ _)

theorem rootCut_mul_sqrt (n : ℕ) {t : ℝ} (_ht : 0 ≤ t) :
    rootCut n t * Real.sqrt t = cut n t := by
  by_cases hh : t ≤ 1/(2*((n : ℝ)+1))
  · simp [rootCut,cut_zero n hh]
  · have hl := lt_of_not_ge hh
    have hp : 0 < t := (by positivity : 0 < 1/(2*((n : ℝ)+1))).trans hl
    simp only [rootCut,max_eq_left hl.le]
    exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr hp))

def cutoff (R : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E := cfc (cut n) R

def rootCutoff (R : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E := cfc (rootCut n) R

theorem cutoff_nonneg (R : E →L[ℂ] E) (n : ℕ) : 0 ≤ cutoff R n :=
  cfc_nonneg (fun t _ => cut_nonneg n t)

theorem cutoff_le_one (R : E →L[ℂ] E) (n : ℕ) : cutoff R n ≤ 1 :=
  cfc_le_one _ _ (fun t _ => cut_le_one n t)

theorem cutoff_norm (R : E →L[ℂ] E) (n : ℕ) : ‖cutoff R n‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (cutoff_nonneg R n)).mpr (cutoff_le_one R n)

theorem cutoff_symmetric (R : E →L[ℂ] E) (n : ℕ) : (cutoff R n).adjoint = cutoff R n :=
  (cutoff_nonneg R n).isSelfAdjoint

theorem root_factor (R : E →L[ℂ] E) (hR : 0 ≤ R) (n : ℕ) :
    rootCutoff R n * CFC.sqrt R = cutoff R n := by
  have hs : IsSelfAdjoint R := hR.isSelfAdjoint
  have he : CFC.sqrt R = cfc Real.sqrt R := by
    rw [CFC.sqrt_eq_real_sqrt R hR,cfcₙ_eq_cfc (hf0 := by simp)]
  rw [rootCutoff,he,← cfc_mul (rootCut n) Real.sqrt R
    (rootCut_continuous n).continuousOn Real.continuous_sqrt.continuousOn]
  exact cfc_congr (fun t ht => rootCut_mul_sqrt n (spectrum_nonneg_of_nonneg hR ht))

theorem root_factor' (R : E →L[ℂ] E) (hR : 0 ≤ R) (n : ℕ) :
    CFC.sqrt R * rootCutoff R n = cutoff R n := by
  have hs : IsSelfAdjoint R := hR.isSelfAdjoint
  have he : CFC.sqrt R = cfc Real.sqrt R := by
    rw [CFC.sqrt_eq_real_sqrt R hR,cfcₙ_eq_cfc (hf0 := by simp)]
  rw [he,rootCutoff,(cfc_commute_cfc Real.sqrt (rootCut n) R).eq]
  simpa only [rootCutoff,he] using root_factor R hR n

theorem residual_norm (R : E →L[ℂ] E) (hR : 0 ≤ R) (n : ℕ) :
    ‖(1-cutoff R n)*R‖ ≤ 1/((n : ℝ)+1) := by
  have hs : IsSelfAdjoint R := hR.isSelfAdjoint
  have he : (1-cutoff R n)*R = cfc (fun t => (1-cut n t)*t) R := by
    rw [cfc_mul (fun t => 1-cut n t) (fun t => t) R
      (continuous_const.sub (cut_continuous n)).continuousOn continuous_id.continuousOn]
    rw [cfc_sub (fun _ : ℝ => 1) (cut n) R continuous_const.continuousOn
      (cut_continuous n).continuousOn,cfc_const_one ℝ R (ha := hs),cfc_id' ℝ R (ha := hs)]
    rfl
  rw [he]
  apply norm_cfc_le (by positivity)
  intro t ht
  exact (Real.norm_eq_abs _).trans_le (residual_bound n (spectrum_nonneg_of_nonneg hR ht))

end QuantumNLS.CFCCutoffsR13
