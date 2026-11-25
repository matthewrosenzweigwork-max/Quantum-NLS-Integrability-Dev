import NlsGge.Spectral.ActualPhysicalL2ZsACFundamentalWellPosedV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual rough source fundamental solution applied to an initial vector. -/
def actualPhysicalFloquetState33 (u : PhysicalL2) (z : ℂ)
    (v : Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ :=
  (actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t).mulVec v

/-- Nonzero initial data give strictly positive energy integral along the
actual rough source flow. Continuity and the initial value are realized,
not supplied as additional source hypotheses. -/
theorem actualPhysicalFloquet_energy_integral_pos33
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    0 < ∫ t in (0 : ℝ)..1,
      (‖actualPhysicalFloquetState33 u z v t 0‖ ^ 2 +
        ‖actualPhysicalFloquetState33 u z v t 1‖ ^ 2) := by
  let F := actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z
  obtain ⟨hinit, hAC, _⟩ := actualPhysicalL2ZsDysonTsum_is_AC_fundamental u z
  have hentry (i j : Fin 2) : ContinuousOn (fun t => F t i j) (Set.Icc (0 : ℝ) 1) := by
    have h := (hAC i j).continuousOn
    apply h.mono
    intro t ht
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hstate (i : Fin 2) : ContinuousOn
      (fun t => actualPhysicalFloquetState33 u z v t i) (Set.Icc (0 : ℝ) 1) := by
    simpa only [F, actualPhysicalFloquetState33, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.add_apply, Pi.mul_apply] using!
      ((hentry i 0).mul continuousOn_const).add ((hentry i 1).mul continuousOn_const)
  have hinitial : actualPhysicalFloquetState33 u z v 0 = v := by
    unfold actualPhysicalFloquetState33
    rw [hinit]
    simp
  have hnzero : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    fin_cases i <;> simp_all
  have henergy0 : 0 < ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rcases hnzero with h | h
    · have hp := norm_pos_iff.mpr h
      nlinarith [sq_nonneg ‖v 1‖]
    · have hp := norm_pos_iff.mpr h
      nlinarith [sq_nonneg ‖v 0‖]
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · exact ((hstate 0).norm.pow 2).add ((hstate 1).norm.pow 2)
  · intro t ht
    positivity
  · refine ⟨0, by norm_num, ?_⟩
    rw [hinitial]
    exact henergy0

end NlsGge.SpectralFoundations
end
