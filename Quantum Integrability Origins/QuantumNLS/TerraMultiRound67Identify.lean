import QuantumNLS.TerraMultiRound67SmoothNorms
import QuantumNLS.TerraMultiRound67SmoothDense
import QuantumNLS.TerraMultiRound66SmoothCorrection

/-! Identify the explicit H¹ correction with the REG-004 correction by smooth
    evaluation and density. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open QuantumNLS.ClassicalCharges QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound66SmoothCorrection
open QuantumNLS.TerraMultiRound67SmoothNorms QuantumNLS.TerraMultiRound67RealDensity
open QuantumNLS.TerraMultiRound67Correction QuantumNLS.TerraMultiRound67SmoothDense
namespace QuantumNLS.TerraMultiRound67Identify
variable {L : ℝ} [Fact (0 < L)]

theorem smooth_correction_eq (κ : ℝ) (hκ : 0 < κ) (u : Hk L 1)
    (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    correction κ u = Rfield (L := L) 2 (by omega) κ u := by
  let f := physRep L 1 (coordinates (L := L) 1 u)
  let A : ℝ → ℝ := fun x => ‖f x‖^2 * ‖deriv f x‖^2
  let B : ℝ → ℝ := fun x => ‖deriv (fun y => ‖f y‖^2) x‖^2
  let S : ℝ → ℝ := fun x => ‖f x‖^6
  have hA : Continuous A := by
    dsimp [A]
    exact (hf.smooth.continuous.norm.pow 2).mul ((contDiff_infty_iff_deriv.mp hf.smooth).2.continuous.norm.pow 2)
  have hB : Continuous B := by
    dsimp [B]
    exact ((contDiff_infty_iff_deriv.mp (hf.smooth.norm_sq (𝕜 := ℂ))).2.continuous.norm.pow 2)
  have hquart : (∫ x in (0 : ℝ)..L,
      6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
      (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2) =
      ((6 * (∫ x in (0 : ℝ)..L, A x) + ∫ x in (0 : ℝ)..L, B x : ℝ) : ℂ) := by
    calc
      _ = ∫ x in (0 : ℝ)..L, 6 * ((A x : ℝ) : ℂ) + ((B x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only [A, B]
        exact congrArg (fun z : ℂ => 6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) + z)
          (density_embedded_deriv_sq ((contDiff_infty_iff_deriv.mp hf.smooth).1 x))
      _ = _ := by
        have hAc : IntervalIntegrable (fun x => ((A x : ℝ) : ℂ)) volume 0 L := by
          change IntervalIntegrable (Complex.ofReal ∘ A) volume 0 L
          exact (Complex.continuous_ofReal.comp hA).intervalIntegrable 0 L
        have hBc : IntervalIntegrable (fun x => ((B x : ℝ) : ℂ)) volume 0 L := by
          change IntervalIntegrable (Complex.ofReal ∘ B) volume 0 L
          exact (Complex.continuous_ofReal.comp hB).intervalIntegrable 0 L
        rw [intervalIntegral.integral_add (hAc.const_mul 6) hBc,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
          intervalIntegral.integral_ofReal]
        push_cast
        ring
  have hs := smooth_Rfield_correction L κ hκ u f rfl hf
  rw [hquart, intervalIntegral.integral_ofReal] at hs
  unfold correction
  rw [smooth_weighted_norm u hf, smooth_density_norm u hf, smooth_sextic u hf]
  apply Complex.ofReal_injective
  push_cast
  push_cast at hs
  simpa only [A, B, S, f] using hs.symm

theorem correction_eq_Rfield (κ : ℝ) (hκ : 0 < κ) :
    correction (L := L) κ = Rfield (L := L) 2 (by omega) κ := by
  apply continuous_candidate_eq_Rfield κ hκ (correction κ) (continuous_correction κ)
  intro u hu
  exact smooth_correction_eq κ hκ u hu

#print axioms smooth_correction_eq
#print axioms correction_eq_Rfield
end QuantumNLS.TerraMultiRound67Identify
