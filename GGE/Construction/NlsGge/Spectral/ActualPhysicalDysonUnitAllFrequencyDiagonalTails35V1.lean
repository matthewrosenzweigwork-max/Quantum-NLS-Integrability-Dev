import NlsGge.Spectral.ComplexEvenSeriesGeometricTail34V1
import NlsGge.Spectral.ActualPhysicalDyson00AllFrequencyEveryOrderBound35V1
import NlsGge.Spectral.ActualPhysicalDyson11AllFrequencyEveryOrderBound35V1
import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Actual 00 endpoint tail at every real frequency with a frequency-independent bound, after summability and parity identification of
the actual interaction series. The smallness hypothesis is on the explicit
coefficient; it will be realized eventually in the subsequent limit theorem. -/
theorem actualPhysicalDysonUnit00_allFrequency_tail35
    (u : PhysicalL2) (x Y : ℝ) (hY : 0 < Y)
    (hsmall : ‖u‖*Real.sqrt (‖u‖^2/(4*Y)) < 1) :
    ‖actualZsInteractionState32 ((x : ℂ)+Complex.I*(Y : ℂ))
        (actualComplexZsDysonTsum
          (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
          ((x : ℂ)+Complex.I*(Y : ℂ))) 1 0 0 - 1‖ ≤
      (‖u‖*Real.sqrt (‖u‖^2/(4*Y))) /
        (1-‖u‖*Real.sqrt (‖u‖^2/(4*Y))) := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let B := actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))
  let f : ℕ → ℂ := fun k => genericRoughMatrixDysonTerm32 B k 1 0 0
  let A : ℝ := ‖u‖*Real.sqrt (‖u‖^2/(4*Y))
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have ho (k : ℕ) : f (2*k+1) = 0 :=
    (actualInteractionDyson_odd_diagonal_zero32 U ((x : ℂ)+Complex.I*(Y : ℂ)) k 1).1
  have hb (k : ℕ) : ‖f (2*k)‖ ≤ A^k :=
    actualPhysicalDyson00_allFrequency_everyOrder_bound35 u x Y hY k 1 (by norm_num)
  have ht := complexEvenSeriesGeometricTail_bound34 f A hA hsmall ho hb
  have hz : f 0 = 1 := by simp [f, genericRoughMatrixDysonTerm32]
  rw [actualPhysicalInteractionState_unit_eq_Dyson32 u ((x : ℂ)+Complex.I*(Y : ℂ))]
  change ‖(∑' k : ℕ, f k)-1‖ ≤ A/(1-A)
  simpa only [hz] using ht.2

/-- Actual scaled 11 endpoint tail at every real frequency with a frequency-independent bound, whose zeroth term is exp(-2Y). The
weighted series is proved summable before scalar multiplication is moved
through its sum. This does not assert that the complex trace is real. -/
theorem actualPhysicalDysonUnitScaled11_allFrequency_tail35
    (u : PhysicalL2) (x Y : ℝ) (hY : 0 < Y)
    (hsmall : ‖u‖*Real.sqrt (‖u‖^2/(4*Y)) < 1) :
    ‖(Real.exp (-2*Y) : ℂ)*actualZsInteractionState32 ((x : ℂ)+Complex.I*(Y : ℂ))
        (actualComplexZsDysonTsum
          (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
          ((x : ℂ)+Complex.I*(Y : ℂ))) 1 1 1 - (Real.exp (-2*Y) : ℂ)‖ ≤
      (‖u‖*Real.sqrt (‖u‖^2/(4*Y))) /
        (1-‖u‖*Real.sqrt (‖u‖^2/(4*Y))) := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let B := actualZsInteractionCoefficient32 U ((x : ℂ)+Complex.I*(Y : ℂ))
  let c : ℂ := (Real.exp (-2*Y) : ℂ)
  let f : ℕ → ℂ := fun k => genericRoughMatrixDysonTerm32 B k 1 1 1
  let g : ℕ → ℂ := fun k => c*f k
  let A : ℝ := ‖u‖*Real.sqrt (‖u‖^2/(4*Y))
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have ho (k : ℕ) : g (2*k+1) = 0 := by
    dsimp only [g, f]
    rw [(actualInteractionDyson_odd_diagonal_zero32 U ((x : ℂ)+Complex.I*(Y : ℂ)) k 1).2,
      mul_zero]
  have hb (k : ℕ) : ‖g (2*k)‖ ≤ A^k := by
    simpa only [mul_one] using
      actualPhysicalDyson11_allFrequency_everyOrder_bound35 u x Y hY k 1 (by norm_num)
  have ht := complexEvenSeriesGeometricTail_bound34 g A hA hsmall ho hb
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hf : Summable f := by
    have hs := ht.1.mul_left c⁻¹
    convert hs using 1
    funext k
    dsimp only [g]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hz : g 0 = c := by simp [g, f, genericRoughMatrixDysonTerm32]
  have heq : (∑' k : ℕ, g k) = c*(∑' k : ℕ, f k) := hf.tsum_mul_left c
  rw [actualPhysicalInteractionState_unit_eq_Dyson32 u ((x : ℂ)+Complex.I*(Y : ℂ))]
  change ‖c*(∑' k : ℕ, f k)-c‖ ≤ A/(1-A)
  simpa only [hz, heq] using ht.2

end NlsGge.SpectralFoundations
end
