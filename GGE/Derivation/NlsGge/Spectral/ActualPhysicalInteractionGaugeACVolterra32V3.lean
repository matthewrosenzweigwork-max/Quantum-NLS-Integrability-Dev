import NlsGge.Spectral.ActualPhysicalInteractionGaugeAEODE32V2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem contDiff_actualZsInverseFreeWeight32 (z : ℂ) (i : Fin 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t => actualZsInverseFreeWeight32 z t i) := by
  have h : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun t : ℝ => t • (-actualZsFreeRate32 z i)) := contDiff_smul_const _
  exact h.cexp

/-- Removing the explicit smooth free diagonal preserves the actual rough
fundamental solution's absolute continuity on the FULL doubled interval. -/
theorem absolutelyContinuous_actualPhysicalInteractionState32
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun t => actualZsInteractionState32 z
        (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t i j) 0 2 := by
  have hcd : ContDiff ℝ 1 (fun t => actualZsInverseFreeWeight32 z t i) :=
    (contDiff_actualZsInverseFreeWeight32 z i).of_le (by simp)
  have hw : AbsolutelyContinuousOnInterval
      (fun t => actualZsInverseFreeWeight32 z t i) 0 2 :=
    hcd.contDiffOn.absolutelyContinuousOnInterval
  have hX := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z i j
  simpa only [actualZsInteractionState32, Pi.smul_apply, smul_eq_mul] using! hw.smul hX

/-- The actual gauged coefficient has integrable entries. Exponential ratios
are continuous and their denominator is everywhere nonzero. -/
theorem intervalIntegrable_actualPhysicalInteractionCoefficient32
    (u : PhysicalL2) (z : ℂ) (i k : Fin 2) :
    IntervalIntegrable
      (fun t => actualZsInteractionCoefficient32
        (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t i k) volume 0 2 := by
  by_cases hik : i = k
  · simpa [actualZsInteractionCoefficient32, hik] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 2)
  · have hw : ContinuousOn
        (fun t => actualZsInverseFreeWeight32 z t i / actualZsInverseFreeWeight32 z t k)
        (Set.uIcc (0 : ℝ) 2) :=
      (contDiff_actualZsInverseFreeWeight32 z i).continuous.continuousOn.div
        (contDiff_actualZsInverseFreeWeight32 z k).continuous.continuousOn
        (fun t _ => actualZsInverseFreeWeight_ne_zero32 z t k)
    have hA := actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k
    have hprod := hA.mul_continuousOn hw
    convert hprod using 1
    ext t
    simp only [actualZsInteractionCoefficient32, hik, ite_false,
      actualPhysicalL2ZsCoefficient]
    ring

theorem intervalIntegrable_actualPhysicalInteractionProduct32
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable
      (fun t => (actualZsInteractionCoefficient32
        (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *
        actualZsInteractionState32 z
          (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t) i j)
      volume 0 2 := by
  have hA (k : Fin 2) := intervalIntegrable_actualPhysicalInteractionCoefficient32 u z i k
  have hG (k : Fin 2) := (absolutelyContinuous_actualPhysicalInteractionState32 u z k j).continuousOn
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using
    ((hA 0).mul_continuousOn (hG 0)).add ((hA 1).mul_continuousOn (hG 1))

theorem actualPhysicalInteractionState_initial32 (u : PhysicalL2) (z : ℂ) :
    actualZsInteractionState32 z
      (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) 0 = 1 := by
  ext i j
  simp only [actualZsInteractionState32, actualZsInverseFreeWeight32, zero_smul,
    Complex.exp_zero, one_mul]
  exact actualPhysicalL2ZsDysonTsum_initial_entry u z i j

/-- The concrete rough interaction state satisfies its genuine Volterra equation.
It has not yet been identified with an interaction Dyson series, and the source
high-energy quasimomentum normalization remains an additional obligation. -/
theorem actualPhysicalInteractionState_integral_equation32
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 2) (i j : Fin 2) :
    actualZsInteractionState32 z
      (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t i j =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t,
          (actualZsInteractionCoefficient32 (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z s *
            actualZsInteractionState32 z
              (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) s) i j := by
  have h := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    (absolutelyContinuous_actualPhysicalInteractionState32 u z i j)
    (intervalIntegrable_actualPhysicalInteractionProduct32 u z i j)
    (actualPhysicalZsInteractionState_ae_hasDerivAt32 u z i j) t ht
  rw [actualPhysicalInteractionState_initial32 u z] at h
  exact h

end NlsGge.SpectralFoundations
end
