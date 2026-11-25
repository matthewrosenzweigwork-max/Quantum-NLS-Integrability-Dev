import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual source potential has L1 norm at most its physical L2 norm on
period one. Both Holder premises and the exact source mass are realized. -/
theorem actualPhysicalRawCover_unitIntegral_norm_le33 (u : PhysicalL2) :
    Integrable (fun x : ℝ => ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    (∫ x in Set.Ioc (0 : ℝ) 1, ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖) ≤ ‖u‖ := by
  have hU : MemLp (fun x : ℝ => naturalPhysicalCoverL2 u (x : SpectralCircle)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    scalarParity_restrict_memLp 0
      ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩
  have hi : Integrable (fun x : ℝ => ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hU.norm
  have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hU) (by simpa using h1)
  have hmass : (∫ x in Set.Ioc (0 : ℝ) 1,
      ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖ ^ (2 : ℝ)) = ‖u‖ ^ 2 := by
    simpa only [Real.rpow_two] using actualPhysicalRawCover_unitIntegral_norm_sq32 u
  have hconstant : (∫ _x in Set.Ioc (0 : ℝ) 1, ‖(1 : ℂ)‖ ^ (2 : ℝ)) = 1 := by
    simp
  rw [hmass, hconstant] at h
  have hsqrt : (‖u‖ ^ 2) ^ (1 / (2 : ℝ)) = ‖u‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg u)]
  refine ⟨hi, ?_⟩
  simpa only [norm_one, mul_one, Real.one_rpow, hsqrt] using h

/-- Every actual subinterval inner potential norm has the same source bound.
No continuity of the rough source representative is assumed. -/
theorem actualPhysicalRawCover_subintervalIntegral_norm_le33
    (u : PhysicalL2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..t, ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖) ≤ ‖u‖ := by
  rw [intervalIntegral.integral_of_le ht.1]
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  apply le_trans (integral_mono_measure (Measure.restrict_mono_set volume hsub)
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))
    (actualPhysicalRawCover_unitIntegral_norm_le33 u).1)
  exact (actualPhysicalRawCover_unitIntegral_norm_le33 u).2

end NlsGge.SpectralFoundations
end
