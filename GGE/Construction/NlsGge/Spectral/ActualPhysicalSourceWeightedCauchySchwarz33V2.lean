import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
import NlsGge.Spectral.FiniteExponentialTriangleMass32V1
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Concrete rough-source weighted interval Cauchy--Schwarz. The squared
kernel mass is at rate 4Y and the source mass has exactly the physical norm;
no assumed bound or half-line extension is introduced. -/
theorem actualPhysicalRawCover_weightedIntegral_norm_le33
    (u : PhysicalL2) (Y t : ℝ) (hY : 0 < Y)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..t,
      ‖naturalPhysicalCoverL2 u (s : SpectralCircle)‖ * Real.exp (-2 * Y * (t-s))) ≤
      Real.sqrt (‖u‖ ^ 2 / (4 * Y)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let g : ℝ → ℝ := fun s => Real.exp (-2 * Y * (t-s))
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hmeasure : ν ≤ volume.restrict (Set.Ioc (0 : ℝ) 1) :=
    Measure.restrict_mono_set volume hsub
  have hU : MemLp U 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    scalarParity_restrict_memLp 0
      ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩
  have hUnorm : MemLp (fun s => ‖U s‖) 2 ν := (hU.mono_measure hmeasure).norm
  have hgm : AEStronglyMeasurable g ν := by
    apply Continuous.aestronglyMeasurable
    dsimp [g]
    fun_prop
  have hgb : ∀ᵐ s ∂ν, ‖g s‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [g]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hY.le (sub_nonneg.mpr hs.2)]
  have hg : MemLp g 2 ν := MemLp.of_bound hgm 1 hgb
  have hgNorm (s : ℝ) : ‖g s‖ = Real.exp (-2 * Y * (t-s)) := by
    dsimp [g]
    rw [abs_of_pos (Real.exp_pos _)]
  have hgSquare (s : ℝ) : ‖g s‖ ^ 2 = Real.exp (-4 * Y * (t-s)) := by
    rw [hgNorm, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmass : (∫ s, ‖U s‖ ^ 2 ∂ν) ≤ ‖u‖ ^ 2 := by
    apply le_trans (integral_mono_measure hmeasure
      (Filter.Eventually.of_forall (fun s => sq_nonneg (‖U s‖)))
      (hU.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
    exact (actualPhysicalRawCover_unitIntegral_norm_sq32 u).le
  have hkernel : (∫ s, ‖g s‖ ^ 2 ∂ν) ≤ 1 / (4 * Y) := by
    have h := finitePastExponentialMass_le32 0 t (4*Y) (by positivity)
    rw [intervalIntegral.integral_of_le ht.1] at h
    simpa only [ν, hgSquare, neg_mul] using h
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hUnorm) (by simpa using hg)
  have hcs' : (∫ s, ‖U s‖ * Real.exp (-2 * Y * (t-s)) ∂ν) ≤
      Real.sqrt (∫ s, ‖U s‖ ^ 2 ∂ν) * Real.sqrt (∫ s, ‖g s‖ ^ 2 ∂ν) := by
    simpa only [norm_norm, hgNorm, Real.rpow_two, ← Real.sqrt_eq_rpow] using hcs
  rw [intervalIntegral.integral_of_le ht.1]
  change (∫ s, ‖U s‖ * Real.exp (-2 * Y * (t-s)) ∂ν) ≤ _
  calc
    _ ≤ Real.sqrt (∫ s, ‖U s‖ ^ 2 ∂ν) * Real.sqrt (∫ s, ‖g s‖ ^ 2 ∂ν) := hcs'
    _ ≤ Real.sqrt (‖u‖ ^ 2) * Real.sqrt (1 / (4 * Y)) :=
      mul_le_mul (Real.sqrt_le_sqrt hmass) (Real.sqrt_le_sqrt hkernel)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (‖u‖ ^ 2 / (4 * Y)) := by
      rw [← Real.sqrt_mul (sq_nonneg ‖u‖)]
      congr 1
      ring

end NlsGge.SpectralFoundations
end
