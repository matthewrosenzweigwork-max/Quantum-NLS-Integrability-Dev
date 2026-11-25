import NlsGge.Spectral.ActualRoughZsDysonFiniteTermEntireV2
import NlsGge.Spectral.ActualPhysicalL2ZsDysonUniformEntrySummabilityV1
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual rough L¹ majorant is uniform on each bounded spectral disk.
No continuous or bounded potential representative is required. -/
theorem actualPhysicalL2ZsCumulativeMajorant_le_radius
    (u : PhysicalL2) (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    actualPhysicalL2ZsCumulativeMajorant u z 2 ≤
      actualPhysicalL2ZsCumulativeMajorant u (R : ℂ) 2 := by
  unfold actualPhysicalL2ZsCumulativeMajorant CumulativePowerV3.actualCumulativeRealIntegral
  apply intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 2)
    (actualPhysicalL2ZsMajorant_intervalIntegrable u z)
    (actualPhysicalL2ZsMajorant_intervalIntegrable u (R : ℂ))
  intro s
  simp only [actualPhysicalL2ZsMajorant, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hR]
  exact add_le_add hz le_rfl

/-- Actual rough physical fields have locally uniform summable bounds for
the genuine Dyson series in the spectral parameter. -/
theorem differentiableOn_actualPhysicalL2ZsDysonTsum_on_ball
    (u : PhysicalL2) (R : ℝ) (hR : 0 ≤ R)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∑' n : ℕ, actualComplexZsDysonTerm
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z n t i j) (Metric.ball 0 R) := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  let majorant : ℕ → ℝ := fun n =>
    (2 * actualPhysicalL2ZsCumulativeMajorant u (R : ℂ) 2) ^ n / (n.factorial : ℝ)
  have hsum : Summable majorant :=
    (NormedSpace.expSeries_div_hasSum_exp
      (2 * actualPhysicalL2ZsCumulativeMajorant u (R : ℂ) 2)).summable
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro n z hz
    have hA (a b : Fin 2) : IntervalIntegrable
        (fun s => zsCoefficientComplex U 0 s a b) volume 0 2 :=
      actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u 0 a b
    exact (analyticOnNhd_actualComplexZsDysonTerm_of_L1
      U hA n t ht i j z (Set.mem_univ z)).differentiableAt.differentiableWithinAt
  · exact Metric.isOpen_ball
  · intro n z hz
    have hz' : ‖z‖ ≤ R := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hz).le
    have hq := actualPhysicalL2ZsCumulativeMajorant_le_radius u z R hR hz'
    have hq0 := actualPhysicalL2ZsCumulativeMajorant_nonneg u z 2 (by norm_num)
    calc
      ‖actualComplexZsDysonTerm U z n t i j‖ ≤
          (2 * actualPhysicalL2ZsCumulativeMajorant u z 2) ^ n / (n.factorial : ℝ) :=
        actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n t ht i j
      _ ≤ majorant n := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hq0)
          (mul_le_mul_of_nonneg_left hq (by norm_num)) n

/-- Entire spectral-parameter dependence of the actual fundamental Dyson
matrix for EVERY physical L² potential, on the true doubled interval. -/
theorem analyticOnNhd_actualPhysicalL2ZsDysonTsum
    (u : PhysicalL2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => actualComplexZsDysonTsum
        (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
        z t i j) Set.univ := by
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [R]
    simp
  have hd := differentiableOn_actualPhysicalL2ZsDysonTsum_on_ball u R hR.le t ht i j
  simpa only [actualComplexZsDysonTsum] using!
    hd.analyticAt (Metric.isOpen_ball.mem_nhds hzball)

end NlsGge.SpectralFoundations
end
