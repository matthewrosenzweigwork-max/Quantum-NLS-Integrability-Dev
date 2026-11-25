import Mathlib
import NlsGge.Composition.TaylorModel

/-!
# R-092: Taylor coefficient A_w bounds with a common decay constant

Source head: Pro round 6 (commit c5547100), section 10G, R-092
`taylorFun_memAw_common_bound` (binding index entry R-092).

The proof follows the house proof of `NlsGge.Composition.taylorFun_memAw`
(`NlsGge/Composition/TaylorModel.lean:34-49`): the decay exponent `s` is the one
produced by `taylorCoeff_fourier_decay`, and `D` is the square root of the
summable series for that `s`.  The head exports this proof data.  No analytic
hypothesis is added.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal Topology
open NlsGge.Composition

namespace NlsGge.ThirdConsultation.R

theorem taylorFun_memAw_common_bound
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (w : ℤ → ℝ) (hw : AdmissibleWeight w)
    (F : X → Y) (K : Set X) (δ ρ M : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hdata : ∀ y ∈ Metric.thickening δ K,
      ∃ p : FormalMultilinearSeries ℝ X Y,
        HasFPowerSeriesOnBall F p y (ENNReal.ofReal ρ) ∧
        ∀ j : ℕ, ‖p j‖ ≤ M * ρ⁻¹ ^ j)
    (S : Finset ℤ) (v : ℤ → X)
    (hcurve : ∀ θ : AddCircle (1 : ℝ),
      (∑ n ∈ S, fourier n θ • v n) ∈ Metric.thickening δ K) :
    ∃ s₀ D : ℝ,
      0 < s₀ ∧ 0 ≤ D ∧
      Summable (fun n : ℤ =>
        w n ^ 2 * Real.exp (-(2 * Real.pi * s₀) * |(n : ℝ)|)) ∧
      D ^ 2 = ∑' n : ℤ,
        w n ^ 2 * Real.exp (-(2 * Real.pi * s₀) * |(n : ℝ)|) ∧
      ∀ k : ℕ,
        MemAw w (NlsGge.Composition.taylorFun F S v k) ∧
        awNorm w (NlsGge.Composition.taylorFun F S v k) ≤
          2 * M * (2 / ρ) ^ k * D := by
  obtain ⟨s, hs, hdec⟩ := taylorCoeff_fourier_decay hδ hρ hM hdata S v hcurve
  have hc : 0 < 2 * Real.pi * s := by positivity
  have hsum := hw.exp_decay (2 * Real.pi * s) hc
  set D : ℝ := Real.sqrt (∑' n : ℤ, w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) with hD
  have hD2 : D ^ 2 = ∑' n : ℤ, w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|) :=
    Real.sq_sqrt (tsum_nonneg fun n => by positivity)
  refine ⟨s, D, hs, Real.sqrt_nonneg _, hsum, hD2, fun k => ?_⟩
  set c : ℝ := 2 * M * (2 / ρ) ^ k with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ n : ℤ, (w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖) ^ 2 ≤
      c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) := by
    intro n
    have h1 := hdec k n
    have hwn := (hw.pos n).le
    have h2 : w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖ ≤
        w n * (c * Real.exp (-(Real.pi * s) * |(n : ℝ)|)) := by
      gcongr; exact h1
    have h0 : 0 ≤ w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖ := by positivity
    calc (w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖) ^ 2
        ≤ (w n * (c * Real.exp (-(Real.pi * s) * |(n : ℝ)|))) ^ 2 := by gcongr
      _ = c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hS : Summable fun n : ℤ =>
      (w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpt (hsum.mul_left _)
  refine ⟨⟨taylorCoeff_continuous hdata S v hcurve k, hS⟩, ?_⟩
  unfold awNorm
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑' n, (w n * ‖fourierCoeff (NlsGge.Composition.taylorFun F S v k) n‖) ^ 2
      ≤ ∑' n : ℤ, c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) :=
        hS.tsum_le_tsum hpt (hsum.mul_left _)
    _ = (c * D) ^ 2 := by
        rw [tsum_mul_left, mul_pow (c) D, hD, Real.sq_sqrt (tsum_nonneg fun n => by positivity)]

end NlsGge.ThirdConsultation.R
