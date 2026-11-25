/- G4045 PRODUCTION01 (proof development kit; source proof development/G4045_PROOF01.lean.txt; target NlsGge/Atomic/G4/G4045.lean).
   slitRoot / slitPrimitive are NOT copied: they come from the landed host NlsGge.Atomic.G4.G4024 (import).
   elementarySlitIntegral is NOT copied here: it is hosted by G4-027 (NlsGge.Atomic.G4.G4027).
   Statement G4045 and NoWindingElementaryValue are verbatim from defs3 STATEMENTS/G4.md and DEFINITIONS/G4.lean.md. -/
import Mathlib
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.Atomic.G4.G4024

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Endpoint characterization of the two possible no-extra-winding values.
It permits either limiting value at the logarithm cut. -/
def NoWindingElementaryValue (γ τ μ ω : ℂ) : Prop :=
  γ ≠ 0 ∧
  Complex.exp ω = -(2 * (μ - τ) / γ) - slitRoot (2 * (μ - τ) / γ) ∧
  |ω.im| ≤ Real.pi


namespace G4045Aux

theorem slitRoot_sq (z : ℂ) : slitRoot z ^ 2 = z ^ 2 - 1 := by
  by_cases h0 : z = 0
  · simp [slitRoot, h0]
  · have h : (0 : ℂ) - z ≠ 0 := by simpa using h0
    have := stdRoot_sq_of_ne38 (τ := 0) (g2 := 4) (z := z) h
    simp only [slitRoot, if_neg h0]
    rw [this]
    ring

theorem wq (z : ℂ) : (-z - slitRoot z) * (-z + slitRoot z) = 1 := by
  linear_combination (-1 : ℂ) * slitRoot_sq z

theorem norm_slitRoot_le (z : ℂ) : ‖slitRoot z‖ ≤ ‖z‖ + 1 := by
  have h1 : ‖slitRoot z‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
    have e : ‖slitRoot z‖ ^ 2 = ‖z ^ 2 - 1‖ := by
      rw [← norm_pow, slitRoot_sq]
    rw [e]
    have h2 : ‖z ^ 2 - 1‖ ≤ ‖z ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    rw [norm_pow, norm_one] at h2
    nlinarith [norm_nonneg z]
  nlinarith [norm_nonneg (slitRoot z), norm_nonneg z, h1]

theorem logNorm_bound (z : ℂ) : |Real.log ‖-z - slitRoot z‖| ≤ Real.log (2 * ‖z‖ + 1) := by
  have hnw : ‖-z - slitRoot z‖ * ‖-z + slitRoot z‖ = 1 := by
    rw [← norm_mul, wq z, norm_one]
  have hw0 : 0 < ‖-z - slitRoot z‖ := by
    rcases (norm_nonneg (-z - slitRoot z)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hnw; exact absurd hnw zero_ne_one
  have hq0 : 0 < ‖-z + slitRoot z‖ := by
    rcases (norm_nonneg (-z + slitRoot z)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hnw; exact absurd hnw zero_ne_one
  have hA : ‖-z - slitRoot z‖ ≤ 2 * ‖z‖ + 1 := by
    have := norm_sub_le (-z) (slitRoot z)
    rw [norm_neg] at this
    linarith [norm_slitRoot_le z]
  have hB : ‖-z + slitRoot z‖ ≤ 2 * ‖z‖ + 1 := by
    have := norm_add_le (-z) (slitRoot z)
    rw [norm_neg] at this
    linarith [norm_slitRoot_le z]
  have hsum : Real.log ‖-z - slitRoot z‖ + Real.log ‖-z + slitRoot z‖ = 0 := by
    rw [← Real.log_mul hw0.ne' hq0.ne', hnw, Real.log_one]
  have hL1 : Real.log ‖-z - slitRoot z‖ ≤ Real.log (2 * ‖z‖ + 1) :=
    Real.log_le_log hw0 hA
  have hL2 : Real.log ‖-z + slitRoot z‖ ≤ Real.log (2 * ‖z‖ + 1) :=
    Real.log_le_log hq0 hB
  rw [abs_le]
  constructor <;> linarith

end G4045Aux

open G4045Aux in
theorem G4045 (γ τ μ ω : ℂ) (hω : NoWindingElementaryValue γ τ μ ω) :
    ‖ω‖ ≤ Real.pi + Real.log 2 + Real.log (1 + 2 * ‖μ - τ‖ / ‖γ‖) := by
  obtain ⟨hγ, hexp, him⟩ := hω
  have hnorm_z : ‖2 * (μ - τ) / γ‖ = 2 * ‖μ - τ‖ / ‖γ‖ := by
    rw [norm_div, norm_mul]
    norm_num
  have hre : ω.re = Real.log ‖-(2 * (μ - τ) / γ) - slitRoot (2 * (μ - τ) / γ)‖ := by
    have h1 : ‖Complex.exp ω‖ = ‖-(2 * (μ - τ) / γ) - slitRoot (2 * (μ - τ) / γ)‖ := by
      rw [hexp]
    rw [Complex.norm_exp] at h1
    rw [← h1, Real.log_exp]
  have hlogb := logNorm_bound (2 * (μ - τ) / γ)
  rw [hnorm_z] at hlogb
  have hsplit : ‖ω‖ ≤ |ω.re| + |ω.im| := Complex.norm_le_abs_re_add_abs_im ω
  have hN0 : 0 ≤ 2 * ‖μ - τ‖ / ‖γ‖ := by positivity
  have hlog2 : Real.log (2 * (2 * ‖μ - τ‖ / ‖γ‖) + 1) ≤
      Real.log 2 + Real.log (1 + 2 * ‖μ - τ‖ / ‖γ‖) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    linarith
  rw [hre] at hsplit
  have hre_abs : |Real.log ‖-(2 * (μ - τ) / γ) - slitRoot (2 * (μ - τ) / γ)‖| ≤
      Real.log (2 * (2 * ‖μ - τ‖ / ‖γ‖) + 1) := hlogb
  linarith [hsplit, hre_abs, him]


end
end NlsGge.GKDefinitionDesign
