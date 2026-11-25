import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Local

/-! # Track B (owner-approved contract 7): rebasing the `H⁻¹` Duhamel identity

`l2_duhamel_rebase` is stated verbatim as in `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c2…3ca056), in the same Lean context. Proof: group law of `freeProp`, commutation of the
continuous linear map `freeProp (-1) (t - s)` with the interval integral, and additivity of the
interval integral (interval integrability from `duhamelIntegrand_intervalIntegrable`).
`duhamel_shift` is the same identity written for the time-shifted representative.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

theorem freeProp_duhamelIntegrand (U : ℝ × PhysicalCircle → ℂ) (s t r : ℝ) :
    freeProp (-1) (t - s) (duhamelIntegrand U s r) = duhamelIntegrand U t r := by
  unfold duhamelIntegrand
  rw [← freeProp_add, show t - s + (s - r) = t - r by ring]

theorem l2_duhamel_rebase (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (h4 : IsL4Loc U)
    (hD : IsHm1Duhamel u U) (s t : ℝ) :
    IntervalIntegrable (duhamelIntegrand U t) volume s t ∧
      l2ToHm1 (u t) = freeProp (-1) (t - s) (l2ToHm1 (u s)) + ∫ r in s..t, duhamelIntegrand U t r := by
  refine ⟨duhamelIntegrand_intervalIntegrable h4 t s t, ?_⟩
  obtain ⟨-, ht⟩ := hD t
  obtain ⟨hs_int, hs⟩ := hD s
  have hcomm : freeProp (-1) (t - s) (∫ r in (0 : ℝ)..s, duhamelIntegrand U s r) =
      ∫ r in (0 : ℝ)..s, duhamelIntegrand U t r := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hs_int]
    exact intervalIntegral.integral_congr fun r _ => freeProp_duhamelIntegrand U s t r
  rw [ht, hs, map_add, hcomm, ← freeProp_add, sub_add_cancel, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (duhamelIntegrand_intervalIntegrable h4 t 0 s)
      (duhamelIntegrand_intervalIntegrable h4 t s t)]

/-- The Duhamel identity of the time-shifted trajectory, from the shifted initial time. -/
theorem duhamel_shift (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (h4 : IsL4Loc U)
    (hD : IsHm1Duhamel u U) (s t : ℝ) :
    l2ToHm1 (u (t + s)) = freeProp (-1) t (l2ToHm1 (u s)) +
      ∫ r in (0 : ℝ)..t, duhamelIntegrand (fun p => U (p.1 + s, p.2)) t r := by
  rw [(l2_duhamel_rebase u U h4 hD s (t + s)).2, add_sub_cancel_right]
  congr 1
  have hc := intervalIntegral.integral_comp_add_right (fun r => duhamelIntegrand U (t + s) r) s
    (a := 0) (b := t)
  rw [zero_add] at hc
  rw [← hc]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [duhamelIntegrand]
  rw [show t + s - (r + s) = t - r by ring]

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
