import NlsGge.Ramer.General.RamerSetting

/-!
# Ramer step 5, generalized (GD1)

Generalization of `NlsGge/Ramer/RamerStep5.lean` to an arbitrary `RamerSetting`.  The explicit
tail estimate of the old file is replaced by `RamerSetting.tail_bound` and
`RamerSetting.tailSup_tendsto` of G0.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter
open scoped Topology

namespace NlsGge.Ramer.Gen

open NlsGge.Pilot NlsGge.Ramer.General

/-- Uniform smallness of the `E`-norm tail of `incl h` on `H`-balls
(old `exists_tail_small`). -/
theorem exists_tail_small (S : RamerSetting) (d ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ h : S.H, ‖h‖ < d →
      ‖S.incl h - S.incl (S.headProj n h)‖ < ε / 2 := by
  have hlim : Tendsto (fun n : ℕ => S.tailSup n * d ^ 2) atTop (𝓝 (0 * d ^ 2)) :=
    S.tailSup_tendsto.mul_const _
  rw [zero_mul] at hlim
  have hpos : 0 < (ε / 2) ^ 2 := by positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨n₀, fun n hn h hh => ?_⟩
  have h1 := S.tail_bound n h
  have h2 : ‖h‖ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (norm_nonneg h) hh.le 2
  have h4 : ‖S.incl h - S.incl (S.headProj n h)‖ ^ 2 < (ε / 2) ^ 2 :=
    lt_of_le_of_lt (h1.trans (mul_le_mul_of_nonneg_left h2 (S.tailSup_nonneg n))) (hn₀ n hn)
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h4

/-- Squared form of the tail bound (old `norm_incl_sub_trunc_sq_le`; the constant is `tailSup n`). -/
theorem norm_incl_sub_trunc_sq_le (S : RamerSetting) (n : ℕ) (h : S.H) :
    ‖S.incl h - S.incl (S.headProj n h)‖ ^ 2 ≤ S.tailSup n * ‖h‖ ^ 2 :=
  S.tail_bound n h

end NlsGge.Ramer.Gen
