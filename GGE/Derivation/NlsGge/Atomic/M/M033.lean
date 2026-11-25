import Mathlib
import NlsGge.Atomic.M.M015
import NlsGge.ThirdConsultation.M.M033Core
import NlsGge.ThirdConsultation.M.M033Bridge

/- M-033 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/M/M033.lean, namespace
   NlsGge.ThirdConsultation.M.  Heads VERBATIM from Pro round 14 (2d599b57) "### M-033" (= followup12 STATEMENTS/M.md
   "## M-033"); bodies of HighModeH1Threshold / MTwoMode.H1Norm from round-14 DEFINITIONS/M.lean.md (host M033Host).
   Route (Molnar Prop. 12, printed p.23): M-015 mean-value point zeta in the closed gap; M-031 localization of both real
   gap endpoints (M033Bridge), so |zeta - n pi| <= Q^2/<n> + sqrt2 Q/<2n>; for n != 0 this radius is <= 3/8, whence
   4 zeta^2 <= (1+|2 pi n|)^2 <= 8 zeta^2, raised to the power m (M033Core).  No hypothesis beyond the printed heads. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M

theorem high_odd_action_comparison
    (u : SobolevR 1) (n : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h : HighModeH1Threshold u n) :
    (2 : ℝ) ^ (-(m : ℤ)) * molnarWeight m n ^ 2 *
      action (physicalOfSobolev u) n ≤
        (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1) ∧
    (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1) ≤
      molnarWeight m n ^ 2 * action (physicalOfSobolev u) n := by
  obtain ⟨hn, h8⟩ := h
  obtain ⟨-, ζ, hζ, hJ⟩ := odd_action_mean_value (physicalOfSobolev u) n m
  have hζ' : ζ ∈ Set.Icc (actualGapLowerAllE02_38 (physicalOfSobolev u) n)
      (actualGapUpperAllE02_38 (physicalOfSobolev u) n) := hζ
  obtain ⟨hlo, hhi⟩ := M033Bridge.high_endpoints u n h8
  have hdist := M033Core.abs_sub_le_of_mem_Icc hζ' hlo hhi
  have hr := M033Core.radius_le n hn (MTwoMode.H1Norm u) h8
  obtain ⟨h1, h2⟩ := M033Core.high_core n hn ζ _ hr hdist
  have hI : 0 ≤ action (physicalOfSobolev u) n :=
    NlsGge.GKDefinitionDesign.realActionNonneg38 (physicalOfSobolev u) n
  rw [hJ]
  exact M033Core.high_pow m ζ _ _ hI h1 h2

/-- Source mean-value/localization statement also covers n=0 and m=0. -/
theorem high_odd_action_mean_value
    (u : SobolevR 1) (n : ℤ) (m : ℕ)
    (h : 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    ∃ zeta : ℝ, zeta ∈ closedGap (physicalOfSobolev u) n ∧
      higherAction (physicalOfSobolev u) n (2 * m + 1) =
        zeta ^ (2 * m) * action (physicalOfSobolev u) n ∧
      |zeta - (n : ℝ) * Real.pi| ≤
        MTwoMode.H1Norm u ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
          Real.sqrt 2 * MTwoMode.H1Norm u /
            NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
  obtain ⟨-, ζ, hζ, hJ⟩ := odd_action_mean_value (physicalOfSobolev u) n m
  have hζ' : ζ ∈ Set.Icc (actualGapLowerAllE02_38 (physicalOfSobolev u) n)
      (actualGapUpperAllE02_38 (physicalOfSobolev u) n) := hζ
  obtain ⟨hlo, hhi⟩ := M033Bridge.high_endpoints u n h
  exact ⟨ζ, hζ, hJ, M033Core.abs_sub_le_of_mem_Icc hζ' hlo hhi⟩

end NlsGge.ThirdConsultation.M
