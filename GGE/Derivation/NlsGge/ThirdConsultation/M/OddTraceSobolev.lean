import Mathlib
import NlsGge.ThirdConsultation.M.OddTraceSobolevCore
import NlsGge.ThirdConsultation.M.MOdd5
import NlsGge.Atomic.M.M017
import NlsGge.Atomic.M.M016SmoothLift
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.KST.KST066
import NlsGge.ThirdConsultation.M.OddActionSummable
import NlsGge.ThirdConsultation.M.OddActionTails
import NlsGge.ThirdConsultation.M.HigherActionContinuous
import NlsGge.ThirdConsultation.M.Round5b

/- MTRACE PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/M/OddTraceSobolev.lean
   (module NlsGge.ThirdConsultation.M.OddTraceSobolev; the name proof development's M043 glue already imports), namespace
   NlsGge.ThirdConsultation.M. Pro round 16 §Q2 support `odd_higher_action_trace_sobolev`, head VERBATIM (followup14
   PRO_DEFINITION_RESPONSE_FP80_16.md L439-509; no packet increment). MAIN-ONLY GLUE: instantiates the lane-checked core
   MTraceCore.odd_trace_sobolev_of with
     M.odd_hierarchy_charge_eq_signedCharge (proof development MOdd5; root probe MODD5_MAINPROBE01 exit 0, in review),
     M.higher_action_trace_finitegap_real (proof development M017; not landed),
     KST.kst066 (landed) for finite-gap H^m density, G6029 conjunct 2 (landed) + M016SM.smooth_lift (proof development) for
     the H^{2m} pair lift, and proof development's odd_higher_action_summable / odd_higher_action_tails_of_tendsto /
     higherAction_continuous_real (in review). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem odd_higher_action_trace_sobolev
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    HasSum (fun n : ℤ =>
      (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1))
      (signedCharge m u) := by
  have hdense : ∀ (m : ℕ) (u : SobolevR m), ∃ v : ℕ → SobolevR m,
      Tendsto v atTop (𝓝 u) ∧ ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (physicalOfSobolev (v j)) := by
    intro m u
    obtain ⟨v, hv, hp⟩ := NlsGge.ThirdConsultation.KST.kst066 (m : ℝ) (Nat.cast_nonneg m) u
    refine ⟨v, hv, fun j => ?_⟩
    have h := hp j
    dsimp only at h
    have e : NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent (m : ℝ) (Nat.cast_nonneg m) (v j) =
        physicalOfSobolev (v j) := by
      rw [← NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M]
      rfl
    rw [e] at h
    exact h.1
  have hlift : ∀ w : PhysicalL2, NlsGge.ThirdConsultation.finiteGap w → ∀ N : ℕ,
      ∃ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N,
        NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice w := fun w hw N =>
    NlsGge.ThirdConsultation.M016SM.smooth_lift w ((NlsGge.GKDefinitionDesign.G6029 w).2.1 hw) N
  exact NlsGge.ThirdConsultation.MTraceCore.odd_trace_sobolev_of
    odd_hierarchy_charge_eq_signedCharge higher_action_trace_finitegap_real hdense hlift
    odd_higher_action_summable odd_higher_action_tails_of_tendsto higherAction_continuous_real m hm u

end NlsGge.ThirdConsultation.M
