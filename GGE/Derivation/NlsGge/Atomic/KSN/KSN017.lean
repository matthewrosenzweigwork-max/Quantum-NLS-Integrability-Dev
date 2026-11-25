import Mathlib
import NlsGge.Atomic.KSN.KSN017Asm
import NlsGge.Atomic.M.M032
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7
/- KSN017 PRODUCTION01 (proof development, AUTHOR of this copy; text = proof development KSN017_PRODUCTION01 with the pending glue
   import resolved to KSPS017Uniform7 (proof development), where Pro's midpoint_first_order_uniform is now proved; head and
   proof otherwise byte-identical; not self-reviewed, not accepted). Original header (proof development): Target NlsGge/Atomic/KSN/KSN017.lean.
   Packet KSN-017, head VERBATIM from Pro round 15 (PRO_DEFINITION_RESPONSE_FP80_15.md Q1 "KSN-017", conclusion
   unchanged; artifact 879be8f1, request pin cc702018). Namespace NlsGge.GKDefinitionDesign with
   `open NlsGge.ThirdConsultation.KSN`. Proof: supporting KSN017_of (KSN017Asm) with its two hypotheses discharged by
   (1) the landed M-032 theorem NlsGge.ThirdConsultation.M.gap_weighted_tail (third conjunct), as KSN-013/014;
   (2) Pro's uniform producer NlsGge.ThirdConsultation.KSPS.midpoint_first_order_uniform (round 15 Q2 head).
   (2) is supplied by NlsGge/ThirdConsultation/KSPS/KSPS017Uniform7.lean. No new hypothesis; no repair. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN017_main :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) :=
  NlsGge.ThirdConsultation.KSN.KSN017_of
    (fun w hw N φ hW hφ hN => (NlsGge.ThirdConsultation.M.gap_weighted_tail w hw N φ hW hφ hN).2.2)
    NlsGge.ThirdConsultation.KSPS.midpoint_first_order_uniform

end NlsGge.GKDefinitionDesign
