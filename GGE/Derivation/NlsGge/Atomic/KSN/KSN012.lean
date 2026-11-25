import Mathlib
import NlsGge.Atomic.KSN.KSN012Asm
import NlsGge.Atomic.KSN.KSN012BetaLocal
import NlsGge.Atomic.KSN.KSN012MissingA
import NlsGge.Atomic.KSN.KSN010
import NlsGge.Atomic.M.M032

/- KSN012 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN012.lean.
   Packet KSN-012, head VERBATIM from Pro (followup13 STATEMENTS/KSN.md `KSN012_main`, round 15 keeps it; request pin
   cc702018). Namespace NlsGge.GKDefinitionDesign with `open NlsGge.ThirdConsultation.KSN` (Pro's block).
   Proof: KSN012L.KSN012_of (KSN012Asm) with
   (1) hbeta := KSN012L.beta_local (KSN012BetaLocal) whose inputs are the landed M-032 theorem
       NlsGge.ThirdConsultation.M.gap_weighted_tail (third conjunct, as in KSN-013/014/017) and
       KSN.KSN012_missingB_holds (KSN012MissingA: Pro r15 uniform midpoint producers + B3 via KSN012Sup5);
   (2) heta  := the second conjunct of the landed KSN010_main.
   No new hypothesis; no repair. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN012_main :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) :=
  NlsGge.ThirdConsultation.KSN012L.KSN012_of
    (fun φ₀ hφ₀ => NlsGge.ThirdConsultation.KSN012L.beta_local
      (fun w hw N φ hW hφ hN => (NlsGge.ThirdConsultation.M.gap_weighted_tail w hw N φ hW hφ hN).2.2)
      NlsGge.ThirdConsultation.KSN.KSN012_missingB_holds φ₀ hφ₀)
    NlsGge.GKDefinitionDesign.KSN010_main.2

end NlsGge.GKDefinitionDesign
