import Mathlib
import NlsGge.Atomic.KSN.KSN018Host
import NlsGge.Atomic.KSN.KSN018Asm
import NlsGge.Atomic.KSN.KSN012
import NlsGge.Atomic.KSN.KSN014
import NlsGge.Atomic.KSN.KSN017
import NlsGge.Atomic.KSN.KSN010
import NlsGge.Atomic.G4.G4014
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceUniform

/- KSN018 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018.lean.
   Packet KSN-018, head VERBATIM from Pro (followup13 STATEMENTS/KSN.md `KSN018_main`; round 15 "Keep head; repair
   prerequisites"; request pin cc702018). Placed, like KSN-012/014/017, in namespace NlsGge.GKDefinitionDesign with
   `open NlsGge.ThirdConsultation.KSN` (the statement file's header opens). Proof: KSN.KSN018_of (KSN018Asm) applied to
   KSN012_main, KSN014_main, KSN017_main, KSN010_main.1, G4014Aux.cartZ_plus/minus and Pro r15
   KSPS.midpoint_dirichlet_difference_uniform (KSPS017Uniform7) / KSPS.antitrace_at_dirichlet_uniform
   (KSPSAntitraceUniform). Route = Pro r15 L858. No new hypothesis; no repair. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN018_main (N : ℕ) (hN : 1 ≤ N) :
  (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
      ∀ x ∈ U, Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
        ‖complexSmoothing N x‖ ≤ C) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
      ‖complexSmoothing N x‖ ≤ C) :=
  NlsGge.ThirdConsultation.KSN.KSN018_of N hN
    NlsGge.GKDefinitionDesign.KSN012_main
    NlsGge.GKDefinitionDesign.KSN014_main
    NlsGge.GKDefinitionDesign.KSN017_main
    NlsGge.GKDefinitionDesign.KSN010_main.1
    (fun n φ h => NlsGge.GKDefinitionDesign.G4014Aux.cartZ_plus n φ h)
    (fun n φ h => NlsGge.GKDefinitionDesign.G4014Aux.cartZ_minus n φ h)
    NlsGge.ThirdConsultation.KSPS.midpoint_dirichlet_difference_uniform
    NlsGge.ThirdConsultation.KSPS.antitrace_at_dirichlet_uniform

end NlsGge.GKDefinitionDesign
