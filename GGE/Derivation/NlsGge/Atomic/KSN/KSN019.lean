import Mathlib
import NlsGge.Atomic.KSN.KSN019Asm
import NlsGge.Atomic.KSN.KSN018
import NlsGge.Atomic.KSN.KSN001Sup5

/- KSN019 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN019.lean.
   Packet KSN-019, head VERBATIM from Pro (followup13 STATEMENTS/KSN.md `KSN019_main`; round 15 "Keep head"; pin
   cc702018). Namespace NlsGge.GKDefinitionDesign with `open NlsGge.ThirdConsultation.KSN`, as KSN-012/014/017/018.
   Proof: KSN.KSN019_of (KSN019Asm) applied to KSN018_main N hN and the landed KSN001Sup5 scalarBirkhoff_analytic.
   TASK_INDEX prerequisites KSN-018, G4-007: G4-007's book Thm A.5 is used through the landed
   NlsGge.Atomic.G1098Reindex.analyticOnNhd_of_coords_of_locBdd_reindex (GK38.Lib.HilbertValuedAnalytic).
   No new hypothesis; no repair. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN019_main (N : ℕ) (hN : 1 ≤ N) :
  AnalyticOnNhd ℂ (complexSmoothing N) (complexDomain (N : ℝ) (Nat.cast_nonneg N)) ∧
  (∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
    ∀ b n, rawCoefficient ((N : ℝ) + 1) (complexSmoothing N x) b n =
      smoothingCoefficient N x b n) ∧
  (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ‖complexSmoothing N x‖ ≤ C) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
      ‖complexSmoothing N x‖ ≤ C) :=
  NlsGge.ThirdConsultation.KSN.KSN019_of N hN (NlsGge.GKDefinitionDesign.KSN018_main N hN)
    (fun b n => NlsGge.ThirdConsultation.KSN.KSN001Aux.scalarBirkhoff_analytic b n)

end NlsGge.GKDefinitionDesign
