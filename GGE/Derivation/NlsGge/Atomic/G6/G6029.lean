import Mathlib
import NlsGge.Atomic.G6.G6029Host
import NlsGge.Atomic.G6.G6029Core
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6023
import NlsGge.Atomic.G2.G2030

/- G6029 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6029.lean.
   Packet G6-029, head VERBATIM from Pro (followup13 STATEMENTS/G6.md; round 15 Q5 "Retain exact head"; pin cc702018),
   shared G6 context block plus the definitions file's `open NlsGge.ThirdConsultation (finiteGap)` (canonical landed
   predicate, Pro: "do not redeclare a second finiteGap"). Proof: G6029Aux.G6029_of applied to X-006
   sourceFamily.Phi_action, G2_030, G6023 and G6013's RightInverse conjunct. TASK_INDEX lists G6-027 as a prerequisite;
   this proof does not need it (Pro's Q5 row: finite support gives every Sobolev membership by G6-023).
   No new hypothesis; no repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6029 (u : PhysicalL2) :
  ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
  (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) ∧
  (∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
    ∀ m : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (m : ℝ)) :=
  G6029Aux.G6029_of (fun u n => sourceFamily.Phi_action u n) G2_030 G6023 G6013.2.2.2.2.2 u

end
end NlsGge.GKDefinitionDesign
