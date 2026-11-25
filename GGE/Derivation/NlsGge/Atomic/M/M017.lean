import Mathlib
import NlsGge.Atomic.M.M016
import NlsGge.Atomic.M.M016SmoothLift
import NlsGge.Atomic.M.M017RealCore
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.M.M017Cx

/- M-017 (REAL HEAD) PRODUCTION02 (adds `open NlsGge.Birkhoff` for fourierSeq38/seqSobolev38/fourierSeq38_mem_iff; root probe MR2P0x) (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/M/M017.lean, namespace NlsGge.ThirdConsultation.M.  Contains ONLY the real head
   `higher_action_trace_finitegap_real`, verbatim from followup13 STATEMENTS/M.md "## M-017" (retained by Pro round 16
   Q2).  The complex head `higher_action_trace_finitegap` waits for the complex chart (h789) and is not in this file.
   Route (see M017_ROUTE.md): u := realPhysicalFromPair φ; finiteGap u ⇒ u ∈ every h^m (landed G6029, conjunct 2) ⇒
   hsmooth (M016SM.smooth_lift) ⇒ real M-016 (finitegap_primitive_laurent_real) gives hrep and
   PrimitiveLaurentCoefficients N φ F (RealPair φ is exactly the lift premise) ⇒ M017R.trace_real_core with u ∈ H¹ and
   finitely many open gaps.  MAIN-ONLY (G6029, M016 closures). -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.M

theorem higher_action_trace_finitegap_real
    (N : ℕ) (φ : KSPS.SobolevC N)
    (hreal : MRiccati.RealPair φ)
    (hfg : finiteGap (MRiccati.realPhysicalFromPair φ))
    (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1) :
    Summable (fun n : ℤ => higherAction (MRiccati.realPhysicalFromPair φ) n k) ∧
    (∑' n : ℤ, higherAction (MRiccati.realPhysicalFromPair φ) n k) =
      (-((2 * Complex.I) ^ (k - 1))⁻¹ *
        hierarchyCharge φ ⟨k, (by omega), hkN⟩).re := by
  set u : PhysicalL2 := MRiccati.realPhysicalFromPair φ with hu
  have hall : ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) := (G6029 u).2.1 hfg
  obtain ⟨R, F, hrep, -, hcoef⟩ :=
    finitegap_primitive_laurent_real u hfg (NlsGge.ThirdConsultation.M016SM.smooth_lift u hall)
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) u).1 (hall 1)
  have hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite :=
    Set.Finite.subset hfg (fun n hn => ne_of_lt hn)
  exact NlsGge.ThirdConsultation.M017R.trace_real_core u hu1 hfin R F hrep.2 N φ (hcoef N φ hreal) k hk hkN

end NlsGge.ThirdConsultation.M
