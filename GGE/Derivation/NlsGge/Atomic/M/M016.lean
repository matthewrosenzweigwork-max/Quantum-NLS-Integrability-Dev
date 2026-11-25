import Mathlib
import NlsGge.Atomic.M.M052
import NlsGge.Atomic.M.M053
import NlsGge.Atomic.KSPS.KSPS031
import NlsGge.Atomic.M.M016Coeff
import NlsGge.Atomic.M.M016Laurent

/- M-016 (REAL HEAD) PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/M/M016.lean, namespace NlsGge.ThirdConsultation.M.  Contains ONLY the real head
   `finitegap_primitive_laurent_real`, verbatim from followup13 STATEMENTS/M.md "## M-016" (retained by Pro round 16
   Q1; dispatched first).  The complex head `finitegap_primitive_laurent` (complex chart, sharp producer, N = 0) is owned
   elsewhere and is NOT in this file.
   Route = Pro round 16 §5 / §6 table "Immediate real M-016": M-052's exterior F (finitegap_primitive_meromorphic_infinity,
   pending proof development, treated as stable) → for each N, φ: the hsmooth lift ψ at N+2 → landed KSPS-031
   (nonresonant_WKB_coefficients at N+2) and landed M-053 (WKB_hierarchy_coefficients_complex at N+2) discharge the two
   hypotheses of the lane-checked core M016Q.laurent_core (half-node identification M016H, hierarchyCharge_lift M016L,
   coefficient comparison M016C).  MAIN-ONLY: KSPS031 + M053 closure ≈ 17k lines. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M

theorem finitegap_primitive_laurent_real
    (u : PhysicalL2) (hfg : finiteGap u)
    (hsmooth : ∀ N : ℕ, ∃ φ : KSPS.SobolevC N,
      KSPS.toPotPair φ = realSlice u) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative (realSlice u) R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      ∀ N : ℕ, ∀ φ : KSPS.SobolevC N,
        KSPS.toPotPair φ = realSlice u → PrimitiveLaurentCoefficients N φ F := by
  obtain ⟨R, F, hrep, hhol, hG, hval⟩ := finitegap_primitive_meromorphic_infinity u hfg
  refine ⟨R, F, hrep, hhol, fun N φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hsmooth (N + 2)
  obtain ⟨C, J, hC, h031⟩ := NlsGge.ThirdConsultation.KSPS.nonresonant_WKB_coefficients (N + 2) (by omega) ψ
  exact NlsGge.ThirdConsultation.M016Q.laurent_core u R F hrep.2 hval hG N φ hφ ψ hψ
    ⟨C, J, hC, fun j hj => by
      obtain ⟨hch, -, -, hb⟩ := h031 j hj
      exact ⟨hch, hb⟩⟩
    (fun k hk hkN => WKB_hierarchy_coefficients_complex (N + 2) ψ k hk hkN)

end NlsGge.ThirdConsultation.M
