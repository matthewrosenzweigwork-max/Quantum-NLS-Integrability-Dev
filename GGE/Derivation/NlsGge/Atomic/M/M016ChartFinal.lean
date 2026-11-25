import Mathlib
import NlsGge.Atomic.M.M016ChartCore
import NlsGge.Atomic.M.M016RayCalib

/- M016 CHARTFINAL PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016ChartFinal.lean. Needs ROOT MAIN PROBE. Pro R16 §1.1 complex finite-gap chart, UNCONDITIONAL in
   φ ∈ gkW and finite-gap, with the not-yet-landed M-052 names `ExteriorPrimitiveRepresentative φ R F` and
   `finiteGapPair φ` replaced by their literal R14 bodies (unfolded, NOT re-hosted), exactly as in h789's landed
   `finitegap_pair_primitive_meromorphic_infinity_of_ray`. The ray hypothesis `hray` is discharged by
   `M.primitive_ray_calibration` (M016RayCalib, S5b). `_of_ray` is kept as the conditional helper (root, review
   proof development). The verbatim Pro head is the wrapper in M016ChartFinalHead_DRAFT.lean.txt, compilable once M-052
   hosts both names; per root it counts only then. -/

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.MPrimitive

theorem finitegap_pair_primitive_meromorphic_infinity_unfolded
    (φ : PotPair) (hW : φ ∈ gkW)
    (hfg : {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      (0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
        ∃ hz : φ ∈ gkW ∧ z ∈ endpointClosureFiber φ, F z = primitive ⟨(φ, z), hz⟩) ∧
      ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 :=
  finitegap_pair_primitive_meromorphic_infinity_of_ray φ hW hfg (primitive_ray_calibration φ hW)

end NlsGge.ThirdConsultation.M
