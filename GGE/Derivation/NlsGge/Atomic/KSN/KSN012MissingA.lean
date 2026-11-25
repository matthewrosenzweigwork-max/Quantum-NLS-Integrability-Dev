import Mathlib
import NlsGge.Atomic.KSN.KSN012MissingACore
import NlsGge.Atomic.KSN.KSN012Sup5
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7

/- KSN012MA PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/KSN/KSN012MissingA.lean. SUPPORT (no packet increment) for KSN-012.
   KSN012_missingA_holds: the body of proof development's `KSN012_missingA` (KSN012_MISSINGPROBE01, VERBATIM, with the probe's
   opens) = KSN012MA.missingA_of applied to Pro r15 KSPS.midpoint_spectral_expansion_uniform,
   KSPS.midpoint_dirichlet_difference_uniform (KSPS017Uniform7) and KSPS017U6.h24_uniform.
   KSN012_missingB_holds: the body of `KSN012_missingB` (verbatim) = landed KSN012Sup5_missingB_of_missingA applied to it.
   No hypothesis added. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem KSN012_missingA_holds :
  ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ ≤ B →
      (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
          ‖NlsGge.ThirdConsultation.KSPS.mu φ n - NlsGge.ThirdConsultation.KSPS.criticalEigenvalue φ n‖ ^ 2)
        else 0) ≤ ENNReal.ofReal C :=
  NlsGge.ThirdConsultation.KSN012MA.missingA_of
    NlsGge.ThirdConsultation.KSPS.midpoint_spectral_expansion_uniform
    NlsGge.ThirdConsultation.KSPS.midpoint_dirichlet_difference_uniform
    NlsGge.ThirdConsultation.KSPS017U6.h24_uniform

theorem KSN012_missingB_holds :
  ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
    ∀ x : PairScale 1, ‖x‖ ≤ B →
      (∑' n : ℤ, if N ≤ n.natAbs then
        ENNReal.ofReal (bracket n ^ 2 *
          ‖muSeq (pairPotential 1 (by norm_num) x) n - lamDot (pairPotential 1 (by norm_num) x) n‖ ^ 2)
        else 0) ≤ ENNReal.ofReal C :=
  NlsGge.ThirdConsultation.KSN.KSN012Sup5_missingB_of_missingA KSN012_missingA_holds

end
end NlsGge.ThirdConsultation.KSN
