import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.PDE.PDE063Core
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport

/- PDE-063 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE, needs ROOT MAIN PROBE (via the
   Round14Rotation host -> h782's Round14ActionFreq, G6041 closure).  Target NlsGge/Atomic/PDE/PDE063.lean, namespace
   NlsGge.ThirdConsultation.PDE.  Head VERBATIM from Pro r14 '### PDE-063' (proof development/PDE063_HEAD_VERBATIM.txt).
   Opens: Pro's prelude plus `open NlsGge.ThirdConsultation.Common` (root lexical repair 22 addendum, as landed PDE-058:
   FiniteSupportSequence / actions are COMMON names and do not resolve from namespace ...PDE otherwise).
   Proof: the generic PDE063Aux.rotation_core at ω n = actualOmega n (actions z0), with the host's membership proofs;
   rotationCurve/rotationDeriv/actions unfold definitionally to the core's carriers and ‖z0 n‖^2.
   Own imports: Mathlib, PDE/Round14Rotation, PDE/PDE063Core, Common/Actions, Common/FiniteSupport. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem finite_support_rotation_regular
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) :
  ∀ r : ℝ,
    ContDiff ℝ 1 (fun t : ℝ => rotationCurve r z0 hz t) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => rotationCurve r z0 hz s)
      (rotationDeriv r z0 hz t) t) ∧
    (∀ (t : ℝ) (n : ℤ),
      ‖carrierCoe38 r (rotationCurve r z0 hz t) n‖^2 = actions z0 n) ∧
    ∀ t : ℝ,
      {n : ℤ | carrierCoe38 r (rotationCurve r z0 hz t) n ≠ 0} =
        {n : ℤ | z0 n ≠ 0} := fun r =>
  PDE063Aux.rotation_core r (fun n => actualOmega n (actions z0)) z0 hz
    (fun t => finiteSupport_mem_seqSobolev38 r _ (rotationSequence_finiteSupport z0 hz t))
    (fun t => finiteSupport_mem_seqSobolev38 r _ (rotationDerivativeSequence_finiteSupport z0 hz t))

end NlsGge.ThirdConsultation.PDE
