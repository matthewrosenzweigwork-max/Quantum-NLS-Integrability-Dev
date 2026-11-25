import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE065Core
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.PDE.Round14Deriv
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.Atomic.PDE.PDE062
import NlsGge.Atomic.PDE.PDE063
import NlsGge.Atomic.PDE.PDE064
import NlsGge.Atomic.G6.G6027

/- PDE-065 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE, needs ROOT MAIN PROBE.
   Target NlsGge/Atomic/PDE/PDE065.lean, namespace NlsGge.ThirdConsultation.PDE.  Head VERBATIM from Pro r14 '### PDE-065'
   (PRO_DEFINITION_RESPONSE_FP80_14.md l.3127-3146; rounds 15/16 print no change).
   Opens: Pro's prelude plus `open NlsGge.ThirdConsultation.Common` (root lexical repair 22 addendum, as landed PDE-058 and
   the PDE-063/064 drafts: FiniteSupportSequence is a COMMON name).
   Proof = Pro's route (r14 §7): one application of the lane-checked PDE065Aux.rotation_nls_core with
     Ω := actualOmega, a := actions z0, c3 := rotationCurve 3 z0 hz, c3' := rotationDeriv 3 z0 hz;
     G6027 1 / G6027 3 (analyticity, level-one inverse laws, embedding compatibility);
     PDE-062 actual_nls_coordinate_field (proof development; DPhi = fderiv birkhoffSobolev by definition);
     PDE-063 finite_support_rotation_regular at r = 3 (moduli = actions z0);
     the definitional coordinates of rotationDeriv / rotationCurve (rotationDerivativeSequence);
     PDE-064 inverse_finite_curve_hasDerivAt (proof development; DPhiinv = fderiv inverseBirkhoffSobolev).
   inverseRotationCurve / inverseRotationPhysical unfold to the core's curve by definition.
   Own imports: Mathlib, PDE/PDE065Core, PDE/Round14InverseRotation (h782), PDE/Round14Rotation, PDE/Round14Deriv,
   Common/Actions, Common/FiniteSupport, Atomic/PDE/PDE062 (h782), PDE063, PDE064 (h782), Atomic/G6/G6027. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem inverse_rotation_is_actual_nls
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) :
  (∀ t0 : ℝ,
    HasDerivAt (fun t : ℝ => physicalCoreBase (inverseRotationCurve z0 hz t))
      (nlsVectorField (inverseRotationCurve z0 hz t0)) t0) ∧
  IsPhysicalNLSSolution (inverseRotationPhysical z0 hz) := by
  obtain ⟨hΦa1, hΨa1, hL1, hR1, -, hc1⟩ := G6027 1 le_rfl
  obtain ⟨-, hΨa3, -, -, -, hc3⟩ := G6027 3 (by norm_num)
  exact PDE065Aux.rotation_nls_core actualOmega (actions z0)
    (fun t => rotationCurve ((3 : ℕ) : ℝ) z0 hz t) (fun t => rotationDeriv ((3 : ℕ) : ℝ) z0 hz t)
    hΦa1 hΨa1 hL1 hR1 (fun z => (hc1 z).2) hΨa3 (fun z => (hc3 z).2)
    (fun u n => actual_nls_coordinate_field u n)
    (finite_support_rotation_regular z0 hz ((3 : ℕ) : ℝ)).2.2.1
    (fun t n => by
      unfold rotationDeriv rotationCurve
      rw [carrierCoe38_mk, carrierCoe38_mk]
      rfl)
    (fun t0 => inverse_finite_curve_hasDerivAt z0 hz t0)

end NlsGge.ThirdConsultation.PDE
