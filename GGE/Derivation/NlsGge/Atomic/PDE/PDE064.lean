import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.Round14Deriv
import NlsGge.ThirdConsultation.PDE.PDE064Core
import NlsGge.Atomic.PDE.PDE063
import NlsGge.Atomic.G6.G6027

/- PDE-064 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/PDE/PDE064.lean,
   namespace NlsGge.ThirdConsultation.PDE. Head VERBATIM from Pro r14 '### PDE-064'.
   Opens: Pro's prelude plus `open NlsGge.ThirdConsultation.Common` (root lexical repair 22 addendum, as landed PDE-058 /
   h783's PDE-063: FiniteSupportSequence is a COMMON name).
   Proof: chain rule (PDE064Aux.hasDerivAt_comp_of_analyticOnNhd) for inverseBirkhoffSobolev 3, analytic on univ by the
   landed G6027 3 (second conjunct), along rotationCurve 3, whose derivative is rotationDeriv 3 by h783's PDE-063
   (finite_support_rotation_regular, second conjunct at r = 3). DPhiinv 3 z = fderiv ℝ (inverseBirkhoffSobolev 3) z and
   inverseRotationCurve z0 hz = fun t => inverseBirkhoffSobolev 3 (rotationCurve 3 z0 hz t) by definition.
   MAIN-ONLY (G6027 / Round14Deriv closures; Round14Rotation -> Round14ActionFreq). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem inverse_finite_curve_hasDerivAt
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) (t0 : ℝ) :
  HasDerivAt (inverseRotationCurve z0 hz)
    (DPhiinv 3 (rotationCurve ((3 : ℕ) : ℝ) z0 hz t0)
      (rotationDeriv ((3 : ℕ) : ℝ) z0 hz t0)) t0 :=
  PDE064Aux.hasDerivAt_comp_of_analyticOnNhd (inverseBirkhoffSobolev 3)
    (G6027 3 (by norm_num)).2.1
    (fun t : ℝ => rotationCurve ((3 : ℕ) : ℝ) z0 hz t)
    (rotationDeriv ((3 : ℕ) : ℝ) z0 hz t0) t0
    ((finite_support_rotation_regular z0 hz ((3 : ℕ) : ℝ)).2.1 t0)

end NlsGge.ThirdConsultation.PDE
