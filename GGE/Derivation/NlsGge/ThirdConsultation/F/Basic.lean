import Mathlib
import NlsGge.Hierarchy.F03Spectral38

/- Host draft for NlsGge/ThirdConsultation/F/Basic.lean (proof development, AUTHOR). Hosts ONLY agreesLocalRemainder, copied verbatim
   from DEFINITIONS/F.lean.md lines 52-60. Checked: no production definition of agreesLocalRemainder; no NlsGge/ThirdConsultation/F directory exists. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F

def agreesLocalRemainder (m : ℕ) (β : ℕ → ℝ)
    (V : SobolevHilbert ((m - 1 : ℕ) : ℝ) → ℝ) : Prop :=
  ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)),
    (∀ n : ℤ, (show WeightedHilbert
        (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n =
      smoothFourier38 U hU hper n) →
    Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
      ‖smoothFourier38 U hU hper n‖ ^ 2) ∧
    V y = spectralEnergy38 m β U hU hper -
      ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖smoothFourier38 U hU hper n‖ ^ 2

end NlsGge.ThirdConsultation.F
