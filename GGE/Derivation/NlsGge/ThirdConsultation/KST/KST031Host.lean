import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST006
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.Lib.CircleArgument

/- KST031Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST031Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (Pro round 7-8 does not change them): physicalComponentBall (:357), UnboundedWeight (:362), productWeight (:368),
   uniformReducedBounds (:428), diagonalThreshold (:437).  proof development's KST031_HOST02 minus its redeclarations:
   `Potential` is the landed NlsGge.ThirdConsultation.KST.Potential (DM004); `periodicPair` is the single host in
   KST029Support (imported, NOT redeclared); AdmissibleWeight/SecondaryWeight come from KST/Basic (KST-local, not
   NlsGge.Composition).  `NlsGge.Atomic.KST044.productWeight` lives in another namespace (no clash).
   LEXICAL REPAIR (elaboration only): attribute [local instance] Classical.propDecidable for the dite in
   diagonalThreshold (as in proof development HOST02).  No KST016 namespace is opened (it would make `Potential` ambiguous). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.GK38 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def physicalComponentBall (ω : ℤ → ℝ) (R : ℝ) : Set Potential :=
  {φ | ∀ channel : Bool, (∑' m : ℤ, ENNReal.ofReal
      (ω (2*m)^2 * ‖physicalFourier (φ channel) m‖^2)) ≤
        ENNReal.ofReal (R^2)}

def UnboundedWeight (w : ℤ → ℝ) : Prop :=
  AdmissibleWeight w ∧ Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop

def productWeight (w v : ℤ → ℝ) : ℤ → ℝ := fun k => w k*v k

def uniformReducedBounds (w : ℤ → ℝ) (M : ℝ) (N : ℕ) : Prop :=
  5 ≤ N ∧ ∀ φ ∈ physicalComponentBall w (2*M), ∀ n : ℤ, N ≤ n.natAbs →
    SmallCoefficients n (a φ n) (b φ n) (c φ n) ∧
    (∀ (z : ℂ) (hz : z ∈ spectralStrip n),
      ‖qOperator φ n z hz ^ 2‖ ≤ (1/2 : ℝ) ∧ IsUnit (1-qOperator φ n z hz)) ∧
    Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.ball (center n) (Real.pi/3)) =
      {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n}

def diagonalThreshold (w : ℤ → ℝ) (M : ℝ) : ℕ :=
  if h : ∃ N : ℕ, uniformReducedBounds w M N then Nat.find h else 0

end NlsGge.ThirdConsultation.KST
end
