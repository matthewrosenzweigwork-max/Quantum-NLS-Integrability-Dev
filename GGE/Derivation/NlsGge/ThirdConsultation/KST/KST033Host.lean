import Mathlib
import NlsGge.GK38.Defs
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST031Host

/- KST033Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST033Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10; Pro rounds 7-12 do not touch them): productOneLe (:373), RealForm (:190),
   componentBall (:396), componentOpenBall (:400), weightedRestriction (:408).  Not defined anywhere in NlsGge
   (grep) nor in any other worker's candidate.  Already landed and imported, NOT redeclared: productWeight
   (KST031Host), weightFact / Weighted / weightedPotential (KST027), periodicPair (KST029Support),
   physicalComponentBall / UnboundedWeight (KST031Host).  `PotPair` is the landed NlsGge.GK38.PotPair.
   No lexical repair: the bodies are the design text. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators
open NlsGge.GK38 NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

def productOneLe {w v : ℤ → ℝ} (hw : ∀ k, 1 ≤ w k)
    (hv : ∀ k, 1 ≤ v k) : ∀ k, 1 ≤ productWeight w v k := by
  intro k
  dsimp [productWeight]
  nlinarith [hw k, hv k]

def RealForm (ε : ℝ) (φ : PotPair) : Prop :=
  (ε = 1 ∨ ε = -1) ∧ φ.2 = (ε : ℂ) • star φ.1

def componentBall (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) : Set (Weighted ω) :=
  {x | ∀ channel : Bool, ‖x channel‖ ≤ R}

def componentOpenBall (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) : Set (Weighted ω) :=
  {x | ∀ channel : Bool, ‖x channel‖ < R}

def weightedRestriction (ω ν : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    [Fact (∀ m : ℤ, 0 < periodOneWeight ν m ^ 2)]
    (hων : ∀ k, ν k ^ 2 ≤ ω k ^ 2) (x : Weighted ω) : Weighted ν :=
  WithLp.toLp 2 (fun channel =>
    weightedComparison (fun m => periodOneWeight ω m ^ 2)
      (fun m => periodOneWeight ν m ^ 2) 1 (by norm_num)
      (fun m => by simpa [periodOneWeight] using hων (2*m)) (x channel))

end NlsGge.ThirdConsultation.KST
end
