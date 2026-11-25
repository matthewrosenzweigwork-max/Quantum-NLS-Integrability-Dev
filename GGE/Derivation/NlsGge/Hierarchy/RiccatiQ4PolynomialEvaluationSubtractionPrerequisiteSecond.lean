import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

theorem riccatiJetEvaluation_sub_prerequisite
    (u : ℝ → ℂ) (x : ℝ) (P Q : Poly) :
    riccatiJetEvaluation u x (P - Q) =
      riccatiJetEvaluation u x P - riccatiJetEvaluation u x Q := by
  unfold riccatiJetEvaluation
  exact map_sub (polynomialEvaluation (fun v => riccatiJetFunction u v x)) P Q

end NlsGge.HierarchyRiccati.Core

namespace NlsGge.HierarchyRiccati

open NlsGge.HierarchyRiccati.Core

def q4BoundaryFluxPolynomialValueBridge : Poly :=
  MvPolynomial.X (false, 0) * MvPolynomial.X (true, 3) -
    MvPolynomial.X (false, 1) * MvPolynomial.X (true, 2) -
    MvPolynomial.X (false, 0) * MvPolynomial.X (false, 1) *
      (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) -
    6 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
      MvPolynomial.X (true, 0) * MvPolynomial.X (true, 1)

def q4BoundaryFluxAfterPolynomialEvaluationBridge (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  polynomialEvaluation (fun v => riccatiJetFunction u v x)
    q4BoundaryFluxPolynomialValueBridge

theorem q4BoundaryFluxAfterPolynomialEvaluationBridge_eq_jetEvaluation
    (u : ℝ → ℂ) :
    q4BoundaryFluxAfterPolynomialEvaluationBridge u =
      fun x => riccatiJetEvaluation u x q4BoundaryFluxPolynomialValueBridge := by
  funext x
  rfl

end NlsGge.HierarchyRiccati
