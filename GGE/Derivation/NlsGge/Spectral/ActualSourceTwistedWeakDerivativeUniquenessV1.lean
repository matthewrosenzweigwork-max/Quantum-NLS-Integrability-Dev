import NlsGge.Schur.SourceFreeDomainTwistedWeakDerivativeIffV1
import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.Schur

/-- The original full twisted-test predicate determines its actual derivative
L² class uniquely, including the zero Fourier coefficient. -/
theorem sourceTwistedWeakDerivative_unique_derivative
    (n : ℤ) (F G H : SourceIntervalL2)
    (hG : SourceTwistedWeakDerivative n F G)
    (hH : SourceTwistedWeakDerivative n F H) : G = H := by
  apply (scalarParityIntervalEquiv n).symm.injective
  apply (scalarParityRepr n).injective
  apply lp.ext
  funext m
  change sourceScalarCoefficient n G m = sourceScalarCoefficient n H m
  exact (sourceTwistedWeakDerivative_fourier_coefficients n F G hG m).trans
    (sourceTwistedWeakDerivative_fourier_coefficients n F H hH m).symm

/-- A realized source weak derivative equals the actual free graph-domain
derivative, rather than merely witnessing domain membership. -/
theorem sourceFreeCoordinateDerivative_eq_actual_weak_derivative
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (b : Bool) (G : SourceIntervalL2)
    (hG : SourceTwistedWeakDerivative n (sourceCoordinateComponent n x b) G) :
    sourceFreeCoordinateDerivative n x hx b = G := by
  exact sourceTwistedWeakDerivative_unique_derivative n
    (sourceCoordinateComponent n x b) (sourceFreeCoordinateDerivative n x hx b) G
    (sourceFreeDomain_has_twisted_weak_derivative n x hx b) hG

/-- The actual reflected free source action is minus-i or plus-i times the
identified weak derivative, with the original Boolean channel convention. -/
theorem sourceFreeDiracAction_eq_actual_weak_derivative
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (b : Bool) (G : SourceIntervalL2)
    (hG : SourceTwistedWeakDerivative n (sourceCoordinateComponent n x b) G) :
    sourceFreeDiracAction n x hx b = (if b then -Complex.I else Complex.I) • G := by
  rw [sourceFreeDiracAction, sourceFreeCoordinateDerivative_eq_actual_weak_derivative n x hx b G hG]

end NlsGge.Schur
end
