import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false

/-! Ring-hom API for evaluating independent formal Riccati jets. -/

namespace NlsGge.HierarchyRiccati.Core

def polynomialEvaluation (values : Jet → ℂ) : Poly →+* ℂ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℂ) values

@[simp] theorem polynomialEvaluation_C (values : Jet → ℂ) (a : ℤ) :
    polynomialEvaluation values (MvPolynomial.C a) = (a : ℂ) := by
  simp [polynomialEvaluation]

@[simp] theorem polynomialEvaluation_X (values : Jet → ℂ) (v : Jet) :
    polynomialEvaluation values (MvPolynomial.X v) = values v := by
  simp [polynomialEvaluation]

@[simp] theorem polynomialEvaluation_add (values : Jet → ℂ) (P Q : Poly) :
    polynomialEvaluation values (P + Q) =
      polynomialEvaluation values P + polynomialEvaluation values Q :=
  map_add (polynomialEvaluation values) P Q

@[simp] theorem polynomialEvaluation_mul (values : Jet → ℂ) (P Q : Poly) :
    polynomialEvaluation values (P * Q) =
      polynomialEvaluation values P * polynomialEvaluation values Q :=
  map_mul (polynomialEvaluation values) P Q

@[simp] theorem spatialD_C (a : ℤ) :
    spatialD (MvPolynomial.C a) = 0 := by
  exact spatialD.map_algebraMap a

end NlsGge.HierarchyRiccati.Core
