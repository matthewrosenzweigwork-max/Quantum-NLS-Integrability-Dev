import Mathlib
import NlsGge.Composition.Bilinear

                                                                                                                                                                                                                                                                              

set_option autoImplicit false

open AddCircle

namespace NlsGge.Atomic.R085

theorem term_eq_expSum {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    (B : X →L[ℝ] Y →L[ℝ] Z) (k l : ℤ) (x : X) (y : Y) (θ : AddCircle (1 : ℝ)) :
    B (fourier k θ • x) (fourier l θ • y) =
      NlsGge.Composition.expSum (NlsGge.Composition.termCoeffs B k l x y) θ :=
  congrFun (NlsGge.Composition.term_eq_expSum B k l x y) θ

end NlsGge.Atomic.R085
