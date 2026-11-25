import NlsGge.Schur.ActualSchurCLMUnitMonoidParentTransportMinimumV3_34
import NlsGge.Schur.ActualSchurCLMUnitsAndParentedInverseValueMinimumV2_35
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Isolate the scalar-algebra dictionary and the exact multiplication CLM used
by the pinned inverse formula on the actual parity-pair endomorphisms. The
chosen algebra is explicitly the Algebra parent of the actual CLM NormedAlgebra;
the scalar-action identity records that it acts on operators pointwise. -/
theorem actualSchurCLMExplicitAlgebraTowerMulLeftRightMinimumV3_36
    (n : ℤ) :
    let E : Type := ParityPair n →L[ℂ] ParityPair n
    let nr : NormedRing E := ContinuousLinearMap.toNormedRing
    letI : NormedRing E := nr
    let un : NonUnitalNormedRing E := nr.toNonUnitalNormedRing
    letI : NonUnitalNormedRing E := un
    letI : NormedAddCommGroup E := un.toNormedAddCommGroup
    let na : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
    letI : NormedAlgebra ℂ E := na
    let alg : Algebra ℂ E := na.toAlgebra
    letI : Algebra ℂ E := alg
    let ns : NormedSpace ℂ E := NormedAlgebra.toNormedSpace E
    letI : NormedSpace ℂ E := ns
    let unSeminormed : NonUnitalSeminormedRing E := un.toNonUnitalSeminormedRing
    let tower : IsScalarTower ℂ E E := inferInstance
    letI : IsScalarTower ℂ E E := tower
    let smulComm : SMulCommClass ℂ E E := inferInstance
    let mulLR :=
      @ContinuousLinearMap.mulLeftRight ℂ inferInstance E unSeminormed ns tower smulComm
    (∀ (c : ℂ) (f : E) (x : ParityPair n),
      ((algebraMap ℂ E c * f) x) = c • f x) ∧
    (∀ (a b f : E) (x : ParityPair n),
      (mulLR a b f) x = (a * f * b) x) := by
  intro E
  constructor
  · intro c f x
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.algebraMap_apply]
  · intro a b f x
    rfl

end NlsGge.Schur
