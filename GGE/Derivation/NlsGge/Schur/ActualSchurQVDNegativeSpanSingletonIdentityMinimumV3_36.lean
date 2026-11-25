import NlsGge.Schur.ActualSchurSourceRingInverseFDerivMinimumV6_35
import NlsGge.Schur.ActualSchurCLMExplicitAlgebraTowerMulLeftRightMinimumV3_36

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The scalar-negative span-singleton conversion used by the actual
complementary-QVD derivative, with the actual parent lets retained in the
proof context and the additive group on scalar-to-endomorphism CLMs made
explicit. -/
theorem actualSchurQVDNegativeSpanSingletonIdentityMinimumV3_36
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
    ∀ (a : E),
      -ContinuousLinearMap.toSpanSingleton ℂ a =
        ContinuousLinearMap.toSpanSingleton ℂ (-a) := by
  intro E
  intro nr
  intro un
  intro na
  intro alg
  intro ns
  intro unSeminormed
  intro tower
  intro smulComm
  intro a
  let clmAdd : AddCommGroup (ℂ →L[ℂ] E) := inferInstance
  letI : AddCommGroup (ℂ →L[ℂ] E) := clmAdd
  have hsum :
      ContinuousLinearMap.toSpanSingleton ℂ a +
        ContinuousLinearMap.toSpanSingleton ℂ (-a) = 0 := by
    calc
      _ = ContinuousLinearMap.toSpanSingleton ℂ (a + -a) := by
        rw [← ContinuousLinearMap.toSpanSingleton_add]
      _ = 0 := by rw [add_neg_cancel, ContinuousLinearMap.toSpanSingleton_zero]
  exact (neg_eq_iff_add_eq_zero).2 hsum

end NlsGge.Schur
