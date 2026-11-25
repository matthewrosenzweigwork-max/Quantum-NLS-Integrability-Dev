import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.FreeResolventPotentialBlocks

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- The source-order left Green column built from the actual complementary
QVD inverse on the actual paired carrier. -/
def actualSchurGreenColumnSourceOrderV3_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  exact (D.comp (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
    (V.comp P)

/-- The source-order right Green row built from the same actual complementary
QVD inverse on the actual paired carrier. -/
def actualSchurGreenRowSourceOrderV3_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  exact P.comp (V.comp (D.comp
    (actualComplementaryQVDJointInverseV5_30 n (z, p))))

/-- The actual inverse equality and the actual canonical intertwining identity
transport the source-order left Green column to its bounded factorization.
This isolates only the operator representation bridge; no norm or Green
estimate is assumed. -/
theorem actualSchurGreenColumn_representationBridgeV3_31
    (n : ℤ) (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n)
    (Sleft Sright : ParityPair n →L[ℂ] ParityPair n)
    (hInv : actualComplementaryQVDJointInverseV5_30 n (z, p) = Sright)
    (hshift : Sleft.comp (freeResolventParityPair n z hz) =
      (freeResolventParityPair n z hz).comp Sright) :
    actualSchurGreenColumnSourceOrderV3_31 n z p hz =
      Sleft.comp (freeResolventPotentialColumn
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
        n z hz) := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  change (D.comp (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
      (V.comp P) = _
  rw [hInv]
  calc
    (D.comp Sright).comp (V.comp P) = (Sleft.comp D).comp (V.comp P) := by
      rw [← hshift]
    _ = Sleft.comp (D.comp (V.comp P)) := ContinuousLinearMap.comp_assoc _ _ _

/-- The actual inverse equality transports the source-order right Green row to
the proved `P V D` row operator composed with the actual `QVD` inverse. This
is an operator representation identity, not a norm estimate. -/
theorem actualSchurGreenRow_representationBridgeV3_31
    (n : ℤ) (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n)
    (Sright : ParityPair n →L[ℂ] ParityPair n)
    (hInv : actualComplementaryQVDJointInverseV5_30 n (z, p) = Sright) :
    actualSchurGreenRowSourceOrderV3_31 n z p hz =
      (resonantPotentialFreeResolventRow
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
        n z hz).comp Sright := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  change P.comp (V.comp (D.comp (actualComplementaryQVDJointInverseV5_30 n (z, p)))) = _
  rw [hInv]
  calc
    P.comp (V.comp (D.comp Sright)) =
        P.comp ((V.comp D).comp Sright) := by
          ext x
          rfl
    _ = (P.comp (V.comp D)).comp Sright := by
      ext x
      rfl

end NlsGge.Schur
