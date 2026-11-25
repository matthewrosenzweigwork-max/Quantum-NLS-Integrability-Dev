import NlsGge.Schur.CoveredH1ParityPairOperatorFromAE
import NlsGge.Schur.FreeResolvent

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The actual free complementary diagonal transported to the paired physical
parity Hilbert space. -/
def freeResolventParityPair (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
    ((freeResolventSquare n z hz).comp
      (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The actual resonant projection transported to the paired physical parity
Hilbert space. -/
def resonantParityPair (n : ℤ) : ParityPair n →L[ℂ] ParityPair n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
    ((resonantSquare n).comp
      (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap)

/-- D V P for the two independent actual H¹ potentials on the actual parity
pair space. -/
def freeResolventPotentialColumn (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (freeResolventParityPair n z hz).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp (resonantParityPair n))

/-- P V D for the two independent actual H¹ potentials on the actual parity
pair space. -/
def resonantPotentialFreeResolventRow (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (resonantParityPair n).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      (freeResolventParityPair n z hz))

/-- D V D, with the source operator order and both independently quantified
potential fields retained. -/
def freeResolventPotentialFreeResolvent (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (freeResolventParityPair n z hz).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      (freeResolventParityPair n z hz))

end NlsGge.Schur
