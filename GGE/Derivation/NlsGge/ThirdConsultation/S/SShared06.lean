import Mathlib
import NlsGge.Schur.ActualSchurEffectiveDerivativeActual38V1
import NlsGge.Schur.ActualSchurPotentialVariation38V1
import NlsGge.Schur.ActualSchurElimination38V1
import NlsGge.Schur.ActualSchurRootMultiplicity38V1
import NlsGge.Schur.ActualSchurBallMapJacobian38V1
import NlsGge.Schur.ActualSchurBallFullEnergy38V1
import NlsGge.Hierarchy.UniformPartitionBound38
import NlsGge.Atomic.S.S039
import NlsGge.Atomic.S.S073

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open Matrix
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

abbrev SchurH1 := WeightedHilbert (sobolevModeWeight (1 : ℝ))
abbrev SchurPair := ActualSchurEffectiveH1PairV3_30

def schurRealPair (w : SchurH1) : SchurPair := (w, actualH1Conj38 w)

def schurParameterDomain (K R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair) : Prop :=
  1 ≤ R ∧ n ≠ 0 ∧ K * R ^ 2 ≤ |(n : ℝ)| ∧
    z ∈ spectralDisk n ∧ ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R

/-- Computational family used only with a proved valid-domain identity to R_n. -/
def resolventFamily (n : ℤ) (z : ℂ) (p : SchurPair) :
    ParityPair n →L[ℂ] ParityPair n :=
  actualSchurResolventFamilyAfterDextV3_32 n p z

def potentialAt (n : ℤ) (p : SchurPair) : ParityPair n →L[ℂ] ParityPair n :=
  actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p

def greenColumn (n : ℤ) (z : ℂ) (p : SchurPair) : ParityPair n →L[ℂ] ParityPair n :=
  (resolventFamily n z p).comp ((potentialAt n p).comp (resonantParityPair n))

def greenRow (n : ℤ) (z : ℂ) (p : SchurPair) : ParityPair n →L[ℂ] ParityPair n :=
  (resonantParityPair n).comp ((potentialAt n p).comp (resolventFamily n z p))

def effectiveAt (n : ℤ) (z : ℂ) (p : SchurPair) : ParityPair n →L[ℂ] ParityPair n :=
  actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)

def entryAt (n : ℤ) (i j : Bool) (z : ℂ) (p : SchurPair) : ℂ :=
  actualSchurCoefficientAfterDext31 n (i, resonantIndex n) (j, resonantIndex n) (z, p)

def alphaAt (n : ℤ) (z : ℂ) (p : SchurPair) : ℂ := entryAt n true true z p

def bAt (n : ℤ) (z : ℂ) (p : SchurPair) : ℂ := entryAt n true false z p

def cAt (n : ℤ) (z : ℂ) (p : SchurPair) : ℂ := entryAt n false true z p

def centerMapAt (n : ℤ) (p : SchurPair) (z : ℂ) : ℂ := spectralCenter n + alphaAt n z p

def centerAt (R : ℝ) (n : ℤ) (p : SchurPair) : ℂ := actualSchurCenter38 R n p

def qAt (R : ℝ) (n : ℤ) (p : SchurPair) : ℂ := actualSchurQn38 R n p

def realQAt (R : ℝ) (n : ℤ) (w : SchurH1) : ℂ := qAt R n (schurRealPair w)

def qRemainderAt (R : ℝ) (n : ℤ) (w : SchurH1) : ℂ := realQAt R n w - w n

def scalarRootAt (n : ℤ) (w : SchurH1) (r : ℝ) : ℝ :=
  r - Real.pi * n - (alphaAt n (r : ℂ) (schurRealPair w)).re

def gapParameter (R : ℝ) (n : ℤ) : ℝ := actualSchurGapParameter38 R n

def reflectedEndsAt (n : ℤ) (w : SchurH1) : ℝ × ℝ :=
  (-actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n),
    -actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n))

def reflectedActionAt (n : ℤ) (w : SchurH1) : ℝ :=
  actualGapActionAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)


def ownDirection (n : ℤ) : SchurPair := (actualH1ModeVector38 n, 0)

def ownDerivative (F : SchurPair → ℂ) (n : ℤ) (p : SchurPair) : ℂ :=
  fderiv ℂ F p (ownDirection n)

def ownWirtinger (F : SchurH1 → ℂ) (n : ℤ) (w : SchurH1) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F w (actualH1ModeVector38 n) -
    Complex.I * fderiv ℝ F w (Complex.I • actualH1ModeVector38 n))

/-- The actual coordinate free domain and perturbed Dirac equation. -/
def diracKernelAt (n : ℤ) (z : ℂ) (p : SchurPair) :
    Submodule ℂ (freeWeightedDomainPointwise n) :=
  LinearMap.ker (freeShiftedCoordinateDirac n z -
    (actualSchurCoordinatePotential38 n p).toLinearMap.comp
      (freeWeightedDomainPointwise n).subtype)

def resonantSpaceAt (n : ℤ) : Submodule ℂ (SectorSquare n) :=
  (resonantSquare n).toLinearMap.range

def effectiveKernelAt (n : ℤ) (z : ℂ) (p : SchurPair) :
    Submodule ℂ (resonantSpaceAt n) :=
  LinearMap.ker
    ((((z - spectralCenter n) • LinearMap.id) -
        (actualSchurEndomorphismToSquareV5_30 n (effectiveAt n z p)).toLinearMap).comp
      (resonantSpaceAt n).subtype)

/-- Numerical threshold conditions only; no claimed analytic theorem is assumed. -/
def schurNumericConditions (R : ℝ) (n : ℤ) : Prop :=
  1 ≤ |(n : ℝ)| ∧
    actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)| ∧
    actualSchurShiftedRootsConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)| ∧
    gapParameter (4 * R) n ≤ (1 / 4 : ℝ)

def schurAllThreshold : ℝ :=
  512 * (1 + |schurCommonThreshold| + |actualSchurCenterThresholdConstant38| +
    |actualSchurShiftedRootsConstant38| + |actualSchurGapLocalConstant38| +
    |freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2|)

def splitCutoff (A R : ℝ) : ℕ := ⌈A * R ^ 6⌉₊

def rhoAt (C R : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-C * (R ^ 3 / |(n : ℝ)| ^ (3 / 2 : ℝ) + R ^ 4 / |(n : ℝ)| ^ 2))

def relativeBallIntegralV6 {lo up : ℝ} (c : BoundedCoefficients lo up)
    (N : ℕ) (R : ℝ) : ℝ :=
  (∫ z in schurH1Ball N R, Real.exp (-fullEnergy38 c N z) ∂planeVolume N) /
    freeNormalizer38 c N

def lowerWeightV6 (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' j : ℕ, NlsGge.coefficient c (j + 1) * r ^ (2 * j)

def Q2At (N : ℕ) (z : FourierPlane N) : ℝ := localCharge38 (planeReal N z) 1

def shiftedRateV6 {lo up : ℝ} (c : BoundedCoefficients lo up) (n : ℤ) : ℝ :=
  NlsGge.Measure.fullWeightRate (shiftedCoefficients38 c).val n

def reservedRateV6 {lo up : ℝ} (c : BoundedCoefficients lo up) (n : ℤ) : ℝ :=
  lowerWeightV6 c.val (2 * Real.pi * (n : ℝ))

def shellLevelV6 (g R₀ : ℝ) (k : ℕ) : ℝ :=
  if (k : ℝ) < R₀ then 0 else g * Real.exp (g * (k : ℝ) ^ (1 / 4 : ℝ))

/-- Literal analytic/real-type input data, never a root-order conclusion. -/
def EntryDerivativeBoundsV6 (g₁ g₂ b e : ℂ → ℂ) (z : ℂ) (d : ℝ) : Prop :=
  AnalyticAt ℂ g₁ z ∧ AnalyticAt ℂ g₂ z ∧ AnalyticAt ℂ b z ∧ AnalyticAt ℂ e z ∧
    ‖deriv g₁ z - 1‖ ≤ d ∧ ‖deriv g₂ z - 1‖ ≤ d ∧
    ‖deriv b z‖ ≤ d ∧ ‖deriv e z‖ ≤ d

def RealTypeRootDataV6 (g₁ g₂ b e : ℂ → ℂ) (r β d : ℝ) : Prop :=
  EntryDerivativeBoundsV6 g₁ g₂ b e (r : ℂ) d ∧
    g₁ r = g₂ r ∧
    g₁ r * g₂ r - b r * e r = 0 ∧
    ‖g₁ r‖ = β ∧ ‖b r‖ = β ∧ ‖e r‖ = β

/-- A literal source root/multiplicity assertion used ONLY as the theorem conclusion. -/
def RealTypeTwoRootMultiplicityV6 (f : ℂ → ℂ) (s : Set ℂ) (ends : ℝ × ℝ) : Prop :=
  ends.1 ≤ ends.2 ∧ (ends.1 : ℂ) ∈ s ∧ (ends.2 : ℂ) ∈ s ∧
    (∀ z ∈ s, f z = 0 ↔ z = (ends.1 : ℂ) ∨ z = (ends.2 : ℂ)) ∧
    AnalyticAt ℂ f (ends.1 : ℂ) ∧ AnalyticAt ℂ f (ends.2 : ℂ) ∧
    (ends.1 < ends.2 → analyticOrderAt f (ends.1 : ℂ) = 1 ∧
      analyticOrderAt f (ends.2 : ℂ) = 1) ∧
    (ends.1 = ends.2 → analyticOrderAt f (ends.1 : ℂ) = 2)

def ownReflectIndexV6 (n : ℤ) (m : Sector n) : Sector n := reflectIndex n m

def prodFactorsV6 (M N : ℕ) (R : ℝ) (ρ a : ℤ → ℝ) (z : FourierPlane N) : ℝ :=
  ∏ i : Fin (2 * N + 1),
    if (modeIndex N i).natAbs ≤ M then (if ‖z i‖ < R then 1 else 0)
    else Real.exp (-(ρ (modeIndex N i) * a (modeIndex N i) * ‖z i‖ ^ 2))

def operatorResolventAt (n : ℤ) (z : ℂ) (V : ParityPair n →L[ℂ] ParityPair n) :
    ParityPair n →L[ℂ] ParityPair n :=
  let D := actualFreeResolventCenterExtensionV1_30 n z
  let Q := freeResolventComplementaryProjectionTransported n
  D.comp (Ring.inverse (1 - Q.comp (V.comp D)))

def operatorEffectiveAt (n : ℤ) (z : ℂ) (V : ParityPair n →L[ℂ] ParityPair n) :
    ParityPair n →L[ℂ] ParityPair n :=
  let P := resonantParityPair n
  P.comp (V.comp P) + P.comp (V.comp ((operatorResolventAt n z V).comp (V.comp P)))

def shellMajorantTermV6 (C g ε : ℝ) (k : ℕ) : ℝ :=
  Real.exp (C * ((k : ℝ) + 2) ^ 9 - ε * g * Real.exp (g * (k : ℝ) ^ (1 / 4 : ℝ)))

def shellMajorantThresholdV6 (C g ε : ℝ) : ℕ :=
  max 1 ⌈(3 ^ 9 * C + 1) / (ε * g ^ 41 / (Nat.factorial 40 : ℝ))⌉₊

def euclideanVectorNormV6 {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i : ι, (v i) ^ 2)

end NlsGge.ThirdConsultation.S
