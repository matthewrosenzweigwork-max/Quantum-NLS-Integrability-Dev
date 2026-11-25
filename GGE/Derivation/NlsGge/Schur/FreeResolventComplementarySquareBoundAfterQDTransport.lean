import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries
import NlsGge.Schur.FreeResolventUniformBoundsPackageAfterScalarSqrtPrerequisite
import NlsGge.Schur.FreeResolventComplexHilbertSchmidtOpNormAfterL2Prerequisites
import NlsGge.Schur.CoveredH1ParityPairPotentialNorm
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The actual complementary factor `D V Q` on the paired physical carrier. -/
def freeResolventComplementaryPotentialA
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (freeResolventParityPair n z hz).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      (freeResolventComplementaryProjectionTransported n))

/-- The actual complementary projection is contractive on the physical paired
Hilbert space. -/
theorem freeResolventComplementaryProjectionTransported_norm_le_one (n : ℤ) :
    ‖freeResolventComplementaryProjectionTransported n‖ ≤ 1 := by
  let E := parityPairRepr n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖E.symm (complementarySquare n (E x))‖ ≤ 1 * ‖x‖
  calc
    ‖E.symm (complementarySquare n (E x))‖ =
        ‖complementarySquare n (E x)‖ := E.symm.norm_map _
    _ ≤ ‖complementarySquare n‖ * ‖E x‖ :=
      (complementarySquare n).le_opNorm _
    _ ≤ 1 * ‖x‖ := by
      rw [E.norm_map]
      gcongr
      exact complementarySquare_norm_le_one n

/-- Actual diagonal range property from the separately checked transported
coordinate identity. -/
theorem freeResolventComplementaryProjectionTransported_comp_freeResolventParityPair
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (freeResolventComplementaryProjectionTransported n).comp
      (freeResolventParityPair n z hz) = freeResolventParityPair n z hz :=
  freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n z hz

/-- On the actual physical pair space, `(D V Q)^2=(D V D)VQ`; the identity
uses the proved range property of the actual diagonal free resolvent. -/
theorem freeResolventComplementaryPotentialA_sq_factorization
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz).comp
        (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz) =
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz).comp
        ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
          (freeResolventComplementaryProjectionTransported n)) := by
  let D := freeResolventParityPair n z hz
  let V := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q := freeResolventComplementaryProjectionTransported n
  apply ContinuousLinearMap.ext
  intro x
  change D (V (Q (D (V (Q x))))) = D (V (D (V (Q x))))
  have hqd : Q (D (V (Q x))) = D (V (Q x)) := by
    have h := congrArg (fun F : ParityPair n →L[ℂ] ParityPair n => F (V (Q x)))
      (freeResolventComplementaryProjectionTransported_comp_freeResolventParityPair n z hz)
    simpa [D, Q, ContinuousLinearMap.comp_apply] using h
  exact congrArg (fun y : ParityPair n => D (V y)) hqd

/-- The fixed source-shaped constant in the two-block H¹ ball estimate. -/
def freeResolventSchurUniformConstant : ℝ :=
  max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant)

/-- Actual square-smallness for `A=D V Q` from the checked source H¹-ball
estimates. All signed indices, disk points, and the two independent potentials
are retained; the threshold is the explicit consequence of the uniform
constants. -/
theorem freeResolventComplementaryPotentialA_square_norm_le_half
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ‖(freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz).comp
        (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz)‖ ≤
      (1 / 2 : ℝ) := by
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let DVD : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
  have hC : 0 ≤ freeResolventSchurUniformConstant := by
    dsimp [freeResolventSchurUniformConstant]
    positivity
  have hCV : 0 ≤ physicalH1MultiplierConstant :=
    physicalH1MultiplierConstant_pos.le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hden : 0 < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn0)
  have hpack := freeResolventPotential_uniform_bounds_on_h1_ball
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hDVDhs : complexHilbertSchmidtNorm DVD ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change complexHilbertSchmidtNorm DVD ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)|
    exact hpack.2
  have hDVDhsMem : IsComplexHilbertSchmidt DVD := by
    change IsComplexHilbertSchmidt
      (freeResolventPotentialFreeResolventOperator u₁ u₂ hu₁ hu₂ n z hz)
    exact (freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
      u₁ u₂ hu₁ hu₂ n z hz).1
  have hDVDop : ‖DVD‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    exact (complexHilbertSchmidt_opNorm_le DVD hDVDhsMem).trans hDVDhs
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 hball₁ hball₂
  have hQ : ‖Q‖ ≤ 1 := freeResolventComplementaryProjectionTransported_norm_le_one n
  have hfactor :
      (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz).comp
          (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz) =
        DVD.comp (V.comp Q) := by
    simpa [V, Q, DVD] using
      freeResolventComplementaryPotentialA_sq_factorization u₁ u₂ hu₁ hu₂ n z hz
  have hprod :
      ‖(freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz).comp
          (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz)‖ ≤
        ‖DVD‖ * ‖V‖ * ‖Q‖ := by
    rw [hfactor]
    calc
      ‖DVD.comp (V.comp Q)‖ ≤ ‖DVD‖ * ‖V.comp Q‖ :=
        DVD.opNorm_comp_le (V.comp Q)
      _ ≤ ‖DVD‖ * (‖V‖ * ‖Q‖) :=
        mul_le_mul_of_nonneg_left (V.opNorm_comp_le Q) (norm_nonneg DVD)
      _ = ‖DVD‖ * ‖V‖ * ‖Q‖ := by ring
  have hprod' : ‖DVD‖ * ‖V‖ * ‖Q‖ ≤
      (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
        (2 * physicalH1MultiplierConstant * R) * 1 := by
    calc
      ‖DVD‖ * ‖V‖ * ‖Q‖ ≤
          (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
            ‖V‖ * ‖Q‖ := by
              gcongr
      _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
            (2 * physicalH1MultiplierConstant * R) * ‖Q‖ := by
              gcongr
      _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
            (2 * physicalH1MultiplierConstant * R) * 1 := by
              gcongr
  have hscalar :
      (2 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2) /
          |(n : ℝ)| ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith [hlarge]
  calc
    ‖(freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz).comp
        (freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz)‖ ≤
        ‖DVD‖ * ‖V‖ * ‖Q‖ := hprod
    _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
          (2 * physicalH1MultiplierConstant * R) * 1 := hprod'
    _ = (2 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2) /
          |(n : ℝ)| := by
            field_simp [ne_of_gt hden] <;> ring
    _ ≤ (1 / 2 : ℝ) := hscalar

end NlsGge.Schur
