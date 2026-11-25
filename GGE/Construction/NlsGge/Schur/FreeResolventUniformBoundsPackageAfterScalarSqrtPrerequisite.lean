import NlsGge.Schur.FreeResolventPotentialColumnRowOperatorBoundsAfterScalarNormPrerequisite
import NlsGge.Schur.FreeResolventDVDHilbertSchmidtFromEnergyAlias
import NlsGge.Schur.FreeResolventSqrtInverseModeEnergyPrerequisite

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private def freeResolventPotentialUniformConstant : ℝ :=
  max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant)

/-- The concrete source-shaped uniform package for the two actual resonant
blocks and the actual DVD Hilbert--Schmidt norm. The two complex H¹ fields
remain independent and are bounded separately by the same radius. -/
theorem freeResolventPotential_uniform_bounds_on_h1_ball
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
          freeResolventPotentialUniformConstant * R / |(n : ℝ)| ∧
      complexHilbertSchmidtNorm
        (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) ≤
          freeResolventPotentialUniformConstant * R / |(n : ℝ)| := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hden : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hn0)
  have ha₁ : 0 ≤ ‖physicalSobolevL2 1 u₁ hu₁‖ := norm_nonneg _
  have ha₂ : 0 ≤ ‖physicalSobolevL2 1 u₂ hu₂‖ := norm_nonneg _
  have hcol := freeResolventPotentialColumn_opNorm_bound_from_prerequisites
    u₁ u₂ hu₁ hu₂ n hn0 z hz
  have hrow := resonantPotentialFreeResolventRow_opNorm_bound_from_prerequisites
    u₁ u₂ hu₁ hu₂ n hn0 z hz
  have hcol' :
      ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        (2 * Real.sqrt 2) * R / |(n : ℝ)| := by
    calc
      ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ ≤
          Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) +
            Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := hcol
      _ ≤ Real.sqrt 2 * R / |(n : ℝ)| + Real.sqrt 2 * R / |(n : ℝ)| :=
        add_le_add
          (freeResolvent_sqrt_inverse_mode_energy_le_prerequisite n hn0 R _ hR0 ha₁ hball₁)
          (freeResolvent_sqrt_inverse_mode_energy_le_prerequisite n hn0 R _ hR0 ha₂ hball₂)
      _ = (2 * Real.sqrt 2) * R / |(n : ℝ)| := by ring
  have hrow' :
      ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        (2 * Real.sqrt 2) * R / |(n : ℝ)| := by
    calc
      ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
          Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) +
            Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := hrow
      _ ≤ Real.sqrt 2 * R / |(n : ℝ)| + Real.sqrt 2 * R / |(n : ℝ)| :=
        add_le_add
          (freeResolvent_sqrt_inverse_mode_energy_le_prerequisite n hn0 R _ hR0 ha₁ hball₁)
          (freeResolvent_sqrt_inverse_mode_energy_le_prerequisite n hn0 R _ hR0 ha₂ hball₂)
      _ = (2 * Real.sqrt 2) * R / |(n : ℝ)| := by ring
  have hsource :
      complexHilbertSchmidtNorm
        (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) ≤
        Real.sqrt
          ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
            (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
              ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)) :=
    by
      simpa only [freeResolventPotentialFreeResolventOperator] using
        (freeResolventPotentialFreeResolvent_isComplexHilbertSchmidt_from_matrix_energy
          u₁ u₂ hu₁ hu₂ n z hz).2
  have hsum :
      ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
        ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 ≤ 2 * R ^ 2 := by
    nlinarith [(sq_le_sq₀ ha₁ hR0).2 hball₁, (sq_le_sq₀ ha₂ hR0).2 hball₂]
  have hconstant :
      2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) ≤
        2 * uniformConvolutionConstant / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + (n : ℝ) ^ 2) hden]
    nlinarith [uniformConvolutionConstant_nonneg]
  have hKnonneg : 0 ≤ uniformConvolutionConstant := uniformConvolutionConstant_nonneg
  have hcoeff_nonneg :
      0 ≤ 2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2) := by positivity
  have henergy :
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
          ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) ≤
        (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 := by
    calc
      _ ≤ (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) * (2 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
      _ ≤ (2 * uniformConvolutionConstant / (n : ℝ) ^ 2) * (2 * R ^ 2) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = (2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2 := by
        rw [div_pow, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hKnonneg]
        ring
  have hhs' :
      complexHilbertSchmidtNorm
        (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz) ≤
        2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := by
    calc
      _ ≤ Real.sqrt
          ((2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
            (‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 +
              ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2)) := hsource
      _ ≤ Real.sqrt ((2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt henergy
      _ = 2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
  have hmain :
      ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
          freeResolventPotentialUniformConstant * R / |(n : ℝ)| := by
    calc
      _ ≤ (2 * Real.sqrt 2) * R / |(n : ℝ)| +
          (2 * Real.sqrt 2) * R / |(n : ℝ)| := add_le_add hcol' hrow'
      _ = (4 * Real.sqrt 2) * R / |(n : ℝ)| := by ring
      _ ≤ freeResolventPotentialUniformConstant * R / |(n : ℝ)| := by
        dsimp [freeResolventPotentialUniformConstant]
        calc
          (4 * Real.sqrt 2) * R / |(n : ℝ)| =
              (4 * Real.sqrt 2) * (R / |(n : ℝ)|) := by ring
          _ ≤ max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant) *
                (R / |(n : ℝ)|) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (div_nonneg hR0 (abs_nonneg _))
          _ = max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant) *
                R / |(n : ℝ)| := by ring
  constructor
  · exact hmain
  · calc
      _ ≤ 2 * Real.sqrt uniformConvolutionConstant * R / |(n : ℝ)| := hhs'
      _ ≤ freeResolventPotentialUniformConstant * R / |(n : ℝ)| := by
        dsimp [freeResolventPotentialUniformConstant]
        calc
          (2 * Real.sqrt uniformConvolutionConstant) * R / |(n : ℝ)| =
              (2 * Real.sqrt uniformConvolutionConstant) * (R / |(n : ℝ)|) := by ring
          _ ≤ max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant) *
                (R / |(n : ℝ)|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _)
              (div_nonneg hR0 (abs_nonneg _))
          _ = max (4 * Real.sqrt 2) (2 * Real.sqrt uniformConvolutionConstant) *
                R / |(n : ℝ)| := by ring

end NlsGge.Schur
