import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G6.Energy031A

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.GKDefinitionDesign

theorem embed1_physicalSobolev (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    physicalSobolev 1 (physicalSobolevEmbed 1 u) := by
  unfold physicalSobolev SobolevSquareSummable
  have hz := (mem_seqSobolev38_iff ((1 : ℕ) : ℝ) _).1
    (carrierCoe38_mem ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u))
  have hfun : (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * 1) *
      ‖(reflectedFourierL2 (physicalSobolevEmbed 1 u)) n‖ ^ 2) =
      fun n : ℤ => Real.rpow (japaneseBracket n) (2 * ((1 : ℕ) : ℝ)) *
        ‖carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) n‖ ^ 2 := by
    funext n
    have hexp : Real.rpow (japaneseBracket n) (2 * 1) =
        Real.rpow (japaneseBracket n) (2 * ((1 : ℕ) : ℝ)) := by norm_num
    have hc : (reflectedFourierL2 (physicalSobolevEmbed 1 u)) n =
        carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u) n :=
      physicalSobolevEmbed_fourier 1 u n
    rw [hexp, hc]
  rw [hfun]
  exact hz

theorem integral_norm_sq_eq_norm_sq (g : PhysicalL2) :
    ∫ x : PhysicalCircle, ‖g x‖ ^ 2 ∂spatialMeasure = ‖g‖ ^ 2 := by
  have h1 : ‖g‖ ^ 2 = RCLike.re (inner ℂ g g) := (inner_self_eq_norm_sq (𝕜 := ℂ) g).symm
  have h2 : inner ℂ g g = ∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure :=
    L2.inner_def g g
  have hint : Integrable (fun a : PhysicalCircle => inner ℂ (g a) (g a)) spatialMeasure :=
    L2.integrable_inner g g
  have h3 : RCLike.re (∫ a : PhysicalCircle, inner ℂ (g a) (g a) ∂spatialMeasure) =
      ∫ a : PhysicalCircle, RCLike.re (inner ℂ (g a) (g a)) ∂spatialMeasure :=
    (integral_re hint).symm
  rw [h1, h2, h3]
  apply integral_congr_ae
  filter_upwards with a
  rw [inner_self_eq_norm_sq (𝕜 := ℂ)]

theorem deriv_coeff_norm_sq (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    ‖fourierSeq38 (physicalSobolevDerivative38 1 u) n‖ ^ 2 =
      (2 * Real.pi * (n : ℝ)) ^ 2 * ‖fourierSeq38 (physicalSobolevEmbed 1 u) n‖ ^ 2 := by
  rw [physicalSobolevDerivative38_reflected, pow_one, ← physicalSobolevEmbed_fourier 1 u n, norm_mul,
    mul_pow]
  congr 1
  have e : ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  rw [e, mul_pow, sq_abs]; ring

theorem energy_quad_summable (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 *
      ‖fourierSeq38 (physicalSobolevEmbed 1 u) n‖ ^ 2) := by
  have h := (mem_seqSobolev38_iff 0 _).1 (fourierSeq38_mem_zero (physicalSobolevDerivative38 1 u))
  unfold SobolevSquareSummable at h
  refine (h.congr (fun n => ?_))
  rw [← deriv_coeff_norm_sq]
  simp

theorem energy_quad_eq (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    (∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 *
      ‖fourierSeq38 (physicalSobolevEmbed 1 u) n‖ ^ 2) =
    ‖physicalSobolevDerivative38 1 u‖ ^ 2 := by
  rw [norm_sq_eq_tsum_fourierSeq38]
  exact tsum_congr (fun n => (deriv_coeff_norm_sq u n).symm)

end NlsGge.GKDefinitionDesign
end
