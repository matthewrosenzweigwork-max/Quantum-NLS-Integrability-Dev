                                                                                                                                                                                                                   
                                                                                                     
                                                                                                              
                                                                                                            
                                                                                                   
import Mathlib
import NlsGge.Birkhoff.SignedMoments38b

set_option autoImplicit false

open MeasureTheory NlsGge.Pilot NlsGge.Birkhoff
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.T
noncomputable section

private theorem t021_amgm_nonneg (b : ℝ) (hb : 0 ≤ b) (j : ℕ) :
    b ^ (2 * j + 1) ≤ (b ^ (2 * j) + b ^ (2 * j + 2)) / 2 := by
  have key : 0 ≤ b ^ (2 * j) * (1 - b) ^ 2 := mul_nonneg (pow_nonneg hb _) (sq_nonneg _)
  have hp1 : b ^ (2 * j + 1) = b ^ (2 * j) * b := pow_succ _ _
  have hp2 : b ^ (2 * j + 2) = b ^ (2 * j) * b ^ 2 := by ring
  rw [hp1, hp2]
  nlinarith [key]

private theorem t021_abs_pow_le (a : ℝ) (j : ℕ) :
    |a ^ (2 * j + 1)| ≤ (a ^ (2 * j) + a ^ (2 * j + 2)) / 2 := by
  have hb0 : 0 ≤ |a| := abs_nonneg a
  have h := t021_amgm_nonneg |a| hb0 j
  have e0 : |a| ^ (2 * j) = a ^ (2 * j) := (Even.pow_abs ⟨j, by ring⟩ a)
  have e2 : |a| ^ (2 * j + 2) = a ^ (2 * j + 2) := (Even.pow_abs ⟨j + 1, by ring⟩ a)
  rw [abs_pow, ← e0, ← e2]
  exact h

theorem oddSpectralMoment_adjacent_bound
    (u : PhysicalL2) (j : ℕ)
    (h0 : Integrable (fun x : ℝ =>
      (2 * x) ^ (2 * j) * actualGapHeightE02_38 u x))
    (h2 : Integrable (fun x : ℝ =>
      (2 * x) ^ (2 * j + 2) * actualGapHeightE02_38 u x)) :
    Integrable (fun x : ℝ =>
      (2 * x) ^ (2 * j + 1) * actualGapHeightE02_38 u x) ∧
    |signedSpectralMoment38 u (2 * j + 1)| ^ 2 ≤
      signedSpectralMoment38 u (2 * j) *
        signedSpectralMoment38 u (2 * j + 2) ∧
    |signedSpectralMoment38 u (2 * j + 1)| ≤
      (signedSpectralMoment38 u (2 * j) +
        signedSpectralMoment38 u (2 * j + 2)) / 2 := by
  have hm : AEStronglyMeasurable (fun x : ℝ =>
      (2 * x) ^ (2 * j + 1) * actualGapHeightE02_38 u x) volume := by
    have hc : AEStronglyMeasurable (fun x : ℝ => 2 * x) volume :=
      (by fun_prop : Continuous fun x : ℝ => 2 * x).aestronglyMeasurable
    have hm0 : AEStronglyMeasurable (fun x : ℝ =>
        (2 * x) * ((2 * x) ^ (2 * j) * actualGapHeightE02_38 u x)) volume :=
      hc.mul h0.aestronglyMeasurable
    exact hm0.congr (Filter.Eventually.of_forall fun x => by dsimp only; ring)
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖(2 * x) ^ (2 * j + 1) * actualGapHeightE02_38 u x‖ ≤
        ((2 * x) ^ (2 * j) * actualGapHeightE02_38 u x +
          (2 * x) ^ (2 * j + 2) * actualGapHeightE02_38 u x) / 2 :=
    Filter.Eventually.of_forall fun x => by
      have hv := actualGapHeightE02_38_nonneg u x
      have hA := t021_abs_pow_le (2 * x) j
      calc ‖(2 * x) ^ (2 * j + 1) * actualGapHeightE02_38 u x‖
          = |(2 * x) ^ (2 * j + 1)| * actualGapHeightE02_38 u x := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv]
        _ ≤ ((2 * x) ^ (2 * j) + (2 * x) ^ (2 * j + 2)) / 2 *
              actualGapHeightE02_38 u x :=
            mul_le_mul_of_nonneg_right hA hv
        _ = ((2 * x) ^ (2 * j) * actualGapHeightE02_38 u x +
              (2 * x) ^ (2 * j + 2) * actualGapHeightE02_38 u x) / 2 := by ring
  have h1 : Integrable (fun x : ℝ =>
      (2 * x) ^ (2 * j + 1) * actualGapHeightE02_38 u x) :=
    Integrable.mono' ((h0.add h2).div_const 2) hm hbound
  refine ⟨h1, ?_, ?_⟩
  · rw [sq_abs]
    exact signedSpectral_cs38 u j h0 h1 h2
  · have h := signedSpectral_amgm38 u j h0 h1 h2
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at h

end
end NlsGge.ThirdConsultation.T
