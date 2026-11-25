import Mathlib
import NlsGge.Ramer.FiniteDivergenceGrowth

                                                                                                                     
                                                                                     
                             
                                                                                                            
                                                                                                              
                                                                                          
set_option autoImplicit false

open MeasureTheory Filter Real Set
open scoped Topology RealInnerProductSpace ENNReal ContDiff
open NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def C1WithGrowth
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ + ‖fderiv ℝ f x‖ ≤ C*(1+‖x‖)

def SmoothCompactSupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

theorem finite_divergence_duality {d : ℕ}
    {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : C1WithGrowth F) (hφ : SmoothCompactSupport φ) :
    ∫ x, φ x * finiteGaussianDivergence F x
        ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ x, inner ℝ
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)) (F x)
        ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨hF1, C, hC⟩ := hF
  obtain ⟨hφs, hφc⟩ := hφ
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (by exact_mod_cast le_top)
  have hFg : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ 1 := fun x => by
    have := hC x; have := norm_nonneg (fderiv ℝ F x); rw [pow_one]; linarith
  have hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ 1 := fun x => by
    have := hC x; have := norm_nonneg (F x); rw [pow_one]; linarith
  obtain ⟨Bφ, hBφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bφ', hBφ'⟩ := (hφ1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have key := (integral_mul_finiteGaussianDivergence_of_growth hF1 C 1 hFg hDg hφ1 Bφ Bφ'
    (fun x => by simpa using hBφ x) (fun x => hBφ' x)).2.2
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [InnerProductSpace.toDual_symm_apply]

end
end NlsGge.ThirdConsultation.R
