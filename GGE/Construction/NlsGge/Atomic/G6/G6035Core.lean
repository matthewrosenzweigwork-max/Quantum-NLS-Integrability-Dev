import Mathlib
import NlsGge.Atomic.G6.G6035Host

                                                                                                                          
                                                                             
                                                                                                                 
                                                                                                                      
                                                                                                               
                                                                                                                
                                                                                                                     
                                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6035S
noncomputable section

theorem w_pos (n : ℤ) : 0 < actionWeight n := sobolevModeWeight_pos 1 n

theorem coe_root (I : PositiveActionSpace) (n : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (positiveActionRoot I) n = (Real.sqrt (actionCoefficient I.val n) : ℂ) := by
  unfold positiveActionRoot
  rw [carrierCoe38_mk]

theorem norm_coe_root_sq (I : PositiveActionSpace) (n : ℤ) :
    ‖carrierCoe38 ((1 : ℕ) : ℝ) (positiveActionRoot I) n‖ ^ 2 = actionCoefficient I.val n := by
  have hc : 0 ≤ actionCoefficient I.val n := div_nonneg (I.2 n) (w_pos n).le
  rw [coe_root, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc]

theorem smw_one (n : ℤ) : sobolevModeWeight ((1 : ℕ) : ℝ) n = actionWeight n := by
  rw [Nat.cast_one]; rfl

theorem actions_root (I : PositiveActionSpace) : coordinateActionsPositive (positiveActionRoot I) = I := by
  apply Subtype.ext
  apply lp.ext
  funext n
  show actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) (positiveActionRoot I) n‖ ^ 2 = I.val n
  rw [norm_coe_root_sq]
  unfold actionCoefficient
  field_simp [(w_pos n).ne']

theorem norm_root (I : PositiveActionSpace) : ‖positiveActionRoot I‖ ^ 2 = weightedActionNorm I.val := by
  have h1 := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (positiveActionRoot I)
  have he : (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) (positiveActionRoot I) n‖ ^ 2) = fun n => ‖I.val n‖ := by
    funext n
    rw [smw_one, norm_coe_root_sq, Real.norm_of_nonneg (I.2 n)]
    unfold actionCoefficient
    field_simp [(w_pos n).ne']
  rw [he] at h1
  have h2 := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) I.val
  simp only [ENNReal.toReal_one, Real.rpow_one] at h2
  unfold weightedActionNorm
  exact h1.unique h2

theorem moduli_root_actions (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 =
      ‖carrierCoe38 ((1 : ℕ) : ℝ) (positiveActionRoot (coordinateActionsPositive z)) n‖ ^ 2 := by
  rw [norm_coe_root_sq]
  show _ = (actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2) / actionWeight n
  field_simp [(w_pos n).ne']

theorem G6035_of
    (h33 : ∀ z w : SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ n : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w n‖^2) →
      transformedNLSHamiltonian z = transformedNLSHamiltonian w) :
  (∀ I : PositiveActionSpace,
    coordinateActionsPositive (positiveActionRoot I) = I ∧
    ‖positiveActionRoot I‖^2 = weightedActionNorm I.val) ∧
  (∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
    transformedNLSHamiltonian z = actionHamiltonian (coordinateActionsPositive z)) ∧
  (∀ (I : PositiveActionSpace) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)),
    coordinateActionsPositive z = I → transformedNLSHamiltonian z = actionHamiltonian I) := by
  have h2 : ∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
      transformedNLSHamiltonian z = actionHamiltonian (coordinateActionsPositive z) :=
    fun z => h33 _ _ (moduli_root_actions z)
  exact ⟨fun I => ⟨actions_root I, norm_root I⟩, h2, fun I z hz => hz ▸ h2 z⟩

end
end NlsGge.ThirdConsultation.G6035S
