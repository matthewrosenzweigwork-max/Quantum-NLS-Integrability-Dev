import QuantumNLS.TerraMultiRound80LowBound
import QuantumNLS.TerraMultiRound80MiddleBound
import QuantumNLS.TerraMultiRound80UpperBound
import QuantumNLS.TerraMultiRound80EndpointBound

/-! Bounded-set control of the physical shifted moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound80PhysicalBound
variable {L : ℝ} [Fact (0 < L)]

theorem physical_power_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, (∫ x : ℝ, |x|^(2*s) ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ M := by
  by_cases hlow : s < 1/2
  · exact QuantumNLS.TerraMultiRound80LowBound.low_physical_power_bounded κ hκ s hs0 hlow B hB
  · by_cases hmiddle : s < 1
    · exact QuantumNLS.TerraMultiRound80MiddleBound.middle_physical_power_bounded κ hκ s (by linarith) hmiddle B hB
    · by_cases h1 : s = 1
      · subst s
        exact QuantumNLS.TerraMultiRound80EndpointBound.physical_one_bounded κ hκ B hB
      · by_cases h2 : s = 2
        · subst s
          exact QuantumNLS.TerraMultiRound80EndpointBound.physical_two_bounded κ hκ B hB
        · exact QuantumNLS.TerraMultiRound80UpperBound.upper_physical_power_bounded κ hκ s (lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm h1)) (lt_of_le_of_ne hs2 h2) B hB

theorem shifted_weight_le_mass_and_power (p x : ℝ) (hp : 0 ≤ p) :
    (1+|x|)^p ≤ (2:ℝ)^p * (1+|x|^p) := by
  have hA : 0 ≤ (2:ℝ)^p := by positivity
  have hx : 0 ≤ |x|^p := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hx1 : |x| ≤ 1
  · have hh := Real.rpow_le_rpow (show 0 ≤ 1+|x| by positivity) (show 1+|x| ≤ 2 by linarith) hp
    nlinarith [mul_nonneg hA hx]
  · have hh := Real.rpow_le_rpow (show 0 ≤ 1+|x| by positivity) (show 1+|x| ≤ 2*|x| by linarith) hp
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg x)] at hh
    nlinarith

theorem shifted_physical_bounded (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (B : Set (H02 L s)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ B, (∫⁻ t : ℝ, ENNReal.ofReal ((1+|t|)^(2*s))
      ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ≤ ENNReal.ofReal M := by
  obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨P, hP⟩ := physical_power_bounded κ hκ s hs0 hs2 B hB
  let A : ℝ := (2:ℝ)^(2*s)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let M : ℝ := A * ((max K 0)^2 + max P 0)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro u hu
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
    infer_instance
  have hsft : Integrable (fun t : ℝ => (1+|t|)^(2*s)) μ :=
    ((QuantumNLS.TerraMultiRound79Characterization.closed_interval_characterization κ hκ u.val s hs0.le hs2).1).mp ⟨u, rfl⟩
  have hbare : Integrable (fun t : ℝ => |t|^(2*s)) μ :=
    (QuantumNLS.TerraMultiRound78Characterization.full_interval_characterization κ hκ u.val s hs0 hs2).1.mpr ⟨u, rfl⟩
  have hconst : Integrable (fun _ : ℝ => (1:ℝ)) μ := integrable_const 1
  have hbound := integral_mono hsft ((hconst.add hbare).const_mul A) (fun t => shifted_weight_le_mass_and_power (2*s) t (by positivity))
  have hmass : (∫ _t : ℝ, (1:ℝ) ∂μ) = ‖u.val‖^2 := by
    simp only [integral_const, measureReal_def, smul_eq_mul, mul_one]
    exact (QuantumNLS.TerraMultiRound68Endpoints.endpoint_results L κ hκ).1 u.val |>.1
  rw [integral_const_mul] at hbound
  simp only [Pi.add_apply] at hbound
  rw [integral_add hconst hbare, hmass] at hbound
  have hnorm : ‖u.val‖ ≤ max K 0 :=
    (WField.norm_val_le (fun n => one_le_def002 L hs0.le n) u).trans ((hK u hu).trans (le_max_left _ _))
  have hnorm2 : ‖u.val‖^2 ≤ (max K 0)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hpbound : (∫ t : ℝ, |t|^(2*s) ∂μ) ≤ max P 0 := (hP u hu).trans (le_max_left _ _)
  have hreal : (∫ t : ℝ, (1+|t|)^(2*s) ∂μ) ≤ M := by
    dsimp [M]
    exact hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hnorm2 hpbound) hA)
  have hnonneg : ∀ᵐ t ∂μ, 0 ≤ (1+|t|)^(2*s) := by
    apply ae_of_all; intro t; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hsft hnonneg]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms physical_power_bounded
#print axioms shifted_weight_le_mass_and_power
#print axioms shifted_physical_bounded
end QuantumNLS.TerraMultiRound80PhysicalBound
