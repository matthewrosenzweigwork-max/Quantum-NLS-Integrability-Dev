import QuantumNLS.TerraMultiRound79MomentTails
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform shifted physical tails at the same Sobolev order. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound79ShiftedTail
variable {L : ℝ} [Fact (0 < L)]

theorem uniform_shifted_physical_tail (κ : ℝ) (hκ : 0 < κ) (s : ℝ)
    (hs0 : 0 < s) (hs2 : s ≤ 2) (u : ℕ → H02 L s) (v : H02 L s)
    (hu : Tendsto u atTop (𝓝 v)) :
    ∀ ε > 0, ∃ R : ℝ, 0 ≤ R ∧ ∀ j,
      (∫⁻ t : ℝ, if R < |t| then ENNReal.ofReal ((1+|t|)^(2*s)) else 0
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val) < ENNReal.ofReal ε := by
  intro ε hε
  let p : ℝ := 2*s
  have hp : 0 < p := by dsimp [p]; positivity
  let A : ℝ := (2:ℝ)^p
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨k, hk⟩ := QuantumNLS.TerraMultiRound79MomentTails.physical_uniform_tail_on_Hs
    κ hκ s hs0 hs2 u v hu (ε / (A+1)) (by positivity)
  obtain ⟨R0, hR0⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hp)) (2*(k:ℝ)+1)
  let R : ℝ := max R0 1
  have hR : 1 ≤ R := le_max_right _ _
  have hRpow : 2*(k:ℝ) < R^p := by
    have hh := hR0 R (le_max_left _ _)
    linarith
  refine ⟨R, by linarith, ?_⟩
  intro j
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val
  let f : ℝ → ℝ := fun t => if 2*(k:ℝ) < |t|^p then |t|^p else 0
  have hpint : Integrable (fun t : ℝ => |t|^p) μ := by
    exact (QuantumNLS.TerraMultiRound78Characterization.full_interval_characterization κ hκ (u j).val s hs0 hs2).1.mpr ⟨u j, rfl⟩
  have hcont : Continuous (fun t : ℝ => |t|^p) := continuous_abs.rpow_const (fun _ => Or.inr hp.le)
  have hset : MeasurableSet {t : ℝ | 2*(k:ℝ) < |t|^p} := measurableSet_lt measurable_const hcont.measurable
  have hfint : Integrable f μ := by
    convert hpint.indicator hset using 1
    funext t
    simp [f, Set.indicator]
  have hfnonneg : ∀ᵐ t ∂μ, 0 ≤ f t := by
    apply ae_of_all
    intro t
    dsimp [f]
    split_ifs <;> positivity
  have hbound : (∫⁻ t : ℝ, if R < |t| then ENNReal.ofReal ((1+|t|)^p) else 0 ∂μ) ≤
      ENNReal.ofReal A * ENNReal.ofReal (∫ t, f t ∂μ) := by
    calc
      _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal A * ENNReal.ofReal (f t) ∂μ := by
        apply lintegral_mono
        intro t
        by_cases ht : R < |t|
        · have habs : 1 ≤ |t| := by linarith
          have hpow : 2*(k:ℝ) < |t|^p := by
            exact lt_of_lt_of_le hRpow (Real.rpow_le_rpow (by linarith) (le_of_lt ht) hp.le)
          have hwt : (1+|t|)^p ≤ A * |t|^p := by
            have hh := Real.rpow_le_rpow (show 0 ≤ 1+|t| by positivity)
              (show 1+|t| ≤ 2*|t| by linarith) hp.le
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg t)] at hh
            exact hh
          simp only [if_pos ht, f, if_pos hpow]
          rw [← ENNReal.ofReal_mul hA.le]
          exact ENNReal.ofReal_le_ofReal hwt
        · simp [ht]
      _ = ENNReal.ofReal A * (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal A * ENNReal.ofReal (∫ t, f t ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hfint hfnonneg]
  have htail : (∫ t, f t ∂μ) < ε/(A+1) := by
    simpa only [f, μ, p] using hk j
  have hn : 0 ≤ ∫ t, f t ∂μ := integral_nonneg_of_ae hfnonneg
  have hlt : A * (∫ t, f t ∂μ) < ε := by
    have h := mul_lt_mul_of_pos_left htail hA
    have hden : 0 < A+1 := by positivity
    have hid : A * (ε/(A+1)) < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    linarith
  have he : ENNReal.ofReal A * ENNReal.ofReal (∫ t, f t ∂μ) < ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hA.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hlt
  exact lt_of_le_of_lt hbound he

#print axioms uniform_shifted_physical_tail
end QuantumNLS.TerraMultiRound79ShiftedTail
