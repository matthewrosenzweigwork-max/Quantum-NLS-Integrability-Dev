import QuantumNLS.TerraMultiRound48Orthant
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Chebyshev

/-! Integrable exponential moments on finite orthants, for the dominated
convergence step in the correlation Taylor remainder. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound48OrthantMoment

/-- Every nonnegative integer moment of the positive exponential density is
integrable, including the absolute-value extension to the real line. -/
theorem exp_abs_pow_integrable (d : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * |x| ^ d) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ d) (Ioi 0) := by
    have hg := Real.GammaIntegral_convergent (s := (d : ℝ) + 1) (by positivity)
    simpa only [show (d : ℝ) + 1 - 1 = d by ring, Real.rpow_natCast] using hg
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_pos hx]

/-- A single time moment times the full product density is integrable. -/
theorem orthant_coordinate_moment (n d : ℕ) (j : Fin n) :
    Integrable (fun t : Fin n → ℝ =>
      (∏ i, Real.exp (-t i)) * |t j| ^ d)
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  let g : Fin n → ℝ → ℝ := fun i x => Real.exp (-x) * if i = j then |x| ^ d else 1
  have hg : ∀ i, Integrable (g i) (volume.restrict (Ioi (0 : ℝ))) := by
    intro i
    change IntegrableOn (g i) (Ioi (0 : ℝ))
    by_cases hij : i = j
    · simpa only [g, ite_eq_left hij] using exp_abs_pow_integrable d
    · simpa only [g, ite_eq_right hij, mul_one] using integrableOn_exp_neg_Ioi 0
  have h := Integrable.fintype_prod hg
  convert h using 1
  funext t
  change (∏ i, Real.exp (-t i)) * |t j| ^ d =
    ∏ i, (Real.exp (-t i) * if i = j then |t i| ^ d else 1)
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- The moment dominating the fixed-field Taylor remainder is integrable for
all finite orthants and all degrees, including degree zero. -/
theorem orthant_sum_moment (n d : ℕ) :
    Integrable (fun t : Fin n → ℝ =>
      (∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ d)
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  cases d with
  | zero => simpa using TerraMultiRound48Orthant.orthant_exp_integrable n
  | succ d =>
    let G : (Fin n → ℝ) → ℝ := fun t =>
      (n : ℝ) ^ d * ∑ j, ((∏ i, Real.exp (-t i)) * |t j| ^ (d + 1))
    have hG : Integrable G (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
      exact (integrable_finsetSum _ (fun j _ => orthant_coordinate_moment n (d + 1) j)).const_mul _
    apply hG.mono'
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · exact continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp ((continuous_apply i).neg))
      · exact (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)).pow _
    · filter_upwards with t
      have he : 0 ≤ ∏ i : Fin n, Real.exp (-t i) := Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
      have hs : 0 ≤ ∑ i : Fin n, |t i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg he (pow_nonneg hs _))]
      have hp := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
        (f := fun i : Fin n => |t i|) (fun i _ => abs_nonneg _) d
      simp only [Finset.card_univ, Fintype.card_fin] at hp
      calc
        _ ≤ (∏ i : Fin n, Real.exp (-t i)) * ((n : ℝ) ^ d * ∑ i, |t i| ^ (d + 1)) :=
          mul_le_mul_of_nonneg_left hp he
        _ = G t := by
          dsimp [G]
          rw [← Finset.mul_sum]
          ring

#print axioms exp_abs_pow_integrable
#print axioms orthant_coordinate_moment
#print axioms orthant_sum_moment
end QuantumNLS.TerraMultiRound48OrthantMoment
