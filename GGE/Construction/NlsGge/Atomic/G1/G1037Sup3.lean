import Mathlib
import NlsGge.GK38.PairPotential

                                                                                            
                                                                                                           
                                                                                           
                                                                                                          
                                                                                                        
                                                                              
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g37_alg_cols (M : Matrix (Fin 2) (Fin 2) ℂ) (a a' Φ Φ' : ℂ) (e1 e2 : Fin 2 → ℂ)
    (h1 : M.mulVec ![1, a] = Φ • ![1, a] + e1) (h2 : M.mulVec ![a', 1] = Φ' • ![a', 1] + e2) :
    (M 0 0 + a * M 0 1 = Φ + e1 0) ∧ (M 1 0 + a * M 1 1 = Φ * a + e1 1) ∧
    (a' * M 0 0 + M 0 1 = Φ' * a' + e2 0) ∧ (a' * M 1 0 + M 1 1 = Φ' + e2 1) := by
  have c10 := congrFun h1 0
  have c11 := congrFun h1 1
  have c20 := congrFun h2 0
  have c21 := congrFun h2 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at c10 c11 c20 c21
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination c10
  · linear_combination c11
  · linear_combination c20
  · linear_combination c21

theorem g37_alg_trace (M : Matrix (Fin 2) (Fin 2) ℂ) (a a' Φ Φ' : ℂ) (e1 e2 : Fin 2 → ℂ)
    (h1 : M.mulVec ![1, a] = Φ • ![1, a] + e1) (h2 : M.mulVec ![a', 1] = Φ' • ![a', 1] + e2) :
    (1 - a * a') * (M.trace - Φ - Φ') = e1 0 - a * e2 0 + e2 1 - a' * e1 1 := by
  obtain ⟨q1, q2, q3, q4⟩ := g37_alg_cols M a a' Φ Φ' e1 e2 h1 h2
  rw [Matrix.trace_fin_two]
  linear_combination q1 - a * q3 + q4 - a' * q2

theorem g37_alg_det (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (a a' Φ Φ' : ℂ)
    (e1 e2 : Fin 2 → ℂ)
    (h1 : M.mulVec ![1, a] = Φ • ![1, a] + e1) (h2 : M.mulVec ![a', 1] = Φ' • ![a', 1] + e2) :
    (1 - a * a') * (Φ * Φ' - 1) =
      -(Φ * (e2 1 - a * e2 0) + Φ' * (e1 0 - a' * e1 1) + e1 0 * e2 1 - e1 1 * e2 0) := by
  obtain ⟨q1, q2, q3, q4⟩ := g37_alg_cols M a a' Φ Φ' e1 e2 h1 h2
  rw [Matrix.det_fin_two] at hdet
  have key : (M 0 0 + a * M 0 1) * (a' * M 1 0 + M 1 1) - (M 1 0 + a * M 1 1) * (a' * M 0 0 + M 0 1)
      = 1 - a * a' := by
    linear_combination (1 - a * a') * hdet
  rw [q1, q4, q2, q3] at key
  linear_combination key

theorem g37_norm4 (x y z w : ℂ) : ‖x - y + z - w‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := by
  have h1 := norm_sub_le (x - y + z) w
  have h2 := norm_add_le (x - y) z
  have h3 := norm_sub_le x y
  linarith

theorem g37_norm4' (x y z w : ℂ) : ‖x + y + z - w‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ + ‖w‖ := by
  have h1 := norm_sub_le (x + y + z) w
  have h2 := norm_add_le (x + y) z
  have h3 := norm_add_le x y
  linarith

theorem g37_est (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (a a' Φ Φ' : ℂ)
    (e1 e2 : Fin 2 → ℂ) (e K c0 : ℝ)
    (h1 : M.mulVec ![1, a] = Φ • ![1, a] + e1) (h2 : M.mulVec ![a', 1] = Φ' • ![a', 1] + e2)
    (ha : ‖a‖ ≤ 1 / 2) (ha' : ‖a'‖ ≤ 1 / 2)
    (he1 : ∀ j, ‖e1 j‖ ≤ e) (he2 : ∀ j, ‖e2 j‖ ≤ e) (he0 : 0 ≤ e) (hec : e ≤ c0)
    (hΦ : ‖Φ‖ ≤ K) (hΦ' : ‖Φ'‖ ≤ K) (hΦi : ‖Φ⁻¹‖ ≤ K) (hΦne : Φ ≠ 0) :
    ‖M.trace - (Φ + Φ⁻¹)‖ ≤ (4 + K * (4 * K + 3 * c0)) * e := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hΦ
  have hc0 : 0 ≤ c0 := he0.trans hec
  have haa : ‖a * a'‖ ≤ 1 / 4 := by
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg a']
  have hd : 3 / 4 ≤ ‖1 - a * a'‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a * a')
    rw [norm_one] at this
    linarith
  -- trace
  have tr := g37_alg_trace M a a' Φ Φ' e1 e2 h1 h2
  have trn : ‖e1 0 - a * e2 0 + e2 1 - a' * e1 1‖ ≤ 3 * e := by
    refine (g37_norm4 _ _ _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := he1 0
    have := he1 1
    have := he2 0
    have := he2 1
    nlinarith [norm_nonneg a, norm_nonneg a', norm_nonneg (e1 0), norm_nonneg (e1 1),
      norm_nonneg (e2 0), norm_nonneg (e2 1)]
  have hT : ‖M.trace - Φ - Φ'‖ ≤ 4 * e := by
    have h := congrArg norm tr
    rw [norm_mul] at h
    nlinarith [norm_nonneg (M.trace - Φ - Φ')]
  -- determinant
  have dt := g37_alg_det M hdet a a' Φ Φ' e1 e2 h1 h2
  have e2le : e * e ≤ c0 * e := mul_le_mul_of_nonneg_right hec he0
  have t1 : ‖Φ * (e2 1 - a * e2 0)‖ ≤ K * (e + e / 2) := by
    rw [norm_mul]
    refine mul_le_mul hΦ ?_ (norm_nonneg _) hK
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := he2 1
    have := he2 0
    nlinarith [norm_nonneg a, norm_nonneg (e2 0)]
  have t2 : ‖Φ' * (e1 0 - a' * e1 1)‖ ≤ K * (e + e / 2) := by
    rw [norm_mul]
    refine mul_le_mul hΦ' ?_ (norm_nonneg _) hK
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := he1 0
    have := he1 1
    nlinarith [norm_nonneg a', norm_nonneg (e1 1)]
  have t3 : ‖e1 0 * e2 1‖ ≤ e * e := by
    rw [norm_mul]
    exact mul_le_mul (he1 0) (he2 1) (norm_nonneg _) he0
  have t4 : ‖e1 1 * e2 0‖ ≤ e * e := by
    rw [norm_mul]
    exact mul_le_mul (he1 1) (he2 0) (norm_nonneg _) he0
  have wn : ‖Φ * (e2 1 - a * e2 0) + Φ' * (e1 0 - a' * e1 1) + e1 0 * e2 1 - e1 1 * e2 0‖ ≤
      3 * K * e + 2 * c0 * e := by
    refine (g37_norm4' _ _ _ _).trans ?_
    nlinarith
  have hP : ‖Φ * Φ' - 1‖ ≤ (4 * K + 3 * c0) * e := by
    have h := congrArg norm dt
    rw [norm_mul, norm_neg] at h
    nlinarith [norm_nonneg (Φ * Φ' - 1), mul_nonneg hc0 he0, mul_nonneg hK he0]
  have hid : Φ' - Φ⁻¹ = Φ⁻¹ * (Φ * Φ' - 1) := by
    field_simp
  have hQ : ‖Φ' - Φ⁻¹‖ ≤ K * ((4 * K + 3 * c0) * e) := by
    rw [hid, norm_mul]
    exact mul_le_mul hΦi hP (norm_nonneg _) hK
  have hsplit : M.trace - (Φ + Φ⁻¹) = (M.trace - Φ - Φ') + (Φ' - Φ⁻¹) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith

end
end NlsGge.GKDefinitionDesign
