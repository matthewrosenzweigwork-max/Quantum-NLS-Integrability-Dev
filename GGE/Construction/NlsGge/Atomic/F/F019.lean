import Mathlib
import NlsGge.Hierarchy.ContractionMonomialBound38

                                                                                                                                                                               
                                                                                                  
                                                                                            
                                                                                                                                   
set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F

theorem f019 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ, 1 ≤ l → l ≤ m →
      ∀ a : Fin (2 * l) → ℕ, (∀ i, a i ≤ m - 1) →
      ∀ N : ℕ, 1 ≤ N → ∀ z : FourierPlane N,
        (∫ x in (0 : ℝ)..1,
          ∏ i : Fin (2 * l), ‖iteratedDeriv (a i) (planeReal N z) x‖) ≤
          C * (N : ℝ) ^ ((∑ i, a i) + l - 1) * (‖planeL2 N z‖ ^ 2) ^ l := by
  refine ⟨(2 * Real.pi) ^ (2 * m * (m - 1)) * 3 ^ m, by positivity, ?_⟩
  intro l hl1 hlm a ha N hN z
  have hcard : (Finset.univ : Finset (Fin (2 * l))).card = 2 * l := by simp
  have hb := integral_prod_bernstein38 (Finset.univ : Finset (Fin (2 * l))) (by rw [hcard]; omega) a N hN z
  rw [hcard] at hb
  set M : ℝ := ∑ i, ‖z i‖ ^ 2 with hM
  have hMn : ‖planeL2 N z‖ ^ 2 = M := planeL2_norm_sq N z
  rw [hMn]
  have hM0 : 0 ≤ M := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e1 : (Real.sqrt (2 * N + 1) * Real.sqrt M) ^ (2 * l - 2) = ((2 * N + 1) * M) ^ (l - 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    have : 2 * l - 2 = 2 * (l - 1) := by omega
    rw [this, pow_mul, Real.sq_sqrt (by positivity)]
  rw [e1] at hb
  set S : ℕ := ∑ i, a i with hS
  have hSle : S ≤ 2 * m * (m - 1) := by
    have h1 : S ≤ ∑ _t : Fin (2 * l), (m - 1) := Finset.sum_le_sum (fun i _ => ha i)
    have h2 : ∑ _t : Fin (2 * l), (m - 1) = 2 * l * (m - 1) := by simp
    have h3 : 2 * l * (m - 1) ≤ 2 * m * (m - 1) := by
      apply Nat.mul_le_mul_right; omega
    omega
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ha' : (2 * Real.pi * N) ^ S ≤ (2 * Real.pi) ^ (2 * m * (m - 1)) * (N : ℝ) ^ S := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2pi hSle) (by positivity)
  have h2N : (2 * (N : ℝ) + 1) ≤ 3 * N := by linarith
  have hb' : ((2 * (N : ℝ) + 1) * M) ^ (l - 1) ≤ 3 ^ m * (N : ℝ) ^ (l - 1) * M ^ (l - 1) := by
    calc ((2 * (N : ℝ) + 1) * M) ^ (l - 1) ≤ (3 * N * M) ^ (l - 1) :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h2N hM0) _
      _ = 3 ^ (l - 1) * (N : ℝ) ^ (l - 1) * M ^ (l - 1) := by rw [mul_pow, mul_pow]
      _ ≤ 3 ^ m * (N : ℝ) ^ (l - 1) * M ^ (l - 1) := by
          gcongr
          · norm_num
          · omega
  have e2 : S + l - 1 = S + (l - 1) := by omega
  have e3 : M ^ l = M ^ (l - 1) * M := by
    rw [← pow_succ]; congr 1; omega
  refine hb.trans ?_
  rw [e2, e3, pow_add]
  calc (2 * Real.pi * N) ^ S * (((2 * (N : ℝ) + 1) * M) ^ (l - 1) * M)
      ≤ ((2 * Real.pi) ^ (2 * m * (m - 1)) * (N : ℝ) ^ S) *
          ((3 ^ m * (N : ℝ) ^ (l - 1) * M ^ (l - 1)) * M) :=
        mul_le_mul ha' (mul_le_mul_of_nonneg_right hb' hM0) (by positivity) (by positivity)
    _ = _ := by ring


end NlsGge.ThirdConsultation.F
