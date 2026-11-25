import Mathlib
import NlsGge.Atomic.M.M016Core1

                                                                                                               
                                                                                         
                                  
                                                                                                        
                                                                                                                  
                                                                                                                       
                                                             
                                                                                                              
                                                                                                                      
                                                    
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M016C

theorem exterior_bound (F : ℂ → ℂ)
    (hG : AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹) 0)
    (a : ℕ → ℂ) (M : ℕ) (x : ℕ → ℂ) (hx0 : ∀ n, x n ≠ 0)
    (hxt : Tendsto (fun n => ‖x n‖) atTop atTop) (C : ℝ)
    (hb : ∀ n, ‖F (x n) + Complex.I * x n - ∑ k ∈ Finset.range M, a k * (x n)⁻¹ ^ k‖ ≤
      C * ‖(x n)⁻¹‖ ^ M) :
    ∃ C' R : ℝ, 0 ≤ C' ∧ 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      ‖F z + Complex.I * z - ∑ k ∈ Finset.range M, a k * z⁻¹ ^ k‖ ≤ C' * ‖z⁻¹‖ ^ M := by
  set g : ℂ → ℂ := fun w => if w = 0 then 0 else F w⁻¹ + Complex.I * w⁻¹ with hg
  have hgv : ∀ w : ℂ, w ≠ 0 → g w = F w⁻¹ + Complex.I * w⁻¹ := fun w hw => by
    simp only [hg, hw, ↓reduceIte]
  have hw0 : ∀ n, (x n)⁻¹ ≠ 0 := fun n => inv_ne_zero (hx0 n)
  have hwt : Tendsto (fun n => (x n)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact hxt.inv_tendsto_atTop
  have hb' : ∀ n, ‖g ((x n)⁻¹) - ∑ k ∈ Finset.range M, a k * (x n)⁻¹ ^ k‖ ≤ C * ‖(x n)⁻¹‖ ^ M := by
    intro n
    rw [hgv _ (hw0 n), inv_inv]
    exact hb n
  obtain ⟨C', r, hC', hr, hdisc⟩ := coeff_match g hG a M (fun n => (x n)⁻¹) hw0 hwt C hb'
  refine ⟨C', 2 / r, hC', by positivity, fun z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hzr : ‖z⁻¹‖ < r := by
    rw [norm_inv, inv_lt_comm₀ hzpos hr]
    have : 1 / r < 2 / r := by
      rw [div_lt_div_iff_of_pos_right hr]; norm_num
    rw [one_div] at this
    linarith
  have h := hdisc z⁻¹ hzr
  rw [hgv _ (inv_ne_zero hz0), inv_inv] at h
  exact h

theorem truncate (E : ℂ → ℂ) (a : ℕ → ℂ) (M K : ℕ) (hKM : K + 1 ≤ M) (C R : ℝ) (hC : 0 ≤ C)
    (hR : 0 < R)
    (hM : ∀ z : ℂ, R ≤ ‖z‖ → ‖E z - ∑ k ∈ Finset.range M, a k * z⁻¹ ^ k‖ ≤ C * ‖z⁻¹‖ ^ M) :
    ∃ C'' R'' : ℝ, 0 ≤ C'' ∧ 0 < R'' ∧ ∀ z : ℂ, R'' ≤ ‖z‖ →
      ‖E z - ∑ k ∈ Finset.range (K + 1), a k * z⁻¹ ^ k‖ ≤ C'' * ‖z⁻¹‖ ^ (K + 1) := by
  set A : ℝ := ∑ k ∈ Finset.range M, ‖a k‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  refine ⟨C + A, max R 1, by positivity, by positivity, fun z hz => ?_⟩
  have hzR : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hw1 : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz1
  have hw0 : 0 ≤ ‖z⁻¹‖ := norm_nonneg _
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => a k * z⁻¹ ^ k) hKM
  have e : E z - ∑ k ∈ Finset.range (K + 1), a k * z⁻¹ ^ k =
      (E z - ∑ k ∈ Finset.range M, a k * z⁻¹ ^ k) + ∑ k ∈ Finset.Ico (K + 1) M, a k * z⁻¹ ^ k := by
    rw [← hsplit]; ring
  rw [e]
  have h1 := hM z hzR
  have h2 : ‖∑ k ∈ Finset.Ico (K + 1) M, a k * z⁻¹ ^ k‖ ≤ A * ‖z⁻¹‖ ^ (K + 1) := by
    calc ‖∑ k ∈ Finset.Ico (K + 1) M, a k * z⁻¹ ^ k‖
        ≤ ∑ k ∈ Finset.Ico (K + 1) M, ‖a k * z⁻¹ ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico (K + 1) M, ‖a k‖ * ‖z⁻¹‖ ^ (K + 1) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact pow_le_pow_of_le_one hw0 hw1 (Finset.mem_Ico.1 hk).1
      _ = (∑ k ∈ Finset.Ico (K + 1) M, ‖a k‖) * ‖z⁻¹‖ ^ (K + 1) := by rw [Finset.sum_mul]
      _ ≤ A * ‖z⁻¹‖ ^ (K + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2) (fun k _ _ => norm_nonneg _)
  have h3 : C * ‖z⁻¹‖ ^ M ≤ C * ‖z⁻¹‖ ^ (K + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hw1 hKM) hC
  calc _ ≤ ‖E z - ∑ k ∈ Finset.range M, a k * z⁻¹ ^ k‖ + ‖∑ k ∈ Finset.Ico (K + 1) M, a k * z⁻¹ ^ k‖ :=
        norm_add_le _ _
    _ ≤ C * ‖z⁻¹‖ ^ (K + 1) + A * ‖z⁻¹‖ ^ (K + 1) := by linarith
    _ = (C + A) * ‖z⁻¹‖ ^ (K + 1) := by ring

end NlsGge.ThirdConsultation.M016C
