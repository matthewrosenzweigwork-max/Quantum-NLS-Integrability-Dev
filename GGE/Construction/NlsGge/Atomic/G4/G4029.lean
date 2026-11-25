                                                                                                                   
                                                                                                               
                                                                                                                     
                                                                                                                
                                                      
import Mathlib
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.Atomic.G4.G4024
import NlsGge.Atomic.G4.G4027

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4029Aux

theorem slitRoot_sq (z : ℂ) : slitRoot z ^ 2 = z ^ 2 - 1 := by
  by_cases h0 : z = 0
  · simp [slitRoot, h0]
  · have h : (0 : ℂ) - z ≠ 0 := by simpa using h0
    have := stdRoot_sq_of_ne38 (τ := 0) (g2 := 4) (z := z) h
    simp only [slitRoot, if_neg h0]
    rw [this]
    ring

theorem wq (z : ℂ) : (-z - slitRoot z) * (-z + slitRoot z) = 1 := by
  linear_combination (-1 : ℂ) * slitRoot_sq z

theorem w_ne (ρ : ℂ) : -ρ - slitRoot ρ ≠ 0 := by
  intro h
  have h1 := wq ρ
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exp_slit (ρ : ℂ) : Complex.exp (slitPrimitive ρ) = -ρ - slitRoot ρ := by
  unfold slitPrimitive
  exact Complex.exp_log (w_ne ρ)

theorem exp_slit_neg (ρ : ℂ) : Complex.exp (-slitPrimitive ρ) = -ρ + slitRoot ρ := by
  rw [Complex.exp_neg, exp_slit]
  exact inv_eq_of_mul_eq_one_right (wq ρ)

theorem norm_slitRoot_le (z : ℂ) : ‖slitRoot z‖ ≤ ‖z‖ + 1 := by
  have h1 : ‖slitRoot z‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
    have e : ‖slitRoot z‖ ^ 2 = ‖z ^ 2 - 1‖ := by
      rw [← norm_pow, slitRoot_sq]
    rw [e]
    have h2 : ‖z ^ 2 - 1‖ ≤ ‖z ^ 2‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    rw [norm_pow, norm_one] at h2
    nlinarith [norm_nonneg z]
  nlinarith [norm_nonneg (slitRoot z), norm_nonneg z, h1]

theorem wbound (z : ℂ) :
    ‖-z - slitRoot z‖ ≤ 2 * ‖z‖ + 1 ∧ ‖-z + slitRoot z‖ ≤ 2 * ‖z‖ + 1 := by
  have h := norm_slitRoot_le z
  constructor
  · have := norm_sub_le (-z) (slitRoot z)
    rw [norm_neg] at this
    linarith
  · have := norm_add_le (-z) (slitRoot z)
    rw [norm_neg] at this
    linarith

theorem val_le (γ τ μ : ℂ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤
      ‖γ‖ * (2 * ‖2 * (μ - τ) / γ‖ + 1) := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rcases hs with rfl | rfl
  · simp only [elementarySlitIntegral, Int.cast_one, one_mul, exp_slit]
    exact (wbound _).1
  · simp only [elementarySlitIntegral, Int.cast_neg, Int.cast_one, neg_one_mul, exp_slit_neg]
    exact (wbound _).2

end G4029Aux

open G4029Aux in
theorem G4029 (γ τ μ : ℂ) (hγ : γ ≠ 0) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (‖2 * (μ - τ) / γ‖ ≤ 1 →
      ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤ 3 * ‖γ‖) ∧
    (1 < ‖2 * (μ - τ) / γ‖ →
      ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤ 6 * ‖μ - τ‖) ∧
    ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤
      3 * ‖γ‖ + 6 * ‖μ - τ‖ := by
  have hgz : γ * (2 * (μ - τ) / γ) = 2 * (μ - τ) := by field_simp
  have hn : ‖γ‖ * ‖2 * (μ - τ) / γ‖ = 2 * ‖μ - τ‖ := by
    rw [← norm_mul, hgz, norm_mul]
    norm_num
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hP0 : 0 ≤ ‖μ - τ‖ := norm_nonneg _
  have p1 : ‖2 * (μ - τ) / γ‖ ≤ 1 →
      ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤ 3 * ‖γ‖ := by
    intro h1
    have h2 : ‖γ‖ * (2 * ‖2 * (μ - τ) / γ‖ + 1) ≤ ‖γ‖ * 3 :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have := val_le γ τ μ s hs
    linarith
  have p2 : 1 < ‖2 * (μ - τ) / γ‖ →
      ‖γ * Complex.exp ((s : ℂ) * elementarySlitIntegral γ τ μ)‖ ≤ 6 * ‖μ - τ‖ := by
    intro h1
    have h3 : ‖γ‖ * 1 < ‖γ‖ * ‖2 * (μ - τ) / γ‖ := mul_lt_mul_of_pos_left h1 hγn
    have := val_le γ τ μ s hs
    nlinarith
  refine ⟨p1, p2, ?_⟩
  rcases le_or_gt ‖2 * (μ - τ) / γ‖ 1 with h | h
  · linarith [p1 h]
  · linarith [p2 h]

end
end NlsGge.GKDefinitionDesign
