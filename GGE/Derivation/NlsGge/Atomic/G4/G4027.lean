/- G4027 PRODUCTION01 (proof development kit; source proof development/G4027_PROOF01.lean.txt; target NlsGge/Atomic/G4/G4027.lean).
   slitRoot / slitPrimitive are NOT copied: they come from the landed host NlsGge.Atomic.G4.G4024 (import).
   elementarySlitIntegral is hosted here. Statement G4027 is verbatim from defs3 STATEMENTS/G4.md. -/
import Mathlib
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.StdRootBranchesSlit
import NlsGge.Atomic.G4.G4024

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def elementarySlitIntegral (γ τ μ : ℂ) : ℂ :=
  slitPrimitive (2 * (μ - τ) / γ)


namespace G4027Aux

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

theorem slit_factor (z : ℂ) (hz : z ≠ 0) : slitRoot z = (-z) * (slitRoot z / (-z)) := by
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
  field_simp

theorem key (γ P S : ℂ) (hγ : γ ≠ 0) (hP : P ≠ 0)
    (hS : slitRoot (2 * P / γ) = (-(2 * P / γ)) * S) :
    γ * (-(2 * P / γ) - slitRoot (2 * P / γ)) = -2 * P * (1 - S) ∧
      γ * (-(2 * P / γ) + slitRoot (2 * P / γ)) = -2 * P * (1 + S) := by
  have hgz : γ * (2 * P / γ) = 2 * P := by field_simp
  rw [hS]
  constructor
  · linear_combination (-(1 - S)) * hgz
  · linear_combination (-(1 + S)) * hgz

theorem S_bound (γ P : ℂ) (hγ : γ ≠ 0) (hP : P ≠ 0) :
    ‖slitRoot (2 * P / γ) / (-(2 * P / γ)) - 1‖ ≤ ‖γ‖ ^ 2 / (4 * ‖P‖ ^ 2) := by
  have hz : 2 * P / γ ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hP) hγ
  have hzn : (0 : ℂ) - 2 * P / γ ≠ 0 := by
    rw [zero_sub]; exact neg_ne_zero.mpr hz
  have hb := stdRoot_ratio_bound38 (τ := 0) (g2 := 4) hzn
  have hsl : slitRoot (2 * P / γ) = stdRoot38 0 4 (2 * P / γ) := by
    rw [slitRoot, if_neg hz]
  rw [zero_sub] at hb
  rw [← hsl] at hb
  refine hb.trans (le_of_eq ?_)
  have hγ' : ‖γ‖ ≠ 0 := norm_ne_zero_iff.mpr hγ
  have hP' : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hP
  rw [norm_neg, norm_div, norm_mul]
  field_simp
  norm_num

end G4027Aux

open G4027Aux in
theorem G4027 (γseq τseq μseq : ℕ → ℂ) (τ μ : ℂ)
    (hγ : Tendsto γseq atTop (𝓝 0)) (hγne : ∀ j : ℕ, γseq j ≠ 0)
    (hτ : Tendsto τseq atTop (𝓝 τ)) (hμ : Tendsto μseq atTop (𝓝 μ))
    (hne : μ ≠ τ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Tendsto (fun j => γseq j * Complex.exp ((s : ℂ) * elementarySlitIntegral (γseq j) (τseq j) (μseq j)))
      atTop (𝓝 (2 * (τ - μ) * (1 - (s : ℂ)))) := by
  have hμτ : μ - τ ≠ 0 := sub_ne_zero.mpr hne
  have hP : Tendsto (fun j => μseq j - τseq j) atTop (𝓝 (μ - τ)) := hμ.sub hτ
  have hPev : ∀ᶠ j in atTop, μseq j - τseq j ≠ 0 := hP.eventually_ne hμτ
  have hSbound : ∀ᶠ j in atTop,
      ‖slitRoot (2 * (μseq j - τseq j) / γseq j) / (-(2 * (μseq j - τseq j) / γseq j)) - 1‖
        ≤ ‖γseq j‖ ^ 2 / (4 * ‖μseq j - τseq j‖ ^ 2) := by
    filter_upwards [hPev] with j hj
    exact S_bound (γseq j) (μseq j - τseq j) (hγne j) hj
  have hS1 : Tendsto (fun j => slitRoot (2 * (μseq j - τseq j) / γseq j) /
      (-(2 * (μseq j - τseq j) / γseq j))) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun j => ‖γseq j‖ ^ 2 / (4 * ‖μseq j - τseq j‖ ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖γseq j‖ ^ 2) atTop (𝓝 0) := by
        have := hγ.norm.pow 2
        simpa using this
      have h2 : Tendsto (fun j => 4 * ‖μseq j - τseq j‖ ^ 2) atTop (𝓝 (4 * ‖μ - τ‖ ^ 2)) :=
        tendsto_const_nhds.mul (hP.norm.pow 2)
      have h3 : (4 * ‖μ - τ‖ ^ 2) ≠ 0 := by
        have : ‖μ - τ‖ ≠ 0 := norm_ne_zero_iff.mpr hμτ
        positivity
      have h4 := h1.div h2 h3
      rw [zero_div] at h4
      exact h4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun j => norm_nonneg _) hSbound
  rcases hs with rfl | rfl
  · have hlim : Tendsto (fun j => -2 * (μseq j - τseq j) *
        (1 - slitRoot (2 * (μseq j - τseq j) / γseq j) / (-(2 * (μseq j - τseq j) / γseq j))))
        atTop (𝓝 (-2 * (μ - τ) * (1 - 1))) :=
      (tendsto_const_nhds.mul hP).mul (tendsto_const_nhds.sub hS1)
    have hval : 2 * (τ - μ) * (1 - ((1 : ℤ) : ℂ)) = -2 * (μ - τ) * (1 - 1) := by
      push_cast; ring
    rw [hval]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hPev] with j hj
    have hz : 2 * (μseq j - τseq j) / γseq j ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero hj) (hγne j)
    have hS := slit_factor _ hz
    simp only [elementarySlitIntegral, Int.cast_one, one_mul, exp_slit]
    exact (key (γseq j) (μseq j - τseq j) _ (hγne j) hj hS).1.symm
  · have hlim : Tendsto (fun j => -2 * (μseq j - τseq j) *
        (1 + slitRoot (2 * (μseq j - τseq j) / γseq j) / (-(2 * (μseq j - τseq j) / γseq j))))
        atTop (𝓝 (-2 * (μ - τ) * (1 + 1))) :=
      (tendsto_const_nhds.mul hP).mul (tendsto_const_nhds.add hS1)
    have hval : 2 * (τ - μ) * (1 - ((-1 : ℤ) : ℂ)) = -2 * (μ - τ) * (1 + 1) := by
      push_cast; ring
    rw [hval]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hPev] with j hj
    have hz : 2 * (μseq j - τseq j) / γseq j ≠ 0 :=
      div_ne_zero (mul_ne_zero two_ne_zero hj) (hγne j)
    have hS := slit_factor _ hz
    simp only [elementarySlitIntegral, Int.cast_neg, Int.cast_one, neg_one_mul, exp_slit_neg]
    exact (key (γseq j) (μseq j - τseq j) _ (hγne j) hj hS).2.symm

end
end NlsGge.GKDefinitionDesign
