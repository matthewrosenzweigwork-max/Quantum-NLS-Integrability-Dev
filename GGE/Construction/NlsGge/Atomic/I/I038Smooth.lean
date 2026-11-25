import Mathlib
import NlsGge.Atomic.I.I037

                                                                                                                    
                                                                                                                 
                                  
                                                                                                                           
                            
                                                                                                                      
                                                                                                                   
                                                                                                                
                                                                                                       
                                                                                                                   
                                                   
                                                                                               
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.I037

namespace NlsGge.ThirdConsultation.I038S

theorem coef_le {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (j : ℕ) :
    0 ≤ c j / (Nat.factorial j : ℝ) ^ p ∧ c j / (Nat.factorial j : ℝ) ^ p ≤ 2 / (Nat.factorial j : ℝ) := by
  have hF : (1 : ℝ) ≤ (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hFp : (Nat.factorial j : ℝ) ≤ (Nat.factorial j : ℝ) ^ p := Real.self_le_rpow_of_one_le hF hp
  have hF0 : (0 : ℝ) < (Nat.factorial j : ℝ) := by linarith
  refine ⟨div_nonneg (by linarith [(hc j).1]) (by positivity), ?_⟩
  calc c j / (Nat.factorial j : ℝ) ^ p ≤ 2 / (Nat.factorial j : ℝ) ^ p :=
        div_le_div_of_nonneg_right (hc j).2 (by positivity)
    _ ≤ 2 / (Nat.factorial j : ℝ) := div_le_div_of_nonneg_left (by norm_num) hF0 hFp

theorem summable_majorant (R : ℝ) :
    Summable (fun j : ℕ => 4 * ((j : ℝ) * R ^ (2 * j - 1) / (Nat.factorial j : ℝ))) := by
  refine Summable.mul_left 4 ?_
  rw [← summable_nat_add_iff 1]
  have key : ∀ k : ℕ, (((k + 1 : ℕ) : ℝ) * R ^ (2 * (k + 1) - 1) / (Nat.factorial (k + 1) : ℝ)) =
      R * ((R ^ 2) ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [h1, Nat.factorial_succ, pow_succ, pow_mul]
    push_cast
    field_simp
  simp only [key]
  exact (Real.summable_pow_div_factorial (R ^ 2)).mul_left R

theorem hasDerivAt_complex {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∑' j : ℕ, ((c j / (Nat.factorial j : ℝ) ^ p : ℝ) : ℂ) * w ^ (2 * j))
      (∑' j : ℕ, ((c j / (Nat.factorial j : ℝ) ^ p : ℝ) : ℂ) * (((2 * j : ℕ) : ℂ) * z ^ (2 * j - 1))) z := by
  set R : ℝ := ‖z‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hmem : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR0
  refine hasDerivAt_tsum_of_isPreconnected (summable_majorant R) Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun j w _ => ((hasDerivAt_pow (2 * j) w).const_mul _)) ?_ h0 ?_ hmem
  · intro j w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    obtain ⟨hβ0, hβ⟩ := coef_le hp hc j
    have hF0 : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hpow : ‖w‖ ^ (2 * j - 1) ≤ R ^ (2 * j - 1) := pow_le_pow_left₀ (norm_nonneg _) hw.le _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0, norm_pow,
      Complex.norm_natCast]
    calc c j / (Nat.factorial j : ℝ) ^ p * (((2 * j : ℕ) : ℝ) * ‖w‖ ^ (2 * j - 1))
        ≤ 2 / (Nat.factorial j : ℝ) * (((2 * j : ℕ) : ℝ) * R ^ (2 * j - 1)) :=
          mul_le_mul hβ (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) (by positivity)
            (by positivity)
      _ = 4 * ((j : ℝ) * R ^ (2 * j - 1) / (Nat.factorial j : ℝ)) := by push_cast; ring
  · refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial ((‖(0 : ℂ)‖) ^ 2)).mul_left 2) (fun j => ?_)
    obtain ⟨hβ0, hβ⟩ := coef_le hp hc j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0, norm_pow, pow_mul]
    have : 0 ≤ (‖(0 : ℂ)‖ ^ 2) ^ j := by positivity
    calc c j / (Nat.factorial j : ℝ) ^ p * (‖(0 : ℂ)‖ ^ 2) ^ j
        ≤ 2 / (Nat.factorial j : ℝ) * (‖(0 : ℂ)‖ ^ 2) ^ j := mul_le_mul_of_nonneg_right hβ this
      _ = 2 * ((‖(0 : ℂ)‖ ^ 2) ^ j / (Nat.factorial j : ℝ)) := by ring

theorem weight_eq_re {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℝ) :
    factorialPowerWeight p c r =
      (∑' j : ℕ, ((c j / (Nat.factorial j : ℝ) ^ p : ℝ) : ℂ) * (r : ℂ) ^ (2 * j)).re := by
  have e : ∀ j : ℕ, ((c j / (Nat.factorial j : ℝ) ^ p : ℝ) : ℂ) * (r : ℂ) ^ (2 * j) =
      ((factorialPowerTerm p c r j : ℝ) : ℂ) := by
    intro j; unfold factorialPowerTerm; push_cast; ring
  simp only [e]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rfl

theorem contDiff_weight {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) :
    ContDiff ℝ 2 (factorialPowerWeight p c) := by
  set G : ℂ → ℂ := fun w => ∑' j : ℕ, ((c j / (Nat.factorial j : ℝ) ^ p : ℝ) : ℂ) * w ^ (2 * j) with hG
  have hd : Differentiable ℂ G := fun w => (hasDerivAt_complex hp hc w).differentiableAt
  have h2 : ContDiff ℝ 2 G := (hd.contDiff (n := 2)).restrict_scalars ℝ
  have h3 : ContDiff ℝ 2 (fun r : ℝ => (G (r : ℂ)).re) :=
    Complex.reCLM.contDiff.comp (h2.comp Complex.ofRealCLM.contDiff)
  have : factorialPowerWeight p c = fun r : ℝ => (G (r : ℂ)).re := funext (weight_eq_re hp hc)
  rw [this]; exact h3

theorem convexOn_weight {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) :
    ConvexOn ℝ Set.univ (factorialPowerWeight p c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hterm : ∀ j : ℕ, factorialPowerTerm p c (a • x + b • y) j ≤
      a • factorialPowerTerm p c x j + b • factorialPowerTerm p c y j := by
    intro j
    obtain ⟨hβ0, -⟩ := coef_le hp hc j
    have hcv := ((Even.convexOn_pow (n := 2 * j) (even_two_mul j)).smul hβ0).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e : ∀ r : ℝ, factorialPowerTerm p c r j = (c j / (Nat.factorial j : ℝ) ^ p) • r ^ (2 * j) := by
      intro r; unfold factorialPowerTerm; rw [smul_eq_mul]; ring
    rw [e, e, e]
    exact hcv
  unfold factorialPowerWeight
  have hs := fun r => summable_term hp hc r
  calc ∑' j, factorialPowerTerm p c (a • x + b • y) j
      ≤ ∑' j, (a • factorialPowerTerm p c x j + b • factorialPowerTerm p c y j) :=
        Summable.tsum_le_tsum hterm (hs _) (((hs x).mul_left a).add ((hs y).mul_left b))
    _ = a • ∑' j, factorialPowerTerm p c x j + b • ∑' j, factorialPowerTerm p c y j := by
        simp only [smul_eq_mul]
        rw [((hs x).mul_left a).tsum_add ((hs y).mul_left b), tsum_mul_left, tsum_mul_left]

end NlsGge.ThirdConsultation.I038S
