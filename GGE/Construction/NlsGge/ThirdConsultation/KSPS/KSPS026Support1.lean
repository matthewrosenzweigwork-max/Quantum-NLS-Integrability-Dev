import Mathlib

                                                                                                                    
                                                                                                             
                                                                                                     
                                                                                 
                                                                                 
                                                                   
                                                                                              
                                                                                                      
                                                    
set_option autoImplicit false
open Filter
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section

def WL1 (w : ℤ → ℝ) (k : ℕ) (z : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => w n ^ k * ‖z n‖)

def WL2 (w : ℤ → ℝ) (k : ℕ) (z : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => (w n ^ k * ‖z n‖) ^ 2)

def WBd (w : ℤ → ℝ) (k : ℕ) (z : ℤ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℤ in cofinite, w n ^ k * ‖z n‖ ≤ C

section
variable {w : ℤ → ℝ} (hw : ∀ n, 1 ≤ w n)
include hw

theorem wpow_nonneg (k : ℕ) (n : ℤ) : 0 ≤ w n ^ k :=
  pow_nonneg (le_trans zero_le_one (hw n)) k

theorem wt_nonneg (k : ℕ) (n : ℤ) (x : ℂ) : 0 ≤ w n ^ k * ‖x‖ :=
  mul_nonneg (wpow_nonneg hw k n) (norm_nonneg _)

theorem wpow_mono {k k' : ℕ} (h : k' ≤ k) (n : ℤ) : w n ^ k' ≤ w n ^ k :=
  pow_le_pow_right₀ (hw n) h

/-- A domination principle for nonnegative weighted quantities. -/
theorem summable_of_le_ev {f g : ℤ → ℝ} (hg : Summable g) (hf0 : ∀ n, 0 ≤ f n)
    (h : ∀ᶠ n in cofinite, f n ≤ g n) : Summable f := by
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
  exact hn

/-! ### l1 -/

theorem WL1.congr {k : ℕ} {z z' : ℤ → ℂ} (h : WL1 w k z) (he : ∀ᶠ n in cofinite, z n = z' n) :
    WL1 w k z' := by
  refine summable_of_le_ev hw h (fun n => wt_nonneg hw k n _) ?_
  filter_upwards [he] with n hn
  rw [hn]

theorem WL1.mono {k k' : ℕ} {z : ℤ → ℂ} (h : WL1 w k z) (hk : k' ≤ k) : WL1 w k' z := by
  refine summable_of_le_ev hw h (fun n => wt_nonneg hw k' n _) (Eventually.of_forall fun n => ?_)
  exact mul_le_mul_of_nonneg_right (wpow_mono hw hk n) (norm_nonneg _)

theorem WL1.add {k : ℕ} {z z' : ℤ → ℂ} (h : WL1 w k z) (h' : WL1 w k z') :
    WL1 w k (fun n => z n + z' n) := by
  refine summable_of_le_ev hw (Summable.add h h') (fun n => wt_nonneg hw k n _) (Eventually.of_forall fun n => ?_)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wpow_nonneg hw k n)

theorem WL1.sub {k : ℕ} {z z' : ℤ → ℂ} (h : WL1 w k z) (h' : WL1 w k z') :
    WL1 w k (fun n => z n - z' n) := by
  refine summable_of_le_ev hw (Summable.add h h') (fun n => wt_nonneg hw k n _) (Eventually.of_forall fun n => ?_)
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (wpow_nonneg hw k n)

theorem WL1.const_mul {k : ℕ} {z : ℤ → ℂ} (c : ℂ) (h : WL1 w k z) : WL1 w k (fun n => c * z n) := by
  refine summable_of_le_ev hw (h.mul_left ‖c‖) (fun n => wt_nonneg hw k n _) (Eventually.of_forall fun n => ?_)
  rw [norm_mul]
  exact le_of_eq (by ring)

/-! ### l2 -/

theorem WL2.congr {k : ℕ} {z z' : ℤ → ℂ} (h : WL2 w k z) (he : ∀ᶠ n in cofinite, z n = z' n) :
    WL2 w k z' := by
  refine summable_of_le_ev hw h (fun n => sq_nonneg _) ?_
  filter_upwards [he] with n hn
  rw [hn]

theorem WL2.mono {k k' : ℕ} {z : ℤ → ℂ} (h : WL2 w k z) (hk : k' ≤ k) : WL2 w k' z := by
  refine summable_of_le_ev hw h (fun n => sq_nonneg _) (Eventually.of_forall fun n => ?_)
  exact pow_le_pow_left₀ (wt_nonneg hw k' n (z n))
    (mul_le_mul_of_nonneg_right (wpow_mono hw hk n) (norm_nonneg _)) 2

theorem WL2.add {k : ℕ} {z z' : ℤ → ℂ} (h : WL2 w k z) (h' : WL2 w k z') :
    WL2 w k (fun n => z n + z' n) := by
  refine summable_of_le_ev hw ((h.mul_left 2).add (h'.mul_left 2)) (fun n => sq_nonneg _)
    (Eventually.of_forall fun n => ?_)
  have h1 : w n ^ k * ‖z n + z' n‖ ≤ w n ^ k * ‖z n‖ + w n ^ k * ‖z' n‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wpow_nonneg hw k n)
  have h0 := wt_nonneg hw k n ((fun n => z n + z' n) n)
  have ha := wt_nonneg hw k n (z n)
  have hb := wt_nonneg hw k n (z' n)
  nlinarith [sq_nonneg (w n ^ k * ‖z n‖ - w n ^ k * ‖z' n‖)]

theorem WL2.sub {k : ℕ} {z z' : ℤ → ℂ} (h : WL2 w k z) (h' : WL2 w k z') :
    WL2 w k (fun n => z n - z' n) := by
  refine summable_of_le_ev hw ((h.mul_left 2).add (h'.mul_left 2)) (fun n => sq_nonneg _)
    (Eventually.of_forall fun n => ?_)
  have h1 : w n ^ k * ‖z n - z' n‖ ≤ w n ^ k * ‖z n‖ + w n ^ k * ‖z' n‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (wpow_nonneg hw k n)
  have h0 := wt_nonneg hw k n ((fun n => z n - z' n) n)
  have ha := wt_nonneg hw k n (z n)
  have hb := wt_nonneg hw k n (z' n)
  nlinarith [sq_nonneg (w n ^ k * ‖z n‖ - w n ^ k * ‖z' n‖)]

theorem WL2.const_mul {k : ℕ} {z : ℤ → ℂ} (c : ℂ) (h : WL2 w k z) : WL2 w k (fun n => c * z n) := by
  refine summable_of_le_ev hw (h.mul_left (‖c‖ ^ 2)) (fun n => sq_nonneg _) (Eventually.of_forall fun n => ?_)
  rw [norm_mul]
  exact le_of_eq (by ring)

/-- `l2` sequences tend to zero, hence are eventually bounded by any positive constant. -/
theorem WL2.eventually_le {k : ℕ} {z : ℤ → ℂ} (h : WL2 w k z) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in cofinite, w n ^ k * ‖z n‖ ≤ ε := by
  have ht := h.tendsto_cofinite_zero
  have hev : ∀ᶠ n in cofinite, (w n ^ k * ‖z n‖) ^ 2 < ε ^ 2 :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with n hn
  have h0 := wt_nonneg hw k n (z n)
  nlinarith

theorem WL2.bd {k : ℕ} {z : ℤ → ℂ} (h : WL2 w k z) : WBd w k z :=
  ⟨1, h.eventually_le hw 1 one_pos⟩

/-- `l2 * l2 → l1` (the Cauchy–Schwarz product step). -/
theorem WL2.mul {a b k : ℕ} {z z' : ℤ → ℂ} (h : WL2 w a z) (h' : WL2 w b z') (hk : a + b = k) :
    WL1 w k (fun n => z n * z' n) := by
  refine summable_of_le_ev hw (Summable.add h h') (fun n => wt_nonneg hw k n _) (Eventually.of_forall fun n => ?_)
  have e : w n ^ k * ‖z n * z' n‖ = (w n ^ a * ‖z n‖) * (w n ^ b * ‖z' n‖) := by
    rw [← hk, pow_add, norm_mul]; ring
  rw [e]
  nlinarith [sq_nonneg (w n ^ a * ‖z n‖ - w n ^ b * ‖z' n‖)]

/-! ### bounded -/

theorem WBd.congr {k : ℕ} {z z' : ℤ → ℂ} (h : WBd w k z) (he : ∀ᶠ n in cofinite, z n = z' n) :
    WBd w k z' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [hC, he] with n hn he'
  rw [← he']; exact hn

theorem WBd.mono {k k' : ℕ} {z : ℤ → ℂ} (h : WBd w k z) (hk : k' ≤ k) : WBd w k' z := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  exact (mul_le_mul_of_nonneg_right (wpow_mono hw hk n) (norm_nonneg _)).trans hn

theorem WBd.add {k : ℕ} {z z' : ℤ → ℂ} (h : WBd w k z) (h' : WBd w k z') :
    WBd w k (fun n => z n + z' n) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', ?_⟩
  filter_upwards [hC, hC'] with n hn hn'
  have h1 : w n ^ k * ‖z n + z' n‖ ≤ w n ^ k * ‖z n‖ + w n ^ k * ‖z' n‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wpow_nonneg hw k n)
  linarith

theorem WBd.sub {k : ℕ} {z z' : ℤ → ℂ} (h : WBd w k z) (h' : WBd w k z') :
    WBd w k (fun n => z n - z' n) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C + C', ?_⟩
  filter_upwards [hC, hC'] with n hn hn'
  have h1 : w n ^ k * ‖z n - z' n‖ ≤ w n ^ k * ‖z n‖ + w n ^ k * ‖z' n‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (wpow_nonneg hw k n)
  linarith

theorem WBd.const_mul {k : ℕ} {z : ℤ → ℂ} (c : ℂ) (h : WBd w k z) : WBd w k (fun n => c * z n) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, ?_⟩
  filter_upwards [hC] with n hn
  have e : w n ^ k * ‖c * z n‖ = ‖c‖ * (w n ^ k * ‖z n‖) := by rw [norm_mul]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

theorem WBd.mul {a b k : ℕ} {z z' : ℤ → ℂ} (h : WBd w a z) (h' : WBd w b z') (hk : a + b = k) :
    WBd w k (fun n => z n * z' n) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C * C', ?_⟩
  filter_upwards [hC, hC'] with n hn hn'
  have e : w n ^ k * ‖z n * z' n‖ = (w n ^ a * ‖z n‖) * (w n ^ b * ‖z' n‖) := by
    rw [← hk, pow_add, norm_mul]; ring
  rw [e]
  have hC0 : 0 ≤ C := (wt_nonneg hw a n (z n)).trans hn
  exact mul_le_mul hn hn' (wt_nonneg hw b n (z' n)) hC0

/-- bounded * l2 → l2. -/
theorem WBd.mul_WL2 {a b k : ℕ} {z z' : ℤ → ℂ} (h : WBd w a z) (h' : WL2 w b z') (hk : a + b = k) :
    WL2 w k (fun n => z n * z' n) := by
  obtain ⟨C, hC⟩ := h
  refine summable_of_le_ev hw (h'.mul_left (C ^ 2)) (fun n => sq_nonneg _) ?_
  filter_upwards [hC] with n hn
  have e : w n ^ k * ‖z n * z' n‖ = (w n ^ a * ‖z n‖) * (w n ^ b * ‖z' n‖) := by
    rw [← hk, pow_add, norm_mul]; ring
  rw [e, mul_pow]
  have h0 := wt_nonneg hw a n (z n)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hn 2) (sq_nonneg _)

/-- bounded * l1 → l1. -/
theorem WBd.mul_WL1 {a b k : ℕ} {z z' : ℤ → ℂ} (h : WBd w a z) (h' : WL1 w b z') (hk : a + b = k) :
    WL1 w k (fun n => z n * z' n) := by
  obtain ⟨C, hC⟩ := h
  refine summable_of_le_ev hw (h'.mul_left C) (fun n => wt_nonneg hw k n _) ?_
  filter_upwards [hC] with n hn
  have e : w n ^ k * ‖z n * z' n‖ = (w n ^ a * ‖z n‖) * (w n ^ b * ‖z' n‖) := by
    rw [← hk, pow_add, norm_mul]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hn (wt_nonneg hw b n (z' n))

/-- bounded at order k+1 → l2 at order k, given that 1/w is square summable. -/
theorem WBd.succ_WL2 (hinv : Summable (fun n : ℤ => (1 / w n) ^ 2)) {k : ℕ} {z : ℤ → ℂ}
    (h : WBd w (k + 1) z) : WL2 w k z := by
  obtain ⟨C, hC⟩ := h
  refine summable_of_le_ev hw (hinv.mul_left (C ^ 2)) (fun n => sq_nonneg _) ?_
  filter_upwards [hC] with n hn
  have hw0 : 0 < w n := lt_of_lt_of_le one_pos (hw n)
  have e : w n ^ k * ‖z n‖ = (w n ^ (k + 1) * ‖z n‖) * (1 / w n) := by
    rw [pow_succ]; field_simp
  rw [e, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (wt_nonneg hw (k + 1) n (z n)) hn 2) (sq_nonneg _)

end

end
end NlsGge.ThirdConsultation.KSPS026W
