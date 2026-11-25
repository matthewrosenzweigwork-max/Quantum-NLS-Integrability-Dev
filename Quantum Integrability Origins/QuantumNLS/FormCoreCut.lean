import Mathlib
import QuantumNLS.FormCoreCalculus

/-!
# R-1602B09D `CC:F03:core`: truncation, the multiplication estimate, cutting families

* `trunc_tendsto`, `approx_of_bounded`: the first step of the printed proof (truncation of the range): `N(h - T_k h) → 0`, so only bounded `h` must be approximated.
* `formN_mul_le`: `N(w h) ≤ M² ∫ w² dμ + 2 ∬ w(x)² |Dh|² + 2 M² E(w)` for `|h| ≤ M`.
* `formN_cut_tendsto`: if `w_k` are measurable with `|w_k| ≤ 1`, `w_k → 0` μ-a.e., and `E_μ(w_k) → 0`, then `N(w_k h) → 0` for bounded `h` of finite form norm.
* `formE_le_lip`: `E_μ(w) ≤ ℓ² μ(ℝ)²` for `ℓ`-Lipschitz `w`; the far cutoff `wfar` (`= 1 - χ_R`) satisfies the hypotheses of `formN_cut_tendsto`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace QuantumNLS.FormCore

/-- `T_M r = max(-M, min(M, r))`. -/
def trunc (M r : ℝ) : ℝ := max (-M) (min M r)

theorem trunc_mono (M : ℝ) {r s : ℝ} (h : r ≤ s) : trunc M r ≤ trunc M s :=
  max_le_max le_rfl (min_le_min le_rfl h)

theorem trunc_sub_le (M : ℝ) {r s : ℝ} (h : r ≤ s) : trunc M s - trunc M r ≤ s - r := by
  simp only [trunc, max_def, min_def]
  split_ifs <;> linarith

theorem abs_trunc_sub_le (M r s : ℝ) : |trunc M r - trunc M s| ≤ |r - s| := by
  rcases le_total r s with h | h
  · have h1 := trunc_mono M h
    have h2 := trunc_sub_le M h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := trunc_mono M h
    have h2 := trunc_sub_le M h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem abs_gap_sub_le (M r s : ℝ) : |(r - trunc M r) - (s - trunc M s)| ≤ |r - s| := by
  rcases le_total r s with h | h
  · have h1 := trunc_mono M h
    have h2 := trunc_sub_le M h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := trunc_mono M h
    have h2 := trunc_sub_le M h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem trunc_zero {M : ℝ} (hM : 0 ≤ M) : trunc M 0 = 0 := by
  simp [trunc, hM]

theorem abs_trunc_le {M : ℝ} (hM : 0 ≤ M) (r : ℝ) : |trunc M r| ≤ |r| := by
  have := abs_trunc_sub_le M r 0
  rwa [trunc_zero hM, sub_zero, sub_zero] at this

theorem abs_gap_le {M : ℝ} (hM : 0 ≤ M) (r : ℝ) : |r - trunc M r| ≤ |r| := by
  have := abs_gap_sub_le M r 0
  rwa [trunc_zero hM, sub_zero, sub_zero, sub_zero] at this

theorem abs_trunc_le_self {M : ℝ} (hM : 0 ≤ M) (r : ℝ) : |trunc M r| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem trunc_eq_self {M r : ℝ} (h : |r| ≤ M) : trunc M r = r := by
  rw [abs_le] at h
  simp only [trunc]
  rw [min_eq_right h.2, max_eq_right h.1]

theorem measurable_trunc (M : ℝ) : Measurable (trunc M) := by unfold trunc; fun_prop

theorem formN_trunc_le {μ : Measure ℝ} {M : ℝ} (hM : 0 ≤ M) {h : ℝ → ℝ} (hh : Measurable h) :
    formN μ (fun x => trunc M (h x)) ≤ formN μ h := by
  unfold formN
  refine add_le_add ?_ ?_
  · refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have := abs_trunc_le hM (h x)
    nlinarith [sq_abs (trunc M (h x)), sq_abs (h x), abs_nonneg (trunc M (h x))]
  · refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
    unfold dq
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have := abs_trunc_sub_le M (h p.1) (h p.2)
    nlinarith [sq_abs (trunc M (h p.1) - trunc M (h p.2)), sq_abs (h p.1 - h p.2),
      abs_nonneg (trunc M (h p.1) - trunc M (h p.2))]

theorem trunc_tendsto {μ : Measure ℝ} {h : ℝ → ℝ} (hh : Measurable h) (hN : formN μ h < ⊤) :
    Tendsto (fun k : ℕ => formN μ (fun x => h x - trunc k (h x))) atTop (𝓝 0) := by
  have hL : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ ≠ ⊤ := ne_top_of_le_ne_top hN.ne (formL2_le_formN μ h)
  have hE : ∫⁻ p, ENNReal.ofReal (dq h p) ∂(μ.prod μ) ≠ ⊤ := ne_top_of_le_ne_top hN.ne (formE_le_formN μ h)
  have hgm : ∀ k : ℕ, Measurable fun x => h x - trunc k (h x) := fun k =>
    hh.sub ((measurable_trunc k).comp hh)
  have T1 : Tendsto (fun k : ℕ => formL2 μ (fun x => h x - trunc k (h x))) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun (k : ℕ) x => ENNReal.ofReal ((h x - trunc k (h x)) ^ 2)) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (h x ^ 2))
      (fun k => ENNReal.measurable_ofReal.comp ((hgm k).pow_const 2))
      (fun k => Eventually.of_forall fun x => by
        refine ENNReal.ofReal_le_ofReal ?_
        have := abs_gap_le (Nat.cast_nonneg k) (h x)
        nlinarith [sq_abs (h x - trunc k (h x)), sq_abs (h x), abs_nonneg (h x - trunc k (h x))])
      hL
      (Eventually.of_forall fun x => by
        obtain ⟨K, hK⟩ := exists_nat_ge |h x|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop K] with k hk
        have : |h x| ≤ k := le_trans hK (by exact_mod_cast hk)
        rw [trunc_eq_self this]; simp)
    simpa [formL2] using this
  have T2 : Tendsto (fun k : ℕ => formE μ (fun x => h x - trunc k (h x))) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ.prod μ)
      (F := fun (k : ℕ) p => ENNReal.ofReal (dq (fun x => h x - trunc k (h x)) p)) (f := fun _ => 0)
      (fun p => ENNReal.ofReal (dq h p))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_dq (hgm k)))
      (fun k => Eventually.of_forall fun p => by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold dq
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have := abs_gap_sub_le k (h p.1) (h p.2)
        nlinarith [sq_abs (h p.1 - trunc k (h p.1) - (h p.2 - trunc k (h p.2))), sq_abs (h p.1 - h p.2),
          abs_nonneg (h p.1 - trunc k (h p.1) - (h p.2 - trunc k (h p.2)))])
      hE
      (Eventually.of_forall fun p => by
        obtain ⟨K, hK⟩ := exists_nat_ge (max |h p.1| |h p.2|)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop K] with k hk
        have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
        have h1 : |h p.1| ≤ k := le_trans (le_trans (le_max_left _ _) hK) hk'
        have h2 : |h p.2| ≤ k := le_trans (le_trans (le_max_right _ _) hK) hk'
        simp only [dq, trunc_eq_self h1, trunc_eq_self h2]
        simp)
    simpa [formE] using this
  have := T1.add T2
  simpa [formN] using this

/-- It suffices to approximate bounded measurable functions of finite form norm. -/
theorem approx_of_bounded {μ : Measure ℝ}
    (hb : ∀ g : ℝ → ℝ, Measurable g → (∃ M : ℝ, ∀ x, |g x| ≤ M) → formN μ g < ⊤ → Approx μ g)
    {h : ℝ → ℝ} (hh : Measurable h) (hN : formN μ h < ⊤) : Approx μ h := by
  apply approx_of_close hh
  intro ε hε
  have ht := trunc_tendsto hh hN
  have hev : ∀ᶠ k : ℕ in atTop, formN μ (fun x => h x - trunc k (h x)) < ENNReal.ofReal ε :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨k, hk⟩ := hev.exists
  have hm : Measurable fun x => trunc k (h x) := (measurable_trunc k).comp hh
  refine ⟨fun x => trunc k (h x), hm, hb _ hm ⟨k, fun x => abs_trunc_le_self (Nat.cast_nonneg k) _⟩ ?_, hk⟩
  exact lt_of_le_of_lt (formN_trunc_le (Nat.cast_nonneg k) hh) hN

/-! ### The multiplication estimate -/

theorem dq_mul_le (h w : ℝ → ℝ) {M : ℝ} (hM : ∀ x, |h x| ≤ M) (p : ℝ × ℝ) :
    dq (fun x => w x * h x) p ≤ 2 * (w p.1 ^ 2 * dq h p) + 2 * (M ^ 2 * dq w p) := by
  unfold dq
  have hy2 : h p.2 ^ 2 ≤ M ^ 2 := by
    have := hM p.2
    nlinarith [abs_nonneg (h p.2), sq_abs (h p.2)]
  have e : 2 * (w p.1 ^ 2 * ((h p.1 - h p.2) ^ 2 / (p.1 - p.2) ^ 2)) +
      2 * (M ^ 2 * ((w p.1 - w p.2) ^ 2 / (p.1 - p.2) ^ 2)) =
      (2 * (w p.1 ^ 2 * (h p.1 - h p.2) ^ 2) + 2 * (M ^ 2 * (w p.1 - w p.2) ^ 2)) / (p.1 - p.2) ^ 2 := by
    ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have key : (w p.1 * h p.1 - w p.2 * h p.2) ^ 2 ≤
      2 * (w p.1 * (h p.1 - h p.2)) ^ 2 + 2 * (h p.2 * (w p.1 - w p.2)) ^ 2 := by
    nlinarith [sq_nonneg (w p.1 * (h p.1 - h p.2) - h p.2 * (w p.1 - w p.2))]
  have e2 : w p.1 * h p.1 - w p.2 * h p.2 = w p.1 * (h p.1 - h p.2) + h p.2 * (w p.1 - w p.2) := by ring
  have h3 : (h p.2 * (w p.1 - w p.2)) ^ 2 ≤ M ^ 2 * (w p.1 - w p.2) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)
  show (w p.1 * h p.1 - w p.2 * h p.2) ^ 2 ≤ _
  nlinarith [key, h3, mul_pow (w p.1) (h p.1 - h p.2) 2]

theorem formN_mul_le {μ : Measure ℝ} {h w : ℝ → ℝ} (hh : Measurable h) (hw : Measurable w) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) :
    formN μ (fun x => w x * h x) ≤
      ENNReal.ofReal (M ^ 2) * ∫⁻ x, ENNReal.ofReal (w x ^ 2) ∂μ +
      (2 * ∫⁻ p, ENNReal.ofReal (w p.1 ^ 2 * dq h p) ∂(μ.prod μ) + 2 * (ENNReal.ofReal (M ^ 2) * formE μ w)) := by
  unfold formN
  have hL : formL2 μ (fun x => w x * h x) ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ x, ENNReal.ofReal (w x ^ 2) ∂μ := by
    unfold formL2
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx2 : h x ^ 2 ≤ M ^ 2 := by
      have := hM x
      nlinarith [abs_nonneg (h x), sq_abs (h x)]
    calc (w x * h x) ^ 2 = w x ^ 2 * h x ^ 2 := by ring
      _ ≤ w x ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hx2 (sq_nonneg _)
      _ = M ^ 2 * w x ^ 2 := by ring
  have hE : formE μ (fun x => w x * h x) ≤
      2 * ∫⁻ p, ENNReal.ofReal (w p.1 ^ 2 * dq h p) ∂(μ.prod μ) + 2 * (ENNReal.ofReal (M ^ 2) * formE μ w) := by
    unfold formE
    calc ∫⁻ p, ENNReal.ofReal (dq (fun x => w x * h x) p) ∂(μ.prod μ)
        ≤ ∫⁻ p, (2 * ENNReal.ofReal (w p.1 ^ 2 * dq h p) + 2 * (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (dq w p)))
            ∂(μ.prod μ) := by
          refine lintegral_mono fun p => ?_
          have hnn1 : 0 ≤ w p.1 ^ 2 * dq h p := mul_nonneg (sq_nonneg _) (dq_nonneg _ _)
          have hnn2 : 0 ≤ M ^ 2 * dq w p := mul_nonneg (sq_nonneg _) (dq_nonneg _ _)
          calc ENNReal.ofReal (dq (fun x => w x * h x) p)
              ≤ ENNReal.ofReal (2 * (w p.1 ^ 2 * dq h p) + 2 * (M ^ 2 * dq w p)) :=
                ENNReal.ofReal_le_ofReal (dq_mul_le h w hM p)
            _ = 2 * ENNReal.ofReal (w p.1 ^ 2 * dq h p) + 2 * ENNReal.ofReal (M ^ 2 * dq w p) :=
                ofReal_two_mul_add _ _ hnn1 hnn2
            _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg M)]
      _ = 2 * ∫⁻ p, ENNReal.ofReal (w p.1 ^ 2 * dq h p) ∂(μ.prod μ) +
            2 * ∫⁻ p, (ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (dq w p)) ∂(μ.prod μ) := by
          refine lintegral_two_mul_add ?_
          have h1 : Measurable fun p : ℝ × ℝ => w p.1 := hw.comp measurable_fst
          exact ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_dq hh))
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc formL2 μ (fun x => w x * h x) + formE μ (fun x => w x * h x)
      ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ x, ENNReal.ofReal (w x ^ 2) ∂μ +
        (2 * ∫⁻ p, ENNReal.ofReal (w p.1 ^ 2 * dq h p) ∂(μ.prod μ) +
          2 * (ENNReal.ofReal (M ^ 2) * formE μ w)) := add_le_add hL hE

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.trunc_tendsto
#print axioms QuantumNLS.FormCore.approx_of_bounded
#print axioms QuantumNLS.FormCore.formN_mul_le
