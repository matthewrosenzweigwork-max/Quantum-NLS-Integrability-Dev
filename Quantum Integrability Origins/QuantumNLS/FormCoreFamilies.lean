import Mathlib
import QuantumNLS.FormCoreCut

/-!
# R-1602B09D `CC:F03:core`: cutting families and the reduction to compact support

* `formN_cut_tendsto`: weights `w_k` with `|w_k| ≤ 1`, `w_k → 0` μ-a.e. and `E_μ(w_k) → 0` give `N(w_k h) → 0` for bounded `h` of finite form norm (dominated convergence in the
  three terms of `formN_mul_le`).
* `formE_le_lip`: `E_μ(w) ≤ ℓ² μ(ℝ)²` for `ℓ`-Lipschitz `w`.
* `wfar k = clamp(|x|/(k+1) - 1)` (= `1 - χ_R`, `R = k+1`): `approx_of_compact`: approximating bounded `h` with `h = 0` outside a bounded set suffices
  (the printed "multiply by `χ_R`" step; `χ_R` is taken piecewise linear, smoothness is only needed for the final mollification).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace QuantumNLS.FormCore

theorem formN_cut_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) (hN : formN μ h < ⊤) {w : ℕ → ℝ → ℝ} (hwm : ∀ k, Measurable (w k))
    (hw1 : ∀ k x, |w k x| ≤ 1) (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => w k x) atTop (𝓝 0))
    (hE : Tendsto (fun k => formE μ (w k)) atTop (𝓝 0)) :
    Tendsto (fun k => formN μ (fun x => w k x * h x)) atTop (𝓝 0) := by
  have hEh : ∫⁻ p, ENNReal.ofReal (dq h p) ∂(μ.prod μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.ne (formE_le_formN μ h)
  have hw2 : ∀ k x, w k x ^ 2 ≤ 1 := fun k x => by
    nlinarith [hw1 k x, abs_nonneg (w k x), sq_abs (w k x)]
  have hI : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (w k x ^ 2) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ)
      (F := fun k x => ENNReal.ofReal (w k x ^ 2)) (f := fun _ => 0) (fun _ => 1)
      (fun k => ENNReal.measurable_ofReal.comp ((hwm k).pow_const 2))
      (fun k => Eventually.of_forall fun x => by
        calc ENNReal.ofReal (w k x ^ 2) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hw2 k x)
          _ = 1 := by simp)
      (by rw [lintegral_const, one_mul]; exact measure_ne_top _ _)
      (hlim.mono fun x hx => by simpa using ENNReal.tendsto_ofReal (hx.pow 2))
    simpa using this
  have A1 : Tendsto (fun k => ENNReal.ofReal (M ^ 2) * ∫⁻ x, ENNReal.ofReal (w k x ^ 2) ∂μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hI (Or.inr ENNReal.ofReal_ne_top)
  have hlim2 : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun k => w k p.1) atTop (𝓝 0) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hlim
  have hI2 : Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (w k p.1 ^ 2 * dq h p) ∂(μ.prod μ)) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ.prod μ)
      (F := fun k p => ENNReal.ofReal (w k p.1 ^ 2 * dq h p)) (f := fun _ => 0)
      (fun p => ENNReal.ofReal (dq h p))
      (fun k => by
        have h1 : Measurable fun p : ℝ × ℝ => w k p.1 := (hwm k).comp measurable_fst
        exact ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_dq hh)))
      (fun k => Eventually.of_forall fun p =>
        ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (dq_nonneg _ _) (hw2 k p.1)))
      hEh
      (hlim2.mono fun p hp => by
        simpa using ENNReal.tendsto_ofReal ((hp.pow 2).mul_const (dq h p)))
    simpa using this
  have A3 : Tendsto (fun k => ENNReal.ofReal (M ^ 2) * formE μ (w k)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hE (Or.inr ENNReal.ofReal_ne_top)
  have hb : Tendsto (fun k => ENNReal.ofReal (M ^ 2) * ∫⁻ x, ENNReal.ofReal (w k x ^ 2) ∂μ +
      (2 * ∫⁻ p, ENNReal.ofReal (w k p.1 ^ 2 * dq h p) ∂(μ.prod μ) +
        2 * (ENNReal.ofReal (M ^ 2) * formE μ (w k)))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k => 2 * ∫⁻ p, ENNReal.ofReal (w k p.1 ^ 2 * dq h p) ∂(μ.prod μ)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hI2 (Or.inr (by simp))
    have h3 : Tendsto (fun k => 2 * (ENNReal.ofReal (M ^ 2) * formE μ (w k))) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul A3 (Or.inr (by simp))
    simpa using A1.add (h2.add h3)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    (fun k => formN_mul_le hh (hwm k) hM)

/-! ### Lipschitz weights -/

theorem formE_le_lip {μ : Measure ℝ} {w : ℝ → ℝ} {ℓ : ℝ}
    (hw : ∀ x y, |w x - w y| ≤ ℓ * |x - y|) :
    formE μ w ≤ ENNReal.ofReal (ℓ ^ 2) * (μ.prod μ) univ := by
  unfold formE
  calc ∫⁻ p, ENNReal.ofReal (dq w p) ∂(μ.prod μ) ≤ ∫⁻ _p, ENNReal.ofReal (ℓ ^ 2) ∂(μ.prod μ) := by
        refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
        by_cases hp : p.1 = p.2
        · simp [dq, hp]; positivity
        · unfold dq
          have hpos : 0 < (p.1 - p.2) ^ 2 := by
            have := sub_ne_zero.2 hp
            exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
          rw [div_le_iff₀ hpos]
          have h1 := hw p.1 p.2
          have h2 : (w p.1 - w p.2) ^ 2 ≤ (ℓ * |p.1 - p.2|) ^ 2 := by
            rw [← sq_abs (w p.1 - w p.2)]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          calc (w p.1 - w p.2) ^ 2 ≤ (ℓ * |p.1 - p.2|) ^ 2 := h2
            _ = ℓ ^ 2 * (p.1 - p.2) ^ 2 := by rw [mul_pow, sq_abs]
    _ = _ := lintegral_const _

/-- `clamp a = min 1 (max 0 a)`. -/
def clamp (a : ℝ) : ℝ := min 1 (max 0 a)

theorem clamp_mono {a b : ℝ} (h : a ≤ b) : clamp a ≤ clamp b :=
  min_le_min le_rfl (max_le_max le_rfl h)

theorem clamp_sub_le {a b : ℝ} (h : a ≤ b) : clamp b - clamp a ≤ b - a := by
  simp only [clamp, max_def, min_def]
  split_ifs <;> linarith

theorem abs_clamp_sub_le (a b : ℝ) : |clamp a - clamp b| ≤ |a - b| := by
  rcases le_total a b with h | h
  · have h1 := clamp_mono h
    have h2 := clamp_sub_le h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := clamp_mono h
    have h2 := clamp_sub_le h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem clamp_nonneg (a : ℝ) : 0 ≤ clamp a := le_min zero_le_one (le_max_left _ _)
theorem clamp_le_one (a : ℝ) : clamp a ≤ 1 := min_le_left _ _
theorem measurable_clamp : Measurable clamp := by unfold clamp; fun_prop

/-- The far cutoff `1 - χ_R`, `R = k+1`. -/
def wfar (k : ℕ) (x : ℝ) : ℝ := clamp (|x| / ((k : ℝ) + 1) - 1)

theorem measurable_wfar (k : ℕ) : Measurable (wfar k) := by
  unfold wfar; exact measurable_clamp.comp (by fun_prop)

theorem wfar_nonneg (k : ℕ) (x : ℝ) : 0 ≤ wfar k x := clamp_nonneg _
theorem wfar_le_one (k : ℕ) (x : ℝ) : wfar k x ≤ 1 := clamp_le_one _

theorem abs_wfar_le (k : ℕ) (x : ℝ) : |wfar k x| ≤ 1 := by
  rw [abs_le]; exact ⟨by linarith [wfar_nonneg k x], wfar_le_one k x⟩

theorem wfar_lip (k : ℕ) (x y : ℝ) : |wfar k x - wfar k y| ≤ (1 / ((k : ℝ) + 1)) * |x - y| := by
  unfold wfar
  refine le_trans (abs_clamp_sub_le _ _) ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have e : |x| / ((k : ℝ) + 1) - 1 - (|y| / ((k : ℝ) + 1) - 1) = (|x| - |y|) / ((k : ℝ) + 1) := by ring
  rw [e, abs_div, abs_of_pos hk]
  calc |(|x| - |y|)| / ((k : ℝ) + 1) ≤ |x - y| / ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) hk.le
    _ = (1 / ((k : ℝ) + 1)) * |x - y| := by ring

theorem wfar_tendsto (x : ℝ) : Tendsto (fun k : ℕ => wfar k x) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_nat_ge |x|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop K] with k hk
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : |x| / ((k : ℝ) + 1) - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hk0]
    have : (K : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simp [wfar, clamp, max_eq_left this]

theorem wfar_eq_one {k : ℕ} {x : ℝ} (hx : 2 * ((k : ℝ) + 1) ≤ |x|) : wfar k x = 1 := by
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : 1 ≤ |x| / ((k : ℝ) + 1) - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hk0]; linarith
  simp only [wfar, clamp]
  rw [max_eq_right (by linarith)]
  exact min_eq_left h1

theorem formE_wfar_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Tendsto (fun k : ℕ => formE μ (wfar k)) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, formE μ (wfar k) ≤ ENNReal.ofReal ((1 / ((k : ℝ) + 1)) ^ 2) * (μ.prod μ) univ :=
    fun k => formE_le_lip (wfar_lip k)
  have hfin : (μ.prod μ) univ ≠ ⊤ := measure_ne_top _ _
  have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 / ((k : ℝ) + 1)) ^ 2)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    simpa using ENNReal.tendsto_ofReal this
  have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 / ((k : ℝ) + 1)) ^ 2) * (μ.prod μ) univ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hfin)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le) hle

theorem wfar_cut_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ}
    (hM : ∀ x, |h x| ≤ M) (hN : formN μ h < ⊤) :
    Tendsto (fun k : ℕ => formN μ (fun x => wfar k x * h x)) atTop (𝓝 0) :=
  formN_cut_tendsto hh hM hN measurable_wfar abs_wfar_le (Eventually.of_forall wfar_tendsto) formE_wfar_tendsto

theorem dq_neg (f : ℝ → ℝ) (p : ℝ × ℝ) : dq (fun x => -f x) p = dq f p := by
  unfold dq
  rw [show (-f p.1 - -f p.2) ^ 2 = (f p.1 - f p.2) ^ 2 by ring]

theorem formN_neg (μ : Measure ℝ) (f : ℝ → ℝ) : formN μ (fun x => -f x) = formN μ f := by
  simp only [formN, formL2, formE, neg_sq, dq_neg]

/-- Reduction to compact support: if every bounded measurable `g` of finite form norm vanishing outside a bounded set is approximable,
then every bounded measurable `h` of finite form norm is. -/
theorem approx_of_compact {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hc : ∀ g : ℝ → ℝ, Measurable g → (∃ M : ℝ, ∀ x, |g x| ≤ M) → (∃ R : ℝ, ∀ x, R ≤ |x| → g x = 0) →
      formN μ g < ⊤ → Approx μ g)
    {h : ℝ → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ x, |h x| ≤ M) (hN : formN μ h < ⊤) : Approx μ h := by
  apply approx_of_close hh
  intro ε hε
  have ht := wfar_cut_tendsto hh hM hN
  have hev : ∀ᶠ k : ℕ in atTop, formN μ (fun x => wfar k x * h x) < ENNReal.ofReal ε :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨k, hk⟩ := hev.exists
  have hwm := measurable_wfar k
  have hgm : Measurable fun x => (1 - wfar k x) * h x := (measurable_const.sub hwm).mul hh
  refine ⟨fun x => (1 - wfar k x) * h x, hgm, ?_, ?_⟩
  · refine hc _ hgm ⟨M, fun x => ?_⟩ ⟨2 * ((k : ℝ) + 1), fun x hx => ?_⟩ ?_
    · rw [abs_mul]
      have h0 : 0 ≤ 1 - wfar k x := by linarith [wfar_le_one k x]
      have h1 : 1 - wfar k x ≤ 1 := by linarith [wfar_nonneg k x]
      rw [abs_of_nonneg h0]
      calc (1 - wfar k x) * |h x| ≤ 1 * M := mul_le_mul h1 (hM x) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · rw [wfar_eq_one hx]; simp
    · have e : (fun x => h x - (1 - wfar k x) * h x) = fun x => wfar k x * h x := by funext x; ring
      -- N(g) ≤ 2 N(h) + 2 N(w h)
      have e2 : (fun x => (1 - wfar k x) * h x) = fun x => h x + (-(wfar k x * h x)) := by funext x; ring
      rw [e2]
      have hwh : Measurable fun x => wfar k x * h x := hwm.mul hh
      refine lt_of_le_of_lt (formN_add_le hh hwh.neg) ?_
      have hneg : formN μ (fun x => -(wfar k x * h x)) = formN μ (fun x => wfar k x * h x) :=
        formN_neg μ _
      rw [hneg]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hN, ENNReal.mul_lt_top (by simp) (lt_trans hk ENNReal.ofReal_lt_top)⟩
  · have e : (fun x => h x - (1 - wfar k x) * h x) = fun x => wfar k x * h x := by funext x; ring
    rw [e]; exact hk

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.formN_cut_tendsto
#print axioms QuantumNLS.FormCore.approx_of_compact
