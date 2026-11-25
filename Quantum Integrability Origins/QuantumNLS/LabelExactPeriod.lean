import QuantumNLS.LabelBlock
import QuantumNLS.BetheSpectralContinuity

/-!
# PROP-005 `prop:B3-exact-period` (label_periods.tex:252-301)

Setting (label_periods.tex:252-266). Cutpoints `x₋ < x₊` as in `eq:B3-two-cuts`, `h > 0`, `Γ` the
positively oriented boundary of `{x₋ < Re z < x₊, |Im z| < h}`;
`A_N(z) = ∏_j (1 + ic/(z − q_j))`, `ℓ_N(z) = Σ_j log(1 + ic/(z − q_j))`, each logarithm defined by its
Taylor series at one.

Statement. For all sufficiently large `N`, `m_n/N = −(1/(2πκ)) ∮_Γ ℓ_N(z) dz`, `m_n = #{j : n_j = n}`.
The actual transfer eigenvalue satisfies `s_N(z) = A_N(z) + e^{izL}/A_N(z − ic)` and
`s_N(z) ∏(z − q_j) = ∏(z − q_j + ic) + e^{izL} ∏(z − q_j − ic)` (the second by analytic continuation
at roots).

Realization.
* `rectIntegral f a b h` — the positively oriented boundary integral of the rectangle
  `[a,b] × [−h,h]`, written as four interval integrals (the same expression as in mathlib's
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` for the corners `a − ih`, `b + ih`);
* `logT u = Σ_{k≥1} (−1)^{k+1} u^k / k` (the Taylor series at one, as a `tsum`), `ellN`, `AN`;
* `root_period` (eq:B3-one-root-period): `∮_Γ log(1 + ic/(z − q)) dz = 2πi·ic` if `x₋ < q < x₊`, `0`
  if `q < x₋` or `q > x₊`, whenever `|z − q| > 2c` on `Γ`. Proof: explicit primitives on the four
  sides: `(z − q) log(1 + ic/(z − q)) + ic·log(±(z − q + ic))` (the branch of the second term switches
  on the left side when the shifted pole is enclosed), instead of termwise integration of the Taylor
  series — the value is the same;
* **`period_of_block`**: deterministic form; **`exact_period_uniform`**, **`exact_period_seq`**:
  for all sufficiently large `N` (uniform neighbourhood form and along sequences), on PROP-004
  (LB1 `LabelBlock` `5e10dacd…`, own, read-only);
* `difference_riccati`, `polynomial_identity`: the identities for the exact transfer formula
  `TransferSeparation.sFun` (accepted chain, `0206f863…`); **`spectralValue_polynomial_identity`**
  (for all `z`, by continuity) and `spectralValue_difference_riccati` for the actual transfer
  eigenvalue `BetheSpectralContinuity.spectralValue` (`f6772092…`, read-only), whose value off the
  roots is `sFun` (`basis_eigenvalue`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Filter Topology Set Complex intervalIntegral
open scoped BigOperators

namespace QuantumNLS.LabelExactPeriod

open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts

/-! ## 1. Rectangle boundary integrals -/

/-- `∮_Γ f`, `Γ` the positively oriented boundary of `[a,b] × [−h,h]`. -/
def rectIntegral (f : ℂ → ℂ) (a b h : ℝ) : ℂ :=
  (∫ x in a..b, f (x + ((-h : ℝ) : ℂ) * I)) - (∫ x in a..b, f (x + h * I)) +
    I • (∫ y in (-h)..h, f (b + y * I)) - I • (∫ y in (-h)..h, f (a + y * I))

lemma ii_h {f : ℂ → ℂ} {a b y0 : ℝ} (hf : ∀ x ∈ uIcc a b, ContinuousAt f (x + y0 * I)) :
    IntervalIntegrable (fun x : ℝ => f (x + y0 * I)) volume a b :=
  ContinuousOn.intervalIntegrable fun x hx =>
    ((hf x hx).comp_of_eq (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + y0 * I) x)
      rfl).continuousWithinAt

lemma ii_v {f : ℂ → ℂ} {c d x0 : ℝ} (hf : ∀ y ∈ uIcc c d, ContinuousAt f (x0 + y * I)) :
    IntervalIntegrable (fun y : ℝ => f (x0 + y * I)) volume c d :=
  ContinuousOn.intervalIntegrable fun y hy =>
    ((hf y hy).comp_of_eq (by fun_prop : ContinuousAt (fun y : ℝ => (x0 : ℂ) + y * I) y)
      rfl).continuousWithinAt

lemma side_h {f F : ℂ → ℂ} {a b y0 : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f (x + y0 * I)) (x + y0 * I))
    (hf : ∀ x ∈ uIcc a b, ContinuousAt f (x + y0 * I)) :
    ∫ x in a..b, f (x + y0 * I) = F (b + y0 * I) - F (a + y0 * I) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + y0 * I)) (fun x hx => ?_)
    (ii_h hf)
  have h1 : HasDerivAt (fun w : ℂ => F (w + y0 * I)) (f (x + y0 * I)) (x : ℂ) :=
    (hF x hx).comp_add_const _ _
  exact h1.comp_ofReal

lemma side_v {f F : ℂ → ℂ} {c d x0 : ℝ}
    (hF : ∀ y ∈ uIcc c d, HasDerivAt F (f (x0 + y * I)) (x0 + y * I))
    (hf : ∀ y ∈ uIcc c d, ContinuousAt f (x0 + y * I)) :
    I • ∫ y in c..d, f (x0 + y * I) = F (x0 + d * I) - F (x0 + c * I) := by
  have : ∫ y in c..d, f (x0 + y * I) * I = F (x0 + d * I) - F (x0 + c * I) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (x0 + y * I)) (fun y hy => ?_)
      ((ii_v hf).mul_const I)
    have h0 : HasDerivAt (fun w : ℂ => x0 + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x0 : ℂ)
    have h1 : HasDerivAt (fun w : ℂ => F (x0 + w * I)) (f (x0 + y * I) * I) (y : ℂ) :=
      (hF y hy).comp (y : ℂ) h0
    exact h1.comp_ofReal
  rw [← this, intervalIntegral.integral_mul_const, smul_eq_mul, mul_comm]

/-- The boundary integral from primitives: `F` on the bottom, top and right sides, `G` on the left. -/
lemma rect_eq_of_primitives {f F G : ℂ → ℂ} {a b h : ℝ}
    (hFb : ∀ x ∈ uIcc a b, HasDerivAt F (f (x + ((-h : ℝ) : ℂ) * I)) (x + ((-h : ℝ) : ℂ) * I))
    (hFt : ∀ x ∈ uIcc a b, HasDerivAt F (f (x + h * I)) (x + h * I))
    (hFr : ∀ y ∈ uIcc (-h) h, HasDerivAt F (f (b + y * I)) (b + y * I))
    (hGl : ∀ y ∈ uIcc (-h) h, HasDerivAt G (f (a + y * I)) (a + y * I))
    (hcb : ∀ x ∈ uIcc a b, ContinuousAt f (x + ((-h : ℝ) : ℂ) * I))
    (hct : ∀ x ∈ uIcc a b, ContinuousAt f (x + h * I))
    (hcr : ∀ y ∈ uIcc (-h) h, ContinuousAt f (b + y * I))
    (hcl : ∀ y ∈ uIcc (-h) h, ContinuousAt f (a + y * I)) :
    rectIntegral f a b h =
      F (a + h * I) - F (a + ((-h : ℝ) : ℂ) * I) - (G (a + h * I) - G (a + ((-h : ℝ) : ℂ) * I)) := by
  unfold rectIntegral
  rw [side_h hFb hcb, side_h hFt hct, side_v hFr hcr, side_v hGl hcl]
  ring

/-- Linearity over finite sums. -/
lemma rectIntegral_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {a b h : ℝ}
    (hcb : ∀ i ∈ s, ∀ x ∈ uIcc a b, ContinuousAt (f i) (x + ((-h : ℝ) : ℂ) * I))
    (hct : ∀ i ∈ s, ∀ x ∈ uIcc a b, ContinuousAt (f i) (x + h * I))
    (hcr : ∀ i ∈ s, ∀ y ∈ uIcc (-h) h, ContinuousAt (f i) (b + y * I))
    (hcl : ∀ i ∈ s, ∀ y ∈ uIcc (-h) h, ContinuousAt (f i) (a + y * I)) :
    rectIntegral (fun z => ∑ i ∈ s, f i z) a b h = ∑ i ∈ s, rectIntegral (f i) a b h := by
  unfold rectIntegral
  rw [intervalIntegral.integral_finsetSum fun i hi => ii_h (hcb i hi),
    intervalIntegral.integral_finsetSum fun i hi => ii_h (hct i hi),
    intervalIntegral.integral_finsetSum fun i hi => ii_v (hcr i hi),
    intervalIntegral.integral_finsetSum fun i hi => ii_v (hcl i hi), Finset.smul_sum,
    Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- Boundary values determine the boundary integral. -/
lemma rectIntegral_congr {f g : ℂ → ℂ} {a b h : ℝ}
    (hb : ∀ x ∈ uIcc a b, f (x + ((-h : ℝ) : ℂ) * I) = g (x + ((-h : ℝ) : ℂ) * I))
    (ht : ∀ x ∈ uIcc a b, f (x + h * I) = g (x + h * I))
    (hr : ∀ y ∈ uIcc (-h) h, f (b + y * I) = g (b + y * I))
    (hl : ∀ y ∈ uIcc (-h) h, f (a + y * I) = g (a + y * I)) :
    rectIntegral f a b h = rectIntegral g a b h := by
  unfold rectIntegral
  rw [intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ht,
    intervalIntegral.integral_congr hr, intervalIntegral.integral_congr hl]

/-! ## 2. One root -/

lemma log_sub_log_neg_of_im_pos {T : ℂ} (hT : 0 < T.im) : log T - log (-T) = Real.pi * I := by
  apply Complex.ext
  · simp [log_re, norm_neg]
  · simp only [sub_im, log_im, mul_im, I_im, mul_one, I_re, mul_zero, add_zero, ofReal_re,
      ofReal_im]
    rw [arg_neg_eq_arg_sub_pi_of_im_pos hT]; ring

lemma log_neg_sub_log_of_im_neg {B : ℂ} (hB : B.im < 0) : log (-B) - log B = Real.pi * I := by
  apply Complex.ext
  · simp [log_re, norm_neg]
  · simp only [sub_im, log_im, mul_im, I_im, mul_one, I_re, mul_zero, add_zero, ofReal_re,
      ofReal_im]
    rw [arg_neg_eq_arg_add_pi_of_im_neg hB]; ring

lemma small_arg {c q : ℝ} (hc : 0 < c) {z : ℂ} (hz : 2 * c < ‖z - q‖) :
    ‖I * c / (z - q)‖ < 1 / 2 := by
  have hw : z - q ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hnw : 0 < ‖z - q‖ := norm_pos_iff.2 hw
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc, div_lt_iff₀ hnw]; linarith

lemma deriv_facts {c q : ℝ} (hc : 0 < c) {z : ℂ} (hz : 2 * c < ‖z - q‖) :
    HasDerivAt (fun z => log (1 + I * c / (z - q)))
        ((-(I * c) / (z - q) ^ 2) / (1 + I * c / (z - q))) z ∧
    HasDerivAt (fun z => (z - q) * log (1 + I * c / (z - q)))
      (log (1 + I * c / (z - q)) - I * c / (z - q + I * c)) z := by
  have hw : z - q ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hu := small_arg hc hz
  have hre : 0 < (1 + I * c / (z - q)).re := by
    have := Complex.abs_re_le_norm (I * c / (z - q))
    simp only [add_re, one_re]
    linarith [neg_abs_le (I * c / (z - q)).re]
  have hslit : 1 + I * c / (z - q) ∈ slitPlane := Or.inl hre
  have hne1 : 1 + I * c / (z - q) ≠ 0 := slitPlane_ne_zero hslit
  have hw2 : z - q + I * c ≠ 0 := by
    intro h
    have : z - q = -(I * c) := by linear_combination h
    rw [this, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc] at hz
    linarith
  have hg : HasDerivAt (fun z => 1 + I * c / (z - q)) (-(I * c) / (z - q) ^ 2) z := by
    have h1 := (((hasDerivAt_id' z).sub_const (q : ℂ)).inv hw).const_mul (I * c)
    have h2 := h1.const_add 1
    convert h2 using 1
    · funext w; simp [div_eq_mul_inv]
    · ring
  have hlog := hg.clog hslit
  refine ⟨hlog, ?_⟩
  have hP : HasDerivAt (fun w => (w - q) * log (1 + I * c / (w - q))) _ z :=
    ((hasDerivAt_id' z).sub_const (q : ℂ)).mul hlog
  refine hP.congr_deriv ?_
  have e1 : 1 + I * c / (z - q) = (z - q + I * c) / (z - q) := by field_simp
  rw [e1]
  field_simp
  ring

lemma hasDerivAt_Q {c q : ℝ} {z : ℂ} (hs : z - q + I * c ∈ slitPlane) :
    HasDerivAt (fun z => I * c * log (z - q + I * c)) (I * c / (z - q + I * c)) z := by
  have h := ((((hasDerivAt_id' z).sub_const (q : ℂ)).add_const (I * c)).clog hs).const_mul (I * c)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_Q' {c q : ℝ} {z : ℂ} (hs : -(z - q + I * c) ∈ slitPlane) :
    HasDerivAt (fun z => I * c * log (-(z - q + I * c))) (I * c / (z - q + I * c)) z := by
  have h0 : HasDerivAt (fun w : ℂ => -(w - q + I * c)) (-1) z :=
    (((hasDerivAt_id' z).sub_const (q : ℂ)).add_const (I * c)).neg
  have h := (h0.clog hs).const_mul (I * c)
  refine h.congr_deriv ?_
  rw [neg_div_neg_eq, mul_one_div]

lemma bdry_dist {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
    (hqb : 2 * c < |q - b|) :
    (∀ x : ℝ, 2 * c < ‖(x : ℂ) + ((-h : ℝ) : ℂ) * I - q‖) ∧
    (∀ x : ℝ, 2 * c < ‖(x : ℂ) + h * I - q‖) ∧
    (∀ y : ℝ, 2 * c < ‖(b : ℂ) + y * I - q‖) ∧ (∀ y : ℝ, 2 * c < ‖(a : ℂ) + y * I - q‖) := by
  refine ⟨fun x => ?_, fun x => ?_, fun y => ?_, fun y => ?_⟩
  · refine lt_of_lt_of_le ?_ (Complex.abs_im_le_norm _)
    simp; rw [abs_of_pos (by linarith)]; linarith
  · refine lt_of_lt_of_le ?_ (Complex.abs_im_le_norm _)
    simp; rw [abs_of_pos (by linarith)]; linarith
  · refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm _)
    simp; rw [abs_sub_comm]; exact hqb
  · refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm _)
    simp; rw [abs_sub_comm]; exact hqa

/-- **eq:B3-one-root-period.** -/
theorem root_period {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
    (hqb : 2 * c < |q - b|) (hab : a < b) :
    rectIntegral (fun z => log (1 + I * c / (z - q))) a b h =
      if a < q ∧ q < b then 2 * Real.pi * I * (I * c) else 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := bdry_dist (q := q) (a := a) (b := b) hc hch hqa hqb
  set f := fun z : ℂ => log (1 + I * c / (z - q))
  set P := fun z : ℂ => (z - q) * log (1 + I * c / (z - q))
  set Q := fun z : ℂ => I * c * log (z - q + I * c)
  set Q' := fun z : ℂ => I * c * log (-(z - q + I * c))
  have hPQ : ∀ z : ℂ, 2 * c < ‖z - q‖ → z - q + I * c ∈ slitPlane →
      HasDerivAt (P + Q) (f z) z :=
    fun z hz hs => ((deriv_facts hc hz).2.add (hasDerivAt_Q hs)).congr_deriv (by ring)
  have hPQ' : ∀ z : ℂ, 2 * c < ‖z - q‖ → -(z - q + I * c) ∈ slitPlane →
      HasDerivAt (P + Q') (f z) z :=
    fun z hz hs => ((deriv_facts hc hz).2.add (hasDerivAt_Q' hs)).congr_deriv (by ring)
  have hcont : ∀ z : ℂ, 2 * c < ‖z - q‖ → ContinuousAt f z := fun z hz =>
    (deriv_facts hc hz).1.continuousAt
  have hc1 := fun x (_ : x ∈ uIcc a b) => hcont _ (d1 x)
  have hc2 := fun x (_ : x ∈ uIcc a b) => hcont _ (d2 x)
  have hc3 := fun y (_ : y ∈ uIcc (-h) h) => hcont _ (d3 y)
  have hc4 := fun y (_ : y ∈ uIcc (-h) h) => hcont _ (d4 y)
  by_cases hin : a < q ∧ q < b
  · simp only [hin, and_self, ↓reduceIte]
    rw [rect_eq_of_primitives (F := P + Q) (G := P + Q')
      (fun x _ => hPQ _ (d1 x) (Or.inr (by simp; linarith)))
      (fun x _ => hPQ _ (d2 x) (Or.inr (by simp; linarith)))
      (fun y _ => hPQ _ (d3 y) (Or.inl (by simp; linarith [hin.2])))
      (fun y _ => hPQ' _ (d4 y) (Or.inl (by simp; linarith [hin.1]))) hc1 hc2 hc3 hc4]
    have hT : 0 < ((a : ℂ) + h * I - q + I * c).im := by simp; linarith
    have hB : ((a : ℂ) + ((-h : ℝ) : ℂ) * I - q + I * c).im < 0 := by simp; linarith
    have e1 := log_sub_log_neg_of_im_pos hT
    have e2 := log_neg_sub_log_of_im_neg hB
    simp only [Pi.add_apply, P, Q, Q']
    linear_combination (I * c) * e1 + (I * c) * e2
  · simp only [hin, ↓reduceIte]
    have h1 : q ≠ a := by intro h; rw [h, sub_self, abs_zero] at hqa; linarith
    have h2 : q ≠ b := by intro h; rw [h, sub_self, abs_zero] at hqb; linarith
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · rw [rect_eq_of_primitives (F := P + Q) (G := P + Q)
        (fun x hx => hPQ _ (d1 x) (Or.inl (by rw [uIcc_of_le hab.le] at hx; simp; linarith [hx.1])))
        (fun x hx => hPQ _ (d2 x) (Or.inl (by rw [uIcc_of_le hab.le] at hx; simp; linarith [hx.1])))
        (fun y _ => hPQ _ (d3 y) (Or.inl (by simp; linarith)))
        (fun y _ => hPQ _ (d4 y) (Or.inl (by simp; linarith))) hc1 hc2 hc3 hc4]
      ring
    · have hqb' : b < q := by
        rcases lt_or_gt_of_ne h2 with h | h
        · exact absurd ⟨hgt, h⟩ hin
        · exact h
      rw [rect_eq_of_primitives (F := P + Q') (G := P + Q')
        (fun x hx => hPQ' _ (d1 x) (Or.inl (by rw [uIcc_of_le hab.le] at hx; simp; linarith [hx.2])))
        (fun x hx => hPQ' _ (d2 x) (Or.inl (by rw [uIcc_of_le hab.le] at hx; simp; linarith [hx.2])))
        (fun y _ => hPQ' _ (d3 y) (Or.inl (by simp; linarith)))
        (fun y _ => hPQ' _ (d4 y) (Or.inl (by simp; linarith))) hc1 hc2 hc3 hc4]
      ring

/-! ## 3. The exact period -/

/-- The Taylor series of `log(1 + u)` at one: `Σ_{k≥1} (−1)^{k+1} u^k / k`. -/
def logT (u : ℂ) : ℂ := ∑' k : ℕ, (-1) ^ (k + 1) * u ^ k / k

lemma logT_eq {u : ℂ} (hu : ‖u‖ < 1) : logT u = log (1 + u) :=
  (Complex.hasSum_taylorSeries_log hu).tsum_eq

/-- `ℓ_N(z) = Σ_j log(1 + ic/(z − q_j))`, logarithms by their Taylor series at one, `c = κ/N`. -/
def ellN (κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ j, logT (I * ((κ / N : ℝ) : ℂ) / (z - q j))

/-- **Exact period, deterministic form.** -/
theorem period_of_block {L κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (B : OnShellBethe L κ N)
    {n : ℤ} {xm xp δ h : ℝ} (hlt : xm < xp) (hblock : BlockConclusion B n xm xp δ)
    (hsmall : 2 * (κ / N) < δ) (hsmallh : 2 * (κ / N) < h) :
    (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) =
      -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ B.q) xm xp h := by
  set c : ℝ := κ / N with hc
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hc0 : 0 < c := div_pos hκ hNr
  have hqa : ∀ j, 2 * c < |B.q j - xm| := fun j => lt_of_lt_of_le hsmall (hblock j).2.1
  have hqb : ∀ j, 2 * c < |B.q j - xp| := fun j => lt_of_lt_of_le hsmall (hblock j).2.2
  have hd := fun j => bdry_dist (q := B.q j) (a := xm) (b := xp) hc0 hsmallh (hqa j) (hqb j)
  have hcont : ∀ j, ∀ z : ℂ, 2 * c < ‖z - B.q j‖ →
      ContinuousAt (fun z => log (1 + I * c / (z - B.q j))) z := fun j z hz =>
    (deriv_facts hc0 hz).1.continuousAt
  have hval : ∀ j, ∀ z : ℂ, 2 * c < ‖z - B.q j‖ →
      logT (I * (c : ℂ) / (z - B.q j)) = log (1 + I * c / (z - B.q j)) := fun j z hz =>
    logT_eq ((small_arg hc0 hz).trans (by norm_num))
  have hcongr : rectIntegral (ellN κ B.q) xm xp h =
      rectIntegral (fun z => ∑ j, log (1 + I * c / (z - B.q j))) xm xp h := by
    refine rectIntegral_congr (fun x _ => ?_) (fun x _ => ?_) (fun y _ => ?_) (fun y _ => ?_) <;>
      exact Finset.sum_congr rfl fun j _ => hval j _ (by first
        | exact (hd j).1 _ | exact (hd j).2.1 _ | exact (hd j).2.2.1 _ | exact (hd j).2.2.2 _)
  rw [hcongr, rectIntegral_sum Finset.univ (fun j _ x _ => hcont j _ ((hd j).1 x))
    (fun j _ x _ => hcont j _ ((hd j).2.1 x)) (fun j _ y _ => hcont j _ ((hd j).2.2.1 y))
    (fun j _ y _ => hcont j _ ((hd j).2.2.2 y))]
  rw [Finset.sum_congr rfl fun j _ => root_period hc0 hsmallh (hqa j) (hqb j) hlt]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfilt : (Finset.univ.filter fun j => xm < B.q j ∧ B.q j < xp) =
      Finset.univ.filter fun j => B.n j = n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hblock j).1
  rw [hfilt]
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [hc]
  push_cast
  field_simp
  rw [I_sq]
  ring

/-- **PROP-005, exact period, uniform form**: there are a weak neighbourhood `U` of `μ` and `N₀` such
that every on-shell configuration with `N ≥ N₀` and `L_N ∈ U` satisfies
`m_n/N = −(1/(2πκ)) ∮_Γ ℓ_N`. -/
theorem exact_period_uniform {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) =
          -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ B.q) xm xp h := by
  have hκ := S.hκ
  obtain ⟨δ, hδ, U, hU, N₀, hN₀⟩ := label_block_uniform S hμ hxm hxp hlt h1 h2 h3 h4
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * κ / min δ h)
  refine ⟨U, hU, max N₀ M, fun N hN hNN B hB => ?_⟩
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hmin : 0 < min δ h := lt_min hδ hh
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hNN
  have hsm : 2 * (κ / N) < min δ h := by
    have h5 : 2 * κ / min δ h < N := lt_of_lt_of_le hM hMN
    rw [div_lt_iff₀ hmin] at h5
    rw [mul_div_assoc', div_lt_iff₀ hNr]
    linarith [mul_comm (N : ℝ) (min δ h)]
  exact period_of_block hκ hN B hlt (hN₀ N hN (le_of_max_le_left hNN) B hB)
    (lt_of_lt_of_le hsm (min_le_left _ _)) (lt_of_lt_of_le hsm (min_le_right _ _))

/-- **PROP-005, exact period along a sequence**: for all sufficiently large `k`. -/
theorem exact_period_seq {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∀ᶠ k in atTop, (((Finset.univ.filter fun j => (B k).n j = n).card : ℝ) / N k : ℂ) =
      -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ (B k).q) xm xp h := by
  obtain ⟨U, hU, N₀, hN₀⟩ := exact_period_uniform S hμ hxm hxp hlt hh h1 h2 h3 h4
  filter_upwards [hconv.eventually (mem_of_superset hU subset_rfl),
    hNtop.eventually (eventually_ge_atTop N₀)] with k hk1 hk2
  exact hN₀ (N k) (hN k) hk2 (B k) hk1

/-! ## 4. The transfer identities -/

/-- `A_N(z) = ∏_j (1 + ic/(z − q_j))`. -/
def AN (c : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ := ∏ j, (1 + I * c / (z - q j))

lemma prod_one_sub_mul_AN (c : ℝ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ q j)
    (hz' : ∀ j, z ≠ q j + I * c) :
    (∏ j, (1 - I * c / (z - q j))) * AN c q (z - I * c) = 1 := by
  unfold AN
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  have h1 : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
  have h2 : z - I * c - q j ≠ 0 := by
    intro h; exact hz' j (by linear_combination h)
  field_simp
  ring

/-- **eq:B3-difference-riccati** for the exact transfer formula `sFun`. -/
theorem difference_riccati (L c : ℝ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ q j)
    (hz' : ∀ j, z ≠ q j + I * c) :
    TransferSeparation.sFun L c q z = AN c q z + exp (I * L * z) / AN c q (z - I * c) := by
  unfold TransferSeparation.sFun
  have h := prod_one_sub_mul_AN c q hz hz'
  rw [div_eq_mul_inv, eq_inv_of_mul_eq_one_left h]
  rfl

/-- **eq:B3-polynomial-identity** for the exact transfer formula `sFun` (off the roots). -/
theorem polynomial_identity (L c : ℝ) {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ q j) :
    TransferSeparation.sFun L c q z * ∏ j, (z - q j) =
      ∏ j, (z - q j + I * c) + exp (I * L * z) * ∏ j, (z - q j - I * c) := by
  unfold TransferSeparation.sFun
  rw [add_mul, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    have h1 : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
    field_simp
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
    field_simp

/-- **eq:B3-polynomial-identity for the actual transfer eigenvalue**, at every `z` (analytic
continuation at the roots). -/
theorem spectralValue_polynomial_identity (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) :
    BetheSpectralContinuity.spectralValue L hc hn z *
        ∏ j, (z - BetheSmooth.sourceRoots L n c j) =
      ∏ j, (z - BetheSmooth.sourceRoots L n c j + I * c) +
        exp (I * L * z) * ∏ j, (z - BetheSmooth.sourceRoots L n c j - I * c) := by
  set q := BetheSmooth.sourceRoots L n c
  have hbe := BetheSpectralContinuity.basis_eigenvalue L hc hn
  have hdense : Dense ((Set.range fun k => (q k : ℂ))ᶜ) :=
    (Set.finite_range _).countable.dense_compl ℂ
  have hcl : Continuous fun z => BetheSpectralContinuity.spectralValue L hc hn z *
      ∏ j, (z - q j) :=
    hbe.1.continuous.mul (continuous_finsetProd _ fun j _ => continuous_id.sub continuous_const)
  have hcr : Continuous fun z : ℂ => ∏ j, (z - q j + I * c) +
      exp (I * L * z) * ∏ j, (z - q j - I * c) :=
    (continuous_finsetProd _ fun j _ => (continuous_id.sub continuous_const).add continuous_const).add
      ((continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_finsetProd _ fun j _ => (continuous_id.sub continuous_const).sub continuous_const))
  have heq := Continuous.ext_on hdense hcl hcr fun w hw => by
    have hw' : ∀ k, w ≠ (q k : ℂ) := fun k h => hw ⟨k, h.symm⟩
    show BetheSpectralContinuity.spectralValue L hc hn w * ∏ j, (w - q j) = _
    rw [hbe.2.1 w hw']
    exact polynomial_identity L c q hw'
  exact congrFun heq z

/-- **eq:B3-difference-riccati for the actual transfer eigenvalue** (where `A_N(z − ic)` is defined). -/
theorem spectralValue_difference_riccati (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j)
    (hz' : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j + I * c) :
    BetheSpectralContinuity.spectralValue L hc hn z =
      AN c (BetheSmooth.sourceRoots L n c) z +
        exp (I * L * z) / AN c (BetheSmooth.sourceRoots L n c) (z - I * c) := by
  rw [(BetheSpectralContinuity.basis_eigenvalue L hc hn).2.1 z hz]
  exact difference_riccati L c _ hz hz'

end QuantumNLS.LabelExactPeriod

#print axioms QuantumNLS.LabelExactPeriod.root_period
#print axioms QuantumNLS.LabelExactPeriod.period_of_block
#print axioms QuantumNLS.LabelExactPeriod.exact_period_uniform
#print axioms QuantumNLS.LabelExactPeriod.exact_period_seq
#print axioms QuantumNLS.LabelExactPeriod.difference_riccati
#print axioms QuantumNLS.LabelExactPeriod.polynomial_identity
#print axioms QuantumNLS.LabelExactPeriod.spectralValue_polynomial_identity
#print axioms QuantumNLS.LabelExactPeriod.spectralValue_difference_riccati
