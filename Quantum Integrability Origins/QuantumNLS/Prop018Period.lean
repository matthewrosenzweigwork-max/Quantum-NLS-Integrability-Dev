import QuantumNLS.HaarNonlinearAbstract

/-!
# PROP-018 `Q7A:prop:reconstruct`, part 1: the exact polynomial period `Q7A:eq:period`

Source: `source-text/chapters/propagation/window_reconstruction.tex:180-196`: for a single root the polynomial-weighted contour integral
of `log(1 + ic/(z − q))` is computed exactly, and `−(1/(2πc)) Re ∮ p ℓ_N = Σ_j Σ_v (−1)^v c^{2v}/(2v+1)! p^{(2v)}(q_j)`, whose
`v ≥ 1` terms are `O(c²)` per root (no order-one first-derivative contribution).

Realization (rectangles `Gam a b h`, positively oriented `rectIntegral`, by explicit primitives as in EP1 `root_period`):
* `rect_inv`: `∮ dz/(z − w) = 2πi` for `w` inside; `rect_zero_of_prim`: `∮ F' = 0` for an entire primitive;
* `rect_sumpow_inv`: `∮ (Σ_r c_r z^{e_r})/(z − w) dz = 2πi Σ_r c_r w^{e_r}`;
* `poly`, `prim` (real coefficient polynomial `p(z) = Σ_{r≤d} p_r z^r` and its primitive);
* **`root_period_poly`**: `∮ p(z) log(1 + ic/(z − q)) dz = 2πi (P(q) − P(q − ic))` for every root `q` inside (integration by parts:
  `(P ℓ)' = p ℓ + P ℓ'`, `ℓ' = (z − q + ic)⁻¹ − (z − q)⁻¹`);
* `mono_period`, **`period_err`**: `|−(1/c) Re(i(P(q) − P(q − ic))) − p(q)| ≤ c² Σ_r |p_r| (1 + |q|)^{r+1}` for `0 < c ≤ 1` (the
  linear term is the exact `p(q)`, the quadratic term is purely imaginary, the rest is `O(c³)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018Period

open QuantumNLS.PeriodReconstruction QuantumNLS.PeriodTwoTerm QuantumNLS.LabelExactPeriod

/-! ## 1. Rectangle residues by primitives -/

lemma rect_zero_of_prim {f F : ℂ → ℂ} (hF : ∀ z, HasDerivAt F (f z) z) (hf : Continuous f) (a b h : ℝ) :
    rectIntegral f a b h = 0 := by
  rw [rect_eq_of_primitives (F := F) (G := F) (fun x _ => hF _) (fun x _ => hF _) (fun y _ => hF _)
    (fun y _ => hF _) (fun x _ => hf.continuousAt) (fun x _ => hf.continuousAt) (fun y _ => hf.continuousAt)
    (fun y _ => hf.continuousAt)]
  ring

/-- `∮ dz/(z − w) = 2πi` for `w` inside the rectangle. -/
theorem rect_inv {a b h : ℝ} {w : ℂ} (hwa : a < w.re) (hwb : w.re < b) (hwh : |w.im| < h) :
    rectIntegral (fun z => (z - w)⁻¹) a b h = 2 * Real.pi * I := by
  rw [abs_lt] at hwh
  have hd : ∀ z : ℂ, z - w ∈ slitPlane → HasDerivAt (fun z => log (z - w)) ((z - w)⁻¹) z := fun z hz => by
    have := ((hasDerivAt_id z).sub_const w).clog hz
    simpa [one_div] using this
  have hd' : ∀ z : ℂ, -(z - w) ∈ slitPlane → HasDerivAt (fun z => log (-(z - w))) ((z - w)⁻¹) z := fun z hz => by
    have h1 : HasDerivAt (fun z : ℂ => -(z - w)) (-1) z := ((hasDerivAt_id' z).sub_const w).neg
    refine (h1.clog hz).congr_deriv ?_
    rw [neg_div_neg_eq, one_div]
  have hc : ∀ z : ℂ, z ≠ w → ContinuousAt (fun z => (z - w)⁻¹) z := fun z hz =>
    (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hz)
  have hne : ∀ z : ℂ, z.im ≠ w.im ∨ z.re ≠ w.re → z ≠ w := fun z h h0 => by
    rcases h with h | h <;> exact h (by rw [h0])
  rw [rect_eq_of_primitives (F := fun z => log (z - w)) (G := fun z => log (-(z - w)))
    (fun x _ => hd _ (Or.inr (by simp; linarith)))
    (fun x _ => hd _ (Or.inr (by simp; linarith)))
    (fun y _ => hd _ (Or.inl (by simp; linarith)))
    (fun y _ => hd' _ (Or.inl (by simp; linarith)))
    (fun x _ => hc _ (hne _ (Or.inl (by simp; linarith))))
    (fun x _ => hc _ (hne _ (Or.inl (by simp; linarith))))
    (fun y _ => hc _ (hne _ (Or.inr (by simp; linarith))))
    (fun y _ => hc _ (hne _ (Or.inr (by simp; linarith))))]
  have hT : 0 < ((a : ℂ) + h * I - w).im := by simp; linarith
  have hB : ((a : ℂ) + ((-h : ℝ) : ℂ) * I - w).im < 0 := by simp; linarith
  have e1 := log_sub_log_neg_of_im_pos hT
  have e2 := log_neg_sub_log_of_im_neg hB
  linear_combination e1 + e2

lemma continuous_pow_inv_ne {w : ℂ} (n : ℕ) {z : ℂ} (hz : z ≠ w) :
    ContinuousAt (fun z : ℂ => z ^ n * (z - w)⁻¹) z :=
  (continuousAt_id.pow n).mul ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hz))

lemma Gam_ne {a b h : ℝ} {w : ℂ} (hwa : a < w.re) (hwb : w.re < b) (hwh : |w.im| < h) {z : ℂ}
    (hz : z ∈ Gam a b h) : z ≠ w := by
  rw [abs_lt] at hwh
  intro h0; subst h0
  rcases hz with ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩ <;> linarith

/-- `∮ zⁿ/(z − w) dz = 2πi wⁿ`. -/
theorem rect_pow_inv {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) {w : ℂ} (hwa : a < w.re) (hwb : w.re < b)
    (hwh : |w.im| < h) (n : ℕ) :
    rectIntegral (fun z => z ^ n * (z - w)⁻¹) a b h = 2 * Real.pi * I * w ^ n := by
  induction n with
  | zero => simp only [pow_zero, one_mul, mul_one]; exact rect_inv hwa hwb hwh
  | succ n ih =>
    have e : rectIntegral (fun z => z ^ (n + 1) * (z - w)⁻¹) a b h =
        rectIntegral (fun z => z ^ n + w * (z ^ n * (z - w)⁻¹)) a b h :=
      QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam hab hh fun z hz => by
        have hzw : z - w ≠ 0 := sub_ne_zero.2 (Gam_ne hwa hwb hwh hz)
        field_simp; ring
    rw [e, rectIntegral_add (f := fun z => z ^ n) (g := fun z => w * (z ^ n * (z - w)⁻¹)) hab hh
      (fun z _ => (continuous_pow n).continuousAt)
      (fun z hz => continuousAt_const.mul (continuous_pow_inv_ne n (Gam_ne hwa hwb hwh hz))),
      rectIntegral_const_mul, ih,
      rect_zero_of_prim (F := fun z => z ^ (n + 1) / (n + 1)) (fun z => by
        have := (hasDerivAt_pow (n + 1) z).div_const ((n : ℂ) + 1)
        refine this.congr_deriv ?_
        have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        field_simp; push_cast; ring) (continuous_pow n)]
    ring

/-- `∮ (Σ_r c_r z^{e_r})/(z − w) dz = 2πi Σ_r c_r w^{e_r}`. -/
theorem rect_sumpow_inv {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) {w : ℂ} (hwa : a < w.re) (hwb : w.re < b)
    (hwh : |w.im| < h) (s : Finset ℕ) (c : ℕ → ℂ) (e : ℕ → ℕ) :
    rectIntegral (fun z => (∑ r ∈ s, c r * z ^ e r) * (z - w)⁻¹) a b h =
      2 * Real.pi * I * ∑ r ∈ s, c r * w ^ e r := by
  have e1 : (fun z => (∑ r ∈ s, c r * z ^ e r) * (z - w)⁻¹) =
      fun z => ∑ r ∈ s, c r * (z ^ e r * (z - w)⁻¹) := by
    funext z; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by ring
  have hc : ∀ r ∈ s, ∀ z ∈ Gam a b h, ContinuousAt (fun z => c r * (z ^ e r * (z - w)⁻¹)) z :=
    fun r _ z hz => continuousAt_const.mul (continuous_pow_inv_ne (e r) (Gam_ne hwa hwb hwh hz))
  rw [e1, rectIntegral_sum s (fun r hr x hx => hc r hr _ (bot_mem hab hx))
    (fun r hr x hx => hc r hr _ (top_mem hab hx)) (fun r hr y hy => hc r hr _ (right_mem hh hy))
    (fun r hr y hy => hc r hr _ (left_mem hh hy)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rectIntegral_const_mul, rect_pow_inv hab hh hwa hwb hwh]; ring

/-! ## 2. Polynomials and the single-root period -/

/-- `p(z) = Σ_{r≤d} p_r z^r` with real coefficients. -/
def poly (p : ℕ → ℝ) (d : ℕ) (z : ℂ) : ℂ := ∑ r ∈ Finset.range (d + 1), (p r : ℂ) * z ^ r

/-- Its primitive `P(z) = Σ_{r≤d} p_r z^{r+1}/(r+1)`. -/
def prim (p : ℕ → ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (d + 1), ((p r : ℂ) / ((r : ℂ) + 1)) * z ^ (r + 1)

lemma hasDerivAt_prim (p : ℕ → ℝ) (d : ℕ) (z : ℂ) : HasDerivAt (prim p d) (poly p d z) z := by
  unfold prim poly
  have h := HasDerivAt.sum (u := Finset.range (d + 1)) (A := fun r z => ((p r : ℂ) / ((r : ℂ) + 1)) * z ^ (r + 1))
    (A' := fun r => ((p r : ℂ) / ((r : ℂ) + 1)) * (((r + 1 : ℕ) : ℂ) * z ^ r)) (x := z)
    fun r _ => ((hasDerivAt_pow (r + 1) z).const_mul _)
  convert h using 1
  · funext w; simp [Finset.sum_apply]
  · refine Finset.sum_congr rfl fun r _ => ?_
    have : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    push_cast; field_simp

lemma continuous_poly (p : ℕ → ℝ) (d : ℕ) : Continuous (poly p d) := by
  unfold poly; fun_prop

lemma continuous_prim (p : ℕ → ℝ) (d : ℕ) : Continuous (prim p d) := by
  unfold prim; fun_prop

lemma prim_eq_sumpow (p : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    prim p d z = ∑ r ∈ Finset.range (d + 1), ((p r : ℂ) / ((r : ℂ) + 1)) * z ^ (r + 1) := rfl

/-- **The single-root polynomial period**: `∮ p(z) log(1 + ic/(z − q)) dz = 2πi (P(q) − P(q − ic))`. -/
theorem root_period_poly {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
    (hqb : 2 * c < |q - b|) (hab : a < b) (hin1 : a < q) (hin2 : q < b) (p : ℕ → ℝ) (d : ℕ) :
    rectIntegral (fun z => poly p d z * log (1 + I * c / (z - q))) a b h =
      2 * Real.pi * I * (prim p d (q : ℂ) - prim p d ((q : ℂ) - I * c)) := by
  obtain ⟨d1, d2, d3, d4⟩ := bdry_dist (q := q) (a := a) (b := b) hc hch hqa hqb
  have hh : 0 ≤ h := by linarith
  -- points of the contour are far from the root
  have hfar : ∀ z ∈ Gam a b h, 2 * c < ‖z - q‖ := by
    intro z hz
    rcases hz with ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩
    · have := Complex.abs_im_le_norm (z - q); simp at this; rw [h1, abs_neg, abs_of_nonneg hh] at this; linarith
    · have := Complex.abs_im_le_norm (z - q); simp at this; rw [h1, abs_of_nonneg hh] at this; linarith
    · have := Complex.abs_re_le_norm (z - q); simp at this; rw [h1, abs_sub_comm] at this; linarith
    · have := Complex.abs_re_le_norm (z - q); simp at this; rw [h1, abs_sub_comm] at this; linarith
  set ℓ : ℂ → ℂ := fun z => log (1 + I * c / (z - q)) with hℓ
  set ℓ' : ℂ → ℂ := fun z => (-(I * c) / (z - q) ^ 2) / (1 + I * c / (z - q)) with hℓ'
  have hℓd : ∀ z : ℂ, 2 * c < ‖z - q‖ → HasDerivAt ℓ (ℓ' z) z := fun z hz => (deriv_facts hc hz).1
  have hne1 : ∀ z : ℂ, 2 * c < ‖z - q‖ → z - q ≠ 0 := fun z hz h0 => by rw [h0, norm_zero] at hz; linarith
  have hne2 : ∀ z : ℂ, 2 * c < ‖z - q‖ → 1 + I * c / (z - q) ≠ 0 := fun z hz => by
    have := small_arg hc hz
    intro h0
    have : ‖I * c / (z - q)‖ = 1 := by
      rw [show I * c / (z - q) = -1 by linear_combination h0, norm_neg, norm_one]
    linarith
  have hℓ'c : ∀ z : ℂ, 2 * c < ‖z - q‖ → ContinuousAt ℓ' z := fun z hz => by
    have h1 : ContinuousAt (fun z : ℂ => z - q) z := continuousAt_id.sub continuousAt_const
    exact ((continuousAt_const.div (h1.pow 2) (pow_ne_zero 2 (hne1 z hz))).div
      (continuousAt_const.add (continuousAt_const.div h1 (hne1 z hz))) (hne2 z hz))
  -- integration by parts: `∮ (p ℓ + P ℓ') = 0`
  have hparts : rectIntegral (fun z => poly p d z * ℓ z + prim p d z * ℓ' z) a b h = 0 := by
    have hF : ∀ z : ℂ, 2 * c < ‖z - q‖ → HasDerivAt (fun z => prim p d z * ℓ z)
        (poly p d z * ℓ z + prim p d z * ℓ' z) z := fun z hz =>
      (hasDerivAt_prim p d z).mul (hℓd z hz)
    have hcont : ∀ z : ℂ, 2 * c < ‖z - q‖ → ContinuousAt (fun z => poly p d z * ℓ z + prim p d z * ℓ' z) z :=
      fun z hz => ((continuous_poly p d).continuousAt.mul (hℓd z hz).continuousAt).add
        ((continuous_prim p d).continuousAt.mul (hℓ'c z hz))
    rw [rect_eq_of_primitives (F := fun z => prim p d z * ℓ z) (G := fun z => prim p d z * ℓ z)
      (fun x _ => hF _ (d1 x)) (fun x _ => hF _ (d2 x)) (fun y _ => hF _ (d3 y)) (fun y _ => hF _ (d4 y))
      (fun x _ => hcont _ (d1 x)) (fun x _ => hcont _ (d2 x)) (fun y _ => hcont _ (d3 y))
      (fun y _ => hcont _ (d4 y))]
    ring
  have hc1 : ∀ z ∈ Gam a b h, ContinuousAt (fun z => poly p d z * ℓ z) z := fun z hz =>
    (continuous_poly p d).continuousAt.mul (hℓd z (hfar z hz)).continuousAt
  have hc2 : ∀ z ∈ Gam a b h, ContinuousAt (fun z => prim p d z * ℓ' z) z := fun z hz =>
    (continuous_prim p d).continuousAt.mul (hℓ'c z (hfar z hz))
  rw [rectIntegral_add hab.le hh hc1 hc2] at hparts
  -- `ℓ' = (z − (q − ic))⁻¹ − (z − q)⁻¹` on the contour
  set w1 : ℂ := (q : ℂ) - I * c
  have hw1 : a < w1.re ∧ w1.re < b ∧ |w1.im| < h := by
    refine ⟨by simp [w1]; linarith, by simp [w1]; linarith, ?_⟩
    simp [w1, abs_of_pos hc]; linarith
  have hw0 : a < (q : ℂ).re ∧ (q : ℂ).re < b ∧ |(q : ℂ).im| < h := by
    refine ⟨by simp; linarith, by simp; linarith, ?_⟩
    simp; linarith
  have e2 : rectIntegral (fun z => prim p d z * ℓ' z) a b h =
      rectIntegral (fun z => prim p d z * (z - w1)⁻¹ + (-1 : ℂ) * (prim p d z * (z - q)⁻¹)) a b h := by
    refine QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam hab.le hh fun z hz => ?_
    have h1 := hne1 z (hfar z hz)
    have h2 := hne2 z (hfar z hz)
    have h3 : z - w1 ≠ 0 := by
      intro h0
      have e0 : z - q = -(I * c) := by simp only [w1] at h0; linear_combination h0
      have := hfar z hz
      rw [e0, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at this
      linarith
    simp only [hℓ', w1] at h3 ⊢
    have e : 1 + I * c / (z - q) = (z - (q - I * c)) / (z - q) := by field_simp; ring
    rw [e]
    field_simp
    ring
  rw [e2, rectIntegral_add (f := fun z => prim p d z * (z - w1)⁻¹)
    (g := fun z => (-1 : ℂ) * (prim p d z * (z - q)⁻¹)) hab.le hh
    (fun z hz => (continuous_prim p d).continuousAt.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.2 (Gam_ne hw1.1 hw1.2.1 hw1.2.2 hz))))
    (fun z hz => continuousAt_const.mul ((continuous_prim p d).continuousAt.mul
      ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 (Gam_ne hw0.1 hw0.2.1 hw0.2.2 hz))))),
    rectIntegral_const_mul] at hparts
  simp_rw [prim_eq_sumpow] at hparts
  rw [rect_sumpow_inv hab.le hh hw1.1 hw1.2.1 hw1.2.2, rect_sumpow_inv hab.le hh hw0.1 hw0.2.1 hw0.2.2]
    at hparts
  simp only [prim_eq_sumpow]
  linear_combination hparts

/-! ## 3. The period error -/

/-- `s_k = Re(i (−i)^k)`-type sign factors are bounded by one. -/
lemma norm_re_le_one (k : ℕ) : |((-I) * (-I) ^ (k + 2)).re| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]

/-- The monomial period: for `n ≥ 1`, `0 < c ≤ 1`,
`|−(1/(nc)) Re(i(qⁿ − (q − ic)ⁿ)) − q^{n−1}| ≤ c² (1 + |q|)ⁿ`. -/
theorem mono_period (n : ℕ) (hn : 1 ≤ n) (q c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    |-(1 / (n * c)) * (I * ((q : ℂ) ^ n - ((q : ℂ) - I * c) ^ n)).re - q ^ (n - 1)| ≤
      c ^ 2 * (1 + |q|) ^ n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℂ := -(I * c) with hy
  have hexp : ((q : ℂ) - I * c) ^ n = ∑ k ∈ Finset.range (n + 1), y ^ k * (q : ℂ) ^ (n - k) * (n.choose k) := by
    rw [show (q : ℂ) - I * c = y + q by rw [hy]; ring]; exact add_pow y q n
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- `n = 1`: exact
    have : n = 1 := by omega
    subst this
    simp only [pow_one, Nat.sub_self, pow_zero]
    have e : (I * ((q : ℂ) - ((q : ℂ) - I * c))).re = -c := by
      simp [mul_comm]
    rw [e]
    have : -(1 / ((1 : ℕ) * c)) * -c - 1 = 0 := by push_cast; field_simp; ring
    rw [this, abs_zero]; positivity
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- peel the `k = 0, 1` terms
  have hsplit : ∑ k ∈ Finset.range (m + 2 + 1), y ^ k * (q : ℂ) ^ (m + 2 - k) * ((m + 2).choose k) =
      ∑ k ∈ Finset.range (m + 1), y ^ (k + 2) * (q : ℂ) ^ (m - k) * ((m + 2).choose (k + 2)) +
        y * (q : ℂ) ^ (m + 1) * (m + 2) + (q : ℂ) ^ (m + 2) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have e1 : ∀ k ∈ Finset.range (m + 1), y ^ (k + 1 + 1) * (q : ℂ) ^ (m + 2 - (k + 1 + 1)) *
        ((m + 2).choose (k + 1 + 1) : ℂ) = y ^ (k + 2) * (q : ℂ) ^ (m - k) * ((m + 2).choose (k + 2) : ℂ) :=
      fun k _ => by rw [show m + 2 - (k + 1 + 1) = m - k by omega]
    rw [Finset.sum_congr rfl e1]
    simp only [zero_add, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      pow_one, Nat.choose_one_right]
    rw [show m + 2 - 1 = m + 1 by omega]
    push_cast; ring
  -- the real part
  set t : ℕ → ℝ := fun k => ((-I) * (-I) ^ (k + 2)).re with ht
  have hre : (I * ((q : ℂ) ^ (m + 2) - ((q : ℂ) - I * c) ^ (m + 2))).re =
      -((m + 2 : ℕ) : ℝ) * c * q ^ (m + 1) +
        ∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) * t k := by
    rw [hexp, hsplit]
    have hIy : I * y = c := by rw [hy]; ring_nf; rw [I_sq]; ring
    have hS : I * ∑ k ∈ Finset.range (m + 1), y ^ (k + 2) * (q : ℂ) ^ (m - k) * ((m + 2).choose (k + 2) : ℂ) =
        -∑ k ∈ Finset.range (m + 1), ((((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) : ℝ) : ℂ) *
          ((-I) * (-I) ^ (k + 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hy, show -(I * (c : ℂ)) = (-I) * c by ring, mul_pow]
      push_cast; ring
    have e1 : I * ((q : ℂ) ^ (m + 2) - (∑ k ∈ Finset.range (m + 1), y ^ (k + 2) * (q : ℂ) ^ (m - k) *
        ((m + 2).choose (k + 2)) + y * (q : ℂ) ^ (m + 1) * (m + 2) + (q : ℂ) ^ (m + 2))) =
        -((c * (m + 2) * q ^ (m + 1) : ℝ) : ℂ) +
          ∑ k ∈ Finset.range (m + 1), ((((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) : ℝ) : ℂ) *
            ((-I) * (-I) ^ (k + 2)) := by
      rw [show I * ((q : ℂ) ^ (m + 2) - (∑ k ∈ Finset.range (m + 1), y ^ (k + 2) * (q : ℂ) ^ (m - k) *
          ((m + 2).choose (k + 2)) + y * (q : ℂ) ^ (m + 1) * (m + 2) + (q : ℂ) ^ (m + 2))) =
          -(I * ∑ k ∈ Finset.range (m + 1), y ^ (k + 2) * (q : ℂ) ^ (m - k) * ((m + 2).choose (k + 2) : ℂ)) -
            (I * y) * (q : ℂ) ^ (m + 1) * (m + 2) by ring, hIy, hS]
      push_cast; ring
    rw [e1, add_re, neg_re, ofReal_re, re_sum]
    simp only [re_ofReal_mul, ht]
    push_cast; ring
  rw [hre]
  have hm : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have e3 : -(1 / (((m + 2 : ℕ) : ℝ) * c)) * (-((m + 2 : ℕ) : ℝ) * c * q ^ (m + 1) +
      ∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) * t k) -
        q ^ (m + 2 - 1) =
      -(1 / (((m + 2 : ℕ) : ℝ) * c)) *
        ∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) * t k := by
    rw [show m + 2 - 1 = m + 1 by omega]
    field_simp; ring
  rw [e3, abs_mul, abs_neg, abs_of_pos (by positivity)]
  -- bound the sum: the `k = 0` term vanishes, the rest is `O(c³)`
  have ht0 : t 0 = 0 := by simp only [ht]; ring_nf; simp
  have hterm : ∀ k ∈ Finset.range (m + 1),
      |((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) * t k| ≤
        c ^ 3 * (((m + 2).choose (k + 2) : ℝ) * |q| ^ (m + 2 - (k + 2))) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rw [ht0, mul_zero, abs_zero]; positivity
    · simp only [abs_mul, abs_pow, Nat.abs_cast, abs_of_pos hc0]
      have h1 : |t k| ≤ 1 := norm_re_le_one k
      have h2 : c ^ (k + 2) ≤ c ^ 3 := pow_le_pow_of_le_one hc0.le hc1 (by omega)
      rw [show m + 2 - (k + 2) = m - k by omega]
      have : 0 ≤ ((m + 2).choose (k + 2) : ℝ) * |q| ^ (m - k) := by positivity
      calc ((m + 2).choose (k + 2) : ℝ) * |q| ^ (m - k) * c ^ (k + 2) * |t k|
          ≤ ((m + 2).choose (k + 2) : ℝ) * |q| ^ (m - k) * c ^ 3 * 1 := by gcongr
        _ = _ := by ring
  have hsum : ∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * |q| ^ (m + 2 - (k + 2)) ≤
      (1 + |q|) ^ (m + 2) := by
    have hfull := add_pow (1 : ℝ) |q| (m + 2)
    rw [hfull]
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have e4 : ∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * |q| ^ (m + 2 - (k + 2)) =
        ∑ k ∈ Finset.range (m + 1), (1 : ℝ) ^ (k + 1 + 1) * |q| ^ (m + 2 - (k + 1 + 1)) *
          ((m + 2).choose (k + 1 + 1) : ℝ) :=
      Finset.sum_congr rfl fun k _ => by rw [one_pow, one_mul, mul_comm]
    rw [e4]
    have : 0 ≤ (1 : ℝ) ^ (0 + 1) * |q| ^ (m + 2 - (0 + 1)) * ((m + 2).choose (0 + 1) : ℝ) := by positivity
    have : 0 ≤ (1 : ℝ) ^ 0 * |q| ^ (m + 2 - 0) * ((m + 2).choose 0 : ℝ) := by positivity
    linarith
  calc 1 / (((m + 2 : ℕ) : ℝ) * c) *
        |∑ k ∈ Finset.range (m + 1), ((m + 2).choose (k + 2) : ℝ) * q ^ (m - k) * c ^ (k + 2) * t k|
      ≤ 1 / (((m + 2 : ℕ) : ℝ) * c) * (c ^ 3 * (1 + |q|) ^ (m + 2)) := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ c ^ 2 * (1 + |q|) ^ (m + 2) := by
        have h1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        have : 0 ≤ c ^ 3 * (1 + |q|) ^ (m + 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 this]

/-- **The polynomial period error**: `|−(1/c) Re(i(P(q) − P(q − ic))) − p(q)| ≤ c² Σ_r |p_r|(1 + |q|)^{r+1}`. -/
theorem period_err (p : ℕ → ℝ) (d : ℕ) (q c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    |-(1 / c) * (I * (prim p d (q : ℂ) - prim p d ((q : ℂ) - I * c))).re - (poly p d (q : ℂ)).re| ≤
      c ^ 2 * ∑ r ∈ Finset.range (d + 1), |p r| * (1 + |q|) ^ (r + 1) := by
  unfold prim poly
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, re_sum, re_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hr : ((r : ℂ) + 1) = (((r + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have e : -(1 / c) * (I * ((p r : ℂ) / ((r : ℂ) + 1) * (q : ℂ) ^ (r + 1) -
      (p r : ℂ) / ((r : ℂ) + 1) * ((q : ℂ) - I * c) ^ (r + 1))).re - ((p r : ℂ) * (q : ℂ) ^ r).re =
      p r * (-(1 / (((r + 1 : ℕ) : ℝ) * c)) * (I * ((q : ℂ) ^ (r + 1) - ((q : ℂ) - I * c) ^ (r + 1))).re -
        q ^ (r + 1 - 1)) := by
    rw [hr, show (I * ((p r : ℂ) / (((r + 1 : ℕ) : ℝ) : ℂ) * (q : ℂ) ^ (r + 1) -
        (p r : ℂ) / (((r + 1 : ℕ) : ℝ) : ℂ) * ((q : ℂ) - I * c) ^ (r + 1))) =
        ((p r / ((r + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (I * ((q : ℂ) ^ (r + 1) - ((q : ℂ) - I * c) ^ (r + 1))) by
          push_cast; ring,
      re_ofReal_mul, show ((p r : ℂ) * (q : ℂ) ^ r).re = p r * q ^ r by
        rw [← ofReal_pow, ← ofReal_mul, ofReal_re], Nat.add_sub_cancel]
    have : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e, abs_mul]
  have := mono_period (r + 1) (by omega) q c hc0 hc1
  calc |p r| * |-(1 / (((r + 1 : ℕ) : ℝ) * c)) * (I * ((q : ℂ) ^ (r + 1) - ((q : ℂ) - I * c) ^ (r + 1))).re -
        q ^ (r + 1 - 1)| ≤ |p r| * (c ^ 2 * (1 + |q|) ^ (r + 1)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = c ^ 2 * (|p r| * (1 + |q|) ^ (r + 1)) := by ring

end QuantumNLS.Prop018Period

#print axioms QuantumNLS.Prop018Period.rect_inv
#print axioms QuantumNLS.Prop018Period.root_period_poly
#print axioms QuantumNLS.Prop018Period.mono_period
#print axioms QuantumNLS.Prop018Period.period_err
