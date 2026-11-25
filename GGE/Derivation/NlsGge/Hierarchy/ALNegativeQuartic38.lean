import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Weights.ComplexEntire
import NlsGge.Weights.DerivativeAsymptotics
import NlsGge.Hierarchy.ALGaussianNormalizer38

/-! # L11 (batch 38): `D:prop:negativeAL` (paper/v2.tex l.2331-2372)

Along the physical lattice plane wave `u(jh) = t e^{2πikjh}` (`α_j = h u(jh)`, `h = 1/L`,
`L = 2N+1`, `|k| ≤ N`), with `θ_k = πkh`, `ω = 2 sin θ_k / h`, `c = cos θ_k`:

* `E_{W,h} = W(ω)t² + b_{h,k} t⁴ + O_h(t⁶)`, `b_{h,k} = (h²/2)W(ω) - (h²ω/8)W'(ω) + (c²/2)W''(ω)`;
* `M_d = h t² + h³ t⁴/2 + O_h(t⁶)`, so the quartic coefficient of `R_h` is `b_{h,k} - h³/2`;
* for `k = N`: `b_{h,N}/W(ω_{h,N}) = -(√2/4) h^{3/2} + O(h^{7/4}) < 0` for `h` small;
* hence for fine grids there are arbitrarily small nonzero plane waves with `R_h < 0`, `f_h > 1`.

The proof follows the source: `D:eq:planegap` (`ALPlaneWaveGap38`), the spectral formula
(`alEnergy38_spectral`), the substitution `q = sin(hλ-θ_k)/h`, `q = t y`, an `arsinh` expansion
with uniform remainders, and a fourth-order Taylor expansion of `W` at `ω` (odd terms integrate
to zero against the semicircle).  All remainders are explicit (`|…| ≤ C t⁶`, resp. `C h^{7/4}`).
Real-analysis core (`taylor4_38`, `OU38`, `alPlane_lam_integral38`, `alPlane_y_expansion38`) is
independent of the AL objects and is valid for any `C⁴` weight. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Set

theorem deriv_pow_bound38 {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    {K : ℝ} (hK0 : 0 ≤ K) (m : ℕ) (hK : ∀ x : ℝ, |x| ≤ 1 → |f' x| ≤ K * |x| ^ m) {s : ℝ}
    (hs : |s| ≤ 1) : |f s| ≤ K * |s| ^ (m + 1) := by
  have hconv : Convex ℝ (uIcc (0:ℝ) s) := convex_uIcc 0 s
  have := hconv.norm_image_sub_le_of_norm_deriv_le (f := f) (C := K * |s| ^ m)
    (fun x _ => (hf x).differentiableAt)
    (fun x hx => by
      rw [(hf x).deriv]
      have hxs : |x| ≤ |s| := by
        rcases le_total 0 s with h | h
        · rw [uIcc_of_le h] at hx; rw [abs_of_nonneg hx.1, abs_of_nonneg h]; exact hx.2
        · rw [uIcc_of_ge h] at hx; rw [abs_of_nonpos hx.2, abs_of_nonpos h]; linarith [hx.1]
      calc ‖f' x‖ = |f' x| := rfl
        _ ≤ K * |x| ^ m := hK x (hxs.trans hs)
        _ ≤ K * |s| ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxs m) hK0)
    (left_mem_uIcc (a := (0:ℝ)) (b := s)) (right_mem_uIcc (a := (0:ℝ)) (b := s))
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [pow_succ]; linarith

/-- one integration step of the Taylor chain -/
theorem taylor_step38 {g g' Q Q' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (x₀ : ℝ)
    (hQ : ∀ s, HasDerivAt Q (Q' s) s) (hQ0 : Q 0 = g x₀) {K : ℝ} (hK0 : 0 ≤ K) (m : ℕ)
    (hb : ∀ s : ℝ, |s| ≤ 1 → |g' (x₀ + s) - Q' s| ≤ K * |s| ^ m) {s : ℝ} (hs : |s| ≤ 1) :
    |g (x₀ + s) - Q s| ≤ K * |s| ^ (m + 1) := by
  have := deriv_pow_bound38 (f := fun s => g (x₀ + s) - Q s) (f' := fun s => g' (x₀ + s) - Q' s)
    (fun x => ((hg (x₀ + x)).comp_const_add x₀ x).sub (hQ x)) (by simp [hQ0]) hK0 m hb hs
  simpa using this

/-- Fourth-order Taylor remainder with explicit constant. -/
theorem taylor4_38 {f f1 f2 f3 f4 : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f1 x) x) (h2 : ∀ x, HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, HasDerivAt f2 (f3 x) x) (h4 : ∀ x, HasDerivAt f3 (f4 x) x)
    (hc : Continuous f4) (x₀ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |s| ≤ 1 →
      |f (x₀ + s) - (f x₀ + f1 x₀ * s + f2 x₀ * s ^ 2 / 2 + f3 x₀ * s ^ 3 / 6)| ≤ M * s ^ 4 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hM0 : 0 ≤ |M| := abs_nonneg _
  have hb3 : ∀ s : ℝ, |s| ≤ 1 → |f4 (x₀ + s) - 0| ≤ |M| * |s| ^ 0 := by
    intro s hs
    have := hM (x₀ + s) ⟨by linarith [(abs_le.mp hs).1], by linarith [(abs_le.mp hs).2]⟩
    simpa using this.trans (le_abs_self M)
  have r3 := fun s (hs : |s| ≤ 1) => taylor_step38 (g := f3) (g' := f4) (Q := fun _ => f3 x₀)
    (Q' := fun _ => 0) h4 x₀ (fun s => hasDerivAt_const s _) rfl hM0 0 hb3 hs
  have hb2 : ∀ s : ℝ, |s| ≤ 1 → |f3 (x₀ + s) - f3 x₀| ≤ |M| * |s| ^ 1 := by
    intro s hs; simpa using r3 s hs
  have r2 := fun s (hs : |s| ≤ 1) => taylor_step38 (g := f2) (g' := f3)
    (Q := fun s => f2 x₀ + f3 x₀ * s) (Q' := fun _ => f3 x₀) h3 x₀
    (fun s => by simpa using ((hasDerivAt_id s).const_mul (f3 x₀)).const_add (f2 x₀)) (by simp) hM0 1 hb2 hs
  have hb1 : ∀ s : ℝ, |s| ≤ 1 → |f2 (x₀ + s) - (f2 x₀ + f3 x₀ * s)| ≤ |M| * |s| ^ 2 :=
    fun s hs => r2 s hs
  have r1 := fun s (hs : |s| ≤ 1) => taylor_step38 (g := f1) (g' := f2)
    (Q := fun s => f1 x₀ + f2 x₀ * s + f3 x₀ * s ^ 2 / 2) (Q' := fun s => f2 x₀ + f3 x₀ * s) h2 x₀
    (fun s => by
      have := (((hasDerivAt_id s).const_mul (f2 x₀)).const_add (f1 x₀)).fun_add
        (((hasDerivAt_pow 2 s).const_mul (f3 x₀)).div_const 2)
      exact this.congr_deriv (by simp; ring)) (by simp) hM0 2 hb1 hs
  have hb0 : ∀ s : ℝ, |s| ≤ 1 → |f1 (x₀ + s) - (f1 x₀ + f2 x₀ * s + f3 x₀ * s ^ 2 / 2)| ≤
      |M| * |s| ^ 3 := fun s hs => r1 s hs
  refine ⟨|M|, hM0, ?_⟩
  intro s hs
  have := taylor_step38 (g := f) (g' := f1)
    (Q := fun s => f x₀ + f1 x₀ * s + f2 x₀ * s ^ 2 / 2 + f3 x₀ * s ^ 3 / 6)
    (Q' := fun s => f1 x₀ + f2 x₀ * s + f3 x₀ * s ^ 2 / 2) h1 x₀
    (fun s => by
      have := ((((hasDerivAt_id s).const_mul (f1 x₀)).const_add (f x₀)).fun_add
        (((hasDerivAt_pow 2 s).const_mul (f2 x₀)).div_const 2)).fun_add
        (((hasDerivAt_pow 3 s).const_mul (f3 x₀)).div_const 6)
      exact this.congr_deriv (by simp; ring)) (by simp) hM0 3 hb0 hs
  have e : |s| ^ (3 + 1) = s ^ 4 := by
    rw [show (3 + 1 : ℕ) = 4 from rfl, pow_abs, abs_of_nonneg (by positivity)]
  rw [e] at this
  exact this


theorem inv_sqrt_one_add_sq_bound38 (s : ℝ) :
    |(Real.sqrt (1 + s ^ 2))⁻¹ - (1 - s ^ 2 / 2)| ≤ |s| ^ 4 := by
  set a := Real.sqrt (1 + s ^ 2) with ha
  have ha2 : a ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have ha1 : 1 ≤ a := by
    rw [ha]; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg s]
  have hs2 : s ^ 2 = a ^ 2 - 1 := by linarith
  have hlt : a - 1 ≤ s ^ 2 / 2 := by nlinarith
  have hapos : 0 < a := by linarith
  have e : a⁻¹ - (1 - s ^ 2 / 2) = (a - 1) ^ 2 * (a + 2) / (2 * a) := by
    rw [hs2]; field_simp; ring
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h4 : |s| ^ 4 = (s ^ 2) ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  rw [h4]
  have h1 : (a - 1) ^ 2 ≤ (s ^ 2 / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hlt 2
  have h2 : 0 ≤ (a - 1) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg h2 (by linarith : (0:ℝ) ≤ a), sq_nonneg s, sq_nonneg (s ^ 2)]

theorem sqrt_one_sub_bound38 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |Real.sqrt (1 - u) - (1 - u / 2)| ≤ u ^ 2 / 2 := by
  set a := Real.sqrt (1 - u) with ha
  have ha2 : a ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hle : a ≤ 1 - u / 2 := by nlinarith [sq_nonneg (a - (1 - u / 2))]
  rw [abs_of_nonpos (by linarith)]
  have : (1 - u / 2 - a) * (1 - u / 2 + a) = u ^ 2 / 4 := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - u / 2 - a) ha0]

theorem inv_sqrt_one_sub_bound38 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    |(Real.sqrt (1 - u))⁻¹ - (1 + u / 2)| ≤ 2 * u ^ 2 := by
  set a := Real.sqrt (1 - u) with ha
  have ha2 : a ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hale : a ≤ 1 := by nlinarith
  have hage : (7:ℝ) / 10 ≤ a := by nlinarith
  have hapos : 0 < a := by linarith
  have hu : u = 1 - a ^ 2 := by linarith
  have e : a⁻¹ - (1 + u / 2) = (1 - a) ^ 2 * (a + 2) / (2 * a) := by
    rw [hu]; field_simp; ring
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h1a : (1 - a) * (1 + a) = u := by rw [hu]; ring
  have hlt : 1 - a ≤ u := by nlinarith
  have h2 : (1 - a) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith) hlt 2
  nlinarith [mul_nonneg (sq_nonneg (1 - a)) (by linarith : (0:ℝ) ≤ a), sq_nonneg u]

theorem arsinh_bound38 {x : ℝ} (hx : |x| ≤ 1) : |Real.arsinh x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 := by
  have := taylor_step38 (g := Real.arsinh) (g' := fun x => (Real.sqrt (1 + x ^ 2))⁻¹)
    (Q := fun s => s - s ^ 3 / 6) (Q' := fun s => 1 - s ^ 2 / 2)
    (fun x => Real.hasDerivAt_arsinh x) 0
    (fun s => by
      have := (hasDerivAt_id s).fun_sub (((hasDerivAt_pow 3 s)).div_const 6)
      exact this.congr_deriv (by simp; ring)) (by simp) (K := 1) zero_le_one 4
    (fun s _ => by simpa using inv_sqrt_one_add_sq_bound38 s) hx
  simpa using this


/-! ### Uniform big-O in `(t, y)`, `t ↓ 0`, `|y| ≤ 1` -/

/-- `f t y = O(t^n)` as `t ↓ 0`, uniformly for `|y| ≤ 1`, with explicit constants. -/
def OU38 (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ t y : ℝ, 0 ≤ t → t ≤ δ → |y| ≤ 1 → |f t y| ≤ C * t ^ n

theorem OU38.add {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : OU38 n f) (hg : OU38 n g) :
    OU38 n (fun t y => f t y + g t y) := by
  obtain ⟨C₁, δ₁, hδ₁, h₁⟩ := hf
  obtain ⟨C₂, δ₂, hδ₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t y ht0 htδ hy => ?_⟩
  have a := h₁ t y ht0 (htδ.trans (min_le_left _ _)) hy
  have b := h₂ t y ht0 (htδ.trans (min_le_right _ _)) hy
  calc |f t y + g t y| ≤ |f t y| + |g t y| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem OU38.neg {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : OU38 n f) : OU38 n (fun t y => -f t y) := by
  obtain ⟨C, δ, hδ, h⟩ := hf
  exact ⟨C, δ, hδ, fun t y ht0 htδ hy => by simpa using h t y ht0 htδ hy⟩

theorem OU38.sub {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : OU38 n f) (hg : OU38 n g) :
    OU38 n (fun t y => f t y - g t y) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem OU38.mul {n m : ℕ} {f g : ℝ → ℝ → ℝ} (hf : OU38 n f) (hg : OU38 m g) :
    OU38 (n + m) (fun t y => f t y * g t y) := by
  obtain ⟨C₁, δ₁, hδ₁, h₁⟩ := hf
  obtain ⟨C₂, δ₂, hδ₂, h₂⟩ := hg
  refine ⟨|C₁| * |C₂|, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t y ht0 htδ hy => ?_⟩
  have a := h₁ t y ht0 (htδ.trans (min_le_left _ _)) hy
  have b := h₂ t y ht0 (htδ.trans (min_le_right _ _)) hy
  rw [abs_mul, pow_add]
  calc |f t y| * |g t y| ≤ (|C₁| * t ^ n) * (|C₂| * t ^ m) := by
        apply mul_le_mul (a.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
          (b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
          (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem OU38.mono {n k : ℕ} {f : ℝ → ℝ → ℝ} (hf : OU38 (n + k) f) : OU38 n f := by
  obtain ⟨C, δ, hδ, h⟩ := hf
  refine ⟨|C|, min δ 1, lt_min hδ one_pos, fun t y ht0 htδ hy => ?_⟩
  have a := h t y ht0 (htδ.trans (min_le_left _ _)) hy
  have ht1 : t ≤ 1 := htδ.trans (min_le_right _ _)
  have : t ^ (n + k) ≤ t ^ n := pow_le_pow_of_le_one ht0 ht1 (by omega)
  calc |f t y| ≤ C * t ^ (n + k) := a
    _ ≤ |C| * t ^ (n + k) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C| * t ^ n := mul_le_mul_of_nonneg_left this (abs_nonneg _)

theorem OU38.congr {n : ℕ} {f g : ℝ → ℝ → ℝ} (h : ∀ t y, f t y = g t y) (hf : OU38 n f) :
    OU38 n g := by
  have : f = g := funext fun t => funext fun y => h t y
  rw [← this]; exact hf

theorem OU38.of_bdd {f : ℝ → ℝ → ℝ} (B : ℝ) (h : ∀ t y : ℝ, 0 ≤ t → t ≤ 1 → |y| ≤ 1 → |f t y| ≤ B) :
    OU38 0 f :=
  ⟨B, 1, one_pos, fun t y ht0 ht1 hy => by simpa using h t y ht0 ht1 hy⟩

theorem OU38.of_pow (n : ℕ) : OU38 n (fun t _ => t ^ n) :=
  ⟨1, 1, one_pos, fun t y ht0 _ _ => by rw [abs_of_nonneg (by positivity)]; simp⟩

theorem OU38.const_mul {n : ℕ} {f : ℝ → ℝ → ℝ} (a : ℝ) (hf : OU38 n f) :
    OU38 n (fun t y => a * f t y) := by
  have := (OU38.of_bdd (f := fun _ _ => a) |a| (fun _ _ _ _ _ => le_refl _)).mul hf
  simpa using this


/-! ### The density factor -/

/-- common small-`t` window: `δ₀(h) = 1/(2h+2)` gives `h t ≤ 1/2`, `t ≤ 1/2`. -/
def dlt38 (h : ℝ) : ℝ := 1 / (2 * h + 2)

theorem dlt38_pos {h : ℝ} (hh : 0 < h) : 0 < dlt38 h := by unfold dlt38; positivity

theorem small_t38 {h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (ht : t ≤ dlt38 h) :
    h * t ≤ 1 / 2 ∧ t ≤ 1 / 2 := by
  unfold dlt38 at ht
  have h2 : 0 < 2 * h + 2 := by positivity
  rw [le_div_iff₀ h2] at ht
  constructor <;> nlinarith

/-- the density `g(t,y) = h⁻¹ arsinh(h t √(1-y²)/√(1-h²t²)) (1-h²t²y²)^{-1/2}`. -/
def alG38 (h t y : ℝ) : ℝ :=
  h⁻¹ * Real.arsinh (h * t * Real.sqrt (1 - y ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) *
    (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2))⁻¹

theorem ou_e38 (h : ℝ) : OU38 2 (fun t _ => h ^ 2 * t ^ 2) :=
  ⟨h ^ 2, 1, one_pos, fun t y ht0 _ _ => by
    rw [abs_of_nonneg (by positivity)]⟩

theorem ou_u38 (h : ℝ) : OU38 2 (fun t y => h ^ 2 * t ^ 2 * y ^ 2) :=
  ⟨h ^ 2, 1, one_pos, fun t y ht0 _ hy => by
    rw [abs_of_nonneg (by positivity)]
    have : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
    nlinarith [sq_nonneg h, sq_nonneg t, mul_nonneg (sq_nonneg h) (sq_nonneg t)]⟩

theorem ou_A1_38 {h : ℝ} (hh : 0 < h) :
    OU38 4 (fun t _ => (Real.sqrt (1 - h ^ 2 * t ^ 2))⁻¹ - (1 + h ^ 2 * t ^ 2 / 2)) := by
  refine ⟨2 * h ^ 4, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
  obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
  have hu0 : 0 ≤ h ^ 2 * t ^ 2 := by positivity
  have hu1 : h ^ 2 * t ^ 2 ≤ 1 / 2 := by nlinarith [mul_nonneg hh.le ht0]
  have := inv_sqrt_one_sub_bound38 hu0 hu1
  calc _ ≤ 2 * (h ^ 2 * t ^ 2) ^ 2 := this
    _ = _ := by ring

theorem ou_B_38 {h : ℝ} (hh : 0 < h) :
    OU38 4 (fun t y => (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2))⁻¹ - (1 + h ^ 2 * t ^ 2 * y ^ 2 / 2)) := by
  refine ⟨2 * h ^ 4, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
  obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
  have hu0 : 0 ≤ h ^ 2 * t ^ 2 * y ^ 2 := by positivity
  have hu1 : h ^ 2 * t ^ 2 * y ^ 2 ≤ 1 / 2 := by
    have : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr hy2)]
  have := inv_sqrt_one_sub_bound38 hu0 hu1
  have hu2 : (h ^ 2 * t ^ 2 * y ^ 2) ^ 2 ≤ (h ^ 2 * t ^ 2) ^ 2 := by
    apply pow_le_pow_left₀ hu0
    nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg t)]
  calc _ ≤ 2 * (h ^ 2 * t ^ 2 * y ^ 2) ^ 2 := this
    _ ≤ 2 * (h ^ 2 * t ^ 2) ^ 2 := by linarith
    _ = _ := by ring


theorem OU38.congr_dom {n : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ t y : ℝ, 0 ≤ t → |y| ≤ 1 → f t y = g t y) (hf : OU38 n f) : OU38 n g := by
  obtain ⟨C, δ, hδ, hb⟩ := hf
  exact ⟨C, δ, hδ, fun t y ht0 htδ hy => by rw [← h t y ht0 hy]; exact hb t y ht0 htδ hy⟩

theorem ou_A1_bdd38 {h : ℝ} (hh : 0 < h) :
    OU38 0 (fun t _ => (Real.sqrt (1 - h ^ 2 * t ^ 2))⁻¹) := by
  refine ⟨2, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
  obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
  have h14 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
  have : (1 : ℝ) / 2 ≤ Real.sqrt (1 - h ^ 2 * t ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  rw [abs_of_nonneg (by positivity)]
  simp only [pow_zero, mul_one]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

theorem ou_B_bdd38 {h : ℝ} (hh : 0 < h) :
    OU38 0 (fun t y => (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2))⁻¹) := by
  refine ⟨2, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
  obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
  have h14 : h ^ 2 * t ^ 2 * y ^ 2 ≤ 1 / 4 := by
    have : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr hy2)]
  have : (1 : ℝ) / 2 ≤ Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  rw [abs_of_nonneg (by positivity)]
  simp only [pow_zero, mul_one]
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

theorem ou_ts_38 : OU38 1 (fun t y => t * Real.sqrt (1 - y ^ 2)) := by
  refine ⟨1, 1, one_pos, fun t y ht0 _ hy => ?_⟩
  have : Real.sqrt (1 - y ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg y]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]

theorem ou_G_38 {h : ℝ} (hh : 0 < h) :
    OU38 5 (fun t y => alG38 h t y -
      t * Real.sqrt (1 - y ^ 2) * (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3))) := by
  set A1 : ℝ → ℝ → ℝ := fun t _ => (Real.sqrt (1 - h ^ 2 * t ^ 2))⁻¹ with hA1
  set B : ℝ → ℝ → ℝ := fun t y => (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2))⁻¹ with hB
  have hr1 : OU38 4 (fun t y => A1 t y - (1 + h ^ 2 * t ^ 2 / 2)) := ou_A1_38 hh
  have hr2 : OU38 4 (fun t y => B t y - (1 + h ^ 2 * t ^ 2 * y ^ 2 / 2)) := ou_B_38 hh
  have hA0 : OU38 0 A1 := ou_A1_bdd38 hh
  have hB0 : OU38 0 B := ou_B_bdd38 hh
  have he := ou_e38 h
  have hu := ou_u38 h
  have hAm : OU38 2 (fun t y => A1 t y - 1) := by
    have := (hr1.mono (n := 2) (k := 2)).add (he.const_mul (1 / 2))
    exact this.congr (fun t y => by ring)
  have hBm : OU38 2 (fun t y => B t y - 1) := by
    have := (hr2.mono (n := 2) (k := 2)).add (hu.const_mul (1 / 2))
    exact this.congr (fun t y => by ring)
  have hq : OU38 2 (fun t y => A1 t y ^ 3 * B t y - 1) := by
    have h1 := (hAm.mul ((hA0.mul hA0).add (hA0.add (OU38.of_bdd (f := fun _ _ => (1:ℝ)) 1
      (fun _ _ _ _ _ => by simp)))) ).mul hB0
    have := h1.add hBm
    exact (OU38.mono (n := 2) (k := 0) this).congr (fun t y => by ring)
  have hbr : OU38 4 (fun t y => A1 t y * B t y - 1 - h ^ 2 * t ^ 2 / 3 - 2 * (h ^ 2 * t ^ 2 * y ^ 2) / 3
      - (h ^ 2 * t ^ 2 - h ^ 2 * t ^ 2 * y ^ 2) / 6 * (A1 t y ^ 3 * B t y)) := by
    have p1 : OU38 4 (fun t y => (h ^ 2 * t ^ 2 * y ^ 2) * (h ^ 2 * t ^ 2)) := hu.mul he
    have p2 : OU38 4 (fun t y => (h ^ 2 * t ^ 2) * (B t y - (1 + h ^ 2 * t ^ 2 * y ^ 2 / 2))) :=
      OU38.mono (n := 4) (k := 2) (he.mul hr2)
    have p3 : OU38 4 (fun t y => (h ^ 2 * t ^ 2 * y ^ 2) * (A1 t y - (1 + h ^ 2 * t ^ 2 / 2))) :=
      OU38.mono (n := 4) (k := 2) (hu.mul hr1)
    have p4 : OU38 4 (fun t y => (A1 t y - (1 + h ^ 2 * t ^ 2 / 2)) *
        (B t y - (1 + h ^ 2 * t ^ 2 * y ^ 2 / 2))) := OU38.mono (n := 4) (k := 4) (hr1.mul hr2)
    have p5 : OU38 4 (fun t y => (h ^ 2 * t ^ 2 - h ^ 2 * t ^ 2 * y ^ 2) / 6 *
        (A1 t y ^ 3 * B t y - 1)) := by
      have := (he.sub hu).const_mul (1 / 6) |>.mul hq
      exact (OU38.mono (n := 4) (k := 0) this).congr (fun t y => by ring)
    have h1 := ((((hr2.add (p1.const_mul (1 / 4))).add (p2.const_mul (1 / 2))).add hr1).add
      (p3.const_mul (1 / 2))).add p4
    have h2 := h1.sub p5
    refine h2.congr (fun t y => ?_)
    ring
  have hprod : OU38 5 (fun t y => t * Real.sqrt (1 - y ^ 2) *
      (A1 t y * B t y - 1 - h ^ 2 * t ^ 2 / 3 - 2 * (h ^ 2 * t ^ 2 * y ^ 2) / 3
      - (h ^ 2 * t ^ 2 - h ^ 2 * t ^ 2 * y ^ 2) / 6 * (A1 t y ^ 3 * B t y))) := ou_ts_38.mul hbr
  have hε : OU38 5 (fun t y => h⁻¹ * (Real.arsinh (h * t * Real.sqrt (1 - y ^ 2) *
      A1 t y) - (h * t * Real.sqrt (1 - y ^ 2) * A1 t y -
      (h * t * Real.sqrt (1 - y ^ 2) * A1 t y) ^ 3 / 6)) * B t y) := by
    refine ⟨64 * h ^ 4, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
    obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
    have hs1 : Real.sqrt (1 - y ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith [sq_nonneg y]
    have hs0 := Real.sqrt_nonneg (1 - y ^ 2)
    have hA2 : A1 t y ≤ 2 := by
      have h14 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
      have : (1 : ℝ) / 2 ≤ Real.sqrt (1 - h ^ 2 * t ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith)
      show (Real.sqrt (1 - h ^ 2 * t ^ 2))⁻¹ ≤ 2
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hB2 : B t y ≤ 2 := by
      have h14 : h ^ 2 * t ^ 2 * y ^ 2 ≤ 1 / 4 := by
        have : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr hy2)]
      have : (1 : ℝ) / 2 ≤ Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith)
      show (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2))⁻¹ ≤ 2
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hA0 : 0 ≤ A1 t y := by show 0 ≤ (Real.sqrt _)⁻¹; positivity
    have hB0 : 0 ≤ B t y := by show 0 ≤ (Real.sqrt _)⁻¹; positivity
    set x := h * t * Real.sqrt (1 - y ^ 2) * A1 t y with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ 2 * (h * t) := by
      rw [hx]
      have : Real.sqrt (1 - y ^ 2) * A1 t y ≤ 1 * 2 :=
        mul_le_mul hs1 hA2 hA0 zero_le_one
      nlinarith [mul_nonneg hh.le ht0]
    have hxa : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; linarith
    have hε := arsinh_bound38 hxa
    have hx5 : |x| ^ 5 ≤ (2 * (h * t)) ^ 5 :=
      pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg hx0]; exact hx1) 5
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hh), abs_of_nonneg hB0]
    calc h⁻¹ * |Real.arsinh x - (x - x ^ 3 / 6)| * B t y
        ≤ h⁻¹ * (2 * (h * t)) ^ 5 * 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hε.trans hx5) (inv_nonneg.mpr hh.le))
            hB2 hB0 (by positivity)
      _ = 64 * h ^ 4 * t ^ 5 := by field_simp; ring
  have := hprod.add hε
  refine this.congr_dom (fun t y ht0 hy => ?_)
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
  have hs2 : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (by linarith)
  have hh0 : h ≠ 0 := hh.ne'
  unfold alG38
  have hx : h * t * Real.sqrt (1 - y ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2) =
      h * t * Real.sqrt (1 - y ^ 2) * A1 t y := by
    simp only [hA1, div_eq_mul_inv]
  rw [hx]
  have hx3 : (h * t * Real.sqrt (1 - y ^ 2) * A1 t y) ^ 3 =
      h ^ 3 * t ^ 3 * Real.sqrt (1 - y ^ 2) * (1 - y ^ 2) * A1 t y ^ 3 := by
    linear_combination (h ^ 3 * t ^ 3 * Real.sqrt (1 - y ^ 2) * A1 t y ^ 3) * hs2
  rw [hx3]
  simp only [hB]
  field_simp
  ring


/-! ### The Taylor polynomial of `W` along the plane wave -/

/-- `P_t(y) = W₀ + t a₁(y) + t² a₂(y) + t³ a₃(y)`, the cubic truncation of
`W(ω+σ)(1 + h²t²(1/3+2y²/3))` (`σ = 2cty - h²ωt²y²/2 + O(t⁴)`). -/
def alPoly38 (h ω c W0 W1 W2 W3 t y : ℝ) : ℝ :=
  W0 + t * (2 * W1 * c * y) +
    t ^ 2 * ((4 * W0 * h ^ 2 * y ^ 2 + 2 * W0 * h ^ 2 - 3 * W1 * h ^ 2 * ω * y ^ 2
      + 12 * W2 * c ^ 2 * y ^ 2) / 6) +
    t ^ 3 * (c * y * (4 * W1 * h ^ 2 * y ^ 2 + 2 * W1 * h ^ 2 - 3 * W2 * h ^ 2 * ω * y ^ 2
      + 4 * W3 * c ^ 2 * y ^ 2) / 3)

theorem ou_ty_38 : OU38 1 (fun t y => t * y) :=
  ⟨1, 1, one_pos, fun t y ht0 _ hy => by
    rw [abs_mul, abs_of_nonneg ht0]; simpa using mul_le_mul_of_nonneg_left hy ht0⟩

theorem ou_poly_bdd38 {Q : ℝ → ℝ → ℝ} (hQ : Continuous fun p : ℝ × ℝ => Q p.1 p.2) :
    OU38 0 Q := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (-1:ℝ)) (b := 1))).exists_bound_of_continuousOn hQ.continuousOn
  refine ⟨C, 1, one_pos, fun t y ht0 ht1 hy => ?_⟩
  have := hC (t, y) ⟨⟨ht0, ht1⟩, abs_le.mp hy⟩
  simpa using this

theorem ou_W_core38 (h ω c W0 W1 W2 W3 M : ℝ) (hh : 0 < h) (hM0 : 0 ≤ M) (W : ℝ → ℝ)
    (hT : ∀ s : ℝ, |s| ≤ 1 → |W (ω + s) - (W0 + W1 * s + W2 * s ^ 2 / 2 + W3 * s ^ 3 / 6)| ≤
      M * s ^ 4) :
    OU38 4 (fun t y => W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
      (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) - alPoly38 h ω c W0 W1 W2 W3 t y) := by
  set σ₁ : ℝ → ℝ → ℝ := fun t y => 2 * c * t * y - h ^ 2 * ω / 2 * t ^ 2 * y ^ 2 with hσ₁
  set σ : ℝ → ℝ → ℝ := fun t y =>
    ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y - ω with hσ
  have hty := ou_ty_38
  have hσ₁1 : OU38 1 σ₁ := by
    have a := hty.const_mul (2 * c)
    have b := ((hty.mul hty).const_mul (-(h ^ 2 * ω / 2)))
    have b' : OU38 1 (fun t y => -(h ^ 2 * ω / 2) * (t * y * (t * y))) :=
      OU38.mono (n := 1) (k := 1) b
    exact (a.add b').congr (fun t y => by simp only [hσ₁]; ring)
  have hρ : OU38 4 (fun t y => σ t y - σ₁ t y) := by
    refine ⟨|ω| * h ^ 4 / 2, dlt38 h, dlt38_pos hh, fun t y ht0 htδ hy => ?_⟩
    obtain ⟨h1, _⟩ := small_t38 hh ht0 htδ
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
    have hu0 : 0 ≤ h ^ 2 * t ^ 2 * y ^ 2 := by positivity
    have hu1 : h ^ 2 * t ^ 2 * y ^ 2 ≤ 1 := by
      have : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr hy2)]
    have := sqrt_one_sub_bound38 hu0 hu1
    have hu2 : (h ^ 2 * t ^ 2 * y ^ 2) ^ 2 ≤ (h ^ 2 * t ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ hu0
      nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg t)]
    have e : σ t y - σ₁ t y = ω * (Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) -
        (1 - h ^ 2 * t ^ 2 * y ^ 2 / 2)) := by simp only [hσ, hσ₁]; ring
    beta_reduce
    rw [e, abs_mul]
    calc |ω| * |Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) - (1 - h ^ 2 * t ^ 2 * y ^ 2 / 2)|
        ≤ |ω| * ((h ^ 2 * t ^ 2 * y ^ 2) ^ 2 / 2) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ |ω| * ((h ^ 2 * t ^ 2) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = _ := by ring
  have hσ1 : OU38 1 σ := by
    have := hσ₁1.add (OU38.mono (n := 1) (k := 3) hρ)
    exact this.congr (fun t y => by ring)
  obtain ⟨Cσ, δσ, hδσ, hCσ⟩ := hσ1
  set δ' := min (min δσ (dlt38 h)) (1 / (|Cσ| + 1)) with hδ'
  have hδ'0 : 0 < δ' := lt_min (lt_min hδσ (dlt38_pos hh)) (by positivity)
  have hσb : ∀ t y : ℝ, 0 ≤ t → t ≤ δ' → |y| ≤ 1 → |σ t y| ≤ |Cσ| * t ∧ |σ t y| ≤ 1 := by
    intro t y ht0 htδ hy
    have h1 := hCσ t y ht0 (htδ.trans ((min_le_left _ _).trans (min_le_left _ _))) hy
    have h2 : |σ t y| ≤ |Cσ| * t := by
      calc |σ t y| ≤ Cσ * t ^ 1 := h1
        _ ≤ |Cσ| * t ^ 1 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = _ := by ring
    refine ⟨h2, ?_⟩
    have h3 : t ≤ 1 / (|Cσ| + 1) := htδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h3
    nlinarith [abs_nonneg Cσ]
  have hρW : OU38 4 (fun t y => W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) -
      (W0 + W1 * σ t y + W2 * σ t y ^ 2 / 2 + W3 * σ t y ^ 3 / 6)) := by
    refine ⟨M * |Cσ| ^ 4, δ', hδ'0, fun t y ht0 htδ hy => ?_⟩
    obtain ⟨hb1, hb2⟩ := hσb t y ht0 htδ hy
    have := hT (σ t y) hb2
    have e : ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y = ω + σ t y := by
      simp only [hσ]; ring
    beta_reduce
    rw [e]
    refine this.trans ?_
    have : (σ t y) ^ 4 = |σ t y| ^ 4 := by
      rw [pow_abs, abs_of_nonneg (by positivity)]
    rw [this]
    calc M * |σ t y| ^ 4 ≤ M * (|Cσ| * t) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb1 4) hM0
      _ = _ := by ring
  -- Lipschitz term
  have hσ0 : OU38 0 σ := OU38.mono (n := 0) (k := 1) ⟨Cσ, δσ, hδσ, hCσ⟩
  have hσ₁0 : OU38 0 σ₁ := OU38.mono (n := 0) (k := 1) hσ₁1
  have hone : OU38 0 (fun _ _ => (1 : ℝ)) := OU38.of_bdd 1 (fun _ _ _ _ _ => by simp)
  have hbr : OU38 0 (fun t y => W1 + W2 * (σ t y + σ₁ t y) / 2 +
      W3 * (σ t y ^ 2 + σ t y * σ₁ t y + σ₁ t y ^ 2) / 6) := by
    have a := (hσ0.add hσ₁0).const_mul (W2 / 2)
    have b := ((hσ0.mul hσ0).add (hσ0.mul hσ₁0)).add (hσ₁0.mul hσ₁0)
    have b' := b.const_mul (W3 / 6)
    have c1 := (hone.const_mul W1).add (a.add b')
    refine c1.congr (fun t y => by ring)
  have hLip : OU38 4 (fun t y => (W0 + W1 * σ t y + W2 * σ t y ^ 2 / 2 + W3 * σ t y ^ 3 / 6) -
      (W0 + W1 * σ₁ t y + W2 * σ₁ t y ^ 2 / 2 + W3 * σ₁ t y ^ 3 / 6)) := by
    have := hρ.mul hbr
    exact (OU38.mono (n := 4) (k := 0) this).congr (fun t y => by ring)
  -- the weight factor
  have hK : OU38 0 (fun t y => 1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) := by
    refine OU38.of_bdd (1 + h ^ 2 * 1) (fun t y ht0 ht1 hy => ?_)
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [abs_nonneg y, sq_abs y]
    have : 0 ≤ h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3) := by positivity
    rw [abs_of_nonneg (by linarith)]
    have h3 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg h, mul_nonneg (sq_nonneg h) (sq_nonneg t),
      mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr hy2),
      mul_nonneg (sq_nonneg h) (sub_nonneg.mpr h3)]
  -- polynomial remainder
  have hQ : OU38 0 (fun t y => (-W1 * h ^ 4 * ω * y ^ 4 / 3 - W1 * h ^ 4 * ω * y ^ 2 / 6 + 4 * W2 * c ^ 2 * h ^ 2 * y ^ 4 / 3 + 2 * W2 * c ^ 2 * h ^ 2 * y ^ 2 / 3 - 2 * W2 * c * h ^ 4 * ω * t * y ^ 5 / 3 - W2 * c * h ^ 4 * ω * t * y ^ 3 / 3 + W2 * h ^ 6 * ω ^ 2 * t ^ 2 * y ^ 6 / 12 + W2 * h ^ 6 * ω ^ 2 * t ^ 2 * y ^ 4 / 24 + W2 * h ^ 4 * ω ^ 2 * y ^ 4 / 8 + 8 * W3 * c ^ 3 * h ^ 2 * t * y ^ 5 / 9 + 4 * W3 * c ^ 3 * h ^ 2 * t * y ^ 3 / 9 - 2 * W3 * c ^ 2 * h ^ 4 * ω * t ^ 2 * y ^ 6 / 3 - W3 * c ^ 2 * h ^ 4 * ω * t ^ 2 * y ^ 4 / 3 - W3 * c ^ 2 * h ^ 2 * ω * y ^ 4 + W3 * c * h ^ 6 * ω ^ 2 * t ^ 3 * y ^ 7 / 6 + W3 * c * h ^ 6 * ω ^ 2 * t ^ 3 * y ^ 5 / 12 + W3 * c * h ^ 4 * ω ^ 2 * t * y ^ 5 / 4 - W3 * h ^ 8 * ω ^ 3 * t ^ 4 * y ^ 8 / 72 - W3 * h ^ 8 * ω ^ 3 * t ^ 4 * y ^ 6 / 144 - W3 * h ^ 6 * ω ^ 3 * t ^ 2 * y ^ 6 / 48)) :=
    ou_poly_bdd38 (by fun_prop)
  have hQt : OU38 4 (fun t y => t ^ 4 * (-W1 * h ^ 4 * ω * y ^ 4 / 3 - W1 * h ^ 4 * ω * y ^ 2 / 6 + 4 * W2 * c ^ 2 * h ^ 2 * y ^ 4 / 3 + 2 * W2 * c ^ 2 * h ^ 2 * y ^ 2 / 3 - 2 * W2 * c * h ^ 4 * ω * t * y ^ 5 / 3 - W2 * c * h ^ 4 * ω * t * y ^ 3 / 3 + W2 * h ^ 6 * ω ^ 2 * t ^ 2 * y ^ 6 / 12 + W2 * h ^ 6 * ω ^ 2 * t ^ 2 * y ^ 4 / 24 + W2 * h ^ 4 * ω ^ 2 * y ^ 4 / 8 + 8 * W3 * c ^ 3 * h ^ 2 * t * y ^ 5 / 9 + 4 * W3 * c ^ 3 * h ^ 2 * t * y ^ 3 / 9 - 2 * W3 * c ^ 2 * h ^ 4 * ω * t ^ 2 * y ^ 6 / 3 - W3 * c ^ 2 * h ^ 4 * ω * t ^ 2 * y ^ 4 / 3 - W3 * c ^ 2 * h ^ 2 * ω * y ^ 4 + W3 * c * h ^ 6 * ω ^ 2 * t ^ 3 * y ^ 7 / 6 + W3 * c * h ^ 6 * ω ^ 2 * t ^ 3 * y ^ 5 / 12 + W3 * c * h ^ 4 * ω ^ 2 * t * y ^ 5 / 4 - W3 * h ^ 8 * ω ^ 3 * t ^ 4 * y ^ 8 / 72 - W3 * h ^ 8 * ω ^ 3 * t ^ 4 * y ^ 6 / 144 - W3 * h ^ 6 * ω ^ 3 * t ^ 2 * y ^ 6 / 48)) := by
    have := (OU38.of_pow 4).mul hQ
    simpa using this
  have h1 := (hρW.mul hK).add (hLip.mul hK)
  have h2 := h1.add hQt
  refine (OU38.mono (n := 4) (k := 0) h2).congr (fun t y => ?_)
  simp only [hσ, hσ₁, alPoly38]
  ring


/-! ### Change of variables `q = sin(hλ-θ)/h` -/

theorem arcosh_eq_arsinh38 {R : ℝ} (hR : 1 ≤ R) :
    Real.arcosh R = Real.arsinh (Real.sqrt (R ^ 2 - 1)) := by
  have h0 : 0 ≤ R ^ 2 - 1 := by nlinarith
  have e : Real.sqrt (1 + Real.sqrt (R ^ 2 - 1) ^ 2) = R := by
    rw [Real.sq_sqrt h0, show 1 + (R ^ 2 - 1) = R ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  unfold Real.arcosh Real.arsinh
  rw [e, add_comm]

/-- `sin φ ≥ sin ε` on `[ε, π - ε]`. -/
theorem sin_ge_of_mem38 {ε φ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ Real.pi / 2) (h1 : ε ≤ φ)
    (h2 : φ ≤ Real.pi - ε) : Real.sin ε ≤ Real.sin φ := by
  rcases le_total φ (Real.pi / 2) with h | h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
  · rw [← Real.sin_pi_sub φ]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

theorem abs_sin_ge38 {ε φ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ Real.pi / 2) (h1 : ε ≤ |φ|)
    (h2 : |φ| ≤ Real.pi - ε) : Real.sin ε ≤ |Real.sin φ| := by
  rcases le_total 0 φ with h | h
  · rw [abs_of_nonneg h] at h1 h2
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
    exact sin_ge_of_mem38 hε0 hε h1 h2
  · rw [abs_of_nonpos h] at h1 h2
    rw [← abs_neg, ← Real.sin_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith))]
    exact sin_ge_of_mem38 hε0 hε h1 h2

theorem abs_cos_le_of_sin_ge38 {u φ : ℝ} (hu : 0 ≤ u) (h : u ≤ |Real.sin φ|) :
    |Real.cos φ| ≤ Real.sqrt (1 - u ^ 2) := by
  apply Real.abs_le_sqrt
  have h1 : u ^ 2 ≤ Real.sin φ ^ 2 := by
    rw [← sq_abs (Real.sin φ)]; exact pow_le_pow_left₀ hu h 2
  nlinarith [Real.sin_sq_add_cos_sq φ]


/-- the integrand in the variable `q`. -/
def alGq38 (W : ℝ → ℝ) (h t θ q : ℝ) : ℝ :=
  W (2 * Real.cos θ * q + (2 * Real.sin θ / h) * Real.sqrt (1 - h ^ 2 * q ^ 2)) *
    (h⁻¹ * Real.arsinh (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) *
      (Real.sqrt (1 - h ^ 2 * q ^ 2))⁻¹)

theorem mid_identity38 (W : ℝ → ℝ) {h t θ φ : ℝ} (hh : 0 < h) (ht0 : 0 < t) (hht : h * t ≤ 1 / 2)
    (hcos : 0 ≤ Real.cos φ) (hs : |Real.sin φ| ≤ h * t) :
    W (2 * Real.sin (φ + θ) / h) *
        (h⁻¹ * Real.arcosh (max 1 (|Real.cos φ| / Real.sqrt (1 - h ^ 2 * t ^ 2)))) =
      alGq38 W h t θ (Real.sin φ / h) * Real.cos φ := by
  set q := Real.sin φ / h with hq
  have hsq : Real.sin φ = h * q := by rw [hq]; field_simp
  have hq2 : q ^ 2 ≤ t ^ 2 := by
    have : (h * q) ^ 2 ≤ (h * t) ^ 2 := by
      rw [← hsq]; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
    have h2 : h ^ 2 * q ^ 2 ≤ h ^ 2 * t ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hcs : Real.cos φ ^ 2 = 1 - h ^ 2 * q ^ 2 := by
    have := Real.sin_sq_add_cos_sq φ
    rw [hsq] at this; nlinarith
  have hC : Real.cos φ = Real.sqrt (1 - h ^ 2 * q ^ 2) := by
    rw [← hcs]; exact (Real.sqrt_sq hcos).symm
  have ht2 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht0.le]
  have hs0 : 0 < Real.sqrt (1 - h ^ 2 * t ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hs0sq : Real.sqrt (1 - h ^ 2 * t ^ 2) ^ 2 = 1 - h ^ 2 * t ^ 2 := Real.sq_sqrt (by linarith)
  have hC0 : 0 < Real.cos φ := by
    rw [hC]; apply Real.sqrt_pos.mpr
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hq2)]
  have hR : 1 ≤ Real.cos φ / Real.sqrt (1 - h ^ 2 * t ^ 2) := by
    rw [le_div_iff₀ hs0, one_mul]
    apply le_of_sq_le_sq _ hC0.le
    rw [hcs, hs0sq]; nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hq2)]
  rw [abs_of_nonneg hcos, max_eq_right hR, arcosh_eq_arsinh38 hR]
  have e1 : Real.sqrt ((Real.cos φ / Real.sqrt (1 - h ^ 2 * t ^ 2)) ^ 2 - 1) =
      h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2) := by
    have hnn : 0 ≤ h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2) := by positivity
    rw [← Real.sqrt_sq hnn]
    congr 1
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hq2), hcs, hs0sq]
    have hne : 1 - h ^ 2 * t ^ 2 ≠ 0 := by linarith
    field_simp
    ring
  rw [e1]
  have e2 : 2 * Real.sin (φ + θ) / h = 2 * Real.cos θ * q +
      (2 * Real.sin θ / h) * Real.sqrt (1 - h ^ 2 * q ^ 2) := by
    rw [Real.sin_add, ← hC, hsq]; field_simp
  rw [e2]
  unfold alGq38
  rw [← hC]
  field_simp


theorem continuousOn_Gq38 {W : ℝ → ℝ} (hW : Continuous W) {h t θ : ℝ} (hh : 0 < h)
    (ht0 : 0 < t) (hht : h * t ≤ 1 / 2) :
    ContinuousOn (alGq38 W h t θ) (Set.Icc (-t) t) := by
  unfold alGq38
  have hne : ∀ q ∈ Set.Icc (-t) t, Real.sqrt (1 - h ^ 2 * q ^ 2) ≠ 0 := by
    intro q hq
    apply (Real.sqrt_pos.mpr _).ne'
    have : q ^ 2 ≤ t ^ 2 := by nlinarith [hq.1, hq.2]
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr this), mul_nonneg hh.le ht0.le]
  have hne2 : Real.sqrt (1 - h ^ 2 * t ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    nlinarith [mul_nonneg hh.le ht0.le]
  refine (hW.comp_continuousOn (by fun_prop)).mul ?_
  refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) hne)
  refine ContinuousOn.mul continuousOn_const ?_
  exact Real.continuous_arsinh.comp_continuousOn (by fun_prop (disch := exact hne2))


theorem alPlane_lam_integral38 {W : ℝ → ℝ} (hW : Continuous W) {h t θ : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) (ht0 : 0 < t) (ht : t ≤ 1 / 2) (hθ : |θ| ≤ Real.pi / 2 - Real.pi * h / 2) :
    ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
        W (2 * Real.sin (h * lam) / h) *
          (h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * lam - θ)| / Real.sqrt (1 - h ^ 2 * t ^ 2)))) =
      t * ∫ y in (-1 : ℝ)..1, alGq38 W h t θ (t * y) := by
  have hpi := Real.pi_pos
  have hht : h * t ≤ 1 / 2 := by nlinarith
  have hht0 : 0 ≤ h * t := by positivity
  set ε := Real.arcsin (h * t) with hε
  have hε0 : 0 ≤ ε := Real.arcsin_nonneg.mpr hht0
  have hsinε : Real.sin ε = h * t := Real.sin_arcsin (by linarith) (by linarith)
  have hεle : ε ≤ Real.pi * h / 2 := by
    rw [hε, Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
      ⟨by nlinarith, by nlinarith⟩]
    have := Real.mul_le_sin (x := Real.pi * h / 2) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * h / 2) = h := by field_simp
    nlinarith
  have hεpi : ε ≤ Real.pi / 2 := by nlinarith
  have hθ1 := (abs_le.mp hθ).1
  have hθ2 := (abs_le.mp hθ).2
  set a := (θ - ε) / h with ha
  set b := (θ + ε) / h with hb
  obtain ⟨hi, hhi⟩ : ∃ hi : ℝ, hi = Real.pi / (2 * h) := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo : ℝ, lo = -hi := ⟨_, rfl⟩
  rw [← hhi, ← hlo]
  have hhhi : h * hi = Real.pi / 2 := by rw [hhi]; field_simp
  have hhlo : h * lo = -(Real.pi / 2) := by rw [hlo, mul_neg, hhhi]
  have hlo' : lo = (-(Real.pi / 2)) / h := by rw [eq_div_iff hh.ne']; linarith
  have hhi' : hi = (Real.pi / 2) / h := by rw [eq_div_iff hh.ne']; linarith
  have hloa : lo ≤ a := by
    rw [hlo', ha]; exact div_le_div_of_nonneg_right (by linarith) hh.le
  have hab : a ≤ b := by
    rw [ha, hb]; exact div_le_div_of_nonneg_right (by linarith) hh.le
  have hbhi : b ≤ hi := by
    rw [hhi', hb]; exact div_le_div_of_nonneg_right (by linarith) hh.le
  have hha : h * a = θ - ε := by rw [ha]; field_simp
  have hhb : h * b = θ + ε := by rw [hb]; field_simp
  set F : ℝ → ℝ := fun lam => W (2 * Real.sin (h * lam) / h) *
    (h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * lam - θ)| / Real.sqrt (1 - h ^ 2 * t ^ 2)))) with hF
  have hs0 : 0 < Real.sqrt (1 - h ^ 2 * t ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hFc : Continuous F := by
    have h1 : Continuous fun lam : ℝ => max 1 (|Real.cos (h * lam - θ)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2)) := by fun_prop
    have h2 : Continuous fun lam : ℝ => Real.arcosh (max 1 (|Real.cos (h * lam - θ)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2))) :=
      Real.continuousOn_arcosh.comp_continuous h1 (fun x => Set.mem_Ici.mpr (le_max_left _ _))
    have h3 : Continuous fun lam : ℝ => W (2 * Real.sin (h * lam) / h) := hW.comp (by fun_prop)
    exact h3.mul (continuous_const.mul h2)
  -- zero regions
  have hzero : ∀ lam : ℝ, ε ≤ |h * lam - θ| → |h * lam - θ| ≤ Real.pi - ε → F lam = 0 := by
    intro lam h1 h2
    have := abs_sin_ge38 hε0 hεpi h1 h2
    rw [hsinε] at this
    have h3 := abs_cos_le_of_sin_ge38 hht0 this
    have h4 : |Real.cos (h * lam - θ)| / Real.sqrt (1 - h ^ 2 * t ^ 2) ≤ 1 := by
      rw [div_le_one hs0, ← mul_pow]; exact h3
    simp only [hF]
    rw [max_eq_left h4, Real.arcosh_zero]; simp
  have z1 : ∫ lam in lo..a, F lam = 0 := by
    have : Set.EqOn F (fun _ => (0 : ℝ)) (Set.uIcc lo a) := by
      intro lam hl
      rw [Set.uIcc_of_le hloa] at hl
      have e1 : h * lam ≤ θ - ε := by rw [← hha]; exact mul_le_mul_of_nonneg_left hl.2 hh.le
      have e2 : -(Real.pi / 2) ≤ h * lam := by
        rw [← hhlo]; exact mul_le_mul_of_nonneg_left hl.1 hh.le
      apply hzero
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    rw [intervalIntegral.integral_congr this]; simp
  have z2 : ∫ lam in b..hi, F lam = 0 := by
    have : Set.EqOn F (fun _ => (0 : ℝ)) (Set.uIcc b hi) := by
      intro lam hl
      rw [Set.uIcc_of_le hbhi] at hl
      have e1 : θ + ε ≤ h * lam := by rw [← hhb]; exact mul_le_mul_of_nonneg_left hl.1 hh.le
      have e2 : h * lam ≤ Real.pi / 2 := by
        rw [← hhhi]; exact mul_le_mul_of_nonneg_left hl.2 hh.le
      apply hzero
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [intervalIntegral.integral_congr this]; simp
  -- middle region
  have hmid : ∫ lam in a..b, F lam =
      ∫ lam in a..b, (alGq38 W h t θ ∘ fun lam => Real.sin (h * lam - θ) / h) lam *
        Real.cos (h * lam - θ) := by
    apply intervalIntegral.integral_congr
    intro lam hl
    rw [Set.uIcc_of_le hab] at hl
    have e1 : h * lam ≤ θ + ε := by rw [← hhb]; exact mul_le_mul_of_nonneg_left hl.2 hh.le
    have e2 : θ - ε ≤ h * lam := by rw [← hha]; exact mul_le_mul_of_nonneg_left hl.1 hh.le
    have hcos : 0 ≤ Real.cos (h * lam - θ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hs1 : Real.sin (h * lam - θ) ≤ h * t := by
      rw [← hsinε]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hεpi (by linarith)
    have hs2 : -(h * t) ≤ Real.sin (h * lam - θ) := by
      rw [← hsinε, ← Real.sin_neg]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have := mid_identity38 W (θ := θ) (φ := h * lam - θ) hh ht0 hht hcos (abs_le.mpr ⟨hs2, hs1⟩)
    rw [sub_add_cancel] at this
    exact this
  have hsub : ∫ lam in a..b, (alGq38 W h t θ ∘ fun lam => Real.sin (h * lam - θ) / h) lam *
        Real.cos (h * lam - θ) = ∫ q in (Real.sin (h * a - θ) / h)..(Real.sin (h * b - θ) / h),
        alGq38 W h t θ q := by
    apply intervalIntegral.integral_comp_mul_deriv' (f := fun lam => Real.sin (h * lam - θ) / h)
      (f' := fun lam => Real.cos (h * lam - θ))
    · intro lam _
      have := (((hasDerivAt_id lam).const_mul h).sub_const θ).sin.div_const h
      exact this.congr_deriv (by field_simp; simp)
    · exact (by fun_prop : Continuous fun lam : ℝ => Real.cos (h * lam - θ)).continuousOn
    · refine (continuousOn_Gq38 hW hh ht0 hht).mono ?_
      rintro _ ⟨lam, hl, rfl⟩
      rw [Set.uIcc_of_le hab] at hl
      have e1 : h * lam ≤ θ + ε := by rw [← hhb]; exact mul_le_mul_of_nonneg_left hl.2 hh.le
      have e2 : θ - ε ≤ h * lam := by rw [← hha]; exact mul_le_mul_of_nonneg_left hl.1 hh.le
      have hs1 : Real.sin (h * lam - θ) ≤ h * t := by
        rw [← hsinε]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hεpi (by linarith)
      have hs2 : -(h * t) ≤ Real.sin (h * lam - θ) := by
        rw [← hsinε, ← Real.sin_neg]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
      constructor
      · rw [le_div_iff₀ hh]; nlinarith
      · rw [div_le_iff₀ hh]; nlinarith
  have hqa : Real.sin (h * a - θ) / h = -t := by
    rw [hha, show θ - ε - θ = -ε by ring, Real.sin_neg, hsinε]; field_simp
  have hqb : Real.sin (h * b - θ) / h = t := by
    rw [hhb, show θ + ε - θ = ε by ring, hsinε]; field_simp
  have hscale : ∫ y in (-1 : ℝ)..1, alGq38 W h t θ (t * y) =
      t⁻¹ * ∫ q in (-t)..t, alGq38 W h t θ q := by
    rw [intervalIntegral.integral_comp_mul_left (fun q => alGq38 W h t θ q) ht0.ne']
    simp
  rw [hscale, ← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable lo a)
    (hFc.intervalIntegrable a hi), ← intervalIntegral.integral_add_adjacent_intervals
    (hFc.intervalIntegrable a b) (hFc.intervalIntegrable b hi), z1, z2, hmid, hsub, hqa, hqb]
  field_simp
  ring


/-! ### Moments against the semicircle -/

theorem integral_y2_sqrt38 : ∫ y in (-1 : ℝ)..1, y ^ 2 * Real.sqrt (1 - y ^ 2) = Real.pi / 8 := by
  set F : ℝ → ℝ := fun y => Real.arcsin y / 8 -
    y * Real.sqrt (1 - y ^ 2) * (1 - 2 * y ^ 2) / 8 with hF
  have hcont : ContinuousOn F (Icc (-1) 1) := by
    apply Continuous.continuousOn
    simp only [hF]; fun_prop
  have hder : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (x ^ 2 * Real.sqrt (1 - x ^ 2)) x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hpos : 0 < 1 - x ^ 2 := by nlinarith
    have hr : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hpos
    have hr2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hpos.le
    have d1 := (Real.hasDerivAt_arcsin hx1.ne' hx2.ne).div_const 8
    have d2 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := by
      have := ((hasDerivAt_pow 2 x).const_sub 1).sqrt hpos.ne'
      simpa using this
    have d3 := (((hasDerivAt_id x).mul d2).mul
      (((hasDerivAt_pow 2 x).const_mul 2).const_sub 1)).div_const 8
    have := d1.sub d3
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, id, Nat.cast_ofNat]
    field_simp
    rw [hr2]
    norm_num
    ring
  have hint : IntervalIntegrable (fun y : ℝ => y ^ 2 * Real.sqrt (1 - y ^ 2)) MeasureTheory.volume
      (-1) 1 := (by fun_prop : Continuous fun y : ℝ => y ^ 2 * Real.sqrt (1 - y ^ 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hder hint]
  simp only [hF]
  norm_num
  ring


theorem odd_integral38 (f : ℝ → ℝ) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x in (-1 : ℝ)..1, f x = 0 := by
  have := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) f
  simp only [hodd, intervalIntegral.integral_neg, neg_neg] at this
  linarith

theorem poly_moment38 (p0 p1 p2 p3 : ℝ) :
    ∫ y in (-1 : ℝ)..1, Real.sqrt (1 - y ^ 2) * (p0 + p1 * y + p2 * y ^ 2 + p3 * y ^ 3) =
      p0 * (Real.pi / 2) + p2 * (Real.pi / 8) := by
  have hc : ∀ k : ℕ, Continuous fun y : ℝ => y ^ k * Real.sqrt (1 - y ^ 2) := fun k => by fun_prop
  have i0 : ∫ y in (-1 : ℝ)..1, Real.sqrt (1 - y ^ 2) = Real.pi / 2 := integral_sqrt_one_sub_sq
  have i1 : ∫ y in (-1 : ℝ)..1, y * Real.sqrt (1 - y ^ 2) = 0 :=
    odd_integral38 _ (fun x => by simp)
  have i3 : ∫ y in (-1 : ℝ)..1, y ^ 3 * Real.sqrt (1 - y ^ 2) = 0 :=
    odd_integral38 _ (fun x => by simp; ring)
  have e : ∀ y : ℝ, Real.sqrt (1 - y ^ 2) * (p0 + p1 * y + p2 * y ^ 2 + p3 * y ^ 3) =
      p0 * Real.sqrt (1 - y ^ 2) + p1 * (y * Real.sqrt (1 - y ^ 2)) +
      p2 * (y ^ 2 * Real.sqrt (1 - y ^ 2)) + p3 * (y ^ 3 * Real.sqrt (1 - y ^ 2)) := fun y => by ring
  simp_rw [e]
  have hI : ∀ k : ℕ, IntervalIntegrable (fun y : ℝ => y ^ k * Real.sqrt (1 - y ^ 2))
      MeasureTheory.volume (-1) 1 := fun k => (hc k).intervalIntegrable _ _
  have h0 := hI 0
  have h1 := hI 1
  have h2 := hI 2
  have h3 := hI 3
  simp only [pow_zero, one_mul, pow_one] at h0 h1
  rw [intervalIntegral.integral_add ((h0.const_mul p0).add (h1.const_mul p1) |>.add (h2.const_mul p2))
      (h3.const_mul p3),
    intervalIntegral.integral_add ((h0.const_mul p0).add (h1.const_mul p1)) (h2.const_mul p2),
    intervalIntegral.integral_add (h0.const_mul p0) (h1.const_mul p1)]
  simp only [intervalIntegral.integral_const_mul, i0, i1, integral_y2_sqrt38, i3]
  ring


/-! ### The `y`-integral expansion -/

theorem ou_WA_bdd38 (h ω c W0 W1 W2 W3 M : ℝ) (hh : 0 < h) (hM0 : 0 ≤ M) (W : ℝ → ℝ)
    (hT : ∀ s : ℝ, |s| ≤ 1 → |W (ω + s) - (W0 + W1 * s + W2 * s ^ 2 / 2 + W3 * s ^ 3 / 6)| ≤
      M * s ^ 4) :
    OU38 0 (fun t y => W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y)) := by
  have core := OU38.mono (n := 0) (k := 4) (ou_W_core38 h ω c W0 W1 W2 W3 M hh hM0 W hT)
  have hP : OU38 0 (alPoly38 h ω c W0 W1 W2 W3) :=
    ou_poly_bdd38 (by unfold alPoly38; fun_prop)
  obtain ⟨C, δ, hδ, hb⟩ := core.add hP
  refine ⟨|C|, δ, hδ, fun t y ht0 htδ hy => ?_⟩
  have h1 := hb t y ht0 htδ hy
  simp only [pow_zero, mul_one] at h1 ⊢
  have hK : 1 ≤ 1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3) := by
    have : 0 ≤ h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3) := by positivity
    linarith
  have e : W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
      (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) - alPoly38 h ω c W0 W1 W2 W3 t y +
      alPoly38 h ω c W0 W1 W2 W3 t y =
      W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
      (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) := by ring
  rw [e] at h1
  rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3))]
    at h1
  calc _ ≤ |W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y)| *
        (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) :=
        le_mul_of_one_le_right (abs_nonneg _) hK
    _ ≤ C := h1
    _ ≤ |C| := le_abs_self C

theorem continuousOn_alG38 {h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t ≤ 1 / 2) :
    ContinuousOn (alG38 h t) (Set.Icc (-1) 1) := by
  unfold alG38
  have hne : ∀ y ∈ Set.Icc (-1 : ℝ) 1, Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) ≠ 0 := by
    intro y hy
    apply (Real.sqrt_pos.mpr _).ne'
    have : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (sq_nonneg t)) (sub_nonneg.mpr this),
      mul_nonneg hh.le ht0]
  have hne2 : Real.sqrt (1 - h ^ 2 * t ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    nlinarith [mul_nonneg hh.le ht0]
  refine ContinuousOn.mul ?_ (ContinuousOn.inv₀ (by fun_prop) hne)
  refine ContinuousOn.mul continuousOn_const ?_
  exact Real.continuous_arsinh.comp_continuousOn (by fun_prop (disch := exact hne2))

/-- the explicit `t⁴` coefficient (before the factor `2/π`). -/
def alB38 (h ω c W0 W1 W2 : ℝ) : ℝ :=
  Real.pi / 2 * (W0 * h ^ 2 / 3) +
    Real.pi / 8 * ((4 * W0 * h ^ 2 - 3 * W1 * h ^ 2 * ω + 12 * W2 * c ^ 2) / 6)

theorem alPlane_y_expansion38 {W W1 W2 W3 W4 : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt W (W1 x) x) (h2 : ∀ x, HasDerivAt W1 (W2 x) x)
    (h3 : ∀ x, HasDerivAt W2 (W3 x) x) (h4 : ∀ x, HasDerivAt W3 (W4 x) x)
    (hc4 : Continuous W4) {h : ℝ} (hh : 0 < h) (ω c : ℝ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |(∫ y in (-1 : ℝ)..1, W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
          alG38 h t y) -
        t * (Real.pi / 2 * W ω + t ^ 2 * alB38 h ω c (W ω) (W1 ω) (W2 ω))| ≤ C * t ^ 5 := by
  obtain ⟨M, hM0, hT⟩ := taylor4_38 h1 h2 h3 h4 hc4 ω
  have core := ou_W_core38 h ω c (W ω) (W1 ω) (W2 ω) (W3 ω) M hh hM0 W hT
  have hWA := ou_WA_bdd38 h ω c (W ω) (W1 ω) (W2 ω) (W3 ω) M hh hM0 W hT
  have hG := ou_G_38 hh
  have hcomb := (hWA.mul hG).add (ou_ts_38.mul core)
  obtain ⟨C, δ₁, hδ₁, hb⟩ := hcomb
  refine ⟨2 * |C|, min δ₁ (dlt38 h), lt_min hδ₁ (dlt38_pos hh), fun t ht0 htδ => ?_⟩
  obtain ⟨hht, _⟩ := small_t38 hh ht0.le (htδ.trans (min_le_right _ _))
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun x => (h1 x).continuousAt
  set f : ℝ → ℝ := fun y => W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
    alG38 h t y with hf
  set g : ℝ → ℝ := fun y => t * Real.sqrt (1 - y ^ 2) *
    alPoly38 h ω c (W ω) (W1 ω) (W2 ω) (W3 ω) t y with hg
  have hfc : ContinuousOn f (Set.uIcc (-1) 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact ((hWc.comp (by fun_prop)).continuousOn).mul (continuousOn_alG38 hh ht0.le hht)
  have hgc : Continuous g := by simp only [hg, alPoly38]; fun_prop
  have hfi : IntervalIntegrable f MeasureTheory.volume (-1) 1 := hfc.intervalIntegrable
  have hgi : IntervalIntegrable g MeasureTheory.volume (-1) 1 := hgc.intervalIntegrable _ _
  have hdiff : ‖∫ y in (-1 : ℝ)..1, (f y - g y)‖ ≤ |C| * t ^ 5 * |(1 : ℝ) - (-1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [Set.uIoc_of_le (by norm_num)] at hy
    have := hb t y ht0.le (htδ.trans (min_le_left _ _)) (abs_le.mpr ⟨hy.1.le, hy.2⟩)
    simp only at this
    have e : f y - g y = W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
        (alG38 h t y - t * Real.sqrt (1 - y ^ 2) * (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3))) +
        t * Real.sqrt (1 - y ^ 2) *
        (W (ω * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * c * t * y) *
          (1 + h ^ 2 * t ^ 2 * (1 / 3 + 2 * y ^ 2 / 3)) -
          alPoly38 h ω c (W ω) (W1 ω) (W2 ω) (W3 ω) t y) := by
      simp only [hf, hg]; ring
    rw [Real.norm_eq_abs, e]
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hgint : ∫ y in (-1 : ℝ)..1, g y =
      t * (Real.pi / 2 * W ω + t ^ 2 * alB38 h ω c (W ω) (W1 ω) (W2 ω)) := by
    have e : ∀ y : ℝ, g y = t * (Real.sqrt (1 - y ^ 2) *
        ((W ω + t ^ 2 * (2 * W ω * h ^ 2 / 6)) +
         (t * (2 * W1 ω * c) + t ^ 3 * (c * (2 * W1 ω * h ^ 2) / 3)) * y +
         (t ^ 2 * ((4 * W ω * h ^ 2 - 3 * W1 ω * h ^ 2 * ω + 12 * W2 ω * c ^ 2) / 6)) * y ^ 2 +
         (t ^ 3 * (c * (4 * W1 ω * h ^ 2 - 3 * W2 ω * h ^ 2 * ω + 4 * W3 ω * c ^ 2) / 3)) *
           y ^ 3)) := fun y => by
      simp only [hg, alPoly38]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, poly_moment38]
    unfold alB38
    ring
  have hsplit : (∫ y in (-1 : ℝ)..1, f y) - ∫ y in (-1 : ℝ)..1, g y =
      ∫ y in (-1 : ℝ)..1, (f y - g y) := (intervalIntegral.integral_sub hfi hgi).symm
  rw [← hgint]
  show |(∫ y in (-1 : ℝ)..1, f y) - ∫ y in (-1 : ℝ)..1, g y| ≤ _
  rw [hsplit]
  have : |(1 : ℝ) - (-1)| = 2 := by norm_num
  rw [this] at hdiff
  rw [← Real.norm_eq_abs]
  calc _ ≤ |C| * t ^ 5 * 2 := hdiff
    _ = _ := by ring


/-! ## The weight `W` is `C⁴` (indeed entire) -/

section Weight

variable {lo up : ℝ} {c : ℕ → ℝ}

theorem weight_contDiff38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) :
    ContDiff ℝ 4 (NlsGge.Weights.weight c) := by
  have hd : Differentiable ℂ (NlsGge.Weights.complexWeight c) := fun w =>
    (NlsGge.Weights.complexWeight_hasDerivAt lo up c hc.1 (fun j => (hc.2.2 j).1)
      (fun j => (hc.2.2 j).2) w).differentiableAt
  have h1 : ContDiff ℂ 4 (NlsGge.Weights.complexWeight c) := hd.contDiff
  have h2 : ContDiff ℝ 4 (NlsGge.Weights.complexWeight c) := h1.restrict_scalars ℝ
  have h3 : ContDiff ℝ 4 (fun r : ℝ => (NlsGge.Weights.complexWeight c (r : ℂ)).re) :=
    Complex.reCLM.contDiff.comp (h2.comp Complex.ofRealCLM.contDiff)
  have : NlsGge.Weights.weight c = fun r : ℝ => (NlsGge.Weights.complexWeight c (r : ℂ)).re :=
    funext fun r => by
      rw [NlsGge.Weights.complexWeight_ofReal lo up c hc.1 (fun j => (hc.2.2 j).1)
        (fun j => (hc.2.2 j).2) r]
      simp
  rw [this]; exact h3

theorem weight_chain38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) :
    (∀ x, HasDerivAt (NlsGge.Weights.weight c) (deriv (NlsGge.Weights.weight c) x) x) ∧
    (∀ x, HasDerivAt (deriv (NlsGge.Weights.weight c)) (deriv (deriv (NlsGge.Weights.weight c)) x) x) ∧
    (∀ x, HasDerivAt (deriv (deriv (NlsGge.Weights.weight c)))
      (deriv (deriv (deriv (NlsGge.Weights.weight c))) x) x) ∧
    (∀ x, HasDerivAt (deriv (deriv (deriv (NlsGge.Weights.weight c))))
      (deriv (deriv (deriv (deriv (NlsGge.Weights.weight c)))) x) x) ∧
    Continuous (deriv (deriv (deriv (deriv (NlsGge.Weights.weight c))))) := by
  have c4 := weight_contDiff38 hc
  have s4 := (contDiff_succ_iff_deriv (n := 3)).mp c4
  have s3 := (contDiff_succ_iff_deriv (n := 2)).mp s4.2.2
  have s2 := (contDiff_succ_iff_deriv (n := 1)).mp s3.2.2
  have s1 := (contDiff_succ_iff_deriv (n := 0)).mp s2.2.2
  exact ⟨fun x => (s4.1 x).hasDerivAt, fun x => (s3.1 x).hasDerivAt, fun x => (s2.1 x).hasDerivAt,
    fun x => (s1.1 x).hasDerivAt, s1.2.2.continuous⟩

end Weight

/-! ## Plane-wave data -/

/-- `b_{h,k} = (h²/2) W(ω) - (h² ω/8) W'(ω) + (c²/2) W''(ω)`, `ω = ω_{h,k}`, `c = cos(π k h)`
(`D:eq:bquartic`). -/
def alBQuartic38 (W : ℝ → ℝ) (h : ℝ) (k : ℤ) : ℝ :=
  h ^ 2 / 2 * W (alOmega38 h k) -
    h ^ 2 * alOmega38 h k / 8 * deriv W (alOmega38 h k) +
    Real.cos (Real.pi * k * h) ^ 2 / 2 * deriv (deriv W) (alOmega38 h k)

theorem alGq_eq38 (W : ℝ → ℝ) {h t θ : ℝ} (ht0 : 0 ≤ t) (y : ℝ) :
    alGq38 W h t θ (t * y) =
      W ((2 * Real.sin θ / h) * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) + 2 * Real.cos θ * t * y) *
        alG38 h t y := by
  unfold alGq38 alG38
  have e1 : 1 - h ^ 2 * (t * y) ^ 2 = 1 - h ^ 2 * t ^ 2 * y ^ 2 := by ring
  have e2 : Real.sqrt (t ^ 2 - (t * y) ^ 2) = t * Real.sqrt (1 - y ^ 2) := by
    rw [show t ^ 2 - (t * y) ^ 2 = t ^ 2 * (1 - y ^ 2) by ring, Real.sqrt_mul (sq_nonneg t),
      Real.sqrt_sq ht0]
  rw [e1, e2]
  ring_nf

theorem norm_alPlaneWave38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (j : ZMod L) :
    ‖alPlaneWave38 L k t j‖ = t / L := by
  unfold alPlaneWave38
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((j.val : ℕ) : ℂ) / (L : ℂ) =
      ((2 * Real.pi * k * (j.val : ℝ) / L : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]


section Energy

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- `D:eq:planeexpansion` with explicit remainder: for `L = 2N+1`, `h = 1/L`, `|k| ≤ N`,
`|E_{W,h}(α(t)) - (W(ω)t² + b_{h,k}t⁴)| ≤ C t⁶` for `0 < t ≤ δ`, `α(t)_j = h t e^{2πikjh}`. -/
theorem alPlane_energy_expansion38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (N : ℕ) (k : ℤ)
    (hk : |k| ≤ N) {h : ℝ} (hh : h = 1 / ((2 * N + 1 : ℕ) : ℝ)) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |alEnergy38 c h (alPlaneWave38 (2 * N + 1) k t) -
        (NlsGge.Weights.weight c (alOmega38 h k) * t ^ 2 +
          alBQuartic38 (NlsGge.Weights.weight c) h k * t ^ 4)| ≤ C * t ^ 6 := by
  have hLpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hLh : ((2 * N + 1 : ℕ) : ℝ) * h = 1 := by rw [hh]; field_simp
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hLpos]; push_cast; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hpi := Real.pi_pos
  obtain ⟨hch1, hch2, hch3, hch4, hch5⟩ := weight_chain38 hc
  have hWc : Continuous (NlsGge.Weights.weight c) :=
    (weight_contDiff38 hc).continuous
  obtain ⟨C₅, δ₅, hδ₅, hy⟩ := alPlane_y_expansion38 hch1 hch2 hch3 hch4 hch5 hh0
    (alOmega38 h k) (Real.cos (Real.pi * k * h))
  refine ⟨2 / Real.pi * |C₅|, min δ₅ (1 / 2), lt_min hδ₅ (by norm_num), fun t ht0 htδ => ?_⟩
  have ht1 : t ≤ 1 / 2 := htδ.trans (min_le_right _ _)
  have ht5 : t ≤ δ₅ := htδ.trans (min_le_left _ _)
  have hht : h * t < 1 := by nlinarith
  have hα : IsALField38 (alPlaneWave38 (2 * N + 1) k t) := by
    intro j
    rw [norm_alPlaneWave38 _ k ht0.le j]
    have : t / ((2 * N + 1 : ℕ) : ℝ) = h * t := by rw [hh]; field_simp
    rw [this]; exact hht
  have hodd : Odd (2 * N + 1) := ⟨N, rfl⟩
  have hh' : h = (((2 * N + 1 : ℕ) : ℝ))⁻¹ := by rw [hh, one_div]
  have hh'' : h = 1 / (((2 * N + 1 : ℕ) : ℝ)) := hh
  rw [alEnergy38_spectral hc hα hodd hh']
  have hθ : |Real.pi * k * h| ≤ Real.pi / 2 - Real.pi * h / 2 := by
    have hkN : (|k| : ℝ) ≤ N := by exact_mod_cast hk
    have e : |Real.pi * k * h| = Real.pi * |(k : ℝ)| * h := by
      rw [abs_mul, abs_mul, abs_of_pos hpi, abs_of_pos hh0]
    rw [e]
    push_cast at hLh
    nlinarith [mul_nonneg (mul_nonneg hpi.le hh0.le) (sub_nonneg.2 hkN)]
  have hint := alPlane_lam_integral38 (W := NlsGge.Weights.weight c) hWc hh0 hh1 ht0 ht1 hθ
  have hcongr : ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
      NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) *
        alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam =
      ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
        NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) *
          (h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * lam - Real.pi * k * h)| /
            Real.sqrt (1 - h ^ 2 * t ^ 2)))) := by
    apply intervalIntegral.integral_congr
    intro lam _
    simp only [alVh38]
    rw [alPlaneWave_gap38 (2 * N + 1) k hh'' ht0.le hht lam]
  rw [hcongr, hint]
  have hcg : ∫ y in (-1 : ℝ)..1, alGq38 (NlsGge.Weights.weight c) h t (Real.pi * k * h) (t * y) =
      ∫ y in (-1 : ℝ)..1, NlsGge.Weights.weight c
        (alOmega38 h k * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) +
          2 * Real.cos (Real.pi * k * h) * t * y) * alG38 h t y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact alGq_eq38 _ ht0.le y
  rw [hcg]
  have hyy := hy t ht0 ht5
  have hb : alBQuartic38 (NlsGge.Weights.weight c) h k =
      2 / Real.pi * alB38 h (alOmega38 h k) (Real.cos (Real.pi * k * h))
        (NlsGge.Weights.weight c (alOmega38 h k))
        (deriv (NlsGge.Weights.weight c) (alOmega38 h k))
        (deriv (deriv (NlsGge.Weights.weight c)) (alOmega38 h k)) := by
    unfold alBQuartic38 alB38
    field_simp
    ring
  rw [hb]
  set I := ∫ y in (-1 : ℝ)..1, NlsGge.Weights.weight c
        (alOmega38 h k * Real.sqrt (1 - h ^ 2 * t ^ 2 * y ^ 2) +
          2 * Real.cos (Real.pi * k * h) * t * y) * alG38 h t y with hI
  set B := alB38 h (alOmega38 h k) (Real.cos (Real.pi * k * h))
        (NlsGge.Weights.weight c (alOmega38 h k))
        (deriv (NlsGge.Weights.weight c) (alOmega38 h k))
        (deriv (deriv (NlsGge.Weights.weight c)) (alOmega38 h k)) with hB
  have e : 2 / Real.pi * (t * I) - (NlsGge.Weights.weight c (alOmega38 h k) * t ^ 2 +
      2 / Real.pi * B * t ^ 4) = 2 / Real.pi * t * (I - t * (Real.pi / 2 *
        NlsGge.Weights.weight c (alOmega38 h k) + t ^ 2 * B)) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / Real.pi * t)]
  calc 2 / Real.pi * t * |I - t * (Real.pi / 2 * NlsGge.Weights.weight c (alOmega38 h k) +
        t ^ 2 * B)| ≤ 2 / Real.pi * t * (C₅ * t ^ 5) :=
        mul_le_mul_of_nonneg_left hyy (by positivity)
    _ ≤ 2 / Real.pi * t * (|C₅| * t ^ 5) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ = _ := by ring

end Energy


/-- `M_d = h t² + h³t⁴/2 + O_h(t⁶)` along the plane wave (`D:eq:planeexpansion` companion). -/
theorem alPlane_mass_expansion38 (N : ℕ) (k : ℤ) {h : ℝ} (hh : h = 1 / ((2 * N + 1 : ℕ) : ℝ)) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) - (h * t ^ 2 + h ^ 3 * t ^ 4 / 2)|
        ≤ C * t ^ 6 := by
  have hLpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hLh : ((2 * N + 1 : ℕ) : ℝ) * h = 1 := by rw [hh]; field_simp
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hLpos]; push_cast; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  refine ⟨2 * h ^ 5, 1 / 2, by norm_num, fun t ht0 htδ => ?_⟩
  have hx0 : 0 ≤ h ^ 2 * t ^ 2 := by positivity
  have hx1 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by
    have : h * t ≤ 1 / 2 := by nlinarith
    nlinarith [mul_nonneg hh0.le ht0.le]
  have hn : ∀ j : ZMod (2 * N + 1), ‖alPlaneWave38 (2 * N + 1) k t j‖ ^ 2 = h ^ 2 * t ^ 2 := by
    intro j
    rw [norm_alPlaneWave38 _ k ht0.le j]
    have : t / ((2 * N + 1 : ℕ) : ℝ) = h * t := by rw [hh]; field_simp
    rw [this]; ring
  have hM : alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) =
      -(((2 * N + 1 : ℕ) : ℝ) * Real.log (1 - h ^ 2 * t ^ 2)) := by
    unfold alMass38
    simp only [hn, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hlog := Real.abs_log_sub_add_sum_range_le (x := h ^ 2 * t ^ 2)
    (by rw [abs_of_nonneg hx0]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg hx0] at hlog
  norm_num at hlog
  set x := h ^ 2 * t ^ 2 with hx
  have hr : |x + x ^ 2 / 2 + Real.log (1 - x)| ≤ 2 * x ^ 3 := by
    refine hlog.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ 3 := by positivity
    nlinarith
  have e : alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) - (h * t ^ 2 + h ^ 3 * t ^ 4 / 2) =
      -(((2 * N + 1 : ℕ) : ℝ) * (x + x ^ 2 / 2 + Real.log (1 - x))) := by
    rw [hM]
    have h1 : ((2 * N + 1 : ℕ) : ℝ) * x = h * t ^ 2 := by
      rw [hx]; calc ((2 * N + 1 : ℕ) : ℝ) * (h ^ 2 * t ^ 2) = (((2 * N + 1 : ℕ) : ℝ) * h) * h * t ^ 2 := by ring
        _ = _ := by rw [hLh]; ring
    have h2 : ((2 * N + 1 : ℕ) : ℝ) * (x ^ 2 / 2) = h ^ 3 * t ^ 4 / 2 := by
      rw [hx]; calc ((2 * N + 1 : ℕ) : ℝ) * ((h ^ 2 * t ^ 2) ^ 2 / 2) =
          (((2 * N + 1 : ℕ) : ℝ) * h) * h ^ 3 * t ^ 4 / 2 := by ring
        _ = _ := by rw [hLh]; ring
    linarith
  rw [e, abs_neg, abs_mul, abs_of_pos hLpos]
  calc ((2 * N + 1 : ℕ) : ℝ) * |x + x ^ 2 / 2 + Real.log (1 - x)|
      ≤ ((2 * N + 1 : ℕ) : ℝ) * (2 * x ^ 3) := mul_le_mul_of_nonneg_left hr hLpos.le
    _ = 2 * h ^ 5 * t ^ 6 := by
        rw [hx]; calc ((2 * N + 1 : ℕ) : ℝ) * (2 * (h ^ 2 * t ^ 2) ^ 3) =
          2 * (((2 * N + 1 : ℕ) : ℝ) * h) * h ^ 5 * t ^ 6 := by ring
          _ = _ := by rw [hLh]; ring

/-- The nonlinear remainder `R_h` (`D:eq:ALR`) at the plane wave `u(jh) = t e^{2πikjh}`:
`R_h = E_{W,h} - M_d - Σ_{k'} a_{h,k'} |û(k')|²`.  For this field `û(k') = t δ_{k',k}`
(Parseval for the pure mode `k`, `|k| ≤ N`), so the Gaussian part is `a_{h,k} t² =
(W(ω_{h,k}) - h) t²` (`D:eq:ALrates`). -/
def alPlaneR38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (h t : ℝ) : ℝ :=
  alEnergy38 c h (alPlaneWave38 (2 * N + 1) k t) -
    alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) - alRate38 c h k * t ^ 2

/-- The quartic coefficient of `R_h` is `b_{h,k} - h³/2`. -/
theorem alPlane_R_expansion38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (N : ℕ) (k : ℤ) (hk : |k| ≤ N) {h : ℝ}
    (hh : h = 1 / ((2 * N + 1 : ℕ) : ℝ)) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |alPlaneR38 c N k h t - (alBQuartic38 (NlsGge.Weights.weight c) h k - h ^ 3 / 2) * t ^ 4|
        ≤ C * t ^ 6 := by
  obtain ⟨C₁, δ₁, hδ₁, h₁⟩ := alPlane_energy_expansion38 hc N k hk hh
  obtain ⟨C₂, δ₂, hδ₂, h₂⟩ := alPlane_mass_expansion38 N k hh
  refine ⟨C₁ + C₂, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht0 htδ => ?_⟩
  have a := h₁ t ht0 (htδ.trans (min_le_left _ _))
  have b := h₂ t ht0 (htδ.trans (min_le_right _ _))
  have e : alPlaneR38 c N k h t - (alBQuartic38 (NlsGge.Weights.weight c) h k - h ^ 3 / 2) * t ^ 4 =
      (alEnergy38 c h (alPlaneWave38 (2 * N + 1) k t) -
        (NlsGge.Weights.weight c (alOmega38 h k) * t ^ 2 +
          alBQuartic38 (NlsGge.Weights.weight c) h k * t ^ 4)) -
      (alMass38 (2 * N + 1) (alPlaneWave38 (2 * N + 1) k t) - (h * t ^ 2 + h ^ 3 * t ^ 4 / 2)) := by
    unfold alPlaneR38 alRate38; ring
  rw [e]
  calc _ ≤ |_| + |_| := abs_sub _ _
    _ ≤ C₁ * t ^ 6 + C₂ * t ^ 6 := add_le_add a b
    _ = _ := by ring



/-! ## The highest mode `k = N` -/

/-- Pure algebra for `D:eq:negativeedge`: with `s⁴ = h`, `q⁴ = ω`, `ωh = 2κ`, the quartic
coefficient normalised by `W` is `-(√2/4)s⁶ + O(s⁷)`. -/
theorem edge_core38 {C h ω κ c₀ A B s q : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hq : 0 < q)
    (hsh : s ^ 4 = h) (hqω : q ^ 4 = ω) (hωh : ω * h = 2 * κ) (hκ1 : κ ≤ 1)
    (hκ2 : 2 - 2 * κ ≤ 3 * h ^ 2) (hκ0 : 99 / 100 ≤ κ) (hh1 : h ≤ 1 / 16)
    (hc2 : c₀ ^ 2 ≤ 3 * h ^ 2)
    (hA : |A - 2 / q ^ 2| ≤ C / q ^ 3) (hB : |B - 4 / q ^ 4| ≤ C / q ^ 5) :
    |h ^ 2 / 2 - h ^ 2 * ω / 8 * A + c₀ ^ 2 / 2 * B + Real.sqrt 2 / 4 * s ^ 6| ≤
      (8 + 2 * C) * s ^ 7 := by
  have hh0 : 0 < h := by rw [← hsh]; positivity
  have hs1 : s ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : 1 < s ^ 4 := one_lt_pow₀ hcon (by norm_num)
    linarith
  have hωpos : 0 < ω := by rw [← hqω]; positivity
  -- (sq)^4 = 2κ, hence 1 ≤ s q ≤ 2
  have hsq4 : (s * q) ^ 4 = 2 * κ := by rw [mul_pow, hsh, hqω, mul_comm, hωh]
  have hsq0 : 0 < s * q := by positivity
  have hsq1 : 1 ≤ s * q := by
    by_contra hcon
    push Not at hcon
    have : (s * q) ^ 4 < 1 := pow_lt_one₀ hsq0.le hcon (by norm_num)
    linarith
  have hsq2 : s * q ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 4 < (s * q) ^ 4 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    linarith
  have hq1 : 1 / s ≤ q := by rw [div_le_iff₀ hs]; linarith
  have hq2 : q ≤ 2 / s := by rw [le_div_iff₀ hs]; linarith
  have hqs : 1 / q ≤ s := by rw [div_le_iff₀ hq]; linarith
  -- the main identity
  have hqpos2 : 0 < q ^ 2 := by positivity
  set a1 := A - 2 / q ^ 2 with ha1
  set a2 := B - 4 / q ^ 4 with ha2
  have hAe : A = 2 / q ^ 2 + a1 := by rw [ha1]; ring
  have hBe : B = 4 / q ^ 4 + a2 := by rw [ha2]; ring
  have hωq : ω / q ^ 2 = q ^ 2 := by rw [← hqω]; field_simp
  -- √(2κ) = (sq)²
  have hr : Real.sqrt (2 * κ) = (s * q) ^ 2 := by
    rw [← hsq4, show (s * q) ^ 4 = ((s * q) ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have h6 : h ^ 2 * q ^ 2 / 4 = s ^ 6 * Real.sqrt (2 * κ) / 4 := by
    rw [hr, ← hsh]; ring
  have hmain : h ^ 2 / 2 - h ^ 2 * ω / 8 * A + c₀ ^ 2 / 2 * B + Real.sqrt 2 / 4 * s ^ 6 =
      h ^ 2 / 2 + s ^ 6 / 4 * (Real.sqrt 2 - Real.sqrt (2 * κ)) - h ^ 2 * ω / 8 * a1 +
      2 * c₀ ^ 2 / q ^ 4 + c₀ ^ 2 / 2 * a2 := by
    rw [hAe, hBe]
    have : h ^ 2 * ω / 8 * (2 / q ^ 2) = h ^ 2 * (ω / q ^ 2) / 4 := by ring
    have e2 : h ^ 2 * ω / 8 * (2 / q ^ 2 + a1) = h ^ 2 * q ^ 2 / 4 + h ^ 2 * ω / 8 * a1 := by
      rw [mul_add, this, hωq]
    rw [e2]
    have e3 : h ^ 2 * q ^ 2 / 4 = s ^ 6 / 4 * Real.sqrt (2 * κ) := by rw [h6]; ring
    rw [e3]
    ring
  rw [hmain]
  -- bounds
  have hss : ∀ n : ℕ, 7 ≤ n → s ^ n ≤ s ^ 7 := fun n hn => pow_le_pow_of_le_one hs.le hs1 hn
  have b1 : |h ^ 2 / 2| ≤ 1 / 2 * s ^ 7 := by
    rw [abs_of_nonneg (by positivity), ← hsh, ← pow_mul]
    have := hss 8 (by norm_num)
    nlinarith
  have b2 : |s ^ 6 / 4 * (Real.sqrt 2 - Real.sqrt (2 * κ))| ≤ s ^ 7 := by
    have hu : Real.sqrt (2 * κ) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
    have hr2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hu2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 * κ by linarith)
    have hr1 : 1 ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have hup0 : 0 ≤ Real.sqrt (2 * κ) := Real.sqrt_nonneg _
    have hd : Real.sqrt 2 - Real.sqrt (2 * κ) ≤ 3 * h ^ 2 := by
      nlinarith
    have hd0 : 0 ≤ Real.sqrt 2 - Real.sqrt (2 * κ) := by linarith
    rw [abs_of_nonneg (by positivity)]
    have : s ^ 6 / 4 * (Real.sqrt 2 - Real.sqrt (2 * κ)) ≤ s ^ 6 / 4 * (3 * h ^ 2) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have e : s ^ 6 / 4 * (3 * h ^ 2) = 3 / 4 * s ^ 14 := by rw [← hsh]; ring
    have := hss 14 (by norm_num)
    linarith [pow_nonneg hs.le 7]
  have b3 : |h ^ 2 * ω / 8 * a1| ≤ C / 4 * s ^ 7 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ h ^ 2 * ω / 8)]
    have hq3 : 0 < q ^ 3 := by positivity
    have h1 : |a1| ≤ C / q ^ 3 := hA
    have e : h ^ 2 * ω / 8 * (C / q ^ 3) = C / 8 * s ^ 8 * q := by
      rw [← hqω, ← hsh]; field_simp
    calc h ^ 2 * ω / 8 * |a1| ≤ h ^ 2 * ω / 8 * (C / q ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C / 8 * s ^ 8 * q := e
      _ ≤ C / 8 * s ^ 8 * (2 / s) := by
          apply mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ = C / 4 * s ^ 7 := by field_simp; ring
  have b4 : |2 * c₀ ^ 2 / q ^ 4| ≤ 6 * s ^ 7 := by
    rw [abs_of_nonneg (by positivity)]
    have hq4 : 1 / q ^ 4 ≤ s ^ 4 := by
      rw [div_le_iff₀ (by positivity)]
      have h14 : 1 ≤ (s * q) ^ 4 := one_le_pow₀ hsq1
      rw [mul_pow] at h14
      linarith
    have : 2 * c₀ ^ 2 / q ^ 4 = 2 * c₀ ^ 2 * (1 / q ^ 4) := by ring
    rw [this]
    calc 2 * c₀ ^ 2 * (1 / q ^ 4) ≤ 2 * (3 * h ^ 2) * s ^ 4 := by
          apply mul_le_mul (by linarith) hq4 (by positivity) (by positivity)
      _ = 6 * s ^ 12 := by rw [← hsh]; ring
      _ ≤ 6 * s ^ 7 := by have := hss 12 (by norm_num); linarith
  have b5 : |c₀ ^ 2 / 2 * a2| ≤ 3 / 2 * C * s ^ 7 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c₀ ^ 2 / 2)]
    have hq5 : 1 / q ^ 5 ≤ s ^ 5 := by
      rw [div_le_iff₀ (by positivity)]
      have h15 : 1 ≤ (s * q) ^ 5 := one_le_pow₀ hsq1
      rw [mul_pow] at h15
      linarith
    have h2 : |a2| ≤ C / q ^ 5 := hB
    have h3 : C / q ^ 5 = C * (1 / q ^ 5) := by ring
    calc c₀ ^ 2 / 2 * |a2| ≤ (3 * h ^ 2 / 2) * (C * s ^ 5) := by
          apply mul_le_mul (by linarith) _ (abs_nonneg _) (by positivity)
          rw [h3] at h2
          exact h2.trans (mul_le_mul_of_nonneg_left hq5 hC)
      _ = 3 / 2 * C * s ^ 13 := by rw [← hsh]; ring
      _ ≤ 3 / 2 * C * s ^ 7 :=
          mul_le_mul_of_nonneg_left (hss 13 (by norm_num)) (by positivity)
  have c1 := abs_le.mp b1
  have c2 := abs_le.mp b2
  have c3 := abs_le.mp b3
  have c4 := abs_le.mp b4
  have c5 := abs_le.mp b5
  have p7 := pow_nonneg hs.le 7
  have p8 := mul_nonneg hC p7
  apply abs_le.mpr
  constructor <;> linarith


theorem rpow_quarter38 {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ ((n : ℝ) / 4) = (x ^ (1 / 4 : ℝ)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring

theorem rpow_quarter_neg38 {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-((n : ℝ) / 4)) = ((x ^ (1 / 4 : ℝ)) ^ n)⁻¹ := by
  rw [Real.rpow_neg hx, rpow_quarter38 hx]

/-- `D:eq:negativeedge` with explicit remainder, uniformly in the coefficient class:
`|b_{h,N}/W(ω_{h,N}) + (√2/4) h^{3/2}| ≤ K h^{7/4}` for `h = 1/(2N+1) ≤ h₀`. -/
theorem alPlane_edge_asymptotics38 (lo up : ℝ) (hlo : 0 < lo) (hlu : lo ≤ up) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ ∀ c : ℕ → ℝ, (∀ j, lo ≤ c j) → (∀ j, c j ≤ up) →
      ∀ (N : ℕ) (h : ℝ), h = 1 / ((2 * N + 1 : ℕ) : ℝ) → h ≤ h₀ →
        |alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) /
            NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) +
          Real.sqrt 2 / 4 * h ^ (3 / 2 : ℝ)| ≤ K * h ^ (7 / 4 : ℝ) := by
  obtain ⟨C₀, hC₀, hW02⟩ := NlsGge.Weights.weight_uniform_derivative_asymptotics lo up hlo hlu
  refine ⟨8 + 2 * C₀, 1 / 16, by positivity, by norm_num, fun c hcl hcu N h hh hh16 => ?_⟩
  have hLpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hLh : ((2 * N + 1 : ℕ) : ℝ) * h = 1 := by rw [hh]; field_simp
  push_cast at hLh
  have hh0 : 0 < h := by rw [hh]; positivity
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  set x := Real.pi * h / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 10 := by rw [hx]; nlinarith
  have hθ : Real.pi * ((N : ℤ) : ℝ) * h = Real.pi / 2 - x := by
    rw [hx, Int.cast_natCast]; nlinarith
  have hsin : Real.sin (Real.pi * ((N : ℤ) : ℝ) * h) = Real.cos x := by
    rw [hθ, Real.sin_pi_div_two_sub]
  have hcos : Real.cos (Real.pi * ((N : ℤ) : ℝ) * h) = Real.sin x := by
    rw [hθ, Real.cos_pi_div_two_sub]
  set κ := Real.cos x with hκ
  have hκ1 : κ ≤ 1 := Real.cos_le_one x
  have hκ0 : 1 - x ^ 2 / 2 ≤ κ := Real.one_sub_sq_div_two_le_cos
  have hx2 : x ^ 2 ≤ 3 * h ^ 2 := by
    have hp2 : Real.pi ^ 2 ≤ 12 := by nlinarith
    have e : x ^ 2 = Real.pi ^ 2 * h ^ 2 / 4 := by rw [hx]; ring
    rw [e]; nlinarith [mul_nonneg (sub_nonneg.2 hp2) (sq_nonneg h)]
  have hκ0' : 99 / 100 ≤ κ := by nlinarith
  have hκ2 : 2 - 2 * κ ≤ 3 * h ^ 2 := by nlinarith
  have hc2 : Real.sin x ^ 2 ≤ 3 * h ^ 2 := by
    have h1 : Real.sin x ≤ x := Real.sin_le hx0
    have h2 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_gt_three])
    nlinarith
  set ω := alOmega38 h (N : ℤ) with hω
  have hωκ : ω = 2 * κ / h := by rw [hω]; unfold alOmega38; rw [hsin]
  have hωh : ω * h = 2 * κ := by rw [hωκ]; field_simp
  have hω16 : 16 ≤ ω := by
    rw [hωκ, le_div_iff₀ hh0]; nlinarith
  have hω0 : 0 < ω := by linarith
  set s := h ^ (1 / 4 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hh0 _
  have hsh : s ^ 4 = h := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hh0.le]; norm_num
  set q := ω ^ (1 / 4 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hω0 _
  have hqω : q ^ 4 = ω := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hω0.le]; norm_num
  have hWpos : 0 < NlsGge.Weights.weight c ω := NlsGge.Weights.weight_pos lo up c hlo hcl hcu ω
  obtain ⟨hA, hB⟩ := hW02 c hcl hcu ω hω16
  have e1 : ω ^ (-1 / 2 : ℝ) = (q ^ 2)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(((2 : ℕ) : ℝ) / 4) by norm_num, rpow_quarter_neg38 hω0.le 2]
  have e2 : ω ^ (-3 / 4 : ℝ) = (q ^ 3)⁻¹ := by
    rw [show (-3 / 4 : ℝ) = -(((3 : ℕ) : ℝ) / 4) by norm_num, rpow_quarter_neg38 hω0.le 3]
  have e3 : ω ^ (-5 / 4 : ℝ) = (q ^ 5)⁻¹ := by
    rw [show (-5 / 4 : ℝ) = -(((5 : ℕ) : ℝ) / 4) by norm_num, rpow_quarter_neg38 hω0.le 5]
  rw [e1, e2] at hA
  rw [e3] at hB
  have hA' : |deriv (NlsGge.Weights.weight c) ω / NlsGge.Weights.weight c ω - 2 / q ^ 2| ≤
      C₀ / q ^ 3 := by
    rw [div_eq_mul_inv 2, div_eq_mul_inv C₀]; exact hA
  have hB' : |deriv (deriv (NlsGge.Weights.weight c)) ω / NlsGge.Weights.weight c ω -
      4 / q ^ 4| ≤ C₀ / q ^ 5 := by
    rw [hqω, div_eq_mul_inv C₀]; exact hB
  have hcore := edge_core38 (C := C₀) hC₀.le hs0 hq0 hsh hqω hωh hκ1 hκ2 hκ0' (by linarith)
    hc2 hA' hB'
  have hb : alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) / NlsGge.Weights.weight c ω =
      h ^ 2 / 2 - h ^ 2 * ω / 8 * (deriv (NlsGge.Weights.weight c) ω /
        NlsGge.Weights.weight c ω) + Real.sin x ^ 2 / 2 *
        (deriv (deriv (NlsGge.Weights.weight c)) ω / NlsGge.Weights.weight c ω) := by
    unfold alBQuartic38
    rw [← hω, hcos]
    field_simp
  have e6 : h ^ (3 / 2 : ℝ) = s ^ 6 := by
    rw [show (3 / 2 : ℝ) = ((6 : ℕ) : ℝ) / 4 by norm_num, rpow_quarter38 hh0.le 6]
  have e7 : h ^ (7 / 4 : ℝ) = s ^ 7 := by
    rw [show (7 / 4 : ℝ) = ((7 : ℕ) : ℝ) / 4 by norm_num, rpow_quarter38 hh0.le 7]
  rw [hb, e6, e7]
  exact hcore


/-- Sign claim of `D:eq:negativeedge`: for `h ≤ h₀`, `b_{h,N}/W(ω_{h,N}) ≤ -(√2/8)h^{3/2} < 0`
(together with the asymptotic `|b/W + (√2/4)h^{3/2}| ≤ K h^{7/4}`). -/
theorem alPlane_edge_negative38 (lo up : ℝ) (hlo : 0 < lo) (hlu : lo ≤ up) :
    ∃ K h₀ : ℝ, 0 < K ∧ 0 < h₀ ∧ ∀ c : ℕ → ℝ, (∀ j, lo ≤ c j) → (∀ j, c j ≤ up) →
      ∀ (N : ℕ) (h : ℝ), h = 1 / ((2 * N + 1 : ℕ) : ℝ) → h ≤ h₀ →
        |alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) /
            NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) +
          Real.sqrt 2 / 4 * h ^ (3 / 2 : ℝ)| ≤ K * h ^ (7 / 4 : ℝ) ∧
        alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) /
            NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) ≤
          -(Real.sqrt 2 / 8 * h ^ (3 / 2 : ℝ)) ∧
        alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) < 0 := by
  obtain ⟨K, h₁, hK, hh₁, hasym⟩ := alPlane_edge_asymptotics38 lo up hlo hlu
  set s₀ : ℝ := 1 / (8 * K + 8) with hs₀
  have hs₀0 : 0 < s₀ := by rw [hs₀]; positivity
  refine ⟨K, min h₁ (s₀ ^ 4), hK, lt_min hh₁ (by positivity), fun c hcl hcu N h hh hh0' => ?_⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hha := hasym c hcl hcu N h hh (hh0'.trans (min_le_left _ _))
  refine ⟨hha, ?_⟩
  set s := h ^ (1 / 4 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hh0 _
  have hsh : s ^ 4 = h := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hh0.le]; norm_num
  have hss : s ≤ s₀ := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs₀0.le ?_
    rw [hsh]; exact hh0'.trans (min_le_right _ _)
  have e6 : h ^ (3 / 2 : ℝ) = s ^ 6 := by
    rw [show (3 / 2 : ℝ) = ((6 : ℕ) : ℝ) / 4 by norm_num, rpow_quarter38 hh0.le 6]
  have e7 : h ^ (7 / 4 : ℝ) = s ^ 7 := by
    rw [show (7 / 4 : ℝ) = ((7 : ℕ) : ℝ) / 4 by norm_num, rpow_quarter38 hh0.le 7]
  rw [e6, e7] at hha
  rw [e6]
  have hKs : K * s ≤ 1 / 8 := by
    calc K * s ≤ K * s₀ := mul_le_mul_of_nonneg_left hss hK.le
      _ = K / (8 * K + 8) := by rw [hs₀]; ring
      _ ≤ 1 / 8 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hr1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs6 : 0 < s ^ 6 := by positivity
  have hb : alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) /
      NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) ≤ -(Real.sqrt 2 / 8 * s ^ 6) := by
    have h1 := (abs_le.mp hha).2
    have h2 : K * s ^ 7 ≤ 1 / 8 * s ^ 6 := by
      have : K * s ^ 7 = (K * s) * s ^ 6 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hKs hs6.le
    nlinarith
  refine ⟨hb, ?_⟩
  have hWpos : 0 < NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) :=
    NlsGge.Weights.weight_pos lo up c hlo hcl hcu _
  have hneg : alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) /
      NlsGge.Weights.weight c (alOmega38 h (N : ℤ)) < 0 := by
    have : 0 < Real.sqrt 2 / 8 * s ^ 6 := by positivity
    linarith
  exact (div_neg_iff.mp hneg).elim (fun h' => absurd h'.2 (not_lt.mpr hWpos.le))
    (fun h' => h'.1)


/-- The `o(h^{3/2})` form of `D:eq:negativeedge`: as `N → ∞` (`h = 1/(2N+1)`),
`b_{h,N} / (W(ω_{h,N}) h^{3/2}) → -√2/4`, i.e. `b_{h,N}/W(ω_{h,N}) = -(√2/4)h^{3/2} + o(h^{3/2})`. -/
theorem alPlane_edge_little_o38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) :
    Filter.Tendsto (fun N : ℕ =>
      alBQuartic38 (NlsGge.Weights.weight c) (1 / ((2 * N + 1 : ℕ) : ℝ)) (N : ℤ) /
        (NlsGge.Weights.weight c (alOmega38 (1 / ((2 * N + 1 : ℕ) : ℝ)) (N : ℤ)) *
          (1 / ((2 * N + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ)))
      Filter.atTop (nhds (-(Real.sqrt 2 / 4))) := by
  obtain ⟨hlo, hlu, hbd⟩ := hc
  obtain ⟨K, h₀, hK, hh₀, hasym⟩ := alPlane_edge_asymptotics38 lo up hlo hlu
  set hN : ℕ → ℝ := fun N => 1 / ((2 * N + 1 : ℕ) : ℝ) with hhN
  have hlim : Filter.Tendsto hN Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      exact Filter.tendsto_atTop_mono (fun N : ℕ => (by omega : N ≤ 2 * N + 1)) Filter.tendsto_id
    simpa [hhN, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h1
  have hev : ∀ᶠ N in Filter.atTop, hN N < h₀ := hlim.eventually (Iio_mem_nhds hh₀)
  have hg : Filter.Tendsto (fun N : ℕ => K * hN N ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
    have := (hlim.rpow_const (p := (1 / 4 : ℝ)) (Or.inr (by norm_num))).const_mul K
    simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [hev] with N hN0
  have hh0 : 0 < hN N := by simp only [hhN]; positivity
  have hwp := NlsGge.Weights.weight_pos lo up c hlo (fun j => (hbd j).1) (fun j => (hbd j).2)
    (alOmega38 (hN N) (N : ℤ))
  have hasy := hasym c (fun j => (hbd j).1) (fun j => (hbd j).2) N (hN N) rfl hN0.le
  have h32 : 0 < hN N ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hh0 _
  set b := alBQuartic38 (NlsGge.Weights.weight c) (hN N) (N : ℤ)
  set W := NlsGge.Weights.weight c (alOmega38 (hN N) (N : ℤ))
  have e : b / (W * hN N ^ (3 / 2 : ℝ)) - -(Real.sqrt 2 / 4) =
      (b / W + Real.sqrt 2 / 4 * hN N ^ (3 / 2 : ℝ)) / hN N ^ (3 / 2 : ℝ) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, e, abs_div, abs_of_pos h32, div_le_iff₀ h32]
  refine hasy.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add hh0]; norm_num



/-! ## The remainder `R_h` in Fourier coordinates, at the plane wave -/

/-- The plane wave is a character of `ZMod L`: `α_j = (t/L) e^{2πikj/L}`. -/
theorem alPlaneWave_char38 (L : ℕ) [NeZero L] (k : ℤ) (t : ℝ) (x : ZMod L) :
    alPlaneWave38 L k t x = ((t / L : ℝ) : ℂ) * ZMod.stdAddChar ((k : ZMod L) * x) := by
  have e : (k : ZMod L) * x = ((k * (x.val : ℤ) : ℤ) : ZMod L) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [e, ZMod.stdAddChar_coe]
  unfold alPlaneWave38
  congr 2
  push_cast; ring

/-- Discrete Fourier transform of the plane wave: `û = t · 1_{j = k}` (the pure mode `k`). -/
theorem dft_plane38 (N : ℕ) (k : ℤ) (t : ℝ) (j : ZMod (2 * N + 1)) :
    ZMod.dft (alPlaneWave38 (2 * N + 1) k t) j = if j = (k : ZMod (2 * N + 1)) then (t : ℂ) else 0 := by
  have hL : ((2 * N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * N + 1 ≠ 0)
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  have e : ∀ x : ZMod (2 * N + 1), ZMod.stdAddChar (-(x * j)) * alPlaneWave38 (2 * N + 1) k t x =
      ((t / (2 * N + 1 : ℕ) : ℝ) : ℂ) * ZMod.stdAddChar (x * ((k : ZMod (2 * N + 1)) - j)) := by
    intro x
    rw [alPlaneWave_char38, mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum,
    AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _)]
  by_cases hj : j = (k : ZMod (2 * N + 1))
  · simp only [hj, sub_self, ↓reduceIte, ZMod.card]
    have hL' : (2 * (N : ℂ) + 1) ≠ 0 := by
      have := hL; push_cast at this; exact this
    push_cast
    field_simp
  · have : (k : ZMod (2 * N + 1)) - j ≠ 0 := fun h0 => hj (sub_eq_zero.mp h0).symm
    simp [hj, this]

/-- For the plane wave (`|k| ≤ N`, `h = 1/(2N+1)`) the Fourier-coordinate remainder `R_h`
(`alRemainder38`, `D:eq:ALR`, with `û = DFT α`, `α_j = h u(jh)`) is
`E_{W,h} - M_d - a_{h,k} t²`, since `û = t · 1_{k}`. -/
theorem alRemainder_plane38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (hk : |k| ≤ N) (h t : ℝ) :
    alRemainder38 c h (ZMod.dft (alPlaneWave38 (2 * N + 1) k t)) = alPlaneR38 c N k h t := by
  unfold alRemainder38 alPlaneR38
  rw [LinearEquiv.symm_apply_apply]
  have hspec : ((k : ZMod (2 * N + 1))).valMinAbs = k := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have := abs_le.mp hk
    constructor <;> push_cast <;> omega
  have hsum : ∑ j : ZMod (2 * N + 1), alRate38 c h j.valMinAbs *
      ‖ZMod.dft (alPlaneWave38 (2 * N + 1) k t) j‖ ^ 2 =
      ∑ j : ZMod (2 * N + 1), if j = (k : ZMod (2 * N + 1)) then alRate38 c h k * t ^ 2 else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dft_plane38]
    by_cases hj : j = (k : ZMod (2 * N + 1))
    · subst hj; simp [hspec]
    · simp [hj]
  rw [hsum, Finset.sum_ite_eq']
  simp

/-- `D:prop:negativeAL`, last sentence: for every sufficiently fine grid (`h ≤ h₀`, `k = N`)
there are arbitrarily small nonzero plane waves (all `0 < t ≤ t₀`) with `R_h < 0` and `f_h > 1`
(`alReweight38 = 1_{h max_j|u(jh)|<1} e^{-R_h}`, Fourier coordinates `û = DFT α`); the quartic
coefficient `b_{h,N} - h³/2` of `R_h` is negative. -/
theorem alPlane_negative_remainder38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ (N : ℕ) (h : ℝ), h = 1 / ((2 * N + 1 : ℕ) : ℝ) → h ≤ h₀ →
      alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) - h ^ 3 / 2 < 0 ∧
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
        IsALField38 (alPlaneWave38 (2 * N + 1) (N : ℤ) t) ∧
        alRemainder38 c h (ZMod.dft (alPlaneWave38 (2 * N + 1) (N : ℤ) t)) < 0 ∧
        1 < alReweight38 c h (ZMod.dft (alPlaneWave38 (2 * N + 1) (N : ℤ) t)) := by
  obtain ⟨hlo, hlu, hbd⟩ := hc
  obtain ⟨K, h₀, hK, hh₀, hneg⟩ := alPlane_edge_negative38 lo up hlo hlu
  refine ⟨h₀, hh₀, fun N h hh hhle => ?_⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hcl : ∀ j, lo ≤ c j := fun j => (hbd j).1
  have hcu : ∀ j, c j ≤ up := fun j => (hbd j).2
  obtain ⟨-, -, hb⟩ := hneg c hcl hcu N h hh hhle
  have hqneg : alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) - h ^ 3 / 2 < 0 := by
    have : 0 < h ^ 3 := by positivity
    linarith
  refine ⟨hqneg, ?_⟩
  obtain ⟨C, δ, hδ, hR⟩ := alPlane_R_expansion38 ⟨hlo, hlu, hbd⟩ N (N : ℤ)
    (by simp) hh
  set q := alBQuartic38 (NlsGge.Weights.weight c) h (N : ℤ) - h ^ 3 / 2 with hq
  set t₀ := min δ (min (1 / 2) (-q / (2 * (|C| + 1)))) with ht₀
  have hqpos : 0 < -q := by linarith
  have ht₀0 : 0 < t₀ := lt_min hδ (lt_min (by norm_num) (by positivity))
  refine ⟨t₀, ht₀0, fun t ht0 htle => ?_⟩
  have htδ : t ≤ δ := htle.trans (min_le_left _ _)
  have ht1 : t ≤ 1 / 2 := htle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htq : t ≤ -q / (2 * (|C| + 1)) := htle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hht : h * t < 1 := by
    have : 1 / ((2 * N + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; push_cast
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have hh1 : h ≤ 1 := by rw [hh]; exact this
    nlinarith
  have hα : IsALField38 (alPlaneWave38 (2 * N + 1) (N : ℤ) t) := by
    intro j
    rw [norm_alPlaneWave38 _ (N : ℤ) ht0.le j]
    have : t / ((2 * N + 1 : ℕ) : ℝ) = h * t := by rw [hh]; field_simp
    rw [this]; exact hht
  have hRb := hR t ht0 htδ
  have h1 := (abs_le.mp hRb).2
  have hCt : C * t ^ 6 ≤ |C| * t * t ^ 4 := by
    have h4 : 0 ≤ t ^ 4 := by positivity
    have : t ^ 2 ≤ t := by nlinarith
    calc C * t ^ 6 ≤ |C| * t ^ 6 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |C| * t ^ 2 * t ^ 4 := by ring
      _ ≤ |C| * t * t ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (abs_nonneg _)) h4
  have hAbs : |C| * t < -q / 2 := by
    have h2 : (|C| + 1) * t ≤ -q / 2 := by
      have := mul_le_mul_of_nonneg_left htq (by positivity : (0:ℝ) ≤ |C| + 1)
      calc (|C| + 1) * t ≤ (|C| + 1) * (-q / (2 * (|C| + 1))) := this
        _ = -q / 2 := by field_simp
    nlinarith [abs_nonneg C]
  have hRneg : alPlaneR38 c N (N : ℤ) h t < 0 := by
    have h4 : 0 < t ^ 4 := by positivity
    have : q * t ^ 4 + |C| * t * t ^ 4 < 0 := by
      have : (q + |C| * t) * t ^ 4 < 0 := mul_neg_of_neg_of_pos (by linarith) h4
      linarith
    linarith
  have hRem : alRemainder38 c h (ZMod.dft (alPlaneWave38 (2 * N + 1) (N : ℤ) t)) < 0 := by
    rw [alRemainder_plane38 c N (N : ℤ) (by simp)]; exact hRneg
  refine ⟨hα, hRem, ?_⟩
  unfold alReweight38
  simp only [LinearEquiv.symm_apply_apply, hα, ↓reduceIte]
  exact Real.one_lt_exp_iff.mpr (by linarith)

end NlsGge.AblowitzLadik
