import Mathlib

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open Complex

/-- Cauchy estimate for an entire function bounded by `δ` on the closed disc of radius `r`
around `c`. -/
lemma window38_cauchy_deriv_bound {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hb : ∀ z : ℂ, ‖z - c‖ ≤ r → ‖h z‖ ≤ δ) : ‖deriv h c‖ ≤ δ / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hh.diffContOnCl
    (fun z hz => hb z (by rw [mem_sphere_iff_norm] at hz; exact hz.le))

/-- Elementary bound `cos t ≤ 1 - t^2/4` for `|t| ≤ 1/2`. -/
lemma window38_cos_le (t : ℝ) (ht : |t| ≤ 1 / 2) : Real.cos t ≤ 1 - t ^ 2 / 4 := by
  have h1 : |t| ≤ 1 := by linarith
  have hb := (abs_le.1 (Real.cos_bound h1)).2
  have h4 : |t| ^ 4 = t ^ 2 * t ^ 2 := by
    have : |t| ^ 2 = t ^ 2 := sq_abs t
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = t ^ 2 * t ^ 2 := by rw [this]; ring
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    have : |t| ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    rw [sq_abs] at this; linarith
  have h0 : 0 ≤ t ^ 2 := sq_nonneg t
  rw [h4] at hb
  nlinarith

/-- Cosine lower bound `cos t ≥ 7/8` for `|t| ≤ 1/2`. -/
lemma window38_cos_ge (t : ℝ) (ht : |t| ≤ 1 / 2) : 7 / 8 ≤ Real.cos t := by
  have h := Real.one_sub_sq_div_two_le_cos (x := t)
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    have : |t| ^ 2 ≤ (1 / 2) ^ 2 := by gcongr
    rw [sq_abs] at this; linarith
  linarith

theorem windowGapStructure_E02_38 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f x).im = 0) (n : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hbox : ∀ z : ℂ, |z.re - n * Real.pi| ≤ 1 → |z.im| ≤ 1 →
      ‖f z - Complex.cos z‖ ≤ δ) :
    let W := Set.Icc ((n : ℝ) * Real.pi - 1 / 2) ((n : ℝ) * Real.pi + 1 / 2)
    let g : ℝ → ℝ := fun x => Real.cos ((n : ℝ) * Real.pi) * (f x).re
    StrictConcaveOn ℝ W g ∧ Continuous g ∧
    g ((n : ℝ) * Real.pi - 1 / 2) < 1 ∧ g ((n : ℝ) * Real.pi + 1 / 2) < 1 ∧
    (∀ x ∈ W, -1 < g x) ∧ (∀ x ∈ W, ‖f x‖ = |g x|) ∧
    (∀ x ∈ W, 1 ≤ ‖f x‖ → |x - (n : ℝ) * Real.pi| ≤ 2 * Real.sqrt δ) := by
  intro W g
  set h : ℂ → ℂ := fun z => f z - Complex.cos z with hhdef
  have hhd : Differentiable ℂ h := hf.sub Complex.differentiable_cos
  have hbh : ∀ z : ℂ, |z.re - n * Real.pi| ≤ 1 → |z.im| ≤ 1 → ‖h z‖ ≤ δ := hbox
  -- first Cauchy estimate
  have h1 : ∀ c : ℂ, |c.re - n * Real.pi| ≤ 3 / 4 → |c.im| ≤ 3 / 4 → ‖deriv h c‖ ≤ 4 * δ := by
    intro c hc1 hc2
    have key := window38_cauchy_deriv_bound hhd (c := c) (r := 1 / 4) (δ := δ) (by norm_num)
      (fun z hz => by
        have hre : |z.re - c.re| ≤ 1 / 4 := by
          have := Complex.abs_re_le_norm (z - c)
          rw [Complex.sub_re] at this; linarith
        have him : |z.im - c.im| ≤ 1 / 4 := by
          have := Complex.abs_im_le_norm (z - c)
          rw [Complex.sub_im] at this; linarith
        apply hbh
        · rw [abs_le] at hre hc1 ⊢; constructor <;> linarith
        · rw [abs_le] at him hc2 ⊢; constructor <;> linarith)
    have : δ / (1 / 4) = 4 * δ := by ring
    rwa [this] at key
  have hd1 : Differentiable ℂ (deriv h) := by
    have := hhd.contDiff (n := 2)
    exact this.differentiable_deriv_two
  -- second Cauchy estimate at real window points
  have h2 : ∀ x : ℝ, x ∈ W → ‖deriv (deriv h) (x : ℂ)‖ ≤ 16 * δ := by
    intro x hx
    have hx' := Set.mem_Icc.1 hx
    have key := window38_cauchy_deriv_bound hd1 (c := (x : ℂ)) (r := 1 / 4) (δ := 4 * δ)
      (by norm_num)
      (fun z hz => by
        have hre : |z.re - x| ≤ 1 / 4 := by
          have := Complex.abs_re_le_norm (z - (x : ℂ))
          rw [Complex.sub_re, Complex.ofReal_re] at this; linarith
        have him : |z.im| ≤ 1 / 4 := by
          have := Complex.abs_im_le_norm (z - (x : ℂ))
          rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this; linarith
        apply h1
        · rw [abs_le] at hre ⊢; constructor <;> linarith [hx'.1, hx'.2]
        · rw [abs_le] at him ⊢; constructor <;> linarith)
    have : 4 * δ / (1 / 4) = 16 * δ := by ring
    rwa [this] at key
  -- pointwise estimate of g against cos(x - nπ)
  have hcn : |Real.cos ((n : ℝ) * Real.pi)| = 1 := Real.abs_cos_int_mul_pi n
  have hsn : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
  have hcc : ∀ x : ℝ, Real.cos ((n : ℝ) * Real.pi) * Real.cos x =
      Real.cos (x - (n : ℝ) * Real.pi) := by
    intro x
    rw [Real.cos_sub, hsn]; ring
  have hgap : ∀ x : ℝ, x ∈ W → |g x - Real.cos (x - (n : ℝ) * Real.pi)| ≤ δ := by
    intro x hx
    have hx' := Set.mem_Icc.1 hx
    have hb := hbh (x : ℂ) (by rw [Complex.ofReal_re, abs_le]; constructor <;> linarith)
      (by rw [Complex.ofReal_im, abs_zero]; norm_num)
    have hre : |(f x).re - Real.cos x| ≤ δ := by
      have e1 : ((f x).re - Real.cos x) = (h (x : ℂ)).re := by
        simp only [hhdef, Complex.sub_re, ← Complex.ofReal_cos, Complex.ofReal_re]
      rw [e1]
      exact (Complex.abs_re_le_norm _).trans hb
    have e2 : g x - Real.cos (x - (n : ℝ) * Real.pi) =
        Real.cos ((n : ℝ) * Real.pi) * ((f x).re - Real.cos x) := by
      simp only [g]; rw [← hcc x]; ring
    rw [e2, abs_mul, hcn, one_mul]; exact hre
  have hWt : ∀ x : ℝ, x ∈ W → |x - (n : ℝ) * Real.pi| ≤ 1 / 2 := by
    intro x hx
    have hx' := Set.mem_Icc.1 hx
    rw [abs_le]; constructor <;> linarith
  -- continuity
  have hcont : Continuous g := by
    have : Continuous (fun x : ℝ => f (x : ℂ)) := hf.continuous.comp Complex.continuous_ofReal
    exact continuous_const.mul (Complex.continuous_re.comp this)
  -- second derivative of g
  have hφ : ∀ y : ℝ, HasDerivAt (fun x : ℝ => (f (x : ℂ)).re) (deriv f (y : ℂ)).re y :=
    fun y => (hf (y : ℂ)).hasDerivAt.real_of_complex
  have hf1 : Differentiable ℂ (deriv f) := by
    have := hf.contDiff (n := 2)
    exact this.differentiable_deriv_two
  have hg1 : deriv g = fun y : ℝ => Real.cos ((n : ℝ) * Real.pi) * (deriv f (y : ℂ)).re := by
    funext y
    exact ((hφ y).const_mul (Real.cos ((n : ℝ) * Real.pi))).deriv
  have hψ : ∀ y : ℝ, HasDerivAt (fun x : ℝ => (deriv f (x : ℂ)).re)
      (deriv (deriv f) (y : ℂ)).re y :=
    fun y => (hf1 (y : ℂ)).hasDerivAt.real_of_complex
  have hg2 : ∀ y : ℝ, deriv^[2] g y =
      Real.cos ((n : ℝ) * Real.pi) * (deriv (deriv f) (y : ℂ)).re := by
    intro y
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [hg1]
    exact ((hψ y).const_mul (Real.cos ((n : ℝ) * Real.pi))).deriv
  -- f'' = h'' - cos
  have hfeq : f = fun z => h z + Complex.cos z := by
    funext z; simp [hhdef]
  have hf1eq : deriv f = fun z => deriv h z - Complex.sin z := by
    funext z
    have hh2 : HasDerivAt (fun z => h z + Complex.cos z) (deriv h z + -Complex.sin z) z :=
      (hhd z).hasDerivAt.add (Complex.hasDerivAt_cos z)
    rw [← hfeq] at hh2
    rw [hh2.deriv]; ring
  have hf2 : ∀ z : ℂ, deriv (deriv f) z = deriv (deriv h) z - Complex.cos z := by
    intro z
    rw [hf1eq]
    have := ((hd1 z).hasDerivAt.sub (Complex.hasDerivAt_sin z)).deriv
    exact this
  have hneg : ∀ x : ℝ, x ∈ W → deriv^[2] g x < 0 := by
    intro x hx
    rw [hg2, hf2, Complex.sub_re, ← Complex.ofReal_cos, Complex.ofReal_re]
    have hhre : |(deriv (deriv h) (x : ℂ)).re| ≤ 16 * δ :=
      (Complex.abs_re_le_norm _).trans (h2 x hx)
    have hcge := window38_cos_ge _ (hWt x hx)
    have := hcc x
    have hm : Real.cos ((n : ℝ) * Real.pi) * (deriv (deriv h) (x : ℂ)).re ≤ 16 * δ := by
      calc _ ≤ |Real.cos ((n : ℝ) * Real.pi) * (deriv (deriv h) (x : ℂ)).re| := le_abs_self _
        _ = |(deriv (deriv h) (x : ℂ)).re| := by rw [abs_mul, hcn, one_mul]
        _ ≤ 16 * δ := hhre
    rw [mul_sub]
    linarith
  have hgl : ∀ x : ℝ, x ∈ W → g x ≤ Real.cos (x - (n : ℝ) * Real.pi) + δ := by
    intro x hx; have := (abs_le.1 (hgap x hx)).2; linarith
  have hgg : ∀ x : ℝ, x ∈ W → Real.cos (x - (n : ℝ) * Real.pi) - δ ≤ g x := by
    intro x hx; have := (abs_le.1 (hgap x hx)).1; linarith
  have hnorm : ∀ x : ℝ, x ∈ W → ‖f x‖ = |g x| := by
    intro x _
    have : |(f x).re| = ‖f x‖ := Complex.abs_re_eq_norm.2 (hreal x)
    simp only [g]; rw [abs_mul, hcn, one_mul, this]
  have hlow : ∀ x : ℝ, x ∈ W → -1 < g x := by
    intro x hx
    have := hgg x hx
    have := window38_cos_ge _ (hWt x hx)
    linarith
  have hmem1 : (n : ℝ) * Real.pi - 1 / 2 ∈ W := by
    constructor <;> linarith
  have hmem2 : (n : ℝ) * Real.pi + 1 / 2 ∈ W := by
    constructor <;> linarith
  refine ⟨strictConcaveOn_of_deriv2_neg' (convex_Icc _ _) hcont.continuousOn hneg, hcont, ?_, ?_,
    hlow, hnorm, ?_⟩
  · have := hgl _ hmem1
    have h3 := window38_cos_le ((n : ℝ) * Real.pi - 1 / 2 - (n : ℝ) * Real.pi)
      (by norm_num [abs_of_neg])
    have e : (n : ℝ) * Real.pi - 1 / 2 - (n : ℝ) * Real.pi = -(1 / 2) := by ring
    rw [e] at h3 this
    nlinarith
  · have := hgl _ hmem2
    have h3 := window38_cos_le ((n : ℝ) * Real.pi + 1 / 2 - (n : ℝ) * Real.pi)
      (by norm_num [abs_of_pos])
    have e : (n : ℝ) * Real.pi + 1 / 2 - (n : ℝ) * Real.pi = 1 / 2 := by ring
    rw [e] at h3 this
    nlinarith
  · intro x hx hx1
    rw [hnorm x hx] at hx1
    have hgx : 1 ≤ g x := by
      rcases le_or_gt 0 (g x) with h0 | h0
      · rwa [abs_of_nonneg h0] at hx1
      · exfalso
        have := hlow x hx
        rw [abs_of_neg h0] at hx1
        linarith
    have h3 := window38_cos_le _ (hWt x hx)
    have h4 := hgl x hx
    have hsq : (x - (n : ℝ) * Real.pi) ^ 2 ≤ (2 * Real.sqrt δ) ^ 2 := by
      have : (2 * Real.sqrt δ) ^ 2 = 4 * δ := by
        rw [mul_pow, Real.sq_sqrt hδ0]; norm_num
      rw [this]; linarith
    exact abs_le_of_sq_le_sq hsq (by positivity)

end NlsGge.SpectralFoundations
