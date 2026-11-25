import NlsGge.GK38.Lib.EntireProductsC34g

/-!
# L4c part 2b, module h: Lemma C.4 and the circle corollaries

* `omitProd_asymp` (book Lemma C.4): `f_n(λ, σ̃) = sin λ/(λ - nπ) + ℓ²_n` on `D_n`, uniformly on
  `‖σ̃‖ ≤ K`.  Proof as in the book: `f_n(λ, σ̃) = f_n(λ, 0) · ∏_{m≠n} (σ_m - λ)/(mπ - λ)` and Lemma C.3
  with `ρ = σ°`, `N = 0`, `c = 4/(3π)`; the factor `‖sincAt n λ‖ ≤ e^{π/4}` on `D_n`.
* `omitProd_circle_bound` (the plan's statement): `‖f_n(z, σ̃)‖ ≤ C ‖sin z‖` on `‖z‖ = Nπ + π/2`,
  `C` uniform in `n`, `N`, `‖σ̃‖ ≤ K`.
* `omitProd_hdecay`: for fixed `n`, `σ̃` the entire function `f_n(·, σ̃)` satisfies the hypothesis `hdecay`
  of `interpolation_lemma` (`φ/sin → 0` on the circles), the form the L4b review (L4B-1) requires.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### `‖sin w‖ ≤ ‖w‖ e^{‖w‖}` and the bound on `sincAt` -/

theorem norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have h1 := norm_cexp_sub_one_le (-w * Complex.I)
  have h2 := norm_cexp_sub_one_le (w * Complex.I)
  have e : Complex.sin w = ((Complex.exp (-w * Complex.I) - 1) - (Complex.exp (w * Complex.I) - 1))
      * Complex.I / 2 := by
    rw [Complex.sin]; ring
  rw [e, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h3 : ‖(Complex.exp (-w * Complex.I) - 1) - (Complex.exp (w * Complex.I) - 1)‖
      ≤ ‖w‖ * Real.exp ‖w‖ + ‖w‖ * Real.exp ‖w‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simpa [norm_neg, norm_mul, Complex.norm_I] using h1
    · simpa [norm_mul, Complex.norm_I] using h2
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  linarith

theorem norm_cos_int_mul_pi_le (n : ℤ) : ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖ ≤ 1 := by
  have : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]; push_cast; rfl
  rw [this, Complex.norm_real]
  exact Real.abs_cos_le_one _

theorem norm_sincAt_le (n : ℤ) {lam : ℂ} (hlam : lam ∈ Dn n) :
    ‖sincAt n lam‖ ≤ Real.exp (Real.pi / 4) := by
  have hpi := Real.pi_pos
  have hD : ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
    simpa [Dn, Metric.mem_ball, dist_eq_norm] using hlam
  have he1 : (1 : ℝ) ≤ Real.exp (Real.pi / 4) := Real.one_le_exp (by positivity)
  unfold sincAt
  by_cases h : lam = (n : ℂ) * (Real.pi : ℂ)
  · simp only [h, ite_true]
    rw [Complex.norm_real]
    exact (Real.abs_cos_le_one _).trans he1
  · simp only [h, ite_false]
    set w : ℂ := lam - (n : ℂ) * (Real.pi : ℂ) with hw
    have hw0 : w ≠ 0 := sub_ne_zero.mpr h
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hs : Complex.sin lam = Complex.sin w * Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
      have : lam = w + (n : ℂ) * (Real.pi : ℂ) := by rw [hw]; ring
      rw [this, Complex.sin_add]
      have h0 : Complex.sin ((n : ℂ) * (Real.pi : ℂ)) = 0 := by
        have := Complex.sin_int_mul_pi n
        simpa using this
      rw [h0, mul_zero, add_zero]
    rw [norm_div, hs, norm_mul]
    have hc := norm_cos_int_mul_pi_le n
    have hsw := norm_sin_le_exp w
    rw [div_le_iff₀ hwpos]
    calc ‖Complex.sin w‖ * ‖Complex.cos ((n : ℂ) * (Real.pi : ℂ))‖
        ≤ ‖Complex.sin w‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ ≤ ‖w‖ * Real.exp ‖w‖ := by rw [mul_one]; exact hsw
      _ ≤ Real.exp (Real.pi / 4) * ‖w‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hD.le) hwpos.le

/-! ### Lemma C.4 -/

theorem sep_sigmaZero {n : ℤ} {lam : ℂ} (hlam : lam ∈ Dn n) (m : ℤ) (hm : m ≠ n) :
    (3 * Real.pi / 4) * |(m : ℝ) - n| ≤ ‖sigmaZero m - lam‖ := by
  have hpi := Real.pi_pos
  have hD : ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
    simpa [Dn, Metric.mem_ball, dist_eq_norm] using hlam
  have hj : 1 ≤ |(m : ℝ) - n| := by
    have h1 : (1 : ℤ) ≤ |m - n| := Int.one_le_abs (sub_ne_zero.mpr hm)
    have : (1 : ℝ) ≤ ((|m - n| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [Int.cast_abs] using this
  have hn : ‖((m : ℂ) - n) * (Real.pi : ℂ)‖ = Real.pi * |(m : ℝ) - n| := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    have : ‖(m : ℂ) - n‖ = |(m : ℝ) - n| := norm_int_sub_cast m n
    rw [this]; ring
  have e : ((m : ℂ) - n) * (Real.pi : ℂ) = (sigmaZero m - lam) + (lam - (n : ℂ) * (Real.pi : ℂ)) := by
    simp only [sigmaZero]; ring
  have h2 : Real.pi * |(m : ℝ) - n| ≤ ‖sigmaZero m - lam‖ + Real.pi / 4 := by
    calc Real.pi * |(m : ℝ) - n| = ‖((m : ℂ) - n) * (Real.pi : ℂ)‖ := hn.symm
      _ = ‖(sigmaZero m - lam) + (lam - (n : ℂ) * (Real.pi : ℂ))‖ := by rw [e]
      _ ≤ ‖sigmaZero m - lam‖ + ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖sigmaZero m - lam‖ + Real.pi / 4 := by linarith
  nlinarith

theorem omitProd_asymp (K : ℝ) :
    ∃ C : ℝ, ∀ s : L2Seq, ‖s‖ ≤ K → ∃ b : ℤ → ℝ,
      (∀ n : ℤ, ∀ lam ∈ Dn n, ‖omitProd n s lam - sincAt n lam‖ ≤ b n) ∧
      Summable (fun n => b n ^ 2) ∧ ∑' n, b n ^ 2 ≤ C := by
  have hpi := Real.pi_pos
  set c : ℝ := (3 * Real.pi / 4)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcinv : c⁻¹ = 3 * Real.pi / 4 := by rw [hc, inv_inv]
  obtain ⟨C0, hC0⟩ := ratioProd_l2 0 (max K 0 ^ 2) c hcpos
  refine ⟨Real.exp (Real.pi / 4) ^ 2 * C0, fun s hs => ?_⟩
  have hinj : Function.Injective sigmaZero := by
    intro a b h
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    have : (a : ℂ) = b := mul_right_cancel₀ hpiC h
    exact_mod_cast this
  have hK : ∑' n, ‖sigmaOf s n - sigmaZero n‖ ^ 2 ≤ max K 0 ^ 2 := by
    have e : ∀ n, sigmaOf s n - sigmaZero n = s n := fun n => by simp [sigmaOf, sigmaZero]
    simp_rw [e]
    rw [tsum_sq_l2]
    exact pow_le_pow_left₀ (norm_nonneg _) (hs.trans (le_max_left _ _)) 2
  have hsep : ∀ n : ℤ, ((0 : ℕ) : ℝ) ≤ |(n : ℝ)| → ∀ m, m ≠ n → ∀ lam ∈ Dn n,
      c⁻¹ * |(m : ℝ) - n| ≤ ‖sigmaZero m - lam‖ := by
    intro n _ m hm lam hlam
    rw [hcinv]; exact sep_sigmaZero hlam m hm
  obtain ⟨b', hb', hsum', hbound'⟩ := hC0 (sigmaOf s) sigmaZero 0 (summable_dev_sigmaOf s)
    summable_dev_sigmaZero hinj (fun n => by rw [dev_sigmaZero, norm_zero]) hK hsep
  set E : ℝ := Real.exp (Real.pi / 4) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨fun n => E * b' n, ?_, ?_, ?_⟩
  · intro n lam hlam
    obtain ⟨hmul, hb⟩ := hb' n (by simp) lam hlam
    have hne : ∀ m, m ≠ n → (m : ℂ) * (Real.pi : ℂ) ≠ lam := by
      intro m hm h
      have := hsep n (by simp) m hm lam hlam
      change c⁻¹ * |(m : ℝ) - n| ≤ ‖(m : ℂ) * (Real.pi : ℂ) - lam‖ at this
      rw [h, sub_self, norm_zero] at this
      have hpos : 0 < |(m : ℝ) - n| := by
        rw [abs_pos, sub_ne_zero]; exact_mod_cast hm
      have : 0 < c⁻¹ * |(m : ℝ) - n| := by positivity
      linarith
    rw [omitProd_eq_ratio n s hne hmul, omitProd_zero_eq_sincAt]
    have : sincAt n lam * ratioProd (sigmaOf s) sigmaZero n lam - sincAt n lam
        = sincAt n lam * (ratioProd (sigmaOf s) sigmaZero n lam - 1) := by ring
    rw [this, norm_mul]
    exact mul_le_mul (norm_sincAt_le n hlam) hb (norm_nonneg _) hE0
  · simpa [mul_pow] using hsum'.mul_left (E ^ 2)
  · calc ∑' n, (E * b' n) ^ 2 = E ^ 2 * ∑' n, b' n ^ 2 := by
          rw [← tsum_mul_left]; exact tsum_congr fun n => by ring
      _ ≤ E ^ 2 * C0 := mul_le_mul_of_nonneg_left hbound' (sq_nonneg _)

/-! ### The circle corollaries -/

/-- The plan's `omitProd_circle_bound`: `O(1)` growth of `f_n/sin` on the circles, uniform in `n`. -/
theorem omitProd_circle_bound (K : ℝ) :
    ∃ C : ℝ, ∀ s : L2Seq, ‖s‖ ≤ K → ∀ (n : ℤ) (N : ℕ) (z : ℂ),
      ‖z‖ = N * Real.pi + Real.pi / 2 → ‖omitProd n s z‖ ≤ C * ‖Complex.sin z‖ := by
  obtain ⟨C, hC0, hC⟩ := omitProd_circle_bound_dist K
  refine ⟨2 / Real.pi * C, fun s hs n N z hz => ?_⟩
  have h1 := hC s hs n N z hz
  have hd : Real.pi / 2 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
    have := pi_mul_dd_le hz n
    have h2 := half_le_circDist N n
    rw [norm_sub_rev] at this
    nlinarith [Real.pi_pos]
  have hpos : 0 < Real.pi / 2 := by positivity
  have h3 : ‖omitProd n s z‖ * (Real.pi / 2) ≤ C * ‖Complex.sin z‖ :=
    (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans h1
  have : ‖omitProd n s z‖ ≤ C * ‖Complex.sin z‖ / (Real.pi / 2) := by
    rw [le_div_iff₀ hpos]; exact h3
  calc ‖omitProd n s z‖ ≤ C * ‖Complex.sin z‖ / (Real.pi / 2) := this
    _ = 2 / Real.pi * C * ‖Complex.sin z‖ := by field_simp

/-- For fixed `n` and `σ̃`, `f_n(·, σ̃)` satisfies the `o(1)` growth hypothesis `hdecay` of
`interpolation_lemma` (book Lemma F.4, in the corrected form): `f_n/sin → 0` on the circles. -/
theorem omitProd_hdecay (n : ℤ) (s : L2Seq) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ z : ℂ, ‖z‖ = m * Real.pi + Real.pi / 2 →
      ‖omitProd n s z‖ ≤ ε * ‖Complex.sin z‖ := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := omitProd_circle_bound_dist ‖s‖
  have hpi := Real.pi_pos
  refine ⟨⌈C / ε / Real.pi⌉₊ + n.natAbs, fun m hm z hz => ?_⟩
  have h1 := hC s le_rfl n m z hz
  have hd : (m : ℝ) * Real.pi - |(n : ℝ)| * Real.pi ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
    have h2 := norm_sub_norm_le z ((n : ℂ) * (Real.pi : ℂ))
    have h3 : ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]; simp
    rw [h3, hz] at h2
    linarith
  have hm' : (⌈C / ε / Real.pi⌉₊ : ℝ) + (n.natAbs : ℝ) ≤ m := by exact_mod_cast hm
  have hn : |(n : ℝ)| = (n.natAbs : ℝ) := by simp
  have hceil := Nat.le_ceil (C / ε / Real.pi)
  have hbig : C / ε ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
    have : C / ε / Real.pi * Real.pi ≤ (m : ℝ) * Real.pi - |(n : ℝ)| * Real.pi := by
      rw [hn, ← sub_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hpi.le
    rw [div_mul_cancel₀ _ hpi.ne'] at this
    linarith
  have hpos : 0 < C / ε := by positivity
  have h4 : ‖omitProd n s z‖ * (C / ε) ≤ C * ‖Complex.sin z‖ :=
    (mul_le_mul_of_nonneg_left hbig (norm_nonneg _)).trans h1
  have h5 : ‖omitProd n s z‖ ≤ C * ‖Complex.sin z‖ / (C / ε) := by
    rw [le_div_iff₀ hpos]; exact h4
  calc ‖omitProd n s z‖ ≤ C * ‖Complex.sin z‖ / (C / ε) := h5
    _ = ε * ‖Complex.sin z‖ := by field_simp

end

end NlsGge.GK38.Lib

/-- The plan's name for the fixed-index circle decay theorem. -/
theorem NlsGge.GK38.Lib.omitProd_circle_decay (n : ℤ) (s : NlsGge.GK38.Lib.L2Seq) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ z : ℂ, ‖z‖ = m * Real.pi + Real.pi / 2 →
      ‖NlsGge.GK38.Lib.omitProd n s z‖ ≤ ε * ‖Complex.sin z‖ :=
  NlsGge.GK38.Lib.omitProd_hdecay n s
