import Mathlib

/-!
# L4b, part 1: the finite Hilbert form (book Lemma F.5, Fourier proof)

Source: Grébert–Kappeler book, Appendix F, Lemma F.5 (GKP Lemma 22.5).  The book proves
`‖H‖ ≤ π` for the discrete Hilbert transform `(Hx)_n = Σ_{m≠n} x_m/(m-n)` by writing
`(Hx, y) = ⟨h x̌, y̌⟩` with `h(t) = 2πi (t - 1/2)` on `[0,1]` and `|h| ≤ π`.  Mathlib has no Hilbert
inequality, so it is proved here, first for finite windows (trigonometric polynomials; no
convergence questions):

* `integral_hilbH_char`: `∫₀¹ h(t) e^{2πikt} dt = 1/k` (`k ≠ 0`), `= 0` (`k = 0`);
* `hilbertForm_eq_integral`: the finite bilinear form is `∫₀¹ h x̌ ȳ`;
* `hilbertForm_bound`: `|Σ_{n∈T} Σ_{m∈S, m≠n} x_m ȳ_n/(m-n)| ≤ π (Σ_S|x|²)^{1/2} (Σ_T|y|²)^{1/2}`.

The extension to all of `ℓ²(ℤ)` is in `InterpolationHilbertOp`.
-/

set_option autoImplicit false

open MeasureTheory intervalIntegral Complex

namespace NlsGge.GK38.Lib

noncomputable section

/-- The character `t ↦ e^{2πikt}`. -/
def hilbChar (k : ℤ) (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * t)

/-- The kernel `h(t) = 2πi (t - 1/2)` of book Lemma F.5. -/
def hilbH (t : ℝ) : ℂ := 2 * Real.pi * Complex.I * ((t : ℂ) - 1 / 2)

theorem continuous_hilbChar (k : ℤ) : Continuous (hilbChar k) := by
  unfold hilbChar; fun_prop

theorem continuous_hilbH : Continuous hilbH := by
  unfold hilbH; fun_prop

theorem hilbChar_zero (t : ℝ) : hilbChar 0 t = 1 := by simp [hilbChar]

/-- `e_m(t) conj(e_n(t)) = e_{m-n}(t)`. -/
theorem hilbChar_mul_conj (m n : ℤ) (t : ℝ) :
    hilbChar m t * (starRingEnd ℂ) (hilbChar n t) = hilbChar (m - n) t := by
  unfold hilbChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  push_cast
  ring

theorem norm_hilbChar (k : ℤ) (t : ℝ) : ‖hilbChar k t‖ = 1 := by
  unfold hilbChar
  rw [Complex.norm_exp]
  simp

theorem hilbChar_one (k : ℤ) : hilbChar k 1 = 1 := by
  unfold hilbChar
  have := Complex.exp_int_mul_two_pi_mul_I k
  rw [← this]
  congr 1
  push_cast
  ring

theorem integral_hilbChar (k : ℤ) :
    ∫ t in (0 : ℝ)..1, hilbChar k t = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk; simp [hilbChar_zero]
  · simp only [hk, ite_false]
    have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    have e : (fun t : ℝ => hilbChar k t) = fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * k * t) := rfl
    rw [e, this]
    have h1 := hilbChar_one k
    unfold hilbChar at h1
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1 ⊢
    rw [h1]; simp

theorem integral_hilbH_char (k : ℤ) :
    ∫ t in (0 : ℝ)..1, hilbH t * hilbChar k t = if k = 0 then 0 else 1 / (k : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hk : k = 0
  · subst hk
    simp only [hilbChar_zero, mul_one, ite_true]
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Real.pi * Complex.I * ((s : ℂ) ^ 2 - s)) (hilbH t) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have h2 := ((h1.pow 2).sub h1).const_mul (Real.pi * Complex.I)
      convert h2 using 1
      unfold hilbH; push_cast; ring
    rw [integral_eq_sub_of_hasDerivAt hd (by
      exact (continuous_hilbH.intervalIntegrable _ _))]
    simp
  · simp only [hk, ite_false]
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    set c : ℂ := 2 * Real.pi * Complex.I * k with hc
    have hc0 : c ≠ 0 := by simp [hc, hpi, hk', Complex.I_ne_zero]
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => 2 * Real.pi * Complex.I * (Complex.exp (c * s) *
          (((s : ℂ) - 1 / 2) / c - 1 / c ^ 2))) (hilbH t * hilbChar k t) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ))) (Complex.exp (c * t) * (c * 1)) t :=
        (h1.const_mul c).cexp
      have h3 : HasDerivAt (fun s : ℝ => ((s : ℂ) - 1 / 2) / c - 1 / c ^ 2) (1 / c) t := by
        have := ((h1.sub_const (1 / 2 : ℂ)).div_const c).sub_const (1 / c ^ 2)
        simpa using this
      have h4 := (h2.mul h3).const_mul (2 * Real.pi * Complex.I)
      convert h4 using 1
      unfold hilbH hilbChar
      rw [← hc]
      field_simp
      ring
    rw [integral_eq_sub_of_hasDerivAt hd (by
      exact ((continuous_hilbH.mul (continuous_hilbChar k)).intervalIntegrable _ _))]
    have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      have := hilbChar_one k
      unfold hilbChar at this
      simpa [hc] using this
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero] at h1 ⊢
    rw [h1]
    rw [hc]
    field_simp
    ring

/-! ### Finite trigonometric sums -/

/-- The trigonometric polynomial `x̌(t) = Σ_{m∈S} x_m e^{2πimt}`. -/
def hilbCheck (S : Finset ℤ) (x : ℤ → ℂ) (t : ℝ) : ℂ := ∑ m ∈ S, x m * hilbChar m t

theorem continuous_hilbCheck (S : Finset ℤ) (x : ℤ → ℂ) : Continuous (hilbCheck S x) := by
  unfold hilbCheck
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_hilbChar m)

/-- Expansion of `∫ w x̌ ȳ` against the characters. -/
theorem integral_weight_check (w : ℝ → ℂ) (hw : Continuous w) (S T : Finset ℤ) (x y : ℤ → ℂ) :
    ∫ t in (0 : ℝ)..1, w t * (hilbCheck S x t * (starRingEnd ℂ) (hilbCheck T y t))
      = ∑ n ∈ T, ∑ m ∈ S, x m * (starRingEnd ℂ) (y n) * ∫ t in (0 : ℝ)..1, w t * hilbChar (m - n) t := by
  have e : ∀ t : ℝ, w t * (hilbCheck S x t * (starRingEnd ℂ) (hilbCheck T y t))
      = ∑ n ∈ T, ∑ m ∈ S, x m * (starRingEnd ℂ) (y n) * (w t * hilbChar (m - n) t) := by
    intro t
    unfold hilbCheck
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← hilbChar_mul_conj m n t]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro m _
      exact (continuous_const.mul (hw.mul (continuous_hilbChar _))).intervalIntegrable _ _
  · intro n _
    have := IntervalIntegrable.sum S (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := fun m t => x m * (starRingEnd ℂ) (y n) * (w t * hilbChar (m - n) t)) fun m _ =>
      (continuous_const.mul (hw.mul (continuous_hilbChar _))).intervalIntegrable _ _
    simpa [Finset.sum_fn] using this

/-- The finite Hilbert form `Σ_{n∈T} Σ_{m∈S, m≠n} x_m ȳ_n/(m-n)`. -/
def hilbertForm (S T : Finset ℤ) (x y : ℤ → ℂ) : ℂ :=
  ∑ n ∈ T, ∑ m ∈ S, if m = n then 0 else x m * (starRingEnd ℂ) (y n) / ((m : ℂ) - n)

theorem hilbertForm_eq_integral (S T : Finset ℤ) (x y : ℤ → ℂ) :
    hilbertForm S T x y
      = ∫ t in (0 : ℝ)..1, hilbH t * (hilbCheck S x t * (starRingEnd ℂ) (hilbCheck T y t)) := by
  rw [integral_weight_check _ continuous_hilbH]
  unfold hilbertForm
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [integral_hilbH_char]
  by_cases h : m = n
  · simp [h]
  · have h' : m - n ≠ 0 := sub_ne_zero.mpr h
    simp only [h, h', ite_false]
    push_cast
    ring

/-- Parseval for trigonometric polynomials. -/
theorem integral_check_sq (S : Finset ℤ) (x : ℤ → ℂ) :
    ∫ t in (0 : ℝ)..1, ‖hilbCheck S x t‖ ^ 2 = ∑ m ∈ S, ‖x m‖ ^ 2 := by
  have h1 : ((∫ t in (0 : ℝ)..1, ‖hilbCheck S x t‖ ^ 2 : ℝ) : ℂ)
      = ∫ t in (0 : ℝ)..1, (1 : ℂ) * (hilbCheck S x t * (starRingEnd ℂ) (hilbCheck S x t)) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [one_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [integral_weight_check (fun _ => 1) continuous_const] at h1
  have h2 : ((∑ m ∈ S, ‖x m‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ S, ∑ m ∈ S, x m * (starRingEnd ℂ) (x n) *
      ∫ t in (0 : ℝ)..1, (1 : ℂ) * hilbChar (m - n) t := by
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    simp_rw [one_mul, integral_hilbChar, sub_eq_zero]
    rw [Finset.sum_eq_single n]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro m _ hm; simp [hm]
    · intro h; exact absurd hn h
  exact_mod_cast h1.trans h2.symm

theorem norm_hilbH_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖hilbH t‖ ≤ Real.pi := by
  unfold hilbH
  have h1 : ‖(2 * Real.pi * Complex.I * ((t : ℂ) - 1 / 2))‖ = 2 * Real.pi * |t - 1 / 2| := by
    rw [norm_mul, norm_mul]
    have : ((t : ℂ) - 1 / 2) = ((t - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real]
    simp [abs_of_pos Real.pi_pos]
  rw [h1]
  have : |t - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  nlinarith [Real.pi_pos]

/-- **Finite Hilbert inequality** (book Lemma F.5, Fourier proof).  For finite windows `S`, `T` and
arbitrary sequences `x`, `y`:
`|Σ_{n∈T} Σ_{m∈S, m≠n} x_m ȳ_n/(m-n)| ≤ π (Σ_S|x|²)^{1/2} (Σ_T|y|²)^{1/2}`. -/
theorem hilbertForm_bound (S T : Finset ℤ) (x y : ℤ → ℂ) :
    ‖hilbertForm S T x y‖ ≤ Real.pi * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) := by
  set A : ℝ := ∑ m ∈ S, ‖x m‖ ^ 2 with hA
  set B : ℝ := ∑ n ∈ T, ‖y n‖ ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => by positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hpi := Real.pi_pos
  -- the AM-GM form with a free parameter `s > 0`
  have key : ∀ s : ℝ, 0 < s → ‖hilbertForm S T x y‖ ≤ Real.pi / 2 * (s * A + B / s) := by
    intro s hs
    rw [hilbertForm_eq_integral]
    set f := hilbCheck S x with hf
    set g := hilbCheck T y with hg
    have hfc : Continuous f := continuous_hilbCheck S x
    have hgc : Continuous g := continuous_hilbCheck T y
    have hint : IntervalIntegrable (fun t : ℝ => ‖f t‖ ^ 2) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => ‖f t‖ ^ 2).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t : ℝ => ‖g t‖ ^ 2) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => ‖g t‖ ^ 2).intervalIntegrable _ _
    calc ‖∫ t in (0 : ℝ)..1, hilbH t * (f t * (starRingEnd ℂ) (g t))‖
        ≤ ∫ t in (0 : ℝ)..1, ‖hilbH t * (f t * (starRingEnd ℂ) (g t))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0 : ℝ)..1, Real.pi / 2 * (s * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / s) := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
          · exact (by have := continuous_hilbH; have := hfc; have := hgc; fun_prop :
              Continuous fun t : ℝ => ‖hilbH t * (f t * (starRingEnd ℂ) (g t))‖).intervalIntegrable _ _
          · exact ((hint.const_mul s).add (hint2.div_const s)).const_mul _
          · intro t ht
            rw [norm_mul, norm_mul, Complex.norm_conj]
            have h1 := norm_hilbH_le t ht
            have h2 : ‖f t‖ * ‖g t‖ ≤ (s * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / s) / 2 := by
              have : 0 ≤ (Real.sqrt s * ‖f t‖ - ‖g t‖ / Real.sqrt s) ^ 2 := sq_nonneg _
              have hs' : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
              have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
              have e : (Real.sqrt s * ‖f t‖ - ‖g t‖ / Real.sqrt s) ^ 2
                  = s * ‖f t‖ ^ 2 - 2 * (‖f t‖ * ‖g t‖) + ‖g t‖ ^ 2 / s := by
                rw [sub_sq, mul_pow, div_pow, hs']
                field_simp
              linarith
            calc ‖hilbH t‖ * (‖f t‖ * ‖g t‖) ≤ Real.pi * (‖f t‖ * ‖g t‖) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ ≤ Real.pi * ((s * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / s) / 2) :=
                  mul_le_mul_of_nonneg_left h2 hpi.le
              _ = Real.pi / 2 * (s * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / s) := by ring
      _ = Real.pi / 2 * (s * A + B / s) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hint.const_mul s)
            (hint2.div_const s), intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
            hf, hg, integral_check_sq, integral_check_sq]
  by_cases hA' : A = 0
  · have hx : ∀ m ∈ S, x m = 0 := by
      intro m hm
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hA' m hm
      simpa using this
    have : hilbertForm S T x y = 0 := by
      unfold hilbertForm
      refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun m hm => ?_
      simp [hx m hm]
    rw [this]; simp; positivity
  by_cases hB' : B = 0
  · have hy : ∀ n ∈ T, y n = 0 := by
      intro n hn
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hB' n hn
      simpa using this
    have : hilbertForm S T x y = 0 := by
      unfold hilbertForm
      refine Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun m _ => ?_
      simp [hy n hn]
    rw [this]; simp; positivity
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA')
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB')
  have := key (Real.sqrt B / Real.sqrt A) (div_pos (Real.sqrt_pos.mpr hBpos) (Real.sqrt_pos.mpr hApos))
  refine this.trans (le_of_eq ?_)
  have hsA := Real.sqrt_pos.mpr hApos
  have hsB := Real.sqrt_pos.mpr hBpos
  have eA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have eB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  generalize Real.sqrt A = a at *
  generalize Real.sqrt B = b at *
  rw [← eA, ← eB]
  field_simp
  ring

end

end NlsGge.GK38.Lib
