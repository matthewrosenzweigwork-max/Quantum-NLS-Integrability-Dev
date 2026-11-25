import NlsGge.Weights.Regularity
import NlsGge.Spectral.ActualGapLocalizationAllUE02_38

/-! H01 (v2 `B:lem:uniformsymbol`): hierarchy-uniform logarithmic symbol bound.

Conventions. `weightTerm c r j = c_j/(j!)^4 * r^(2j)`, `partialWeight c m = W_m` (m inclusive,
m = 0 allowed), `weight c = W`, and `a_{m,n} = W_m(2 π n)`. Gap labels are the Lean labels of
E02/E03 (`actualGapLowerAllE02_38`, `actualGapUpperAllE02_38`); since `W_m`, `W` and `⟨n⟩` are even
the Schur/Lean label reflection `g_n ↦ -g_{-n}` does not affect the statement. The gap `g_n` is
taken as the closed interval between its lower and upper endpoints (a stronger statement than
for the open gap). The constants depend only on `(lower, upper, B)`. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Mean value estimate for the logarithm of a positive function with a log-derivative bound. -/
lemma log_increment_le38 (F : ℝ → ℝ) (C : ℝ)
    (hpos : ∀ r, 0 < F r) (hdiff : ∀ r, DifferentiableAt ℝ F r)
    (hnn : ∀ r, 0 < r → 0 ≤ deriv F r / F r)
    (hle : ∀ r, 0 < r → deriv F r / F r ≤ C * r ^ (-1 / 2 : ℝ))
    (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    |Real.log (F q) - Real.log (F p)| ≤ C * p ^ (-1 / 2 : ℝ) * (q - p) := by
  rcases hpq.eq_or_lt with h | h
  · subst h; simp
  have hderiv : ∀ x, HasDerivAt (fun y => Real.log (F y)) (deriv F x / F x) x := fun x =>
    ((hdiff x).hasDerivAt).log (hpos x).ne'
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun y => Real.log (F y))
    (fun x => deriv F x / F x) h
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt) (fun x _ => hderiv x)
  have hcp : p < c := hc.1
  have hc0 : 0 < c := hp.trans hcp
  have hqp : 0 < q - p := sub_pos.2 h
  have hslope : Real.log (F q) - Real.log (F p) = deriv F c / F c * (q - p) := by
    field_simp at hceq ⊢
    linarith
  have h1 : c ^ (-1 / 2 : ℝ) ≤ p ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hp hcp.le (by norm_num)
  have hC : 0 ≤ C := by
    have := (hnn c hc0).trans (hle c hc0)
    have hpos' : 0 < c ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hc0 _
    by_contra hneg
    push Not at hneg
    nlinarith
  rw [hslope, abs_of_nonneg (mul_nonneg (hnn c hc0) hqp.le)]
  calc deriv F c / F c * (q - p) ≤ (C * c ^ (-1 / 2 : ℝ)) * (q - p) :=
        mul_le_mul_of_nonneg_right (hle c hc0) hqp.le
    _ ≤ (C * p ^ (-1 / 2 : ℝ)) * (q - p) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) hqp.le

lemma log_increment_min38 (F : ℝ → ℝ) (C : ℝ)
    (hpos : ∀ r, 0 < F r) (hdiff : ∀ r, DifferentiableAt ℝ F r)
    (hnn : ∀ r, 0 < r → 0 ≤ deriv F r / F r)
    (hle : ∀ r, 0 < r → deriv F r / F r ≤ C * r ^ (-1 / 2 : ℝ))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    |Real.log (F q) - Real.log (F p)| ≤ C * (min p q) ^ (-1 / 2 : ℝ) * |q - p| := by
  rcases le_total p q with h | h
  · have := log_increment_le38 F C hpos hdiff hnn hle p q hp h
    have e : |q - p| = q - p := abs_of_nonneg (sub_nonneg.2 h)
    rw [min_eq_left h, e]; exact this
  · have := log_increment_le38 F C hpos hdiff hnn hle q p hq h
    have e : |q - p| = p - q := by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 h)
    rw [min_eq_right h, e]
    rwa [abs_sub_comm] at this

lemma abs_exp_sub_one_le38 (s : ℝ) : |Real.exp s - 1| ≤ |s| * Real.exp |s| := by
  have h1 := Real.add_one_le_exp s
  have h2 := Real.add_one_le_exp (-s)
  have h3 : 0 < Real.exp s := Real.exp_pos s
  have h4 : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs, abs_of_nonneg (by linarith)]
    have : Real.exp s - 1 ≤ s * Real.exp s := by nlinarith
    exact this
  · rw [abs_of_nonpos hs]
    have h5 : 1 ≤ Real.exp (-s) := by
      have := Real.one_le_exp (neg_nonneg.2 hs); exact this
    have h6 : Real.exp s ≤ 1 := Real.exp_le_one_iff.2 hs
    rw [abs_of_nonpos (by linarith)]
    nlinarith

lemma bracket_pos38 (n : ℤ) : 1 ≤ japaneseBracket n := by
  unfold japaneseBracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])

lemma bracket_sq38 (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  exact Real.sq_sqrt (by positivity)

lemma rpow_three_half38 (b : ℝ) (hb : 0 < b) :
    b ^ (-(3 / 2) : ℝ) = (b * Real.sqrt b)⁻¹ := by
  have h : b * Real.sqrt b = b ^ ((3 : ℝ) / 2) := by
    have h : b ^ ((3 : ℝ) / 2) = b ^ ((1 : ℝ) + 1 / 2) := by norm_num
    rw [h, Real.rpow_add hb, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h, Real.rpow_neg hb.le]

lemma gapHigh38 (C lower K : ℝ) (hC : 0 ≤ C) (hlower : 0 < lower) (hK : 0 < K) (F : ℝ → ℝ)
    (heven : ∀ r, F (-r) = F r) (hlow : ∀ r, lower ≤ F r) (hdiff : ∀ r, DifferentiableAt ℝ F r)
    (hnn : ∀ r, 0 < r → 0 ≤ deriv F r / F r)
    (hle : ∀ r, 0 < r → deriv F r / F r ≤ C * r ^ (-1 / 2 : ℝ))
    (n : ℤ) (l : ℝ) (hl : |l - (n : ℝ) * Real.pi| ≤ K / japaneseBracket n) (hK1 : K + 1 ≤ |(n : ℝ)|) :
    |F (2 * l) - F (2 * Real.pi * n)| ≤
      (4 * C * K * Real.exp (4 * C * K)) * F (2 * Real.pi * n) *
        (japaneseBracket n * Real.sqrt (japaneseBracket n))⁻¹ := by
  set Dhigh : ℝ := 4 * C * K * Real.exp (4 * C * K) with hDh
  have hFpos : ∀ r, 0 < F r := fun r => hlower.trans_le (hlow r)
  set b := japaneseBracket n with hb
  have hb1 : 1 ≤ b := bracket_pos38 n
  have hb0 : 0 < b := by linarith
  have hsb : 1 ≤ Real.sqrt b := Real.one_le_sqrt.2 hb1
  have hbsb : 1 ≤ b * Real.sqrt b := by nlinarith
  have hbsb0 : 0 < b * Real.sqrt b := by linarith
  set a := F (2 * Real.pi * n) with ha
  have ha0 : 0 < a := hFpos _
  have hn1 : 1 ≤ |(n : ℝ)| := by linarith
  have hnpos : 0 < |(n : ℝ)| := by linarith
  have hpi := Real.pi_gt_three
  have hKb : K / b ≤ K := div_le_self hK.le hb1
  set p0 : ℝ := 2 * Real.pi * |(n : ℝ)| with hp0
  set q0 : ℝ := 2 * |l| with hq0
  have hFa : F (2 * Real.pi * n) = F p0 := by
    rcases le_total 0 (n : ℝ) with h | h
    · rw [hp0, abs_of_nonneg h]
    · rw [hp0, abs_of_nonpos h, show 2 * Real.pi * -(n : ℝ) = -(2 * Real.pi * n) by ring,
        heven]
  have hFl : F (2 * l) = F q0 := by
    rcases le_total 0 l with h | h
    · rw [hq0, abs_of_nonneg h]
    · rw [hq0, abs_of_nonpos h, show 2 * -l = -(2 * l) by ring, heven]
  have hdist : |q0 - p0| ≤ 2 * K / b := by
    have h1 : |(|l| - Real.pi * |(n : ℝ)|)| ≤ |l - (n : ℝ) * Real.pi| := by
      have : Real.pi * |(n : ℝ)| = |(n : ℝ) * Real.pi| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]; ring
      rw [this]; exact abs_abs_sub_abs_le_abs_sub _ _
    have : q0 - p0 = 2 * (|l| - Real.pi * |(n : ℝ)|) := by rw [hq0, hp0]; ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc 2 * |(|l| - Real.pi * |(n : ℝ)|)| ≤ 2 * (K / b) := by linarith
      _ = 2 * K / b := by ring
  have hmin : Real.pi * |(n : ℝ)| ≤ min p0 q0 := by
    apply le_min
    · rw [hp0]; nlinarith [Real.pi_pos]
    · have h1 : |l - (n : ℝ) * Real.pi| ≤ K := hl.trans hKb
      have h2 : Real.pi * |(n : ℝ)| = |(n : ℝ) * Real.pi| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]; ring
      have h3 : |(n : ℝ) * Real.pi| - |l| ≤ |l - (n : ℝ) * Real.pi| := by
        have := abs_sub_abs_le_abs_sub ((n : ℝ) * Real.pi) l
        rwa [abs_sub_comm] at this
      rw [hq0]
      have hKn : K ≤ |(n : ℝ)| := by linarith
      nlinarith
  -- bound on increment of log
  have hp0pos : 0 < p0 := by rw [hp0]; exact mul_pos (mul_pos two_pos Real.pi_pos) hnpos
  have hpin : 0 < Real.pi * |(n : ℝ)| := mul_pos Real.pi_pos hnpos
  have hq0pos : 0 < q0 := lt_of_lt_of_le hpin (hmin.trans (min_le_right _ _))
  have hsym : |Real.log (F q0) - Real.log (F p0)| ≤
      C * (min p0 q0) ^ (-1 / 2 : ℝ) * |q0 - p0| :=
    log_increment_min38 F C hFpos hdiff hnn hle p0 q0 hp0pos hq0pos
  have hpow : (min p0 q0) ^ (-1 / 2 : ℝ) ≤ (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmin (by norm_num)
  have hsq : (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) ≤ 2 / Real.sqrt b := by
    have e : (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) = (Real.sqrt (Real.pi * |(n : ℝ)|))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]; norm_num
    rw [e]
    have hbn : b ≤ 4 * (Real.pi * |(n : ℝ)|) := by
      have hb2 : b ^ 2 = 1 + (n : ℝ) ^ 2 := bracket_sq38 n
      have hn2 : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
      have h2n : b ≤ 2 * |(n : ℝ)| := by
        apply le_of_sq_le_sq _ (by positivity)
        nlinarith [hb2, hn2, hn1]
      have := Real.pi_gt_three
      nlinarith [mul_pos Real.pi_pos hnpos]
    have h1 : Real.sqrt b ≤ 2 * Real.sqrt (Real.pi * |(n : ℝ)|) := by
      have : Real.sqrt b ≤ Real.sqrt (4 * (Real.pi * |(n : ℝ)|)) := Real.sqrt_le_sqrt hbn
      rw [Real.sqrt_mul (by norm_num)] at this
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rwa [h4] at this
    have hs0 : 0 < Real.sqrt (Real.pi * |(n : ℝ)|) := Real.sqrt_pos.2 (by positivity)
    rw [inv_eq_one_div, div_le_div_iff₀ hs0 (by linarith)]
    linarith
  set s := Real.log (F q0) - Real.log (F p0) with hs
  have hsbound : |s| ≤ 4 * C * K / (b * Real.sqrt b) := by
    have h1 : |s| ≤ C * (2 / Real.sqrt b) * (2 * K / b) := by
      refine hsym.trans ?_
      have : (min p0 q0) ^ (-1 / 2 : ℝ) ≤ 2 / Real.sqrt b := hpow.trans hsq
      have h3 : C * (min p0 q0) ^ (-1 / 2 : ℝ) ≤ C * (2 / Real.sqrt b) :=
        mul_le_mul_of_nonneg_left this hC
      exact mul_le_mul h3 hdist (abs_nonneg _) (by positivity)
    calc |s| ≤ C * (2 / Real.sqrt b) * (2 * K / b) := h1
      _ = 4 * C * K / (b * Real.sqrt b) := by field_simp; ring
  have hsS : |s| ≤ 4 * C * K := by
    refine hsbound.trans ?_
    rw [div_le_iff₀ hbsb0]
    have : 0 ≤ 4 * C * K := by positivity
    nlinarith
  have hFq : F q0 = F p0 * Real.exp s := by
    rw [hs, Real.exp_sub, Real.exp_log (hFpos _), Real.exp_log (hFpos _)]
    field_simp [(hFpos p0).ne']
  have haF : a = F p0 := ha.trans hFa
  rw [hFl, haF, hFq]
  have e1 : |F p0 * Real.exp s - F p0| = F p0 * |Real.exp s - 1| := by
    rw [← mul_sub_one, abs_mul, abs_of_pos (hFpos p0)]
  rw [e1]
  have e2 : |Real.exp s - 1| ≤ |s| * Real.exp |s| := abs_exp_sub_one_le38 s
  have e3 : Real.exp |s| ≤ Real.exp (4 * C * K) := Real.exp_le_exp.2 hsS
  have e4 : |Real.exp s - 1| ≤ 4 * C * K / (b * Real.sqrt b) * Real.exp (4 * C * K) :=
    e2.trans (mul_le_mul hsbound e3 (Real.exp_pos _).le (by positivity))
  calc F p0 * |Real.exp s - 1|
      ≤ F p0 * (4 * C * K / (b * Real.sqrt b) * Real.exp (4 * C * K)) :=
        mul_le_mul_of_nonneg_left e4 (hFpos _).le
    _ = Dhigh * F p0 * (b * Real.sqrt b)⁻¹ := by rw [hDh]; field_simp

lemma gapLow38 (C lower K : ℝ) (hlower : 0 < lower) (hK : 0 < K) (M : ℝ → ℝ) (F : ℝ → ℝ)
    (heven : ∀ r, F (-r) = F r) (hlow : ∀ r, lower ≤ F r) (hdiff : ∀ r, DifferentiableAt ℝ F r)
    (hnn : ∀ r, 0 < r → 0 ≤ deriv F r / F r)
    (hle : ∀ r, 0 < r → deriv F r / F r ≤ C * r ^ (-1 / 2 : ℝ))
    (hM : ∀ R r, |r| ≤ R → F r ≤ M R)
    (n : ℤ) (l : ℝ) (hl : |l - (n : ℝ) * Real.pi| ≤ K / japaneseBracket n) (N0 : ℕ) (hn : |(n : ℝ)| < N0) :
    |F (2 * l) - F (2 * Real.pi * n)| ≤
      ((|M (2 * ((N0 : ℝ) * Real.pi + K))| / lower + 1) *
        (Real.sqrt (1 + (N0 : ℝ) ^ 2) * Real.sqrt (Real.sqrt (1 + (N0 : ℝ) ^ 2)))) *
        F (2 * Real.pi * n) * (japaneseBracket n * Real.sqrt (japaneseBracket n))⁻¹ := by
  set Λ : ℝ := (N0 : ℝ) * Real.pi + K with hΛ
  set M0 : ℝ := M (2 * Λ) with hM0
  set bN : ℝ := Real.sqrt (1 + (N0 : ℝ) ^ 2) with hbN
  set P : ℝ := bN * Real.sqrt bN with hP
  set Dlow : ℝ := (|M0| / lower + 1) * P with hDl
  have hFpos : ∀ r, 0 < F r := fun r => hlower.trans_le (hlow r)
  set b := japaneseBracket n with hb
  have hb1 : 1 ≤ b := bracket_pos38 n
  have hb0 : 0 < b := by linarith
  have hsb : 1 ≤ Real.sqrt b := Real.one_le_sqrt.2 hb1
  have hbsb : 1 ≤ b * Real.sqrt b := by nlinarith
  have hbsb0 : 0 < b * Real.sqrt b := by linarith
  set a := F (2 * Real.pi * n) with ha
  have ha0 : 0 < a := hFpos _
  have hl' : |l| ≤ Λ := by
    have h1 : |l| ≤ |(n : ℝ) * Real.pi| + |l - (n : ℝ) * Real.pi| := by
      have := abs_sub_abs_le_abs_sub l ((n : ℝ) * Real.pi)
      have h2 := abs_add_le ((n : ℝ) * Real.pi) (l - (n : ℝ) * Real.pi)
      simpa using h2
    have h2 : |(n : ℝ) * Real.pi| ≤ (N0 : ℝ) * Real.pi := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_right hn.le Real.pi_pos.le
    have h3 : |l - (n : ℝ) * Real.pi| ≤ K := by
      have hKb : K / b ≤ K := div_le_self hK.le hb1
      exact hl.trans hKb
    rw [hΛ]; linarith
  have hFl : F (2 * l) ≤ M0 := hM _ _ (by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith)
  have hM0 : 0 < M0 := lt_of_lt_of_le (hFpos _) hFl
  have habs : |F (2 * l) - a| ≤ (M0 / lower + 1) * a := by
    have h1 : F (2 * l) ≤ (M0 / lower) * a := by
      calc F (2 * l) ≤ M0 := hFl
        _ = (M0 / lower) * lower := by field_simp
        _ ≤ (M0 / lower) * a := mul_le_mul_of_nonneg_left (by rw [ha]; exact hlow _) (by positivity)
    rw [abs_le]
    constructor <;> nlinarith [hFpos (2 * l)]
  have hbP : b * Real.sqrt b ≤ P := by
    have h1 : b ≤ bN := by
      rw [hb]; unfold japaneseBracket
      apply Real.sqrt_le_sqrt
      have : (n : ℝ) ^ 2 ≤ (N0 : ℝ) ^ 2 := by
        rw [← sq_abs (n : ℝ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hn.le 2
      linarith
    exact mul_le_mul h1 (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) (by linarith)
  have hinv : 1 ≤ P * (b * Real.sqrt b)⁻¹ := by
    rw [← div_eq_mul_inv, one_le_div hbsb0]; exact hbP
  calc |F (2 * l) - a| ≤ (M0 / lower + 1) * a := habs
    _ ≤ (|M0| / lower + 1) * a := by
        have : M0 ≤ |M0| := le_abs_self _
        have : M0 / lower ≤ |M0| / lower := div_le_div_of_nonneg_right this hlower.le
        nlinarith
    _ = (|M0| / lower + 1) * a * 1 := by ring
    _ ≤ (|M0| / lower + 1) * a * (P * (b * Real.sqrt b)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = Dlow * a * (b * Real.sqrt b)⁻¹ := by rw [hDl]; ring

/-- The abstract gap estimate, with constant depending only on `(C, lower, K, M)`. -/
lemma gapEstimate_abstract38 (C lower K : ℝ) (hC : 0 ≤ C) (hlower : 0 < lower) (hK : 0 < K)
    (M : ℝ → ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ F : ℝ → ℝ,
      (∀ r, F (-r) = F r) → (∀ r, lower ≤ F r) → (∀ r, DifferentiableAt ℝ F r) →
      (∀ r, 0 < r → 0 ≤ deriv F r / F r) →
      (∀ r, 0 < r → deriv F r / F r ≤ C * r ^ (-1 / 2 : ℝ)) →
      (∀ R r, |r| ≤ R → F r ≤ M R) →
      ∀ (n : ℤ) (l : ℝ), |l - (n : ℝ) * Real.pi| ≤ K / japaneseBracket n →
        |F (2 * l) - F (2 * Real.pi * n)| ≤
          D * F (2 * Real.pi * n) * japaneseBracket n ^ (-(3 / 2) : ℝ) := by
  set N0 : ℕ := ⌈K⌉₊ + 1 with hN0
  set bN : ℝ := Real.sqrt (1 + (N0 : ℝ) ^ 2) with hbN
  set P : ℝ := bN * Real.sqrt bN with hP
  set Dhigh : ℝ := 4 * C * K * Real.exp (4 * C * K) with hDh
  set Dlow : ℝ := (|M (2 * ((N0 : ℝ) * Real.pi + K))| / lower + 1) * P with hDl
  have hbN1 : 1 ≤ bN := Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (N0 : ℝ)])
  have hP1 : 1 ≤ P := by
    have : 1 ≤ Real.sqrt bN := Real.one_le_sqrt.2 hbN1
    nlinarith
  have hDh0 : 0 ≤ Dhigh := by positivity
  have hDl0 : 0 < Dlow := by positivity
  refine ⟨max Dhigh Dlow + 1, by
    have := le_max_right Dhigh Dlow
    linarith, ?_⟩
  intro F heven hlow hdiff hnn hle hM n l hl
  have hb0 : 0 < japaneseBracket n := by have := bracket_pos38 n; linarith
  rw [rpow_three_half38 _ hb0]
  have hFa : 0 < F (2 * Real.pi * n) := hlower.trans_le (hlow _)
  have hinv : 0 ≤ F (2 * Real.pi * n) * (japaneseBracket n * Real.sqrt (japaneseBracket n))⁻¹ := by
    have : 0 < (japaneseBracket n * Real.sqrt (japaneseBracket n))⁻¹ :=
      inv_pos.2 (mul_pos hb0 (Real.sqrt_pos.2 hb0))
    positivity
  by_cases hn : (N0 : ℝ) ≤ |(n : ℝ)|
  · have hK1 : K + 1 ≤ |(n : ℝ)| := by
      have : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
      have h2 : ((N0 : ℕ) : ℝ) = (⌈K⌉₊ : ℝ) + 1 := by rw [hN0]; push_cast; ring
      linarith
    have := gapHigh38 C lower K hC hlower hK F heven hlow hdiff hnn hle n l hl hK1
    refine this.trans ?_
    have := le_max_left Dhigh Dlow
    nlinarith
  · have hn' := not_le.1 hn
    have := gapLow38 C lower K hlower hK M F heven hlow hdiff hnn hle hM n l hl N0 hn'
    refine this.trans ?_
    have := le_max_right Dhigh Dlow
    nlinarith

lemma partialWeight_even38 (c : ℕ → ℝ) (m : ℕ) (r : ℝ) :
    partialWeight c m (-r) = partialWeight c m r := by
  unfold partialWeight; simp

lemma weight_even38 (c : ℕ → ℝ) (r : ℝ) : weight c (-r) = weight c r := by
  unfold weight; simp

/-- Logarithmic derivative bounds with the explicit constant `2^{5/4}` for `1 ≤ c_j ≤ 2`,
for every partial symbol `W_m` (m ≥ 0, including `m = 0`) and for the full symbol. -/
theorem uniformLogDerivative_one_two38 (c : ℕ → ℝ)
    (hbound : ∀ j : ℕ, 1 ≤ c j) (hupper : ∀ j : ℕ, c j ≤ 2) :
    (∀ (m : ℕ) (r : ℝ), 0 < r →
      0 ≤ deriv (partialWeight c m) r / partialWeight c m r ∧
      deriv (partialWeight c m) r / partialWeight c m r ≤
        (2 : ℝ) ^ (5 / 4 : ℝ) * r ^ (-1 / 2 : ℝ)) ∧
    (∀ r : ℝ, 0 < r →
      0 ≤ deriv (weight c) r / weight c r ∧
      deriv (weight c) r / weight c r ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * r ^ (-1 / 2 : ℝ)) := by
  refine ⟨fun m r hr => ⟨partialWeight_logDerivative_nonneg 1 c one_pos hbound m r hr,
    partialWeight_logDerivative_le_one_two c hbound hupper m r hr⟩,
    fun r hr => ⟨weight_logDerivative_nonneg 1 2 c one_pos hbound hupper r hr,
    weight_logDerivative_le_one_two c hbound hupper r hr⟩⟩

/-- H01 gap estimate, hierarchy-uniform. For coefficient bounds `lower ≤ c_j ≤ upper` and
`B ≥ 1` there is `C_B` (depending only on `lower, upper, B`) such that for every such `c`, every
`H¹` potential with `‖u‖_{H¹} ≤ B`, every `n : ℤ` and every `λ` in the closed gap
`[g_n^-, g_n^+]`: `|W_m(2λ) - a_{m,n}| ≤ C_B a_{m,n} ⟨n⟩^{-3/2}` for all `m`, and likewise for `W`,
where `a_{m,n} = W_m(2πn)`. -/
theorem uniformSymbolGap38 (lower upper : ℝ) (hlower : 0 < lower) (hle : lower ≤ upper)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ c : ℕ → ℝ, (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ n : ℤ,
          ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
            (∀ m : ℕ, |partialWeight c m (2 * l) - partialWeight c m (2 * Real.pi * n)| ≤
              CB * partialWeight c m (2 * Real.pi * n) * japaneseBracket n ^ (-(3 / 2) : ℝ)) ∧
            |weight c (2 * l) - weight c (2 * Real.pi * n)| ≤
              CB * weight c (2 * Real.pi * n) * japaneseBracket n ^ (-(3 / 2) : ℝ) := by
  obtain ⟨K, hK, hloc⟩ := actualGapLocalization_allU_E02_38 B hB
  have hupper0 : 0 ≤ upper := (hlower.le.trans hle)
  obtain ⟨D, hD, hDF⟩ := gapEstimate_abstract38 (2 * (upper / lower) ^ (1 / 4 : ℝ)) lower K
    (by positivity) hlower hK (fun R => upper * Real.exp (4 * Real.sqrt R))
  refine ⟨D, hD, fun c hbound hupper u hu hB' n l hl => ?_⟩
  have hl' := hloc u hu hB' n l hl
  have hMw : ∀ R r : ℝ, |r| ≤ R → weight c r ≤ upper * Real.exp (4 * Real.sqrt R) := fun R r hr =>
    (weight_upper lower upper c hlower hbound hupper r).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        have := Real.sqrt_le_sqrt hr; linarith)) hupper0)
  refine ⟨fun m => hDF _ (partialWeight_even38 c m) (partialWeight_lower lower c hlower hbound m)
    (fun r => (partialWeight_hasDerivAt c m r).differentiableAt)
    (fun r hr => partialWeight_logDerivative_nonneg lower c hlower hbound m r hr)
    (fun r hr => partialWeight_logDerivative_le lower upper c hlower hbound hupper m r hr)
    (fun R r hr => (partialWeight_le_weight lower upper c hlower hbound hupper m r).trans
      (hMw R r hr)) n l hl',
    hDF _ (weight_even38 c) (weight_lower lower upper c hlower hbound hupper)
    (fun r => (weight_hasDerivAt lower upper c hlower hbound hupper r).differentiableAt)
    (fun r hr => weight_logDerivative_nonneg lower upper c hlower hbound hupper r hr)
    (fun r hr => weight_logDerivative_le lower upper c hlower hbound hupper r hr)
    hMw n l hl'⟩

end NlsGge.Weights
end
