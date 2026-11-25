import Mathlib

/-!
# W03.01 / W03.02: the source weight `w_n = exp(a √|n|) ⟨n⟩^b`

Source: `paper/v2.tex`, lines 1438-1452 (`D:lem:composition` and the first paragraph of its
proof).  Here `⟨x⟩ = (1 + x^2)^{1/2}` and `⟨n⟩^b` is a real power.

Main results:
* `NlsGge.Composition.sqrt_sub_le` : the scalar inequality
  `√|x+y| - √|x| - √|y| ≤ -(2-√2) √|y|` for `|y| ≤ |x|` (source line 1451);
* `NlsGge.Composition.srcWeight_ratio` : `w_{k+l} ≤ r_l w_k w_l` for `|l| ≤ |k|`, with
  `r_l = 2^{|b|/2} ⟨l⟩^{2|b|} exp(-(2-√2) a √|l|)` (source display line 1448);
* `NlsGge.Composition.summable_srcWeight_inv_sq` : `∑ w_n^{-2} < ∞` (source line 1446);
* `NlsGge.Composition.summable_ratioMajorant_sq` : `r ∈ ℓ²`;
* `NlsGge.Composition.summable_srcWeight_sq_mul_exp` : `∑ w_n^2 e^{-c|n|} < ∞` for `c > 0`
  (source line 1471, the constant `D_η`).
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open Real

/-- Japanese bracket `⟨x⟩ = (1 + x^2)^{1/2}`. -/
def jbr (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

/-- The source weight `w_n = exp(a √|n|) ⟨n⟩^b` (real power `b`). -/
def srcWeight (a b : ℝ) (n : ℤ) : ℝ := Real.exp (a * Real.sqrt |(n : ℝ)|) * jbr n ^ b

/-- The source ratio majorant `r_l = C_b ⟨l⟩^{2|b|} exp(-(2-√2) a √|l|)`, with
`C_b = 2^{|b|/2}`. -/
def ratioMajorant (a b : ℝ) (l : ℤ) : ℝ :=
  (2 : ℝ) ^ (|b| / 2) * jbr l ^ (2 * |b|) * Real.exp (-(2 - Real.sqrt 2) * a * Real.sqrt |(l : ℝ)|)

theorem one_le_jbr (x : ℝ) : 1 ≤ jbr x := by
  unfold jbr
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg x])

theorem jbr_pos (x : ℝ) : 0 < jbr x := lt_of_lt_of_le one_pos (one_le_jbr x)

theorem jbr_neg (x : ℝ) : jbr (-x) = jbr x := by simp [jbr]

theorem jbr_sq (x : ℝ) : jbr x ^ 2 = 1 + x ^ 2 := by
  unfold jbr
  rw [Real.sq_sqrt (by positivity)]

/-- Peetre-type inequality `⟨x+y⟩ ≤ √2 ⟨x⟩ ⟨y⟩`. -/
theorem jbr_add_le (x y : ℝ) : jbr (x + y) ≤ Real.sqrt 2 * jbr x * jbr y := by
  have h1 : 0 ≤ Real.sqrt 2 * jbr x * jbr y := by
    have := jbr_pos x; have := jbr_pos y; positivity
  rw [← abs_of_nonneg h1, ← abs_of_pos (jbr_pos (x + y))]
  apply sq_le_sq.mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), jbr_sq, jbr_sq, jbr_sq]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * y)]

theorem rpow_jbr_pos (x b : ℝ) : 0 < jbr x ^ b := Real.rpow_pos_of_pos (jbr_pos x) b

/-- Polynomial part of the ratio bound: `⟨x+y⟩^b ≤ 2^{|b|/2} ⟨y⟩^{2|b|} ⟨x⟩^b ⟨y⟩^b`. -/
theorem jbr_rpow_add_le (b x y : ℝ) :
    jbr (x + y) ^ b ≤ (2 : ℝ) ^ (|b| / 2) * jbr y ^ (2 * |b|) * (jbr x ^ b * jbr y ^ b) := by
  have hx := jbr_pos x
  have hy := jbr_pos y
  have hxy := jbr_pos (x + y)
  have hy1 := one_le_jbr y
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2 : ∀ t : ℝ, Real.sqrt 2 ^ t = (2 : ℝ) ^ (t / 2) := by
    intro t
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    calc jbr (x + y) ^ b ≤ (Real.sqrt 2 * jbr x * jbr y) ^ b :=
          Real.rpow_le_rpow hxy.le (jbr_add_le x y) hb
      _ = (2 : ℝ) ^ (b / 2) * (jbr x ^ b * jbr y ^ b) := by
          rw [Real.mul_rpow (by positivity) hy.le, Real.mul_rpow hs2 hx.le, hsqrt2]; ring
      _ = (2 : ℝ) ^ (b / 2) * 1 * (jbr x ^ b * jbr y ^ b) := by ring
      _ ≤ (2 : ℝ) ^ (b / 2) * jbr y ^ (2 * b) * (jbr x ^ b * jbr y ^ b) := by
          gcongr
          exact Real.one_le_rpow hy1 (by linarith)
  · -- `b < 0`: use `⟨x⟩ ≤ √2 ⟨x+y⟩ ⟨y⟩`.
    rw [abs_of_neg hb]
    set β := -b with hβ
    have hβpos : 0 < β := by linarith
    have hkey : jbr x ≤ Real.sqrt 2 * jbr (x + y) * jbr y := by
      have := jbr_add_le (x + y) (-y)
      simpa [jbr_neg] using this
    -- jbr x ^ β ≤ (√2 ⟨x+y⟩ ⟨y⟩)^β
    have h1 : jbr x ^ β ≤ (2 : ℝ) ^ (β / 2) * jbr (x + y) ^ β * jbr y ^ β := by
      calc jbr x ^ β ≤ (Real.sqrt 2 * jbr (x + y) * jbr y) ^ β :=
            Real.rpow_le_rpow hx.le hkey hβpos.le
        _ = _ := by
            rw [Real.mul_rpow (by positivity) hy.le, Real.mul_rpow hs2 hxy.le, hsqrt2]
    have eb : b = -β := by simp [hβ]
    rw [eb, Real.rpow_neg hxy.le, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
    have hxb := Real.rpow_pos_of_pos hx β
    have hyb := Real.rpow_pos_of_pos hy β
    have hxyb := Real.rpow_pos_of_pos hxy β
    have h2 : jbr y ^ (2 * β) = jbr y ^ β * jbr y ^ β := by
      rw [two_mul, Real.rpow_add hy]
    rw [h2, inv_le_iff_one_le_mul₀ hxyb]
    have : (2 : ℝ) ^ (β / 2) * (jbr y ^ β * jbr y ^ β) * ((jbr x ^ β)⁻¹ * (jbr y ^ β)⁻¹) *
        jbr (x + y) ^ β = ((2 : ℝ) ^ (β / 2) * jbr (x + y) ^ β * jbr y ^ β) / jbr x ^ β := by
      field_simp
    have this' : jbr (x + y) ^ β * ((2 : ℝ) ^ (β / 2) * (jbr y ^ β * jbr y ^ β) *
        ((jbr x ^ β)⁻¹ * (jbr y ^ β)⁻¹)) =
        ((2 : ℝ) ^ (β / 2) * jbr (x + y) ^ β * jbr y ^ β) / jbr x ^ β := by
      rw [← this]; ring
    rw [this, le_div_iff₀ hxb, one_mul]
    exact h1

/-- The scalar inequality of the source (line 1451):
`√|x+y| - √|x| - √|y| ≤ -(2-√2) √|y|` whenever `|y| ≤ |x|`. -/
theorem sqrt_sub_le (x y : ℝ) (hxy : |y| ≤ |x|) :
    Real.sqrt |x + y| - Real.sqrt |x| - Real.sqrt |y| ≤ -(2 - Real.sqrt 2) * Real.sqrt |y| := by
  -- Reduce to `√(|x|+|y|) ≤ √|x| + (√2 - 1) √|y|`.
  set u := Real.sqrt |x| with hu
  set v := Real.sqrt |y| with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hvu : v ≤ u := Real.sqrt_le_sqrt hxy
  have hu2 : u ^ 2 = |x| := Real.sq_sqrt (abs_nonneg x)
  have hv2 : v ^ 2 = |y| := Real.sq_sqrt (abs_nonneg y)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hrhs : 0 ≤ u + (Real.sqrt 2 - 1) * v := by nlinarith
  have hle : Real.sqrt |x + y| ≤ u + (Real.sqrt 2 - 1) * v := by
    rw [Real.sqrt_le_left hrhs]
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ = u ^ 2 + v ^ 2 := by rw [hu2, hv2]
      _ ≤ (u + (Real.sqrt 2 - 1) * v) ^ 2 := by
        have : (u + (Real.sqrt 2 - 1) * v) ^ 2 - (u ^ 2 + v ^ 2)
            = 2 * (Real.sqrt 2 - 1) * v * (u - v) := by nlinarith [hs]
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (Real.sqrt 2 - 1)) hv0)
          (by linarith : (0:ℝ) ≤ u - v)]
  linarith

theorem srcWeight_pos (a b : ℝ) (n : ℤ) : 0 < srcWeight a b n :=
  mul_pos (Real.exp_pos _) (rpow_jbr_pos _ _)

theorem srcWeight_neg (a b : ℝ) (n : ℤ) : srcWeight a b (-n) = srcWeight a b n := by
  simp [srcWeight, jbr_neg, abs_neg]

theorem ratioMajorant_nonneg (a b : ℝ) (l : ℤ) : 0 ≤ ratioMajorant a b l := by
  unfold ratioMajorant
  have := rpow_jbr_pos (l : ℝ) (2 * |b|)
  positivity

/-- W03.02: the ratio bound `w_{k+l} ≤ r_l w_k w_l` for `|l| ≤ |k|` (source display, line
1448).  Requires only `0 ≤ a`. -/
theorem srcWeight_ratio {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (k l : ℤ) (hkl : |l| ≤ |k|) :
    srcWeight a b (k + l) ≤ ratioMajorant a b l * (srcWeight a b k * srcWeight a b l) := by
  have hkl' : |(l : ℝ)| ≤ |(k : ℝ)| := by exact_mod_cast hkl
  have hs := sqrt_sub_le (k : ℝ) (l : ℝ) hkl'
  have hexp : Real.exp (a * Real.sqrt |((k + l : ℤ) : ℝ)|) ≤
      Real.exp (-(2 - Real.sqrt 2) * a * Real.sqrt |(l : ℝ)|) *
        (Real.exp (a * Real.sqrt |(k : ℝ)|) * Real.exp (a * Real.sqrt |(l : ℝ)|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  have hpoly := jbr_rpow_add_le b (k : ℝ) (l : ℝ)
  unfold srcWeight ratioMajorant
  push_cast at hexp ⊢
  have e1 := Real.exp_pos (a * Real.sqrt |(k : ℝ) + l|)
  have p1 := rpow_jbr_pos ((k : ℝ) + l) b
  calc Real.exp (a * Real.sqrt |(k : ℝ) + l|) * jbr ((k : ℝ) + l) ^ b
      ≤ (Real.exp (-(2 - Real.sqrt 2) * a * Real.sqrt |(l : ℝ)|) *
          (Real.exp (a * Real.sqrt |(k : ℝ)|) * Real.exp (a * Real.sqrt |(l : ℝ)|))) *
        ((2 : ℝ) ^ (|b| / 2) * jbr l ^ (2 * |b|) * (jbr k ^ b * jbr l ^ b)) := by
        gcongr
    _ = _ := by ring

/-! ### Summability -/

/-- `(1 + n^2)^{β/2} e^{-c√n}` is summable over `ℕ` (any real `β`, `c > 0`). -/
theorem summable_nat_jbr_rpow_mul_exp (β : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => jbr n ^ β * Real.exp (-c * Real.sqrt n)) := by
  -- choose an integer `m` with `m/2 ≥ |β| + 2`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * |β| + 4 ≤ (m : ℝ) := exists_nat_ge _
  -- bound for n ≥ 1 by `K * n^{-2}`
  set K : ℝ := (2 : ℝ) ^ |β| * (m.factorial : ℝ) / c ^ m with hK
  have hKpos : 0 ≤ K := by positivity
  have hbound : ∀ n : ℕ, 1 ≤ n →
      jbr n ^ β * Real.exp (-c * Real.sqrt n) ≤ K * ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    -- jbr n ≤ 2 n
    have hj : jbr n ≤ 2 * n := by
      have : jbr n ^ 2 ≤ (2 * n) ^ 2 := by rw [jbr_sq]; nlinarith
      have h0 := jbr_pos (n : ℝ)
      nlinarith
    have hjb : jbr n ^ β ≤ (2 * n) ^ |β| := by
      calc jbr n ^ β ≤ jbr n ^ |β| := Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (le_abs_self β)
        _ ≤ (2 * n) ^ |β| := Real.rpow_le_rpow (jbr_pos _).le hj (abs_nonneg _)
    -- exp(-c√n) ≤ m! / (c √n)^m
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hcs : 0 < c * Real.sqrt n := mul_pos hc hsn
    have he : Real.exp (-c * Real.sqrt n) ≤ (m.factorial : ℝ) / (c * Real.sqrt n) ^ m := by
      have h := Real.pow_div_factorial_le_exp (c * Real.sqrt n) hcs.le m
      rw [neg_mul, Real.exp_neg, le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h
      calc (Real.exp (c * Real.sqrt n))⁻¹ * (c * Real.sqrt n) ^ m
          ≤ (Real.exp (c * Real.sqrt n))⁻¹ * (Real.exp (c * Real.sqrt n) * (m.factorial : ℝ)) := by
            gcongr
        _ = m.factorial := by field_simp
    -- (√n)^m = n^{m/2}
    have hsq : Real.sqrt n ^ m = (n : ℝ) ^ ((m : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      ring_nf
    calc jbr n ^ β * Real.exp (-c * Real.sqrt n)
        ≤ (2 * n) ^ |β| * ((m.factorial : ℝ) / (c * Real.sqrt n) ^ m) := by
          gcongr
      _ = K * ((n : ℝ) ^ |β| / (n : ℝ) ^ ((m : ℝ) / 2)) := by
          rw [Real.mul_rpow (by norm_num) hnpos.le, mul_pow, hsq, hK]
          field_simp
      _ ≤ K * ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
          gcongr
          rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le, ← Real.rpow_add hnpos,
            ← Real.rpow_neg hnpos.le]
          apply Real.rpow_le_rpow_of_exponent_le hn1
          linarith
  have hsum : Summable (fun n : ℕ => K * ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left K
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((summable_nat_add_iff 1).mpr hsum)
  · have := rpow_jbr_pos ((n + 1 : ℕ) : ℝ) β
    positivity
  · exact hbound (n + 1) (by omega)

/-- `⟨n⟩^β e^{-c√|n|}` is summable over `ℤ` (any real `β`, `c > 0`). -/
theorem summable_int_jbr_rpow_mul_exp (β : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => jbr n ^ β * Real.exp (-c * Real.sqrt |(n : ℝ)|)) := by
  have h := summable_nat_jbr_rpow_mul_exp β hc
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa [jbr_neg] using h

/-- W03.01: `∑ w_n^{-2} < ∞` (source line 1446). -/
theorem summable_srcWeight_inv_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun n : ℤ => (srcWeight a b n)⁻¹ ^ 2) := by
  refine (summable_int_jbr_rpow_mul_exp (-2 * b) (by linarith : (0 : ℝ) < 2 * a)).congr ?_
  intro n
  unfold srcWeight
  have hj := jbr_pos (n : ℝ)
  rw [inv_pow, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast (jbr n ^ b),
    ← Real.rpow_mul hj.le, mul_inv, ← Real.exp_neg, ← Real.rpow_neg hj.le]
  push_cast
  ring_nf

/-- `r ∈ ℓ²` (source line 1449). -/
theorem summable_ratioMajorant_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun l : ℤ => ratioMajorant a b l ^ 2) := by
  have hc : 0 < 2 * ((2 - Real.sqrt 2) * a) := by
    have : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have : 0 < 2 - Real.sqrt 2 := by linarith
    positivity
  refine ((summable_int_jbr_rpow_mul_exp (4 * |b|) hc).mul_left (((2 : ℝ) ^ (|b| / 2)) ^ 2)).congr ?_
  intro l
  unfold ratioMajorant
  have hj := jbr_pos (l : ℝ)
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast (jbr l ^ (2 * |b|)),
    ← Real.rpow_mul hj.le]
  push_cast
  ring_nf

/-- `∑ w_n^2 e^{-c|n|} < ∞` for every `c > 0` (source line 1471). -/
theorem summable_srcWeight_sq_mul_exp (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => srcWeight a b n ^ 2 * Real.exp (-c * |(n : ℝ)|)) := by
  -- `2a√x - c x ≤ 2a²/c - (c/2) x ≤ 2a²/c + c/2 - (c/2)√x`
  set K : ℝ := Real.exp (2 * a ^ 2 / c + c / 2) with hK
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_int_jbr_rpow_mul_exp (2 * b) (by linarith : (0 : ℝ) < c / 2)).mul_left K)
  unfold srcWeight
  have hj := jbr_pos (n : ℝ)
  set x : ℝ := |(n : ℝ)| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  set s := Real.sqrt x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast (jbr n ^ b), ← Real.rpow_mul hj.le, hK]
  push_cast
  rw [show Real.exp (2 * (a * s)) * jbr n ^ (b * 2) * Real.exp (-c * x)
      = jbr n ^ (2 * b) * Real.exp (2 * (a * s) + -c * x) by
        rw [Real.exp_add, mul_comm b 2]; ring]
  rw [show Real.exp (2 * a ^ 2 / c + c / 2) * (jbr n ^ (2 * b) * Real.exp (-(c / 2) * s))
      = jbr n ^ (2 * b) * Real.exp (2 * a ^ 2 / c + c / 2 + -(c / 2) * s) by
        rw [Real.exp_add (2 * a ^ 2 / c + c / 2)]; ring]
  apply mul_le_mul_of_nonneg_left _ (rpow_jbr_pos _ _).le
  apply Real.exp_le_exp.mpr
  -- 2 a s - c s² ≤ 2a²/c + c/2 - (c/2) s
  have h1 : 2 * (a * s) - (c / 2) * s ^ 2 ≤ 2 * a ^ 2 / c := by
    have : 2 * a ^ 2 / c - (2 * (a * s) - (c / 2) * s ^ 2) = (c / 2) * (s - 2 * a / c) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (s - 2 * a / c)]
  have h2 : -(c / 2) * s ^ 2 ≤ c / 2 - (c / 2) * s := by nlinarith [sq_nonneg (s - 1)]
  rw [← hs2]
  nlinarith

end NlsGge.Composition
