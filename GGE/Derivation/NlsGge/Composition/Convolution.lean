import Mathlib

/-!
# W03.03 (scalar part): weighted convolution estimate

Source: `paper/v2.tex`, lines 1447-1452.  For a weight `w > 0` with a ratio majorant
`w_{k+l} ≤ r_l w_k w_l` for `|l| ≤ |k|`, split a convolution into `|k| ≥ |l|` and its
complement, apply Young `ℓ² * ℓ¹ → ℓ²` and Cauchy--Schwarz.  The resulting product bound has
constant `C_w = 2 ‖r‖₂`.

Everything is first proved for `ℝ≥0∞`-valued sequences (so that no summability side conditions
are needed), then transferred to nonnegative real sequences with explicit summability.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open scoped ENNReal

/-! ### Elementary `ℝ≥0∞` inequalities -/

theorem ennreal_two_mul_le_add_sq (x y : ℝ≥0∞) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp [ENNReal.top_pow two_ne_zero]
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp [ENNReal.top_pow two_ne_zero]
  lift x to NNReal using hx
  lift y to NNReal using hy
  have h := two_mul_le_add_sq (x : ℝ) (y : ℝ)
  have h' : 2 * x * y ≤ x ^ 2 + y ^ 2 := by exact_mod_cast h
  exact_mod_cast h'

theorem ennreal_sq_tsum {ι : Type*} (f : ι → ℝ≥0∞) :
    (∑' i, f i) ^ 2 = ∑' i, ∑' j, f i * f j := by
  rw [sq, ← ENNReal.tsum_mul_right]
  congr 1; ext i
  rw [← ENNReal.tsum_mul_left]

/-- Cauchy--Schwarz for `ℝ≥0∞`-valued series. -/
theorem ennreal_tsum_mul_sq_le {ι : Type*} (x y : ι → ℝ≥0∞) :
    (∑' i, x i * y i) ^ 2 ≤ (∑' i, x i ^ 2) * ∑' i, y i ^ 2 := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine (ENNReal.mul_le_mul_iff_right h2 h2').mp ?_
  rw [ennreal_sq_tsum, ← ENNReal.tsum_mul_left]
  calc ∑' i, 2 * ∑' j, x i * y i * (x j * y j)
      = ∑' i, ∑' j, 2 * (x i * y j) * (x j * y i) := by
        congr 1; ext i; rw [← ENNReal.tsum_mul_left]; congr 1; ext j; ring
    _ ≤ ∑' i, ∑' j, ((x i * y j) ^ 2 + (x j * y i) ^ 2) :=
        ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ennreal_two_mul_le_add_sq _ _
    _ = ∑' i, ∑' j, (x i ^ 2 * y j ^ 2) + ∑' i, ∑' j, (x j ^ 2 * y i ^ 2) := by
        rw [← ENNReal.tsum_add]; congr 1; ext i; rw [← ENNReal.tsum_add]; congr 1; ext j; ring
    _ = 2 * ((∑' i, x i ^ 2) * ∑' i, y i ^ 2) := by
        rw [ENNReal.tsum_comm (f := fun i j => x j ^ 2 * y i ^ 2)]
        have : ∑' i, ∑' j, x i ^ 2 * y j ^ 2 = (∑' i, x i ^ 2) * ∑' i, y i ^ 2 := by
          rw [← ENNReal.tsum_mul_right]; congr 1; ext i; rw [ENNReal.tsum_mul_left]
        rw [this, two_mul]

theorem ennreal_tsum_shift (f : ℤ → ℝ≥0∞) (k : ℤ) : ∑' n, f (n - k) = ∑' n, f n :=
  (Equiv.subRight k).tsum_eq f

/-- Young's inequality `ℓ¹ * ℓ² → ℓ²` for `ℝ≥0∞`-valued sequences on `ℤ`. -/
theorem ennreal_young (u A : ℤ → ℝ≥0∞) :
    ∑' n, (∑' k, u k * A (n - k)) ^ 2 ≤ (∑' k, u k) ^ 2 * ∑' n, A n ^ 2 := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  refine (ENNReal.mul_le_mul_iff_right h2 h2').mp ?_
  rw [← ENNReal.tsum_mul_left]
  calc ∑' n, 2 * (∑' k, u k * A (n - k)) ^ 2
      = ∑' n, ∑' k, ∑' j, u k * u j * (2 * A (n - k) * A (n - j)) := by
        congr 1; ext n
        rw [ennreal_sq_tsum, ← ENNReal.tsum_mul_left]
        congr 1; ext k; rw [← ENNReal.tsum_mul_left]; congr 1; ext j; ring
    _ ≤ ∑' n, ∑' k, ∑' j, u k * u j * (A (n - k) ^ 2 + A (n - j) ^ 2) :=
        ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j =>
          by gcongr; exact ennreal_two_mul_le_add_sq _ _
    _ = ∑' k, ∑' j, u k * u j * (∑' n, A (n - k) ^ 2 + ∑' n, A (n - j) ^ 2) := by
        rw [ENNReal.tsum_comm]
        congr 1; ext k
        rw [ENNReal.tsum_comm]
        congr 1; ext j
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    _ = ∑' k, ∑' j, u k * u j * (2 * ∑' n, A n ^ 2) := by
        congr 1; ext k; congr 1; ext j
        rw [ennreal_tsum_shift (fun n => A n ^ 2) k, ennreal_tsum_shift (fun n => A n ^ 2) j,
          two_mul]
    _ = 2 * ((∑' k, u k) ^ 2 * ∑' n, A n ^ 2) := by
        have e1 : ∀ k j, u k * u j * (2 * ∑' n, A n ^ 2) = (2 * ∑' n, A n ^ 2) * (u k * u j) :=
          fun k j => by ring
        simp_rw [e1, ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right, sq]; ring

/-! ### The weighted convolution estimate -/

/-- Hypotheses on a weight used for the product estimate: positivity and a square-summable
ratio majorant `w_{k+l} ≤ r_l w_k w_l` whenever `|l| ≤ |k|`. -/
structure RatioMajorant (w r : ℤ → ℝ) : Prop where
  w_pos : ∀ n, 0 < w n
  r_nonneg : ∀ n, 0 ≤ r n
  r_sq : Summable fun n => r n ^ 2
  ratio : ∀ k l : ℤ, |l| ≤ |k| → w (k + l) ≤ r l * (w k * w l)

theorem RatioMajorant.ratio_symm {w r : ℤ → ℝ} (h : RatioMajorant w r) (n k : ℤ) :
    w n ≤ (r (n - k) + r k) * (w k * w (n - k)) := by
  have hw := h.w_pos
  rcases le_total |n - k| |k| with hk | hk
  · have := h.ratio k (n - k) hk
    rw [show k + (n - k) = n by ring] at this
    have : 0 ≤ r k * (w k * w (n - k)) :=
      mul_nonneg (h.r_nonneg k) (mul_nonneg (hw k).le (hw _).le)
    nlinarith
  · have := h.ratio (n - k) k hk
    rw [show n - k + k = n by ring] at this
    have : 0 ≤ r (n - k) * (w k * w (n - k)) :=
      mul_nonneg (h.r_nonneg _) (mul_nonneg (hw k).le (hw _).le)
    nlinarith

/-- `ℝ≥0∞` form of the weighted product estimate. With `A = w a`, `B = w b`,
`∑_n (w_n ∑_k a_k b_{n-k})^2 ≤ 4 ‖r‖₂² ‖A‖₂² ‖B‖₂²`. -/
theorem ennreal_weighted_conv {w r : ℤ → ℝ} (h : RatioMajorant w r) (a b : ℤ → ℝ≥0∞) :
    ∑' n, (ENNReal.ofReal (w n) * ∑' k, a k * b (n - k)) ^ 2 ≤
      4 * (∑' n, ENNReal.ofReal (r n) ^ 2) *
        (∑' n, (ENNReal.ofReal (w n) * a n) ^ 2) * (∑' n, (ENNReal.ofReal (w n) * b n) ^ 2) := by
  set W : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (w n) with hW
  set R : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (r n) with hR
  set A : ℤ → ℝ≥0∞ := fun n => W n * a n with hA
  set B : ℤ → ℝ≥0∞ := fun n => W n * b n with hB
  -- pointwise: `W n * a k * b (n-k) ≤ A k * (R B)(n-k) + (R A) k * B (n-k)`
  have hpt : ∀ n k, W n * (a k * b (n - k)) ≤
      A k * (R (n - k) * B (n - k)) + R k * A k * B (n - k) := by
    intro n k
    have hrs := h.ratio_symm n k
    have hWn : W n ≤ (R (n - k) + R k) * (W k * W (n - k)) := by
      simp only [hW, hR]
      rw [← ENNReal.ofReal_add (h.r_nonneg _) (h.r_nonneg _),
        ← ENNReal.ofReal_mul (h.w_pos k).le,
        ← ENNReal.ofReal_mul (add_nonneg (h.r_nonneg _) (h.r_nonneg _))]
      exact ENNReal.ofReal_le_ofReal hrs
    calc W n * (a k * b (n - k)) ≤ (R (n - k) + R k) * (W k * W (n - k)) * (a k * b (n - k)) :=
          by gcongr
      _ = _ := by simp only [hA, hB]; ring
  have hsum : ∀ n, W n * ∑' k, a k * b (n - k) ≤
      ∑' k, A k * (R (n - k) * B (n - k)) + ∑' k, R k * A k * B (n - k) := by
    intro n
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum (hpt n)
  -- the two pieces
  set P : ℤ → ℝ≥0∞ := fun n => ∑' k, A k * (R (n - k) * B (n - k)) with hP
  set Q : ℤ → ℝ≥0∞ := fun n => ∑' k, R k * A k * B (n - k) with hQ
  have hPsq : ∑' n, P n ^ 2 ≤ (∑' n, R n ^ 2) * (∑' n, A n ^ 2) * ∑' n, B n ^ 2 := by
    -- reindex `k ↦ n - k`
    have hre : ∀ n, P n = ∑' k, (R k * B k) * A (n - k) := by
      intro n
      simp only [hP]
      rw [← (Equiv.subLeft n).tsum_eq]
      congr 1; ext k; simp [Equiv.subLeft_apply]; ring
    simp_rw [hre]
    calc ∑' n, (∑' k, (R k * B k) * A (n - k)) ^ 2
        ≤ (∑' k, R k * B k) ^ 2 * ∑' n, A n ^ 2 := ennreal_young _ _
      _ ≤ ((∑' n, R n ^ 2) * ∑' n, B n ^ 2) * ∑' n, A n ^ 2 :=
          by gcongr; exact ennreal_tsum_mul_sq_le _ _
      _ = _ := by ring
  have hQsq : ∑' n, Q n ^ 2 ≤ (∑' n, R n ^ 2) * (∑' n, A n ^ 2) * ∑' n, B n ^ 2 := by
    calc ∑' n, Q n ^ 2 ≤ (∑' k, R k * A k) ^ 2 * ∑' n, B n ^ 2 := ennreal_young _ _
      _ ≤ ((∑' n, R n ^ 2) * ∑' n, A n ^ 2) * ∑' n, B n ^ 2 :=
          by gcongr; exact ennreal_tsum_mul_sq_le _ _
  calc ∑' n, (W n * ∑' k, a k * b (n - k)) ^ 2 ≤ ∑' n, (P n + Q n) ^ 2 :=
        ENNReal.tsum_le_tsum fun n => by gcongr; exact hsum n
    _ ≤ ∑' n, (2 * P n ^ 2 + 2 * Q n ^ 2) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        have := ennreal_two_mul_le_add_sq (P n) (Q n)
        calc (P n + Q n) ^ 2 = P n ^ 2 + Q n ^ 2 + 2 * P n * Q n := by ring
          _ ≤ P n ^ 2 + Q n ^ 2 + (P n ^ 2 + Q n ^ 2) := add_le_add_right this _
          _ = _ := by ring
    _ = 2 * ∑' n, P n ^ 2 + 2 * ∑' n, Q n ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ 2 * ((∑' n, R n ^ 2) * (∑' n, A n ^ 2) * ∑' n, B n ^ 2) +
          2 * ((∑' n, R n ^ 2) * (∑' n, A n ^ 2) * ∑' n, B n ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The ratio constant `‖r‖₂² = ∑ r_n^2`. -/
def ratioNormSq (r : ℤ → ℝ) : ℝ := ∑' n, r n ^ 2

/-- Real form of the weighted product estimate (source line 1452).  For nonnegative `a, b`
with `w a, w b ∈ ℓ²`, every convolution series converges, `w (a * b) ∈ ℓ²` and
`∑_n (w_n (a*b)_n)^2 ≤ 4 ‖r‖₂² ∑ (w a)^2 ∑ (w b)^2`. -/
theorem weighted_conv_real {w r : ℤ → ℝ} (h : RatioMajorant w r) {a b : ℤ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hA : Summable fun n => (w n * a n) ^ 2) (hB : Summable fun n => (w n * b n) ^ 2) :
    (∀ n, Summable fun k => a k * b (n - k)) ∧
    Summable (fun n => (w n * ∑' k, a k * b (n - k)) ^ 2) ∧
    ∑' n, (w n * ∑' k, a k * b (n - k)) ^ 2 ≤
      4 * ratioNormSq r * (∑' n, (w n * a n) ^ 2) * ∑' n, (w n * b n) ^ 2 := by
  have hw := h.w_pos
  set a' : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (a n)
  set b' : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (b n)
  have key := ennreal_weighted_conv h a' b'
  -- convert the three right-hand sums
  have hconvA : ∑' n, (ENNReal.ofReal (w n) * a' n) ^ 2 = ENNReal.ofReal (∑' n, (w n * a n) ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hA]
    congr 1; ext n
    rw [← ENNReal.ofReal_mul (hw n).le, ← ENNReal.ofReal_pow (mul_nonneg (hw n).le (ha n))]
  have hconvB : ∑' n, (ENNReal.ofReal (w n) * b' n) ^ 2 = ENNReal.ofReal (∑' n, (w n * b n) ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hB]
    congr 1; ext n
    rw [← ENNReal.ofReal_mul (hw n).le, ← ENNReal.ofReal_pow (mul_nonneg (hw n).le (hb n))]
  have hconvR : ∑' n, ENNReal.ofReal (r n) ^ 2 = ENNReal.ofReal (ratioNormSq r) := by
    rw [ratioNormSq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) h.r_sq]
    congr 1; ext n
    rw [← ENNReal.ofReal_pow (h.r_nonneg n)]
  rw [hconvA, hconvB, hconvR] at key
  have hRHS : 4 * ENNReal.ofReal (ratioNormSq r) * ENNReal.ofReal (∑' n, (w n * a n) ^ 2) *
      ENNReal.ofReal (∑' n, (w n * b n) ^ 2) =
      ENNReal.ofReal (4 * ratioNormSq r * (∑' n, (w n * a n) ^ 2) * ∑' n, (w n * b n) ^ 2) := by
    have h1 : 0 ≤ ratioNormSq r := tsum_nonneg fun n => sq_nonneg _
    have h2 : 0 ≤ ∑' n, (w n * a n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [hRHS] at key
  have hfin := lt_of_le_of_lt key ENNReal.ofReal_lt_top
  -- each inner convolution sum is finite
  have hinner_fin : ∀ n, ∑' k, a' k * b' (n - k) ≠ ⊤ := by
    intro n hn
    have : (ENNReal.ofReal (w n) * ∑' k, a' k * b' (n - k)) ^ 2 = ⊤ := by
      rw [hn, ENNReal.mul_top (by simpa using hw n), ENNReal.top_pow two_ne_zero]
    have hle : (ENNReal.ofReal (w n) * ∑' k, a' k * b' (n - k)) ^ 2 ≤
        ∑' n, (ENNReal.ofReal (w n) * ∑' k, a' k * b' (n - k)) ^ 2 :=
      ENNReal.le_tsum (f := fun n => (ENNReal.ofReal (w n) * ∑' k, a' k * b' (n - k)) ^ 2) n
    rw [this] at hle
    exact absurd (lt_of_le_of_lt hle hfin) (by simp)
  have hab : ∀ n k, a' k * b' (n - k) = ENNReal.ofReal (a k * b (n - k)) := by
    intro n k; rw [ENNReal.ofReal_mul (ha k)]
  have hsummable : ∀ n, Summable fun k => a k * b (n - k) := by
    intro n
    have h1 := ENNReal.summable_toReal (hinner_fin n)
    refine h1.congr fun k => ?_
    rw [hab, ENNReal.toReal_ofReal (mul_nonneg (ha k) (hb _))]
  have hinner_eq : ∀ n, ∑' k, a' k * b' (n - k) = ENNReal.ofReal (∑' k, a k * b (n - k)) := by
    intro n
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (ha k) (hb _)) (hsummable n)]
    congr 1; ext k; exact hab n k
  have hterm : ∀ n, (ENNReal.ofReal (w n) * ∑' k, a' k * b' (n - k)) ^ 2 =
      ENNReal.ofReal ((w n * ∑' k, a k * b (n - k)) ^ 2) := by
    intro n
    rw [hinner_eq, ← ENNReal.ofReal_mul (hw n).le, ← ENNReal.ofReal_pow]
    exact mul_nonneg (hw n).le (tsum_nonneg fun k => mul_nonneg (ha k) (hb _))
  simp_rw [hterm] at key hfin
  have hS : Summable (fun n => (w n * ∑' k, a k * b (n - k)) ^ 2) := by
    have h1 := ENNReal.summable_toReal hfin.ne
    refine h1.congr fun n => ?_
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  refine ⟨hsummable, hS, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hS] at key
  have hR0 : 0 ≤ 4 * ratioNormSq r * (∑' n, (w n * a n) ^ 2) * ∑' n, (w n * b n) ^ 2 := by
    have h1 : 0 ≤ ratioNormSq r := tsum_nonneg fun n => sq_nonneg _
    have h2 : 0 ≤ ∑' n, (w n * a n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
    have h3 : 0 ≤ ∑' n, (w n * b n) ^ 2 := tsum_nonneg fun n => sq_nonneg _
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp key

end NlsGge.Composition
