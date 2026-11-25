import Mathlib

/-!
# Mo2 (part B1): extended-nonnegative sequence tools for the Lyapunov-Schmidt estimate

Piece Mo2 of the E01 plan (`campaign/E01_PLAN.md` §6.12), Molnár arXiv:1403.1369, Theorem 5 and
Lemmas 5-10.  Parts B1-B4 prove the Fourier-side localization (`molnar_ls_core`, B4) with explicit
Molnár constants.  Everything is done on sequences `ℤ → ℂ` with sums in `ℝ≥0∞` (no summability
side conditions): Cauchy-Schwarz (`cs`, `cs_weighted`), Young's inequality (`young`, `young'`),
the lattice sums `Σ ⟨k⟩⁻² ≤ 3`, `Σ_{a ≠ 0} a⁻² ≤ 4` (`La_sum`, `Lc_sum`), Minkowski, and the shifted
norm `ν_n(x) = (Σ_m ⟨m+n⟩² |x_m|²)^{1/2}` with the Hankel action `(c ⋆ y)_m = Σ_l c_{m+l} y_l`
(`Q_hk`, `nu_hk`: Molnár Lemma 5 in squared form).  Weight: `⟨k⟩ = 1 + |k|` (Molnár's bracket,
which is submultiplicative).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

namespace NlsGge.GK38.Mo2

noncomputable section


def eW (k : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 + |(k : ℝ)|)
def iW (k : ℤ) : ℝ≥0∞ := ENNReal.ofReal (1 / (1 + |(k : ℝ)|))

theorem eW_ne_zero (k : ℤ) : eW k ≠ 0 := by
  unfold eW; simp; positivity
theorem eW_ne_top (k : ℤ) : eW k ≠ ⊤ := ENNReal.ofReal_ne_top
theorem iW_ne_top (k : ℤ) : iW k ≠ ⊤ := ENNReal.ofReal_ne_top
theorem iW_mul_eW (k : ℤ) : iW k * eW k = 1 := by
  unfold iW eW
  rw [← ENNReal.ofReal_mul (by positivity)]
  have : (0:ℝ) < 1 + |(k : ℝ)| := by positivity
  rw [one_div, inv_mul_cancel₀ this.ne']; simp
theorem eW_mul_iW (k : ℤ) : eW k * iW k = 1 := by rw [mul_comm]; exact iW_mul_eW k
theorem eW_neg (k : ℤ) : eW (-k) = eW k := by unfold eW; simp
theorem eW_add_le (a b : ℤ) : eW (a + b) ≤ eW a * eW b := by
  unfold eW
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have := abs_add_le (a : ℝ) (b : ℝ)
  nlinarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ)]

theorem two_mul_le_sq (x y : ℝ≥0∞) : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by
  by_cases hx : x = ⊤
  · subst hx; simp
  by_cases hy : y = ⊤
  · subst hy; simp
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  have := two_mul_le_add_sq (x : ℝ≥0) y
  rw [← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_add,
    show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by simp, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  calc 2 * (x * y) = 2 * x * y := by ring
    _ ≤ _ := this

/-- Cauchy-Schwarz for nonnegative extended sequences. -/
theorem cs {ι : Type*} (u v : ι → ℝ≥0∞) :
    (∑' i, u i * v i) ^ 2 ≤ (∑' i, u i ^ 2) * ∑' i, v i ^ 2 := by
  have h1 : (∑' i, u i * v i) ^ 2 = ∑' i, ∑' j, (u i * v i) * (u j * v j) := by
    rw [sq, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  have h2 : (∑' i, u i ^ 2) * ∑' i, v i ^ 2 = ∑' i, ∑' j, u i ^ 2 * v j ^ 2 := by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  have h3 : 2 * (∑' i, ∑' j, (u i * v i) * (u j * v j)) ≤
      2 * (∑' i, ∑' j, u i ^ 2 * v j ^ 2) := by
    have e1 : 2 * (∑' i, ∑' j, (u i * v i) * (u j * v j)) =
        ∑' i, ∑' j, 2 * ((u i * v i) * (u j * v j)) := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun i => ?_
      rw [← ENNReal.tsum_mul_left]
    have e2 : ∑' i, ∑' j, 2 * ((u i * v i) * (u j * v j)) ≤
        ∑' i, ∑' j, (u i ^ 2 * v j ^ 2 + u j ^ 2 * v i ^ 2) := by
      refine ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ?_
      have := two_mul_le_sq (u i * v j) (u j * v i)
      calc 2 * ((u i * v i) * (u j * v j)) = 2 * ((u i * v j) * (u j * v i)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have e3 : ∑' i, ∑' j, (u i ^ 2 * v j ^ 2 + u j ^ 2 * v i ^ 2) =
        2 * (∑' i, ∑' j, u i ^ 2 * v j ^ 2) := by
      have : ∑' i, ∑' j, (u i ^ 2 * v j ^ 2 + u j ^ 2 * v i ^ 2) =
          ∑' i, ∑' j, u i ^ 2 * v j ^ 2 + ∑' i, ∑' j, u j ^ 2 * v i ^ 2 := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun i => ?_
        rw [ENNReal.tsum_add]
      rw [this, ENNReal.tsum_comm (f := fun i j => u j ^ 2 * v i ^ 2), two_mul]
    rw [e1]; exact e2.trans e3.le
  rw [h1, h2]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h3


/-- Weighted Cauchy-Schwarz for nonnegative extended sequences. -/
theorem cs_weighted {ι : Type*} (b x : ι → ℝ≥0∞) :
    (∑' i, b i * x i) ^ 2 ≤ (∑' i, b i) * ∑' i, b i * x i ^ 2 := by
  have h1 : (∑' i, b i * x i) ^ 2 = ∑' i, ∑' j, (b i * x i) * (b j * x j) := by
    rw [sq, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  have e2 : ∑' i, ∑' j, b i * b j * x j ^ 2 = (∑' i, b i) * ∑' i, b i * x i ^ 2 := by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have e1 : ∑' i, ∑' j, b i * b j * x i ^ 2 = (∑' i, b i) * ∑' i, b i * x i ^ 2 := by
    have : ∀ i, ∑' j, b i * b j * x i ^ 2 = (b i * x i ^ 2) * ∑' j, b j := fun i => by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun j => by ring
    rw [tsum_congr this, ENNReal.tsum_mul_right, mul_comm]
  have h3 : 2 * (∑' i, ∑' j, (b i * x i) * (b j * x j)) ≤
      2 * ((∑' i, b i) * ∑' i, b i * x i ^ 2) := by
    have e0 : 2 * (∑' i, ∑' j, (b i * x i) * (b j * x j)) =
        ∑' i, ∑' j, 2 * ((b i * x i) * (b j * x j)) := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun i => ?_
      rw [← ENNReal.tsum_mul_left]
    have ee : ∑' i, ∑' j, 2 * ((b i * x i) * (b j * x j)) ≤
        ∑' i, ∑' j, (b i * b j * x i ^ 2 + b i * b j * x j ^ 2) := by
      refine ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ?_
      have := two_mul_le_sq (x i) (x j)
      calc 2 * ((b i * x i) * (b j * x j)) = (b i * b j) * (2 * (x i * x j)) := by ring
        _ ≤ (b i * b j) * (x i ^ 2 + x j ^ 2) := by gcongr
        _ = _ := by ring
    have e3 : ∑' i, ∑' j, (b i * b j * x i ^ 2 + b i * b j * x j ^ 2) =
        2 * ((∑' i, b i) * ∑' i, b i * x i ^ 2) := by
      have : ∑' i, ∑' j, (b i * b j * x i ^ 2 + b i * b j * x j ^ 2) =
          ∑' i, ∑' j, b i * b j * x i ^ 2 + ∑' i, ∑' j, b i * b j * x j ^ 2 := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun i => ?_
        rw [ENNReal.tsum_add]
      rw [this, e1, e2, two_mul]
    rw [e0]; exact ee.trans e3.le
  rw [h1]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h3


theorem young (a b : ℤ → ℝ≥0∞) :
    ∑' m : ℤ, (∑' l : ℤ, a (m + l) * b l) ^ 2 ≤ (∑' l, b l) ^ 2 * ∑' k, a k ^ 2 := by
  have h1 : ∀ m : ℤ, (∑' l : ℤ, a (m + l) * b l) ^ 2 ≤
      (∑' l, b l) * ∑' l, b l * a (m + l) ^ 2 := by
    intro m
    have := cs_weighted b (fun l => a (m + l))
    simpa only [mul_comm] using this
  calc ∑' m : ℤ, (∑' l : ℤ, a (m + l) * b l) ^ 2
      ≤ ∑' m : ℤ, (∑' l, b l) * ∑' l, b l * a (m + l) ^ 2 := ENNReal.tsum_le_tsum h1
    _ = (∑' l, b l) * ∑' m : ℤ, ∑' l, b l * a (m + l) ^ 2 := by rw [ENNReal.tsum_mul_left]
    _ = (∑' l, b l) * ∑' l, ∑' m : ℤ, b l * a (m + l) ^ 2 := by rw [ENNReal.tsum_comm]
    _ = (∑' l, b l) * ∑' l, b l * ∑' k, a k ^ 2 := by
        congr 1
        refine tsum_congr fun l => ?_
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (Equiv.addRight l).tsum_eq (fun k => a k ^ 2)
    _ = (∑' l, b l) ^ 2 * ∑' k, a k ^ 2 := by
        rw [ENNReal.tsum_mul_right]; ring

/-- Young's inequality in the other order (`a ∈ ℓ¹`, `b ∈ ℓ²`). -/
theorem young' (a b : ℤ → ℝ≥0∞) :
    ∑' m : ℤ, (∑' l : ℤ, a (m + l) * b l) ^ 2 ≤ (∑' k, a k) ^ 2 * ∑' l, b l ^ 2 := by
  have e : ∀ m : ℤ, ∑' l : ℤ, a (m + l) * b l = ∑' j : ℤ, b (-m + j) * a j := by
    intro m
    rw [← (Equiv.addLeft m).tsum_eq (fun j => b (-m + j) * a j)]
    refine tsum_congr fun l => ?_
    simp [mul_comm]
  have h := young b a
  calc ∑' m : ℤ, (∑' l : ℤ, a (m + l) * b l) ^ 2
      = ∑' m : ℤ, (∑' j : ℤ, b (-m + j) * a j) ^ 2 := tsum_congr fun m => by rw [e m]
    _ = ∑' m : ℤ, (fun m' : ℤ => (∑' j : ℤ, b (m' + j) * a j) ^ 2) (-m) := rfl
    _ = ∑' m' : ℤ, (∑' j : ℤ, b (m' + j) * a j) ^ 2 :=
        (Equiv.neg ℤ).tsum_eq (fun m' : ℤ => (∑' j : ℤ, b (m' + j) * a j) ^ 2)
    _ ≤ _ := h


/-! ### Lattice sums -/

theorem tel_real (M : ℕ) :
    ∑ i ∈ Finset.range M, (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 - 1 / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

theorem tel_sum :
    ∑' i : ℕ, ENNReal.ofReal (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) ≤ 1 := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro M
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), tel_real]
  calc ENNReal.ofReal (1 - 1 / ((M : ℝ) + 1)) ≤ ENNReal.ofReal 1 := by
        apply ENNReal.ofReal_le_ofReal
        have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
        linarith
    _ = 1 := by simp

theorem H1_sum :
    ∑' i : ℕ, ENNReal.ofReal (1 / (((i : ℝ) + 1) ^ 2)) ≤ 2 := by
  calc ∑' i : ℕ, ENNReal.ofReal (1 / (((i : ℝ) + 1) ^ 2))
      ≤ ∑' i : ℕ, 2 * ENNReal.ofReal (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
    _ = 2 * ∑' i : ℕ, ENNReal.ofReal (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := ENNReal.tsum_mul_left
    _ ≤ 2 * 1 := by gcongr; exact tel_sum
    _ = 2 := by simp

theorem H2_sum :
    ∑' i : ℕ, ENNReal.ofReal (1 / (((i : ℝ) + 2) ^ 2)) ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun i => ?_) tel_sum
  apply ENNReal.ofReal_le_ofReal
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith


theorem iW_sq (k : ℤ) : iW k ^ 2 = ENNReal.ofReal (1 / (1 + |(k : ℝ)|) ^ 2) := by
  unfold iW
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [div_pow, one_pow]

theorem iW_sq_nat (i : ℕ) : iW (i : ℤ) ^ 2 = ENNReal.ofReal (1 / (((i : ℝ) + 1) ^ 2)) := by
  rw [iW_sq]
  have : (1 + |((i : ℤ) : ℝ)|) = (i : ℝ) + 1 := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg i)]; ring
  rw [this]

theorem iW_sq_neg (i : ℕ) :
    iW (-((i : ℤ) + 1)) ^ 2 = ENNReal.ofReal (1 / (((i : ℝ) + 2) ^ 2)) := by
  rw [iW_sq]
  have : (1 + |((-((i : ℤ) + 1) : ℤ) : ℝ)|) = (i : ℝ) + 2 := by
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]; ring
  rw [this]

/-- `Σ_k ⟨k⟩⁻² ≤ 3`. -/
theorem La_sum : ∑' k : ℤ, iW k ^ 2 ≤ 3 := by
  have h1 : Summable fun n : ℕ => iW (n : ℤ) ^ 2 := ENNReal.summable
  have h2 : Summable fun n : ℕ => iW (-((n : ℤ) + 1)) ^ 2 := ENNReal.summable
  have hsplit : ∑' k : ℤ, iW k ^ 2 = ∑' n : ℕ, iW (n : ℤ) ^ 2 + ∑' n : ℕ, iW (-((n : ℤ) + 1)) ^ 2 :=
    tsum_of_nat_of_neg_add_one h1 h2
  rw [hsplit]
  have e1 : ∑' n : ℕ, iW (n : ℤ) ^ 2 ≤ 2 := by
    rw [tsum_congr iW_sq_nat]; exact H1_sum
  have e2 : ∑' n : ℕ, iW (-((n : ℤ) + 1)) ^ 2 ≤ 1 := by
    rw [tsum_congr iW_sq_neg]; exact H2_sum
  have := add_le_add e1 e2
  refine this.trans ?_
  norm_num

theorem Lc_term_nat (i : ℕ) :
    ENNReal.ofReal (1 / (((i + 1 : ℕ) : ℤ) : ℝ) ^ 2) = ENNReal.ofReal (1 / (((i : ℝ) + 1) ^ 2)) := by
  push_cast; rfl

theorem Lc_term_neg (i : ℕ) :
    ENNReal.ofReal (1 / ((-((i : ℤ) + 1) : ℤ) : ℝ) ^ 2) = ENNReal.ofReal (1 / (((i : ℝ) + 1) ^ 2)) := by
  push_cast; congr 2; ring

/-- `Σ_{a ≠ 0} a⁻² ≤ 4`. -/
theorem Lc_sum : ∑' a : ℤ, ENNReal.ofReal (1 / (a : ℝ) ^ 2) ≤ 4 := by
  have h1 : Summable fun n : ℕ => ENNReal.ofReal (1 / ((n : ℤ) : ℝ) ^ 2) := ENNReal.summable
  have h2 : Summable fun n : ℕ => ENNReal.ofReal (1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) :=
    ENNReal.summable
  have hsplit : ∑' a : ℤ, ENNReal.ofReal (1 / (a : ℝ) ^ 2) =
      ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℤ) : ℝ) ^ 2) +
      ∑' n : ℕ, ENNReal.ofReal (1 / ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) :=
    tsum_of_nat_of_neg_add_one h1 h2
  have hz := tsum_eq_zero_add' (f := fun n : ℕ => ENNReal.ofReal (1 / ((n : ℤ) : ℝ) ^ 2))
    ENNReal.summable
  rw [hsplit, tsum_congr Lc_term_neg, hz]
  have h0 : ENNReal.ofReal (1 / (((0 : ℕ) : ℤ) : ℝ) ^ 2) = 0 := by simp
  rw [h0, zero_add, tsum_congr Lc_term_nat]
  calc _ ≤ (2 : ℝ≥0∞) + 2 := add_le_add H1_sum H1_sum
    _ = 4 := by norm_num


/-- Minkowski for `ℓ²` of extended sequences. -/
theorem minkowski (f g : ℤ → ℝ≥0∞) :
    (∑' m, (f m + g m) ^ 2) ^ (1 / 2 : ℝ) ≤
      (∑' m, f m ^ 2) ^ (1 / 2 : ℝ) + (∑' m, g m ^ 2) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := MeasureTheory.Measure.count) (p := 2)
    (f := f) (g := g) (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)
    (by norm_num)
  simp only [MeasureTheory.lintegral_count, Pi.add_apply] at h
  simpa [ENNReal.rpow_two] using h



/-! ### The shifted norm -/

def Q (n : ℤ) (x : ℤ → ℂ) : ℝ≥0∞ := ∑' m, (eW (m + n) * ‖x m‖ₑ) ^ 2

def nu (n : ℤ) (x : ℤ → ℂ) : ℝ≥0∞ := (Q n x) ^ (1 / 2 : ℝ)

theorem sq_rpow_half (X : ℝ≥0∞) : (X ^ 2) ^ (1 / 2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem nu_sq (n : ℤ) (x : ℤ → ℂ) : nu n x ^ 2 = Q n x := rpow_half_sq _

theorem nu_mono (n : ℤ) (x y : ℤ → ℂ) (h : ∀ m, ‖x m‖ₑ ≤ ‖y m‖ₑ) : nu n x ≤ nu n y := by
  unfold nu Q
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_le_tsum fun m => by gcongr; exact h m

theorem nu_add (n : ℤ) (x y : ℤ → ℂ) : nu n (x + y) ≤ nu n x + nu n y := by
  have h1 : nu n (x + y) ≤ (∑' m, (eW (m + n) * ‖x m‖ₑ + eW (m + n) * ‖y m‖ₑ) ^ 2) ^ (1 / 2 : ℝ) := by
    unfold nu Q
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    refine ENNReal.tsum_le_tsum fun m => ?_
    gcongr
    rw [← mul_add]
    gcongr
    simpa using enorm_add_le (x m) (y m)
  refine h1.trans ?_
  exact minkowski (fun m => eW (m + n) * ‖x m‖ₑ) (fun m => eW (m + n) * ‖y m‖ₑ)

theorem nu_smul (n : ℤ) (c : ℂ) (x : ℤ → ℂ) : nu n (c • x) = ‖c‖ₑ * nu n x := by
  unfold nu Q
  have : ∀ m, (eW (m + n) * ‖(c • x) m‖ₑ) ^ 2 = ‖c‖ₑ ^ 2 * (eW (m + n) * ‖x m‖ₑ) ^ 2 := by
    intro m
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
    ring
  rw [tsum_congr this, ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    sq_rpow_half]

theorem nu_point (n : ℤ) (x : ℤ → ℂ) (m : ℤ) : eW (m + n) * ‖x m‖ₑ ≤ nu n x := by
  have h : (eW (m + n) * ‖x m‖ₑ) ^ 2 ≤ Q n x :=
    ENNReal.le_tsum (f := fun m => (eW (m + n) * ‖x m‖ₑ) ^ 2) m
  have := ENNReal.rpow_le_rpow h (show (0:ℝ) ≤ 1 / 2 by norm_num)
  rwa [sq_rpow_half] at this

/-- Hankel action `(c ⋆ y) m = Σ_l c(m+l) y(l)`. -/
def hk (c y : ℤ → ℂ) (m : ℤ) : ℂ := ∑' l, c (m + l) * y l

/-- `S c = Σ_k (⟨k⟩ |c_k|)²`. -/
def SW (c : ℤ → ℂ) : ℝ≥0∞ := ∑' k, (eW k * ‖c k‖ₑ) ^ 2

theorem Q_hk (n : ℤ) (c y : ℤ → ℂ) :
    Q n (hk c y) ≤ SW c * (∑' l, eW (l - n) * ‖y l‖ₑ) ^ 2 := by
  have hpt : ∀ m, eW (m + n) * ‖hk c y m‖ₑ ≤
      ∑' l, (eW (m + l) * ‖c (m + l)‖ₑ) * (eW (l - n) * ‖y l‖ₑ) := by
    intro m
    calc eW (m + n) * ‖hk c y m‖ₑ
        ≤ eW (m + n) * ∑' l, ‖c (m + l)‖ₑ * ‖y l‖ₑ := by
          gcongr
          refine (enorm_tsum_le_tsum_enorm).trans ?_
          exact le_of_eq (tsum_congr fun l => enorm_mul _ _)
      _ = ∑' l, eW (m + n) * (‖c (m + l)‖ₑ * ‖y l‖ₑ) := ENNReal.tsum_mul_left.symm
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          have h1 : eW (m + n) ≤ eW (m + l) * eW (l - n) := by
            have := eW_add_le (m + l) (n - l)
            rw [show m + l + (n - l) = m + n by ring] at this
            rwa [show n - l = -(l - n) by ring, eW_neg] at this
          calc eW (m + n) * (‖c (m + l)‖ₑ * ‖y l‖ₑ)
              ≤ (eW (m + l) * eW (l - n)) * (‖c (m + l)‖ₑ * ‖y l‖ₑ) := by gcongr
            _ = _ := by ring
  calc Q n (hk c y) ≤ ∑' m, (∑' l, (eW (m + l) * ‖c (m + l)‖ₑ) * (eW (l - n) * ‖y l‖ₑ)) ^ 2 :=
        ENNReal.tsum_le_tsum fun m => by gcongr; exact hpt m
    _ ≤ (∑' l, eW (l - n) * ‖y l‖ₑ) ^ 2 * ∑' k, (eW k * ‖c k‖ₑ) ^ 2 :=
        young (fun k => eW k * ‖c k‖ₑ) (fun l => eW (l - n) * ‖y l‖ₑ)
    _ = _ := by unfold SW; ring

theorem nu_hk (n : ℤ) (c y : ℤ → ℂ) :
    nu n (hk c y) ≤ (SW c) ^ (1 / 2 : ℝ) * ∑' l, eW (l - n) * ‖y l‖ₑ := by
  calc nu n (hk c y) = (Q n (hk c y)) ^ (1 / 2 : ℝ) := rfl
    _ ≤ (SW c * (∑' l, eW (l - n) * ‖y l‖ₑ) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (Q_hk n c y) (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]

end

end NlsGge.GK38.Mo2
