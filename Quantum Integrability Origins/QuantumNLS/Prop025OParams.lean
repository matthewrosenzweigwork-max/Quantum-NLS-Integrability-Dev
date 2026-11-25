import Mathlib

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O1:
the parameter arithmetic of eq:MP-parameters (mixed_propagation.tex:684-706).

With `α = 1/(56(d+1))`, `R = N^α`, `ε = N^{-1/8}`, `b = d+2`, `p = 28(d+1)+1`, a cut
`2R ≤ a ≤ 2R + c` (the printed `2R ≤ a < 2R + 2π/L`, `c = 2π/L`), `W_a = (1+a)^{d+1}`,
`Δ_N = ε + R^{-b} + N^{-1}` and
`η^g_N = C_p N R^{-2p} + D_p R^{-1} + C_b (1+a)/(N ε³)` (eq:MP-growing-mass),
every quantitative term of eq:MP-total-error,
`√η^g + W_a/N + W_a Δ_N + N^{-1/4} W_a^7 + a^{-1/4}`, is at most `C N^{-α/4}`
(`total_rate`), and `N ≥ C' W_a⁴` for all sufficiently large `N` (`large_N`).
Here `d = max({2} ∪ 𝓡) ≥ 2`; `α/4 = 1/(224(d+1))` is the printed exponent of eq:MP-main. -/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.Prop025OParams

/-- `α = 1/(56(d+1))`. -/
def alpha (d : ℕ) : ℝ := 1 / (56 * ((d : ℝ) + 1))

lemma alpha_pos (d : ℕ) : 0 < alpha d := by unfold alpha; positivity

lemma alpha_mul (d : ℕ) : alpha d * ((d : ℝ) + 1) = 1 / 56 := by
  unfold alpha; field_simp

lemma alpha_le (d : ℕ) (hd : 2 ≤ d) : alpha d ≤ 1 / 168 := by
  unfold alpha
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma alpha_four (d : ℕ) : alpha d / 4 = 1 / (224 * ((d : ℝ) + 1)) := by
  unfold alpha; field_simp; ring

/-- Monotonicity of `N^e` in the exponent for `N ≥ 1`. -/
lemma rpow_mono {N : ℝ} (hN : 1 ≤ N) {s t : ℝ} (h : s ≤ t) : N ^ s ≤ N ^ t :=
  Real.rpow_le_rpow_of_exponent_le hN h

lemma pow_nat_rpow {N : ℝ} (hN : 0 ≤ N) (x : ℝ) (k : ℕ) : (N ^ x) ^ k = N ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]

lemma mul_rpow_one {N : ℝ} (hN0 : 0 < N) (y : ℝ) : N * N ^ y = N ^ (1 + y) := by
  rw [Real.rpow_add hN0, Real.rpow_one]

lemma rpow_mul_one {N : ℝ} (hN0 : 0 < N) (y : ℝ) : N ^ y * N = N ^ (y + 1) := by
  rw [Real.rpow_add hN0, Real.rpow_one]

/-- `1 + a ≤ (3+c) N^α` on the cut. -/
lemma one_add_a_le {d : ℕ} {N a c : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c) (ha : a ≤ 2 * N ^ alpha d + c) :
    1 + a ≤ (3 + c) * N ^ alpha d := by
  have hx : 1 ≤ N ^ alpha d := Real.one_le_rpow hN (alpha_pos d).le
  nlinarith

/-- `W_a ≤ (3+c)^{d+1} N^{1/56}`. -/
lemma W_le {d : ℕ} {N a c : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c) (ha0 : 0 ≤ a)
    (ha : a ≤ 2 * N ^ alpha d + c) :
    (1 + a) ^ (d+1) ≤ (3 + c) ^ (d+1) * N ^ (1 / 56 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc (1 + a) ^ (d+1) ≤ ((3 + c) * N ^ alpha d) ^ (d+1) :=
        pow_le_pow_left₀ (by linarith) (one_add_a_le hN hc ha) _
    _ = (3 + c) ^ (d+1) * N ^ (1 / 56 : ℝ) := by
        rw [mul_pow, pow_nat_rpow hN0]
        congr 2
        push_cast
        exact alpha_mul d

/-- The growing-window discarded mass `η^g_N ≤ (C_p + D_p + C_b(3+c)) N^{-α}`. -/
lemma etag_le {d : ℕ} (hd : 2 ≤ d) {N a c Cp Dp Cb : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hCp : 0 ≤ Cp) (hDp : 0 ≤ Dp) (hCb : 0 ≤ Cb) (ha0 : 0 ≤ a) (ha : a ≤ 2 * N ^ alpha d + c) :
    Cp * N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹ + Dp * (N ^ alpha d)⁻¹ +
        Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3) ≤
      (Cp + Dp + Cb * (3 + c)) * N ^ (-alpha d) := by
  have hN0 : 0 < N := by linarith
  have hα := alpha_pos d
  have hαle := alpha_le d hd
  -- first term: N * N^{-(1+2α)} = N^{-2α}
  have h1 : N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹ = N ^ (-(2 * alpha d)) := by
    rw [pow_nat_rpow hN0.le, ← Real.rpow_neg hN0.le, mul_rpow_one hN0]
    congr 1
    push_cast
    linear_combination (-56 : ℝ) * alpha_mul d
  have h1' : N ^ (-(2 * alpha d)) ≤ N ^ (-alpha d) := rpow_mono hN (by linarith)
  have h2 : (N ^ alpha d)⁻¹ = N ^ (-alpha d) := (Real.rpow_neg hN0.le _).symm
  -- third term
  have h3 : Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3) ≤ Cb * (3 + c) * N ^ (-alpha d) := by
    have hden : N * (N ^ (-(1/8 : ℝ))) ^ 3 = N ^ (5/8 : ℝ) := by
      rw [pow_nat_rpow hN0.le, mul_rpow_one hN0]
      norm_num
    rw [hden, div_le_iff₀ (Real.rpow_pos_of_pos hN0 _), mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCb
    calc 1 + a ≤ (3 + c) * N ^ alpha d := one_add_a_le hN hc ha
      _ ≤ (3 + c) * (N ^ (-alpha d) * N ^ (5/8 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [← Real.rpow_add hN0]
          exact rpow_mono hN (by linarith)
  have hp : 0 ≤ N ^ (-alpha d) := (Real.rpow_pos_of_pos hN0 _).le
  calc _ = Cp * (N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹) + Dp * (N ^ alpha d)⁻¹ +
        Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3) := by ring
    _ ≤ Cp * N ^ (-alpha d) + Dp * N ^ (-alpha d) + Cb * (3 + c) * N ^ (-alpha d) := by
        rw [h1, h2]
        gcongr
    _ = _ := by ring

/-- **eq:MP-parameters**: every quantitative term of eq:MP-total-error is `≤ C N^{-α/4}`. -/
theorem total_rate (d : ℕ) (hd : 2 ≤ d) (c Cp Dp Cb : ℝ) (hc : 0 ≤ c) (hCp : 0 ≤ Cp)
    (hDp : 0 ≤ Dp) (hCb : 0 ≤ Cb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ a : ℝ, 2 * N ^ alpha d ≤ a → a ≤ 2 * N ^ alpha d + c →
      Real.sqrt (Cp * N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹ + Dp * (N ^ alpha d)⁻¹ +
          Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3)) +
        (1 + a) ^ (d+1) / N +
        (1 + a) ^ (d+1) * (N ^ (-(1/8 : ℝ)) + ((N ^ alpha d) ^ (d+2))⁻¹ + N⁻¹) +
        N ^ (-(1/4 : ℝ)) * ((1 + a) ^ (d+1)) ^ 7 +
        a ^ (-(1/4 : ℝ)) ≤ C * N ^ (-(alpha d / 4)) := by
  set K := (3 + c) ^ (d+1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Kη := Cp + Dp + Cb * (3 + c) with hKη
  have hKη0 : 0 ≤ Kη := by positivity
  refine ⟨Real.sqrt Kη + K + 3 * K + K ^ 7 + 1, by positivity, ?_⟩
  intro N hN a ha1 ha2
  have hN0 : 0 < N := by linarith
  have hα := alpha_pos d
  have hαle := alpha_le d hd
  have hx : 1 ≤ N ^ alpha d := Real.one_le_rpow hN hα.le
  have ha0 : 0 ≤ a := by linarith
  have hW := W_le (d := d) hN hc ha0 ha2
  have hW0 : 0 ≤ (1 + a) ^ (d+1) := by positivity
  have hq : 0 ≤ N ^ (-(alpha d / 4)) := (Real.rpow_pos_of_pos hN0 _).le
  have hmono : ∀ e : ℝ, e ≤ -(alpha d / 4) → N ^ e ≤ N ^ (-(alpha d / 4)) :=
    fun e he => rpow_mono hN he
  -- T1
  have hT1 : Real.sqrt (Cp * N * ((N ^ alpha d) ^ (2 * (28 * (d+1) + 1)))⁻¹ + Dp * (N ^ alpha d)⁻¹ +
      Cb * (1 + a) / (N * (N ^ (-(1/8 : ℝ))) ^ 3)) ≤ Real.sqrt Kη * N ^ (-(alpha d / 4)) := by
    calc _ ≤ Real.sqrt (Kη * N ^ (-alpha d)) :=
          Real.sqrt_le_sqrt (etag_le hd hN hc hCp hDp hCb ha0 ha2)
      _ = Real.sqrt Kη * N ^ (-(alpha d / 2)) := by
          rw [Real.sqrt_mul hKη0, Real.sqrt_eq_rpow (N ^ _), ← Real.rpow_mul hN0.le]
          congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmono _ (by linarith)) (Real.sqrt_nonneg _)
  -- T2
  have hT2 : (1 + a) ^ (d+1) / N ≤ K * N ^ (-(alpha d / 4)) := by
    rw [div_le_iff₀ hN0]
    calc (1 + a) ^ (d+1) ≤ K * N ^ (1 / 56 : ℝ) := hW
      _ ≤ K * (N ^ (-(alpha d / 4)) * N) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          rw [rpow_mul_one hN0]
          exact rpow_mono hN (by linarith)
      _ = _ := by ring
  -- T3
  have hT3 : (1 + a) ^ (d+1) * (N ^ (-(1/8 : ℝ)) + ((N ^ alpha d) ^ (d+2))⁻¹ + N⁻¹) ≤
      3 * K * N ^ (-(alpha d / 4)) := by
    have e1 : N ^ (1/56 : ℝ) * N ^ (-(1/8 : ℝ)) ≤ N ^ (-(alpha d / 4)) := by
      rw [← Real.rpow_add hN0]; exact hmono _ (by linarith)
    have e2 : N ^ (1/56 : ℝ) * ((N ^ alpha d) ^ (d+2))⁻¹ ≤ N ^ (-(alpha d / 4)) := by
      rw [pow_nat_rpow hN0.le, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]
      apply hmono
      have := alpha_mul d
      push_cast
      nlinarith
    have e3 : N ^ (1/56 : ℝ) * N⁻¹ ≤ N ^ (-(alpha d / 4)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; exact hmono _ (by linarith)
    have hs : 0 ≤ N ^ (-(1/8 : ℝ)) + ((N ^ alpha d) ^ (d+2))⁻¹ + N⁻¹ := by positivity
    calc _ ≤ K * N ^ (1 / 56 : ℝ) * (N ^ (-(1/8 : ℝ)) + ((N ^ alpha d) ^ (d+2))⁻¹ + N⁻¹) :=
          mul_le_mul_of_nonneg_right hW hs
      _ = K * (N ^ (1/56 : ℝ) * N ^ (-(1/8 : ℝ)) + N ^ (1/56 : ℝ) * ((N ^ alpha d) ^ (d+2))⁻¹ +
            N ^ (1/56 : ℝ) * N⁻¹) := by ring
      _ ≤ K * (N ^ (-(alpha d / 4)) + N ^ (-(alpha d / 4)) + N ^ (-(alpha d / 4))) := by
          gcongr
      _ = _ := by ring
  -- T4
  have hT4 : N ^ (-(1/4 : ℝ)) * ((1 + a) ^ (d+1)) ^ 7 ≤ K ^ 7 * N ^ (-(alpha d / 4)) := by
    calc _ ≤ N ^ (-(1/4 : ℝ)) * (K * N ^ (1 / 56 : ℝ)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW _) (Real.rpow_pos_of_pos hN0 _).le
      _ = K ^ 7 * (N ^ (-(1/4 : ℝ)) * N ^ ((1/56 : ℝ) * (7 : ℕ))) := by
          rw [mul_pow, pow_nat_rpow hN0.le]; ring
      _ ≤ K ^ 7 * N ^ (-(alpha d / 4)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.rpow_add hN0]; apply hmono; push_cast; linarith
  -- T5
  have hT5 : a ^ (-(1/4 : ℝ)) ≤ N ^ (-(alpha d / 4)) := by
    have ha' : N ^ alpha d ≤ a := by linarith
    calc a ^ (-(1/4 : ℝ)) ≤ (N ^ alpha d) ^ (-(1/4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 _) ha' (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hN0.le]; congr 1; ring
  calc _ ≤ Real.sqrt Kη * N ^ (-(alpha d / 4)) + K * N ^ (-(alpha d / 4)) +
        3 * K * N ^ (-(alpha d / 4)) + K ^ 7 * N ^ (-(alpha d / 4)) + N ^ (-(alpha d / 4)) := by
        gcongr
    _ = _ := by ring

/-- `N ≥ C' W_a⁴` for all sufficiently large `N` (uniformly on the cut window). -/
theorem large_N (d : ℕ) (hd : 2 ≤ d) (c C' : ℝ) (hc : 0 ≤ c) (hC' : 0 ≤ C') :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ a : ℝ, 2 * N ^ alpha d ≤ a →
      a ≤ 2 * N ^ alpha d + c → C' * ((1 + a) ^ (d+1)) ^ 4 ≤ N := by
  set K := C' * ((3 + c) ^ (d+1)) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (K ^ 2), le_max_left _ _, ?_⟩
  intro N hN a ha1 ha2
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hα := alpha_pos d
  have hx : 0 ≤ N ^ alpha d := (Real.rpow_pos_of_pos hN0 _).le
  have ha0 : 0 ≤ a := by linarith
  have hW := W_le (d := d) hN1 hc ha0 ha2
  have hW0 : 0 ≤ (1 + a) ^ (d+1) := by positivity
  have hsq : K ≤ N ^ (1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le ((le_max_right _ _).trans hN)
  calc C' * ((1 + a) ^ (d+1)) ^ 4 ≤ C' * ((3 + c) ^ (d+1) * N ^ (1 / 56 : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW 4) hC'
    _ = K * N ^ ((1/56 : ℝ) * (4 : ℕ)) := by rw [mul_pow, pow_nat_rpow hN0.le]; ring
    _ ≤ N ^ (1/2 : ℝ) * N ^ (1/2 : ℝ) := by
        apply mul_le_mul hsq (rpow_mono hN1 (by push_cast; norm_num))
          (Real.rpow_pos_of_pos hN0 _).le (Real.rpow_pos_of_pos hN0 _).le
    _ = N := by rw [← Real.rpow_add hN0]; norm_num

end QuantumNLS.Prop025OParams

#print axioms QuantumNLS.Prop025OParams.total_rate
#print axioms QuantumNLS.Prop025OParams.large_N
#print axioms QuantumNLS.Prop025OParams.alpha_four
