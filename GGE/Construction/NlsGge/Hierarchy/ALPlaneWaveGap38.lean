import NlsGge.Hierarchy.ALBoundaryKappa38
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Batch 38, L11 plane-gap: `D:eq:planegap` (paper/v2.tex l.2313-2319).
For `α_j = h t e^{2πi k j h}` (`h = 1/L`, `0 ≤ t`, `h t < 1`, `θ_k = π k h`) the monodromy is
`M(z) = (-1)^k B(z)^L` with constant `B`, so `½ tr M(e^{iθ}) = (-1)^k T_L(c)`,
`c = cos(θ - θ_k)/√(1 - h²t²)`, and `κ(θ) = arcosh (max 1 |c|)`, `v_h(λ) = h⁻¹ κ(hλ)`.
The formula holds for every real `θ` (hence in any principal period). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Polynomial.Chebyshev

/-! ### Real Chebyshev facts -/

theorem abs_T_real_neg38 (n : ℕ) (x : ℝ) :
    |(T ℝ n).eval (-x)| = |(T ℝ n).eval x| := by
  rw [T_eval_neg]
  rcases Int.units_eq_one_or (n : ℤ).negOnePow with h | h <;> simp [h]

theorem T_real_abs38 (n : ℕ) (c : ℝ) :
    |(T ℝ n).eval c| = |(T ℝ n).eval (|c|)| := by
  rcases abs_choice c with h | h <;> rw [h]
  exact (abs_T_real_neg38 n c).symm

theorem abs_T_real_le_one_of_abs_le38 (n : ℕ) {c : ℝ} (hc : |c| ≤ 1) :
    |(T ℝ n).eval c| ≤ 1 := by
  obtain ⟨x, -, -, rfl⟩ : ∃ x : ℝ, 0 ≤ x ∧ x ≤ Real.pi ∧ Real.cos x = c :=
    ⟨Real.arccos c, Real.arccos_nonneg c, Real.arccos_le_pi c,
      Real.cos_arccos (abs_le.mp hc).1 (abs_le.mp hc).2⟩
  rw [T_real_cos]
  exact Real.abs_cos_le_one _

/-- For `|c| ≥ 1` write `|c| = cosh y`; then `|T_n c| = cosh (n y)`. -/
theorem abs_T_real_eq_cosh38 (n : ℕ) {c : ℝ} (hc : 1 ≤ |c|) :
    |(T ℝ n).eval c| = Real.cosh (n * Real.arcosh |c|) := by
  rw [T_real_abs38]
  have h := Real.cosh_arcosh hc
  conv_lhs => rw [← h]
  rw [T_real_cosh]
  push_cast
  exact abs_of_pos (Real.cosh_pos _)

theorem one_lt_abs_T_real38 (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 1 < |c|) :
    1 < |(T ℝ n).eval c| := by
  rw [abs_T_real_eq_cosh38 n hc.le]
  have h1 := Real.arcosh_pos hc
  have : (0 : ℝ) < n * Real.arcosh |c| := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact Real.one_lt_cosh.mpr this.ne'

/-- `|T_n(c)| ≤ 1 ↔ |c| ≤ 1` for real `c`, `n ≥ 1`. -/
theorem abs_T_real_le_one_iff38 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    |(T ℝ n).eval c| ≤ 1 ↔ |c| ≤ 1 := by
  constructor
  · intro h
    by_contra h'
    exact absurd (one_lt_abs_T_real38 n hn (not_le.mp h')) (not_lt.mpr h)
  · exact abs_T_real_le_one_of_abs_le38 n

/-- `arcosh (max 1 |T_n c|) = n * arcosh (max 1 |c|)`. -/
theorem arcosh_max_abs_T_real38 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    Real.arcosh (max 1 |(T ℝ n).eval c|) = n * Real.arcosh (max 1 |c|) := by
  rcases le_total |c| 1 with h | h
  · rw [max_eq_left h, max_eq_left ((abs_T_real_le_one_iff38 n hn c).mpr h), Real.arcosh_zero]
    simp
  · rw [max_eq_right h, max_eq_right (by rw [abs_T_real_eq_cosh38 n h]; exact Real.one_le_cosh _),
      abs_T_real_eq_cosh38 n h]
    exact Real.arcosh_cosh (by positivity [Real.arcosh_nonneg h])


/-! ### Plane-wave data and the constant matrix -/

/-- The plane wave `α_j = h t e^{2πi k j h}` with `h = 1/L`, `j` read as `j.val ∈ [0, L)`. -/
def alPlaneWave38 (L : ℕ) (k : ℤ) (t : ℝ) : ZMod L → ℂ :=
  fun j => ((t / (L : ℝ) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((j.val : ℕ) : ℂ) / (L : ℂ))

/-- The constant matrix `B(z) = (1-s²)^{-1/2} [[z e^{-iθ}, s e^{-iθ}], [s e^{iθ}, z⁻¹ e^{iθ}]]`
(`s = h t`, `θ = θ_k = π k h`). -/
def alPlaneB38 (s θ : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * z * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹,
     ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * s * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹;
     ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * s * Complex.exp ((θ : ℂ) * Complex.I),
     ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * z⁻¹ * Complex.exp ((θ : ℂ) * Complex.I)]

/-- Gauge matrix `D_n⁻¹ = diag(u^n, u^{-n})`, `u = e^{iθ}`. -/
def alPlaneGaugeInv38 (u : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u ^ n, 0; 0, (u ^ n)⁻¹]

/-- Gauge matrix `D_n = diag(u^{-n}, u^n)`. -/
def alPlaneGauge38 (u : ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(u ^ n)⁻¹, 0; 0, u ^ n]

theorem alPlaneGauge_mul38 {u : ℂ} (hu : u ≠ 0) (n : ℕ) :
    alPlaneGauge38 u n * alPlaneGaugeInv38 u n = 1 := by
  unfold alPlaneGauge38 alPlaneGaugeInv38
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu]

/-- Gauge conjugation of one step: `A_n(z) = D_{n+1}⁻¹ B(z) D_n`. -/
theorem alPlaneTransfer_step38 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {u : ℂ} (hu0 : u ≠ 0)
    (hun : ‖u‖ = 1) (z : ℂ) (n : ℕ) :
    alTransfer38 (((s : ℝ) : ℂ) * (u ^ 2) ^ n) z =
      alPlaneGaugeInv38 u (n + 1) *
        !![((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * z * u⁻¹,
           ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * s * u⁻¹;
           ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * s * u,
           ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹ * z⁻¹ * u] * alPlaneGauge38 u n := by
  have hstar : star u = u⁻¹ := by
    have : u * star u = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hun]; simp
    exact (eq_inv_of_mul_eq_one_right this)
  have hnorm : ‖((s : ℝ) : ℂ) * (u ^ 2) ^ n‖ = s := by
    rw [norm_mul, norm_pow, norm_pow, hun, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    simp
  have hsq : ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 - s ^ 2 := by nlinarith
    exact_mod_cast (Real.sqrt_pos.mpr this).ne'
  unfold alTransfer38 alPlaneGaugeInv38 alPlaneGauge38
  rw [hnorm]
  have hstar2 : star (((s : ℝ) : ℂ) * (u ^ 2) ^ n) = ((s : ℝ) : ℂ) * (u⁻¹ ^ 2) ^ n := by
    rw [star_mul', star_pow, star_pow, hstar]
    simp
  rw [hstar2]
  have e1 : (u ^ 2) ^ n = (u ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (u⁻¹ ^ 2) ^ n = ((u ^ n)⁻¹) ^ 2 := by simp only [inv_pow, e1]
  have hun0 : u ^ n ≠ 0 := pow_ne_zero _ hu0
  rw [e1, e2]
  simp only [pow_succ u n]
  generalize u ^ n = w at *
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, pow_succ] <;> field_simp


/-! ### Trace of powers of a unimodular `2×2` matrix: Chebyshev -/

theorem fin_two_sq38 (a b c d : ℂ) (h : a * d - b * c = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 =
      (a + d) • (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ) - 1 := by
  rw [pow_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;> first | ring1 | linear_combination h | linear_combination -h

theorem trace_pow_chebyshev38 (a b c d : ℂ) (x : ℝ) (hdet : a * d - b * c = 1)
    (htr : a + d = 2 * (x : ℂ)) (n : ℕ) :
    Matrix.trace ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ) ^ n) =
      2 * (((T ℝ (n : ℤ)).eval x : ℝ) : ℂ) := by
  set B : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; c, d] with hB
  have hsq := fin_two_sq38 a b c d hdet
  have key : ∀ n : ℕ, Matrix.trace (B ^ n) = 2 * (((T ℝ (n : ℤ)).eval x : ℝ) : ℂ) ∧
      Matrix.trace (B ^ (n + 1)) = 2 * (((T ℝ ((n + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [T_zero]
      · simp [hB, T_one, Matrix.trace_fin_two]
        linear_combination htr
    | succ n ih =>
      refine ⟨by simpa using ih.2, ?_⟩
      have e : B ^ (n + 1 + 1) = (a + d) • B ^ (n + 1) - B ^ n := by
        rw [show n + 1 + 1 = n + 2 by ring, pow_add, hsq, mul_sub, mul_one, Matrix.mul_smul,
          pow_succ]
      rw [e, Matrix.trace_sub, Matrix.trace_smul, ih.1, ih.2, htr]
      have := T_add_two ℝ (n : ℤ)
      have h2 : (T ℝ ((n + 1 + 1 : ℕ) : ℤ)).eval x =
          2 * x * (T ℝ ((n + 1 : ℕ) : ℤ)).eval x - (T ℝ (n : ℤ)).eval x := by
        have := congrArg (Polynomial.eval x) this
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat] at this
        push_cast
        exact this
      rw [h2]; push_cast; simp; ring
  exact (key n).1


/-! ### Gauge conjugation of the plane-wave monodromy -/

theorem alPlaneWave_apply38 (L : ℕ) [NeZero L] (k : ℤ) (t : ℝ) (n : ℕ) (hn : n < L) :
    alPlaneWave38 L k t (n : ZMod L) =
      ((t / (L : ℝ) : ℝ) : ℂ) *
        (Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I) ^ 2) ^ n := by
  unfold alPlaneWave38
  rw [ZMod.val_natCast_of_lt hn, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem alPlanePartial38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t / L < 1)
    (z : ℂ) :
    ∀ n : ℕ, n ≤ L →
      alPartial38 (alPlaneWave38 L k t) z n =
        alPlaneGaugeInv38 (Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I)) n *
          (alPlaneB38 (t / L) (Real.pi * k / L) z) ^ n := by
  set u : ℂ := Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hun : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hs0 : 0 ≤ t / (L : ℝ) := by positivity
  intro n
  induction n with
  | zero =>
    intro _
    simp only [alPartial38, pow_zero, mul_one]
    unfold alPlaneGaugeInv38
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    intro hn
    have hnL : n < L := hn
    have hstep : alTransfer38 (((t / (L : ℝ) : ℝ) : ℂ) * (u ^ 2) ^ n) z =
        alPlaneGaugeInv38 u (n + 1) * alPlaneB38 (t / L) (Real.pi * k / L) z *
          alPlaneGauge38 u n := alPlaneTransfer_step38 hs0 ht1 hu0 hun z n
    rw [alPartial38, ih hnL.le, alPlaneWave_apply38 L k t n hnL, hstep]
    generalize alPlaneB38 (t / L) (Real.pi * k / L) z = B
    have hG := alPlaneGauge_mul38 hu0 n
    calc _ = alPlaneGaugeInv38 u (n + 1) * B *
          (alPlaneGauge38 u n * alPlaneGaugeInv38 u n) * B ^ n := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hG, Matrix.mul_one, pow_succ', Matrix.mul_assoc]


/-! ### Half trace of the monodromy -/

theorem alPlaneB_data38 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (θ ϑ : ℝ) :
    let c0 : ℂ := ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ)⁻¹
    let z : ℂ := Complex.exp ((ϑ : ℂ) * Complex.I)
    let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    (c0 * z * u⁻¹) * (c0 * z⁻¹ * u) - (c0 * s * u⁻¹) * (c0 * s * u) = 1 ∧
    (c0 * z * u⁻¹) + (c0 * z⁻¹ * u) =
      2 * ((Real.cos (ϑ - θ) / Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) := by
  intro c0 z u
  have hpos : 0 < 1 - s ^ 2 := by nlinarith
  have hsq : ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hsq2 : ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (s : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have h1s : (1 : ℂ) - (s : ℂ) ^ 2 ≠ 0 := by rw [← hsq2]; exact pow_ne_zero _ hsq
  constructor
  · simp only [c0]
    field_simp
    rw [hsq2]
  · have e1 : z * u⁻¹ = Complex.exp (((ϑ - θ : ℝ) : ℂ) * Complex.I) := by
      simp only [z, u]; rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : z⁻¹ * u = Complex.exp ((((ϑ - θ : ℝ) : ℂ)) * (-Complex.I)) := by
      simp only [z, u]; rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
    have : c0 * z * u⁻¹ + c0 * z⁻¹ * u = c0 * (z * u⁻¹ + z⁻¹ * u) := by ring
    rw [this, e1, e2, mul_neg, Complex.exp_mul_I, ← neg_mul, ← Complex.ofReal_neg,
      Complex.exp_mul_I]
    simp only [c0, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_neg]
    push_cast
    simp
    rw [show (θ : ℂ) - ϑ = -((ϑ : ℂ) - θ) by ring, Complex.cos_neg, Complex.sin_neg]
    field_simp
    ring


theorem alPlaneMonodromy_trace38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t / L < 1) (ϑ : ℝ) :
    Matrix.trace (alMonodromy38 (alPlaneWave38 L k t) (Complex.exp ((ϑ : ℂ) * Complex.I))) / 2 =
      ((-1 : ℂ) ^ k) *
        (((T ℝ (L : ℤ)).eval
          (Real.cos (ϑ - Real.pi * k / L) / Real.sqrt (1 - (t / L) ^ 2)) : ℝ) : ℂ) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hs0 : 0 ≤ t / (L : ℝ) := by positivity
  set z : ℂ := Complex.exp ((ϑ : ℂ) * Complex.I) with hz
  set u : ℂ := Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I) with hu
  have hM : alMonodromy38 (alPlaneWave38 L k t) z =
      alPlaneGaugeInv38 u L * (alPlaneB38 (t / L) (Real.pi * k / L) z) ^ L :=
    alPlanePartial38 L k ht0 ht1 z L le_rfl
  -- the sign
  have huL : u ^ L = (-1 : ℂ) ^ k := by
    rw [hu, ← Complex.exp_nat_mul]
    have : (L : ℂ) * (((Real.pi * k / L : ℝ) : ℂ) * Complex.I) = (k : ℂ) * (Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hσ : ((-1 : ℂ) ^ k)⁻¹ = (-1 : ℂ) ^ k := by
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩ <;> simp [zpow_add₀, zpow_mul]
  obtain ⟨hdet, htr⟩ := alPlaneB_data38 hs0 ht1 (Real.pi * k / L) ϑ
  have hB : Matrix.trace ((alPlaneB38 (t / L) (Real.pi * k / L) z) ^ L) =
      2 * (((T ℝ (L : ℤ)).eval
        (Real.cos (ϑ - Real.pi * k / L) / Real.sqrt (1 - (t / L) ^ 2)) : ℝ) : ℂ) :=
    trace_pow_chebyshev38 _ _ _ _ _ hdet htr L
  rw [hM]
  have hD : alPlaneGaugeInv38 u L = !![(-1 : ℂ) ^ k, 0; 0, (-1 : ℂ) ^ k] := by
    unfold alPlaneGaugeInv38; rw [huL, hσ]
  rw [hD]
  generalize alPlaneB38 (t / L) (Real.pi * k / L) z = B at hB ⊢
  rw [show (!![(-1 : ℂ) ^ k, 0; 0, (-1 : ℂ) ^ k] : Matrix (Fin 2) (Fin 2) ℂ) =
      ((-1 : ℂ) ^ k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) by
        ext i j; fin_cases i <;> fin_cases j <;> simp,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, hB]
  simp only [smul_eq_mul]
  ring


/-! ### The gap formula -/

/-- `κ(θ) = arcosh (max 1 |c|)`, `c = cos(θ - θ_k)/√(1 - h²t²)`, `h = 1/L`, `θ_k = π k h`. -/
theorem alPlaneWave_kappa38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t / L < 1) (θ : ℝ) :
    alKappa38 (alPlaneWave38 L k t) θ =
      Real.arcosh (max 1 (|Real.cos (θ - Real.pi * k / L)| / Real.sqrt (1 - (t / L) ^ 2))) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hpos : 0 < Real.sqrt (1 - (t / L) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : 0 ≤ t / (L : ℝ) := by positivity
    nlinarith
  unfold alKappa38
  rw [alPlaneMonodromy_trace38 L k ht0 ht1 θ, norm_mul, norm_zpow, norm_neg, norm_one,
    one_zpow, one_mul, Complex.norm_real, Real.norm_eq_abs, arcosh_max_abs_T_real38 L hL1,
    ← abs_of_pos hpos, ← abs_div, abs_of_pos hpos]
  field_simp

/-- Closed gap: `κ = 0` iff `|cos(θ - θ_k)| ≤ √(1 - h²t²)`. -/
theorem alPlaneWave_kappa_eq_zero_iff38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t / L < 1) (θ : ℝ) :
    alKappa38 (alPlaneWave38 L k t) θ = 0 ↔
      |Real.cos (θ - Real.pi * k / L)| ≤ Real.sqrt (1 - (t / L) ^ 2) := by
  have hpos : 0 < Real.sqrt (1 - (t / L) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : 0 ≤ t / (L : ℝ) := by positivity
    nlinarith
  rw [alPlaneWave_kappa38 L k ht0 ht1 θ, ← div_le_one hpos]
  constructor
  · intro h
    by_contra h'
    have := Real.arcosh_pos (not_le.mp h')
    rw [max_eq_right (not_le.mp h').le] at h
    linarith
  · intro h
    rw [max_eq_left h, Real.arcosh_zero]

/-- Open gap: if the ratio exceeds one, `κ` is its `arcosh`. -/
theorem alPlaneWave_kappa_of_one_lt38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t / L < 1) (θ : ℝ)
    (h : 1 < |Real.cos (θ - Real.pi * k / L)| / Real.sqrt (1 - (t / L) ^ 2)) :
    alKappa38 (alPlaneWave38 L k t) θ =
      Real.arcosh (|Real.cos (θ - Real.pi * k / L)| / Real.sqrt (1 - (t / L) ^ 2)) := by
  rw [alPlaneWave_kappa38 L k ht0 ht1 θ, max_eq_right h.le]

/-- `D:eq:planegap` (paper/v2.tex l.2313-2319) with `h = 1/L`:
`v_h(λ) = h⁻¹ κ(hλ) = (1/h) arcosh (max 1 (|cos(hλ - θ_k)|/√(1 - h²t²)))`, `θ_k = π k h`;
it vanishes exactly where the ratio is at most one. -/
theorem alPlaneWave_gap38 (L : ℕ) [NeZero L] (k : ℤ) {t h : ℝ} (hh : h = 1 / (L : ℝ))
    (ht0 : 0 ≤ t) (hht : h * t < 1) (lam : ℝ) :
    h⁻¹ * alKappa38 (alPlaneWave38 L k t) (h * lam) =
      h⁻¹ * Real.arcosh
        (max 1 (|Real.cos (h * lam - Real.pi * k * h)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) := by
  have e1 : t / (L : ℝ) = h * t := by rw [hh]; ring
  have ht1 : t / (L : ℝ) < 1 := by rw [e1]; exact hht
  rw [alPlaneWave_kappa38 L k ht0 ht1, e1, mul_pow]
  have e2 : Real.pi * k / (L : ℝ) = Real.pi * k * h := by rw [hh]; ring
  rw [e2]

/-- The same gap written through the monodromy: `v_h(λ) = arcosh (max 1 |½ tr M(e^{ihλ})|)`. -/
theorem alPlaneWave_gap_monodromy38 (L : ℕ) [NeZero L] (k : ℤ) {t h : ℝ} (hh : h = 1 / (L : ℝ))
    (ht0 : 0 ≤ t) (hht : h * t < 1) (lam : ℝ) :
    Real.arcosh (max 1 ‖Matrix.trace (alMonodromy38 (alPlaneWave38 L k t)
        (Complex.exp (((h * lam : ℝ) : ℂ) * Complex.I))) / 2‖) =
      h⁻¹ * Real.arcosh
        (max 1 (|Real.cos (h * lam - Real.pi * k * h)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hinv : h⁻¹ = (L : ℝ) := by rw [hh]; field_simp
  rw [← alPlaneWave_gap38 L k hh ht0 hht lam, hinv]
  unfold alKappa38
  field_simp

end NlsGge.AblowitzLadik

end
