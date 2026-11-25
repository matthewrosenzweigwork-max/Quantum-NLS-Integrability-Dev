import QuantumNLS.DuhamelDuality

/-!
# EXT-003, Route Y stage (i): a short-time gain for the periodic `L⁴` estimate

Route Y (elementary) deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, Section 4): the
quoted EXT-003 input (`ROOT_L2_extension.tex`, lines 3-18) needs a local lifespan depending only on
the `L²` bound, hence a power gain in the length of the time interval for the free `L⁴` estimate.
Bourgain obtains it from `X^{0,b}` spaces; here it is proved directly by the lattice count.

Imports the frozen DD1 (`DuhamelDuality`, `40e83626…`), LS2 (`66db0da6…`) and LS1 (`546d7e5b…`)
read-only.

For a finite Fourier sum `u(t,x) = Σ_{n∈S} a_n e^{−itp_n²} e_n(x)`, `0 < T ≤ 1` and every `s`:
`∫_s^{s+T} ∫_{𝕋_L} |u|⁴ ≤ (2/L)(T + T^{1/4} A^{3/4} Z)(Σ|a_n|²)²`, `A = L²/(4π²)`,
`Z = Σ_{j∈ℤ} |j|^{−3/2}`; hence `≤ K T^{1/4} (Σ|a_n|²)²`. For every `L²` datum (with `T ≤ T_L`),
the `L⁴` free solution satisfies `‖U(·)f‖⁴_{L⁴((s,s+T]×𝕋_L)} ≤ K T^{1/4}‖f‖₂⁴`, i.e. a `T^{1/16}`
gain.

Argument: time integration over `[s, s+T]` bounds each fourfold term by
`min(T, 2/|Ω|)`; on the resonance plane `n₁+n₂ = n₃+n₄`,
`n₁²+n₂²−n₃²−n₄² = −2(n₃−n₁)(n₃−n₂)`; `min(T, A/(|x||y|)) ≤ T^{1/4}A^{3/4}(|x|^{−3/2} + |y|^{−3/2})`;
then `|a₁a₂a₃a₄| ≤ (|a₁a₂|² + |a₃a₄|²)/2` and summation of the decay over the free index.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality

namespace QuantumNLS.ShortTimeGain

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Elementary inequalities -/

lemma min_le_geom {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min u v ≤ u ^ (4⁻¹ : ℝ) * v ^ (3 / 4 : ℝ) := by
  have hs : (4⁻¹ : ℝ) + 3 / 4 ≠ 0 := by norm_num
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    calc u = u ^ ((4⁻¹ : ℝ) + 3 / 4) := by norm_num
      _ = u ^ (4⁻¹ : ℝ) * u ^ (3 / 4 : ℝ) := Real.rpow_add' hu hs
      _ ≤ u ^ (4⁻¹ : ℝ) * v ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu h (by norm_num)) (Real.rpow_nonneg hu _)
  · rw [min_eq_right h]
    calc v = v ^ ((4⁻¹ : ℝ) + 3 / 4) := by norm_num
      _ = v ^ (4⁻¹ : ℝ) * v ^ (3 / 4 : ℝ) := Real.rpow_add' hv hs
      _ ≤ u ^ (4⁻¹ : ℝ) * v ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hv h (by norm_num)) (Real.rpow_nonneg hv _)

lemma prod_rpow_le {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (u * v) ^ (-(3 / 4 : ℝ)) ≤ u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ)) := by
  have key : ∀ {p q : ℝ}, 1 ≤ p → p ≤ q → (p * q) ^ (-(3 / 4 : ℝ)) ≤ p ^ (-(3 / 2 : ℝ)) := by
    intro p q hp hpq
    have hp0 : 0 < p := by linarith
    have hq0 : 0 < q := by linarith
    have h1 : (p * q) ^ (-(3 / 4 : ℝ)) ≤ (p * p) ^ (-(3 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
      exact inv_anti₀ (by positivity)
        (Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hpq hp0.le) (by norm_num))
    calc (p * q) ^ (-(3 / 4 : ℝ)) ≤ (p * p) ^ (-(3 / 4 : ℝ)) := h1
      _ = p ^ (-(3 / 4 : ℝ) + -(3 / 4)) := by
          rw [Real.mul_rpow hp0.le hp0.le, ← Real.rpow_add hp0]
      _ = p ^ (-(3 / 2 : ℝ)) := by norm_num
  rcases le_total u v with h | h
  · exact (key hu h).trans (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _))
  · rw [mul_comm]
    exact (key hv h).trans (le_add_of_nonneg_left (Real.rpow_nonneg (by linarith) _))

/-! ## 2. The time integral of one fourfold phase -/

/-- `J(n) = ∫_s^{s+T} e^{−it(p₁²+p₂²−p₃²−p₄²)} dt`. -/
def J4 (L s T : ℝ) (n1 n2 n3 n4 : ℤ) : ℂ := ∫ t in s..s + T, P4 L t n1 n2 n3 n4

lemma norm_P4 (t : ℝ) (n1 n2 n3 n4 : ℤ) : ‖P4 L t n1 n2 n3 n4‖ = 1 := by
  simp [P4, norm_phase]

lemma norm_J4_le_T (s : ℝ) {T : ℝ} (hT : 0 ≤ T) (n1 n2 n3 n4 : ℤ) :
    ‖J4 L s T n1 n2 n3 n4‖ ≤ T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s + T) (C := 1)
    (f := fun t => P4 L t n1 n2 n3 n4) fun t _ => (norm_P4 t n1 n2 n3 n4).le
  rw [J4]
  calc _ ≤ 1 * |s + T - s| := h
    _ = T := by rw [add_sub_cancel_left, abs_of_nonneg hT, one_mul]

/-- The frequency mismatch `Ω = p₁² + p₂² − p₃² − p₄²`. -/
def Ω (L : ℝ) (n1 n2 n3 n4 : ℤ) : ℝ := freq L n1 ^ 2 + freq L n2 ^ 2 - freq L n3 ^ 2 - freq L n4 ^ 2

lemma norm_J4_le_inv (s T : ℝ) {n1 n2 n3 n4 : ℤ} (hΩ : Ω L n1 n2 n3 n4 ≠ 0) :
    ‖J4 L s T n1 n2 n3 n4‖ ≤ 2 / |Ω L n1 n2 n3 n4| := by
  set c : ℂ := -Complex.I * ((Ω L n1 n2 n3 n4 : ℝ) : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hΩ)
  have hnc : ‖c‖ = |Ω L n1 n2 n3 n4| := by
    simp only [c, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hexp : ∀ x : ℝ, ‖Complex.exp (c * x)‖ = 1 := fun x => by
    have : c * (x : ℂ) = ((-(Ω L n1 n2 n3 n4 * x) : ℝ) : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hJ : J4 L s T n1 n2 n3 n4 = ∫ t in s..s + T, Complex.exp (c * t) := by
    unfold J4
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [P4_eq, Ω, c]
  rw [hJ, integral_exp_mul_complex hc, norm_div, hnc]
  gcongr
  calc ‖Complex.exp (c * ((s + T : ℝ) : ℂ)) - Complex.exp (c * (s : ℂ))‖
      ≤ ‖Complex.exp (c * ((s + T : ℝ) : ℂ))‖ + ‖Complex.exp (c * (s : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [hexp, hexp]; norm_num

/-- On the resonance plane, `Ω = −(8π²/L²)(n₃−n₁)(n₃−n₂)`. -/
lemma Ω_plane {n1 n2 n3 n4 : ℤ} (h : n1 + n2 = n3 + n4) :
    Ω L n1 n2 n3 n4 = -(8 * Real.pi ^ 2 / L ^ 2) * (((n3 - n1) * (n3 - n2) : ℤ) : ℝ) := by
  have h4 : n4 = n1 + n2 - n3 := by omega
  subst h4
  simp only [Ω, freq_sq]
  push_cast
  ring

/-! ## 3. The decay weight and its sums -/

/-- `A = L²/(4π²)`. -/
def A (L : ℝ) : ℝ := L ^ 2 / (4 * Real.pi ^ 2)

lemma A_pos : 0 < A L := by
  have hL : 0 < L := Fact.out
  unfold A; positivity

/-- `φ(j) = T·[j = 0] + T^{1/4} A^{3/4} |j|^{−3/2}`. -/
def φ (L T : ℝ) (j : ℤ) : ℝ :=
  (if j = 0 then T else 0) + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * |(j : ℝ)| ^ (-(3 / 2 : ℝ))

lemma φ_nonneg {T : ℝ} (hT : 0 ≤ T) (j : ℤ) : 0 ≤ φ L T j := by
  unfold φ
  have := A_pos (L := L)
  have h1 : 0 ≤ (if j = 0 then T else 0) := by split_ifs <;> linarith
  have h2 : 0 ≤ T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * |(j : ℝ)| ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hT _) (Real.rpow_nonneg this.le _))
      (Real.rpow_nonneg (abs_nonneg _) _)
  linarith

/-- `Z = Σ_{j∈ℤ} |j|^{−3/2}`. -/
def Z : ℝ := ∑' j : ℤ, |(j : ℝ)| ^ (-(3 / 2 : ℝ))

lemma summable_decay : Summable fun j : ℤ => |(j : ℝ)| ^ (-(3 / 2 : ℝ)) :=
  Real.summable_abs_int_rpow (by norm_num)

/-- Every finite sum of `φ` is at most `B = T + T^{1/4}A^{3/4}Z`. -/
lemma sum_φ_le {T : ℝ} (hT : 0 ≤ T) (F : Finset ℤ) :
    ∑ j ∈ F, φ L T j ≤ T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z := by
  unfold φ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr
  · rw [Finset.sum_ite_eq']
    split_ifs <;> linarith
  · have := A_pos (L := L)
    positivity
  · exact summable_decay.sum_le_tsum F fun j _ => Real.rpow_nonneg (abs_nonneg _) _

lemma sum_φ_shift_le {T : ℝ} (hT : 0 ≤ T) (S : Finset ℤ) (c : ℤ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∑ n ∈ S, φ L T (σ * (n - c)) ≤ T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z := by
  have hinj : Set.InjOn (fun n : ℤ => σ * (n - c)) S := by
    intro x _ y _ hxy
    simp only at hxy
    rcases hσ with rfl | rfl <;> linarith
  rw [← Finset.sum_image (f := φ L T) (g := fun n : ℤ => σ * (n - c)) hinj]
  exact sum_φ_le hT _

/-- **The key pointwise bound** on the resonance plane:
`‖J(n)‖ ≤ φ(n₃ − n₁) + φ(n₃ − n₂)`. -/
lemma norm_J4_le_φ (s : ℝ) {T : ℝ} (hT : 0 ≤ T) {n1 n2 n3 n4 : ℤ} (h : n1 + n2 = n3 + n4) :
    ‖J4 L s T n1 n2 n3 n4‖ ≤ φ L T (n3 - n1) + φ L T (n3 - n2) := by
  have hL : 0 < L := Fact.out
  have hφ1 := φ_nonneg (L := L) hT (n3 - n1)
  have hφ2 := φ_nonneg (L := L) hT (n3 - n2)
  have hTb := norm_J4_le_T (L := L) s hT n1 n2 n3 n4
  by_cases hx : n3 - n1 = 0
  · have : T ≤ φ L T (n3 - n1) := by
      unfold φ; simp only [hx, ↓reduceIte]
      have := A_pos (L := L)
      have : 0 ≤ T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * |((n3 - n1 : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        by positivity
      linarith
    linarith
  by_cases hy : n3 - n2 = 0
  · have : T ≤ φ L T (n3 - n2) := by
      unfold φ; simp only [hy, ↓reduceIte]
      have := A_pos (L := L)
      have : 0 ≤ T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * |((n3 - n2 : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        by positivity
      linarith
    linarith
  -- generic case
  set u : ℝ := |((n3 - n1 : ℤ) : ℝ)|
  set v : ℝ := |((n3 - n2 : ℤ) : ℝ)|
  have hu : 1 ≤ u := by
    simp only [u]; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hx
  have hv : 1 ≤ v := by
    simp only [v]; rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hy
  have hΩ : |Ω L n1 n2 n3 n4| = (8 * Real.pi ^ 2 / L ^ 2) * (u * v) := by
    rw [Ω_plane h, abs_mul, abs_neg, abs_of_pos (by positivity), Int.cast_mul, abs_mul]
  have hΩ0 : Ω L n1 n2 n3 n4 ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hΩ
    have : 0 < (8 * Real.pi ^ 2 / L ^ 2) * (u * v) := by positivity
    linarith
  have hinv := norm_J4_le_inv (L := L) s T hΩ0
  have h2 : 2 / |Ω L n1 n2 n3 n4| = A L / (u * v) := by
    rw [hΩ, A]; field_simp; ring
  rw [h2] at hinv
  have hmin : ‖J4 L s T n1 n2 n3 n4‖ ≤ min T (A L / (u * v)) := le_min hTb hinv
  have hg := min_le_geom hT (div_nonneg (A_pos (L := L)).le (by positivity : (0 : ℝ) ≤ u * v))
  have huv : (A L / (u * v)) ^ (3 / 4 : ℝ) = A L ^ (3 / 4 : ℝ) * (u * v) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.div_rpow (A_pos (L := L)).le (by positivity), Real.rpow_neg (by positivity),
      div_eq_mul_inv]
  have hp := prod_rpow_le hu hv
  calc ‖J4 L s T n1 n2 n3 n4‖ ≤ T ^ (4⁻¹ : ℝ) * (A L / (u * v)) ^ (3 / 4 : ℝ) := hmin.trans hg
    _ = T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * (u * v) ^ (-(3 / 4 : ℝ)) := by rw [huv]; ring
    _ ≤ T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * (u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ))) := by
        have := A_pos (L := L)
        gcongr
    _ ≤ φ L T (n3 - n1) + φ L T (n3 - n2) := by
        unfold φ
        simp only [hx, hy, ↓reduceIte, zero_add]
        simp only [u, v]
        linarith

#print axioms norm_J4_le_φ

lemma sum_φ_sub_le {T : ℝ} (hT : 0 ≤ T) (S : Finset ℤ) (c : ℤ) :
    ∑ n ∈ S, φ L T (n - c) ≤ T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z := by
  have hinj : Set.InjOn (fun n : ℤ => n - c) S := fun x _ y _ hxy => by simpa using hxy
  rw [← Finset.sum_image (f := φ L T) (g := fun n : ℤ => n - c) hinj]
  exact sum_φ_le hT _

lemma sum_φ_sub_le' {T : ℝ} (hT : 0 ≤ T) (S : Finset ℤ) (c : ℤ) :
    ∑ n ∈ S, φ L T (c - n) ≤ T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z := by
  have hinj : Set.InjOn (fun n : ℤ => c - n) S := fun x _ y _ hxy => by simpa using hxy
  rw [← Finset.sum_image (f := φ L T) (g := fun n : ℤ => c - n) hinj]
  exact sum_φ_le hT _

/-! ## 4. The fourfold sum -/

lemma time_sum (S : Finset ℤ) (a : ℤ → ℂ) (s T : ℝ) :
    ((∫ t in s..s + T, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 : ℝ) : ℂ) =
      ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S,
        A4 a n1 n2 n3 n4 * J4 L s T n1 n2 n3 n4 *
          (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [integral_x]
  have hF : ∀ n1 n2 n3 n4 : ℤ, Continuous fun t : ℝ => A4 a n1 n2 n3 n4 *
      P4 L t n1 n2 n3 n4 * (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) := fun n1 n2 n3 n4 =>
    (continuous_const.mul (continuous_P4 n1 n2 n3 n4)).mul continuous_const
  rw [intervalIntegral.integral_finsetSum fun n1 _ => (continuous_finsetSum _ fun n2 _ =>
    continuous_finsetSum _ fun n3 _ => continuous_finsetSum _ fun n4 _ =>
      hF n1 n2 n3 n4).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun n1 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n2 _ => (continuous_finsetSum _ fun n3 _ =>
    continuous_finsetSum _ fun n4 _ => hF n1 n2 n3 n4).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun n2 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n3 _ => (continuous_finsetSum _ fun n4 _ =>
    hF n1 n2 n3 n4).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun n3 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n4 _ => (hF n1 n2 n3 n4).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun n4 _ => ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, J4]

/-- The resonance weight `W(n) = [n₁+n₂ = n₃+n₄] ‖J(n)‖`. -/
def W (L s T : ℝ) (n1 n2 n3 n4 : ℤ) : ℝ :=
  if n1 + n2 = n3 + n4 then ‖J4 L s T n1 n2 n3 n4‖ else 0

lemma W_nonneg (s T : ℝ) (n1 n2 n3 n4 : ℤ) : 0 ≤ W L s T n1 n2 n3 n4 := by
  unfold W; split_ifs <;> positivity

lemma I_le (S : Finset ℤ) (a : ℤ → ℂ) (s : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in s..s + T, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 ≤
      L⁻¹ * ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S,
        ‖A4 a n1 n2 n3 n4‖ * W L s T n1 n2 n3 n4 := by
  have hL : 0 < L := Fact.out
  have hI0 : 0 ≤ ∫ t in s..s + T, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 :=
    intervalIntegral.integral_nonneg (le_add_of_nonneg_right hT) fun t _ =>
      integral_nonneg fun x => by positivity
  have h := congrArg norm (time_sum (L := L) S a s T)
  rw [Complex.norm_real, Real.norm_of_nonneg hI0] at h
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n1 _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n2 _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n3 _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n4 _ => ?_
  rw [norm_mul, norm_mul, W]
  split_ifs with hc
  · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hL.le]
    exact le_of_eq (by ring)
  · rw [norm_zero, mul_zero, mul_zero, mul_zero]

/-- `X(p,q) = |a_p|²|a_q|²`. -/
def X (a : ℤ → ℂ) (p q : ℤ) : ℝ := ‖a p‖ ^ 2 * ‖a q‖ ^ 2

lemma norm_A4_le (a : ℤ → ℂ) (n1 n2 n3 n4 : ℤ) :
    ‖A4 a n1 n2 n3 n4‖ ≤ (X a n1 n2 + X a n3 n4) / 2 := by
  have e : ‖A4 a n1 n2 n3 n4‖ = (‖a n1‖ * ‖a n2‖) * (‖a n3‖ * ‖a n4‖) := by
    simp only [A4, norm_mul, Complex.norm_conj]; ring
  rw [e, X, X]
  nlinarith [sq_nonneg (‖a n1‖ * ‖a n2‖ - ‖a n3‖ * ‖a n4‖)]

lemma elim4 (S : Finset ℤ) (s : ℝ) {T : ℝ} (hT : 0 ≤ T) (n1 n2 n3 : ℤ) :
    ∑ n4 ∈ S, W L s T n1 n2 n3 n4 ≤ φ L T (n3 - n1) + φ L T (n3 - n2) := by
  have hb : ∀ n4 ∈ S, W L s T n1 n2 n3 n4 ≤
      if n4 = n1 + n2 - n3 then φ L T (n3 - n1) + φ L T (n3 - n2) else 0 := by
    intro n4 _
    unfold W
    by_cases hc : n1 + n2 = n3 + n4
    · have h4 : n4 = n1 + n2 - n3 := by omega
      simp only [eq_true hc, eq_true h4, ↓reduceIte]
      exact norm_J4_le_φ (L := L) s hT hc
    · have h4 : ¬ n4 = n1 + n2 - n3 := by omega
      simp only [eq_false hc, eq_false h4, ↓reduceIte, le_refl]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact add_nonneg (φ_nonneg hT _) (φ_nonneg hT _)

lemma elim2 (S : Finset ℤ) (s : ℝ) {T : ℝ} (hT : 0 ≤ T) (n1 n3 n4 : ℤ) :
    ∑ n2 ∈ S, W L s T n1 n2 n3 n4 ≤ φ L T (n3 - n1) + φ L T (n1 - n4) := by
  have hb : ∀ n2 ∈ S, W L s T n1 n2 n3 n4 ≤
      if n2 = n3 + n4 - n1 then φ L T (n3 - n1) + φ L T (n1 - n4) else 0 := by
    intro n2 _
    unfold W
    by_cases hc : n1 + n2 = n3 + n4
    · have h2 : n2 = n3 + n4 - n1 := by omega
      simp only [eq_true hc, eq_true h2, ↓reduceIte]
      have := norm_J4_le_φ (L := L) s hT hc
      rwa [show n3 - n2 = n1 - n4 by omega] at this
    · have h2 : ¬ n2 = n3 + n4 - n1 := by omega
      simp only [eq_false hc, eq_false h2, ↓reduceIte, le_refl]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact add_nonneg (φ_nonneg hT _) (φ_nonneg hT _)

lemma sum4_comm (S : Finset ℤ) (f : ℤ → ℤ → ℤ → ℤ → ℝ) :
    ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, f n1 n2 n3 n4 =
      ∑ n3 ∈ S, ∑ n4 ∈ S, ∑ n1 ∈ S, ∑ n2 ∈ S, f n1 n2 n3 n4 := by
  calc ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, f n1 n2 n3 n4
      = ∑ n1 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, ∑ n2 ∈ S, f n1 n2 n3 n4 :=
        Finset.sum_congr rfl fun n1 _ =>
          Finset.sum_comm.trans (Finset.sum_congr rfl fun n3 _ => Finset.sum_comm)
    _ = ∑ n3 ∈ S, ∑ n4 ∈ S, ∑ n1 ∈ S, ∑ n2 ∈ S, f n1 n2 n3 n4 :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun n3 _ => Finset.sum_comm)

lemma sumX (S : Finset ℤ) (a : ℤ → ℂ) :
    ∑ n1 ∈ S, ∑ n2 ∈ S, X a n1 n2 = (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]; rfl

/-- **Stage (i), finite sums**: `∫_s^{s+T}∫|u|⁴ ≤ (2/L)(T + T^{1/4}A^{3/4}Z)(Σ|a_n|²)²`. -/
theorem gain_finite (S : Finset ℤ) (a : ℤ → ℂ) (s : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in s..s + T, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 ≤
      2 / L * (T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z) * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
  have hL : 0 < L := Fact.out
  set B := T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z
  set P := ∑ n ∈ S, ‖a n‖ ^ 2
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hXn : ∀ p q, 0 ≤ X a p q := fun p q => by unfold X; positivity
  -- first half
  have h1 : ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, X a n1 n2 * W L s T n1 n2 n3 n4 ≤
      2 * B * P ^ 2 := by
    calc ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, X a n1 n2 * W L s T n1 n2 n3 n4
        = ∑ n1 ∈ S, ∑ n2 ∈ S, X a n1 n2 * ∑ n3 ∈ S, ∑ n4 ∈ S, W L s T n1 n2 n3 n4 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ n1 ∈ S, ∑ n2 ∈ S, X a n1 n2 * (2 * B) := by
          refine Finset.sum_le_sum fun n1 _ => Finset.sum_le_sum fun n2 _ =>
            mul_le_mul_of_nonneg_left ?_ (hXn _ _)
          calc ∑ n3 ∈ S, ∑ n4 ∈ S, W L s T n1 n2 n3 n4
              ≤ ∑ n3 ∈ S, (φ L T (n3 - n1) + φ L T (n3 - n2)) :=
                Finset.sum_le_sum fun n3 _ => elim4 S s hT n1 n2 n3
            _ ≤ B + B := by
                rw [Finset.sum_add_distrib]
                exact add_le_add (sum_φ_sub_le hT S n1) (sum_φ_sub_le hT S n2)
            _ = 2 * B := by ring
      _ = 2 * B * P ^ 2 := by
          simp only [← Finset.sum_mul]
          rw [sumX]; ring
  -- second half
  have h2 : ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, X a n3 n4 * W L s T n1 n2 n3 n4 ≤
      2 * B * P ^ 2 := by
    rw [sum4_comm S (fun n1 n2 n3 n4 => X a n3 n4 * W L s T n1 n2 n3 n4)]
    calc ∑ n3 ∈ S, ∑ n4 ∈ S, ∑ n1 ∈ S, ∑ n2 ∈ S, X a n3 n4 * W L s T n1 n2 n3 n4
        = ∑ n3 ∈ S, ∑ n4 ∈ S, X a n3 n4 * ∑ n1 ∈ S, ∑ n2 ∈ S, W L s T n1 n2 n3 n4 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ n3 ∈ S, ∑ n4 ∈ S, X a n3 n4 * (2 * B) := by
          refine Finset.sum_le_sum fun n3 _ => Finset.sum_le_sum fun n4 _ =>
            mul_le_mul_of_nonneg_left ?_ (hXn _ _)
          calc ∑ n1 ∈ S, ∑ n2 ∈ S, W L s T n1 n2 n3 n4
              ≤ ∑ n1 ∈ S, (φ L T (n3 - n1) + φ L T (n1 - n4)) :=
                Finset.sum_le_sum fun n1 _ => elim2 S s hT n1 n3 n4
            _ ≤ B + B := by
                rw [Finset.sum_add_distrib]
                exact add_le_add (sum_φ_sub_le' hT S n3) (sum_φ_sub_le hT S n4)
            _ = 2 * B := by ring
      _ = 2 * B * P ^ 2 := by
          simp only [← Finset.sum_mul]
          rw [sumX]; ring
  have hA2 : 2 * ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, ‖A4 a n1 n2 n3 n4‖ * W L s T n1 n2 n3 n4 ≤
      ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, X a n1 n2 * W L s T n1 n2 n3 n4 +
        ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, X a n3 n4 * W L s T n1 n2 n3 n4 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n1 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n2 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n3 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n4 _ => ?_
    have := mul_le_mul_of_nonneg_right (norm_A4_le a n1 n2 n3 n4)
      (W_nonneg (L := L) s T n1 n2 n3 n4)
    linarith
  have hA : ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, ‖A4 a n1 n2 n3 n4‖ * W L s T n1 n2 n3 n4 ≤
      2 * B * P ^ 2 := by linarith
  refine (I_le S a s hT).trans ?_
  calc L⁻¹ * ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, ‖A4 a n1 n2 n3 n4‖ * W L s T n1 n2 n3 n4
      ≤ L⁻¹ * (2 * B * P ^ 2) := mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hL.le)
    _ = 2 / L * B * P ^ 2 := by ring

/-- The gain constant `K = (2/L)(1 + A^{3/4} Z)`. -/
def Kg (L : ℝ) : ℝ := 2 / L * (1 + A L ^ (3 / 4 : ℝ) * Z)

lemma Z_nonneg : 0 ≤ Z := tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _

lemma Kg_nonneg : 0 ≤ Kg L := by
  have hL : 0 < L := Fact.out
  have := A_pos (L := L)
  have := Z_nonneg
  unfold Kg; positivity

/-- **Stage (i), finite sums, power form**: for `0 < T ≤ 1`,
`∫_s^{s+T}∫|u|⁴ ≤ K T^{1/4}(Σ|a_n|²)²`. -/
theorem gain_finite' (S : Finset ℤ) (a : ℤ → ℂ) (s : ℝ) {T : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1) :
    ∫ t in s..s + T, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 ≤
      Kg L * T ^ (4⁻¹ : ℝ) * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
  have hL : 0 < L := Fact.out
  refine (gain_finite S a s hT0.le).trans ?_
  have hTq : T ≤ T ^ (4⁻¹ : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hT0 hT1 (show (4⁻¹ : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hP : 0 ≤ (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := sq_nonneg _
  have := A_pos (L := L)
  have := Z_nonneg
  unfold Kg
  have hB : T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z ≤
      (1 + A L ^ (3 / 4 : ℝ) * Z) * T ^ (4⁻¹ : ℝ) := by nlinarith
  calc 2 / L * (T + T ^ (4⁻¹ : ℝ) * A L ^ (3 / 4 : ℝ) * Z) * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2
      ≤ 2 / L * ((1 + A L ^ (3 / 4 : ℝ) * Z) * T ^ (4⁻¹ : ℝ)) * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
        gcongr
    _ = 2 / L * (1 + A L ^ (3 / 4 : ℝ) * Z) * T ^ (4⁻¹ : ℝ) * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by ring

#print axioms gain_finite'

/-! ## 5. Every `L²` datum -/

/-- **Stage (i)**: for `0 < T ≤ min(1, T_L)` and every `s`, the `L⁴` free solution on
`(s, s+T] × 𝕋_L` satisfies `‖U(·)f‖⁴_{L⁴} ≤ K T^{1/4}‖f‖₂⁴`. -/
theorem gain_L2 (f : HL L) (s : ℝ) {T : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1) (hTL : T ≤ TL L) :
    ‖freeL4 s (s + T) f‖ ^ 4 ≤ Kg L * T ^ (4⁻¹ : ℝ) * ‖f‖ ^ 4 := by
  have hαβ : s ≤ s + T := by linarith
  have hlen : s + T ≤ s + TL L := by linarith
  have hu := tendsto_freeL4 hαβ hlen f
  have hK : 0 ≤ Kg L * T ^ (4⁻¹ : ℝ) := mul_nonneg Kg_nonneg (Real.rpow_nonneg hT0.le _)
  refine le_of_tendsto (((continuous_pow 4).tendsto _).comp ((continuous_norm.tendsto _).comp hu))
    (Eventually.of_forall fun N => ?_)
  show ‖wN f s (s + T) N‖ ^ 4 ≤ _
  rw [wN, norm_toLp_pow (L := L) _ _ hαβ]
  refine (gain_finite' _ _ s hT0 hT1).trans ?_
  have h0 : 0 ≤ Psum f N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := Psum_le f N
  have h2 : (∑ n ∈ win N, ‖coef f n‖ ^ 2) ^ 2 ≤ ‖f‖ ^ 4 := by
    have := pow_le_pow_left₀ h0 h1 2
    rw [← pow_mul] at this
    exact this
  exact mul_le_mul_of_nonneg_left h2 hK

/-- The gain in norm form: `‖U(·)f‖_{L⁴((s,s+T]×𝕋_L)} ≤ K^{1/4} T^{1/16} ‖f‖₂`. -/
theorem gain_L2_norm (f : HL L) (s : ℝ) {T : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1) (hTL : T ≤ TL L) :
    ‖freeL4 s (s + T) f‖ ≤ Kg L ^ (4⁻¹ : ℝ) * T ^ (16⁻¹ : ℝ) * ‖f‖ := by
  have h4 := gain_L2 f s hT0 hT1 hTL
  have hK := Kg_nonneg (L := L)
  have hr : ‖freeL4 s (s + T) f‖ = (‖freeL4 s (s + T) f‖ ^ 4) ^ (4⁻¹ : ℝ) := by
    rw [show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (norm_nonneg _)
      (by norm_num)]
  rw [hr]
  calc (‖freeL4 s (s + T) f‖ ^ 4) ^ (4⁻¹ : ℝ)
      ≤ (Kg L * T ^ (4⁻¹ : ℝ) * ‖f‖ ^ 4) ^ (4⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = Kg L ^ (4⁻¹ : ℝ) * T ^ (16⁻¹ : ℝ) * ‖f‖ := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow hK (Real.rpow_nonneg hT0.le _), ← Real.rpow_mul hT0.le,
          show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)]
        norm_num

#print axioms gain_L2
#print axioms gain_L2_norm

end QuantumNLS.ShortTimeGain
