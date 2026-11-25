import Mathlib

/-!
# Scalar convolution comparison (source REG-001, `CC:convolution-comparison`)

Source: `source/chapters/regularity/root_confinement.tex:12`, label `CC:convolution-comparison`,
`\ReportID{REG-001}`, status `Proved` in the report.

Statement in the report. Let `a ≥ 0` and let `M : [0,∞) → (0,∞)` be continuously differentiable
with `M(0) = 1` and

  `M'(t) ≤ a ∫_0^t M(s) M(t-s) ds`  for `t ≥ 0`.

Then `M(t) ≤ e^{2√a t}` for all `t ≥ 0`.

Proof route of the report:
1. Catalan majorant. `C_0 = 1`, `C_n = ∑_{j<n} C_j C_{n-1-j}`, with `C_n ≤ 4^n`. Put
   `B(t) = ∑_n C_n a^n t^{2n}/(2n)!`. Then `B' = a (B ⋆ B)`, `B(0) = 1` and `1 ≤ B ≤ cosh(2√a t)`.
2. Comparison `M ≤ B` on `[0,T]` (`comparison_of_convolution_inequality` below).
3. Gronwall (`eq_zero_of_le_integral_of_nonneg` below) applied to `D = (M - B)_+`.

What this file proves, in dependency order (all compiled; axioms `propext`, `Classical.choice`,
`Quot.sound` only):
* `catalan_le_four_pow`: `C_n ≤ 4^n` for Mathlib's `catalan` (step 1, coefficient bound);
* `catalanSeries_term_le`, `catalanSeries_le_cosh`: `0 ≤ B(t) ≤ cosh(2√a t)` for the Catalan
  series `B(t) = ∑ C_n a^n t^{2n}/(2n)!` (step 1, majorant bound);
* `cosh_le_exp_of_nonneg`: `cosh x ≤ e^x` for `x ≥ 0`;
* `continuous_conv`, `continuous_primitive_of_continuous`, `hasDerivAt_primitive`: continuity of
  the convolution and of the primitive;
* `integral_pow_mul_sub_pow`: `∫_0^t s^p (t-s)^q ds = p! q!/(p+q+1)! t^{p+q+1}` (the monomial
  identity used when integrating `B(s)B(t-s)` termwise);
* `pointwise_conv_bound`, `eq_zero_of_le_integral_of_nonneg` (step 3, Gronwall);
* `comparison_of_convolution_inequality` (step 2): for continuous `M`, `B` with `M' ≤ a (M ⋆ M)`
  and `B' = a (B ⋆ B)` on `(0,T)`, `0 ≤ M, B ≤ K` on `[0,T]` and `M(0) ≤ B(0)`, we get `M ≤ B`
  on `[0,T]`.

Status: COMPLETE for the statement. `convolution_comparison_bound` proves the source inequality
`M(t) ≤ e^{2√a t}` for `t ≥ 0`, with the axioms `propext`, `Classical.choice`, `Quot.sound` only.
The Catalan series identities used are proved here (not assumed): `hasSum_conv_catalan`
(`B ⋆ B = ∑ a^n C_{n+1} t^{2n+1}/(2n+1)!`, by dominated convergence over antidiagonals),
`hasDerivAt_catalanSeries_conv` (`B' = a (B ⋆ B)` for `t ≥ 0`, termwise differentiation), continuity
of `B` on `ℝ`, and `B(0) = 1`. Hypotheses of the final theorem are satisfiable: `M = B` itself is a
solution (positive, `B(0) = 1`, `B' = a(B⋆B)`), so the statement is not vacuous.
-/

namespace QuantumNLS.ConvolutionComparison

open Set

noncomputable section

/-! ## Step 1 (coefficient bound): Catalan numbers are at most `4^n`. -/

/-- The Catalan numbers `C_n` of the report are Mathlib's `catalan n`
(`C_0 = 1`, `C_{n+1} = ∑_{i ≤ n} C_i C_{n-i}`). -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hb := Nat.centralBinom_le_four_pow n
  nlinarith

/-! ## Catalan majorant series: the bound `0 ≤ B(t) ≤ cosh(2√a t) ≤ e^{2√a t}`. -/

/-- The Catalan series `B(t) = ∑_n C_n a^n t^{2n}/(2n)!` of the report (the derivative identity
`B' = a (B ⋆ B)` is NOT proved in this file; see the review record). -/
def catalanSeries (a t : ℝ) : ℝ :=
  ∑' n : ℕ, (catalan n : ℝ) * a ^ n * t ^ (2 * n) / ((2 * n).factorial : ℝ)

/-- Each term of the Catalan series is bounded by the corresponding cosh term at
`x = 2√a t`, since `C_n ≤ 4^n` and `x^{2n} = 4^n a^n t^{2n}`. -/
theorem catalanSeries_term_le (a t : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (catalan n : ℝ) * a ^ n * t ^ (2 * n) / ((2 * n).factorial : ℝ)
      ≤ (2 * Real.sqrt a * t) ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have hC : (catalan n : ℝ) ≤ 4 ^ n := by exact_mod_cast catalan_le_four_pow n
  have hpow : (2 * Real.sqrt a * t) ^ (2 * n) = 4 ^ n * a ^ n * t ^ (2 * n) := by
    have hsq : Real.sqrt a ^ (2 * n) = a ^ n := by
      rw [pow_mul, Real.sq_sqrt ha]
    calc (2 * Real.sqrt a * t) ^ (2 * n)
        = 2 ^ (2 * n) * Real.sqrt a ^ (2 * n) * t ^ (2 * n) := by ring
      _ = 4 ^ n * a ^ n * t ^ (2 * n) := by
          rw [hsq, pow_mul]; norm_num
  have hfac : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
  have htpow : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  rw [hpow]
  apply div_le_div_of_nonneg_right _ hfac.le
  have hnn : 0 ≤ a ^ n * t ^ (2 * n) := mul_nonneg (pow_nonneg ha n) htpow
  nlinarith

/-- The Catalan series is bounded by `cosh(2√a t)`. -/
theorem catalanSeries_le_cosh (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    catalanSeries a t ≤ Real.cosh (2 * Real.sqrt a * t) := by
  have hcos := Real.hasSum_cosh (2 * Real.sqrt a * t)
  have hsum : Summable fun n : ℕ => (catalan n : ℝ) * a ^ n * t ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    refine Summable.of_nonneg_of_le ?_ (catalanSeries_term_le a t ha) hcos.summable
    intro n
    have hC : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
    have htpow : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
    have hf : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg ha n)) htpow) hf
  unfold catalanSeries
  rw [← hcos.tsum_eq]
  exact hsum.tsum_le_tsum (catalanSeries_term_le a t ha) hcos.summable

/-- `cosh x ≤ e^x` for `x ≥ 0`. -/
theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h1 : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

/-! ## Convolution and primitive: continuity. -/

/-- The scalar convolution `(M ⋆ N)(t) = ∫_0^t M(s) N(t-s) ds`. -/
def conv (M N : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, M s * N (t - s)

/-- The convolution of continuous functions is continuous. -/
theorem continuous_conv {M N : ℝ → ℝ} (hM : Continuous M) (hN : Continuous N) :
    Continuous (conv M N) := by
  have hf : Continuous (fun p : ℝ × ℝ => (fun (t s : ℝ) => M s * N (t - s)) p.1 p.2) :=
    (hM.comp continuous_snd).mul (hN.comp (continuous_fst.sub continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun (t s : ℝ) => M s * N (t - s)) hf continuous_id

/-- The primitive `x ↦ ∫_0^x D` of a continuous function has derivative `D`. -/
theorem hasDerivAt_primitive {D : ℝ → ℝ} (hD : Continuous D) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, D s) (D x) x :=
  intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 x)
    (hD.stronglyMeasurableAtFilter _ _) hD.continuousAt

/-- The primitive of a continuous function is continuous. -/
theorem continuous_primitive_of_continuous {D : ℝ → ℝ} (hD : Continuous D) :
    Continuous fun y : ℝ => ∫ s in (0 : ℝ)..y, D s :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_primitive hD x).continuousAt

/-! ## Monomial convolution identity (Beta integral over naturals), needed for the Catalan series. -/

/-- `∫_0^t s^p (t-s)^q ds = p! q! / (p+q+1)! · t^{p+q+1}`. Induction on `q` (for all `p`), using
`(t-s)^{q+1} = t (t-s)^q - s (t-s)^q` to get `I(p,q+1) = t I(p,q) - I(p+1,q)`. -/
theorem integral_pow_mul_sub_pow (q : ℕ) : ∀ (p : ℕ) (t : ℝ),
    ∫ s in (0 : ℝ)..t, s ^ p * (t - s) ^ q
      = ((p.factorial : ℝ) * (q.factorial : ℝ) / ((p + q + 1).factorial : ℝ))
        * t ^ (p + q + 1) := by
  induction q with
  | zero =>
    intro p t
    have hp : ((p + 1).factorial : ℝ) = ((p : ℝ) + 1) * (p.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [pow_zero, mul_one, integral_pow, Nat.factorial_zero, Nat.cast_one, add_zero,
      zero_pow (Nat.succ_ne_zero p), sub_zero, hp]
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ q ih =>
    intro p t
    have hsplit : ∀ s : ℝ, s ^ p * (t - s) ^ (q + 1)
        = t * (s ^ p * (t - s) ^ q) - s ^ (p + 1) * (t - s) ^ q := by
      intro s; ring
    simp_rw [hsplit]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun s : ℝ => t * (s ^ p * (t - s) ^ q)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun s : ℝ => s ^ (p + 1) * (t - s) ^ q).intervalIntegrable 0 t)]
    rw [intervalIntegral.integral_const_mul, ih p t, ih (p + 1) t]
    have hf1 : ((p + (q + 1) + 1).factorial : ℝ) = ((p : ℝ) + q + 2) * ((p + q + 1).factorial : ℝ) := by
      rw [show p + (q + 1) + 1 = (p + q + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hf2 : ((p + 1 + q + 1).factorial : ℝ) = ((p : ℝ) + q + 2) * ((p + q + 1).factorial : ℝ) := by
      rw [show p + 1 + q + 1 = (p + q + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    have hf3 : ((p + 1).factorial : ℝ) = ((p : ℝ) + 1) * (p.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf4 : ((q + 1).factorial : ℝ) = ((q : ℝ) + 1) * (q.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpow1 : t ^ (p + 1 + q + 1) = t * t ^ (p + q + 1) := by ring
    have hpow2 : t ^ (p + (q + 1) + 1) = t * t ^ (p + q + 1) := by ring
    rw [hf1, hf2, hf3, hf4, hpow1, hpow2]
    have hX : ((p + q + 1).factorial : ℝ) ≠ 0 := by positivity
    have hY : ((p : ℝ) + q + 2) ≠ 0 := by positivity
    have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
    have hqf : (q.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ## Step 3 (Gronwall): a nonnegative continuous `D` with `D ≤ c ∫_0^t D` vanishes on `[0,T]`. -/

/-- If `D ≥ 0` is continuous and `D(t) ≤ c ∫_0^t D` on `[0,T]`, then `D = 0` on `[0,T]`.
Proof: `G(x) = e^{-cx} E(x)` with `E(x) = ∫_0^x D` has derivative `e^{-cx}(D(x) - cE(x)) ≤ 0`
on `[0,T]`, so `G ≤ G(0) = 0`; since `E ≥ 0`, `E = 0` and then `D ≤ cE = 0`. No sign condition
on `c` is needed. -/
theorem eq_zero_of_le_integral_of_nonneg {T c : ℝ} (D : ℝ → ℝ) (hD : Continuous D)
    (hnn : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hle : ∀ t ∈ Icc 0 T, D t ≤ c * ∫ s in (0 : ℝ)..t, D s) :
    ∀ t ∈ Icc 0 T, D t = 0 := by
  set E : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, D s with hE
  have hEd : ∀ x : ℝ, HasDerivAt E (D x) x := fun x => hasDerivAt_primitive hD x
  set G : ℝ → ℝ := fun x => Real.exp (-c * x) * E x with hG
  have hGd : ∀ x : ℝ, HasDerivAt G (Real.exp (-c * x) * (D x - c * E x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-c * y)) (Real.exp (-c * x) * (-c)) x := by
      have := ((hasDerivAt_id x).const_mul (-c)).exp
      simpa using this
    convert h1.mul (hEd x) using 1
    ring
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hGd x).continuousAt
  have hanti : AntitoneOn G (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => Real.exp (-c * x) * (D x - c * E x)) (convex_Icc 0 T) hGc.continuousOn ?_ ?_
    · intro x _
      exact (hGd x).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Icc 0 T := Ioo_subset_Icc_self hx
      have hle' := hle x hxI
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  intro t ht
  have hT : 0 ≤ T := le_trans ht.1 ht.2
  have hG0 : G t ≤ G 0 := hanti ⟨le_refl 0, hT⟩ ht ht.1
  have hG0' : G 0 = 0 := by simp [hG, hE]
  have hGt : Real.exp (-c * t) * E t ≤ 0 := by linarith
  have hEt0 : 0 ≤ E t :=
    intervalIntegral.integral_nonneg ht.1 (fun u hu => hnn u ⟨hu.1, hu.2.trans ht.2⟩)
  have hEle : E t ≤ 0 := by
    by_contra h
    have h' : 0 < E t := not_le.mp h
    have := mul_pos (Real.exp_pos (-c * t)) h'
    linarith
  have hEzero : E t = 0 := le_antisymm hEle hEt0
  have hDle : D t ≤ c * E t := hle t ht
  rw [hEzero, mul_zero] at hDle
  exact le_antisymm hDle (hnn t ht)

/-! ## Step 2: comparison `M ≤ B` from the convolution inequality. -/

/-- Pointwise convolution bound, the algebraic core of the comparison. With `D = (M-B)_+` and
`0 ≤ M, B ≤ K`: `M(s)M(v) - B(s)B(v) ≤ K D(s) + K D(v)`. -/
theorem pointwise_conv_bound {K ms mv bs bv : ℝ}
    (hmv : 0 ≤ mv) (hmv' : mv ≤ K) (hbs : 0 ≤ bs) (hbs' : bs ≤ K) :
    ms * mv - bs * bv ≤ K * max (ms - bs) 0 + K * max (mv - bv) 0 := by
  have h1 : (ms - bs) * mv ≤ K * max (ms - bs) 0 := by
    rcases le_total (ms - bs) 0 with h | h
    · rw [max_eq_right h]
      nlinarith
    · rw [max_eq_left h]
      nlinarith
  have h2 : bs * (mv - bv) ≤ K * max (mv - bv) 0 := by
    rcases le_total (mv - bv) 0 with h | h
    · rw [max_eq_right h]
      nlinarith
    · rw [max_eq_left h]
      nlinarith
  nlinarith

/-- Comparison: if `M` and `B` are continuous with `0 ≤ M, B ≤ K` on `[0,T]`, `M(0) ≤ B(0)`,
`M'(t) ≤ a (M ⋆ M)(t)` and `B'(t) = a (B ⋆ B)(t)` on `(0,T)`, then `M ≤ B` on `[0,T]`.

Proof: `Ψ(x) = (M - B)(x) - a ∫_0^x G` with `G = M⋆M - B⋆B` is antitone on `[0,T]` (its
derivative is `M' - a M⋆M ≤ 0`), so `M - B ≤ a ∫_0^x G`. With `D = (M-B)_+` and
`F = ∫_0^· D`, the pointwise bound gives `G ≤ 2K F`, hence `M - B ≤ 2aKT F` on `[0,T]`. Then
`D ≤ c F` with `c = 2aKT`, and Gronwall gives `D = 0`. -/
theorem comparison_of_convolution_inequality {a T K : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (M B M' : ℝ → ℝ) (hM : Continuous M) (hB : Continuous B)
    (hM0 : M 0 ≤ B 0)
    (hMb : ∀ t ∈ Icc 0 T, 0 ≤ M t ∧ M t ≤ K) (hBb : ∀ t ∈ Icc 0 T, 0 ≤ B t ∧ B t ≤ K)
    (hMd : ∀ t ∈ Ioo 0 T, HasDerivAt M (M' t) t)
    (hBd : ∀ t ∈ Ioo 0 T, HasDerivAt B (a * conv B B t) t)
    (hMM : ∀ t ∈ Ioo 0 T, M' t ≤ a * conv M M t) :
    ∀ t ∈ Icc 0 T, M t ≤ B t := by
  set G : ℝ → ℝ := fun u => conv M M u - conv B B u with hGdef
  have hGc : Continuous G := (continuous_conv hM hM).sub (continuous_conv hB hB)
  set I : ℝ → ℝ := fun x => a * ∫ s in (0 : ℝ)..x, G s with hIdef
  have hId : ∀ x : ℝ, HasDerivAt I (a * G x) x := fun x =>
    (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 x)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt).const_mul a
  have hIc : Continuous I := continuous_iff_continuousAt.2 fun x => (hId x).continuousAt
  set Ψ : ℝ → ℝ := fun x => M x - B x - I x with hΨdef
  have hΨc : Continuous Ψ := (hM.sub hB).sub hIc
  have hanti : AntitoneOn Ψ (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => M' x - a * conv B B x - a * G x) (convex_Icc 0 T) hΨc.continuousOn ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (((hMd x hx).sub (hBd x hx)).sub (hId x)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have h := hMM x hx
      have key : M' x - a * conv B B x - a * G x = M' x - a * conv M M x := by
        simp only [hGdef]
        ring
      rw [key]
      linarith
  -- `M - B ≤ I` on `[0,T]`
  have hfI : ∀ t ∈ Icc 0 T, M t - B t ≤ I t := by
    intro t ht
    have hΨ0 : Ψ 0 ≤ 0 := by
      simp only [hΨdef, hIdef, intervalIntegral.integral_same, mul_zero, sub_zero]
      linarith
    have hΨt : Ψ t ≤ Ψ 0 := hanti ⟨le_refl 0, hT⟩ ht ht.1
    simp only [hΨdef] at hΨt
    linarith
  -- positive part `D` and its primitive `F`
  set D : ℝ → ℝ := fun x => max (M x - B x) 0 with hDdef
  have hDc : Continuous D := (hM.sub hB).max continuous_const
  have hDnn : ∀ x, 0 ≤ D x := fun x => le_max_right _ _
  set F : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, D s with hFdef
  have hFc : Continuous F := continuous_primitive_of_continuous hDc
  have hFnn : ∀ x, 0 ≤ x → 0 ≤ F x := fun x hx =>
    intervalIntegral.integral_nonneg hx (fun u _ => hDnn u)
  -- `G ≤ 2K F` on `[0,T]`
  have hGbound : ∀ u ∈ Icc 0 T, G u ≤ 2 * K * F u := by
    intro u hu
    have hsub : Continuous fun s : ℝ => u - s := continuous_const.sub continuous_id
    have hMint : Continuous fun s : ℝ => M s * M (u - s) := hM.mul (hM.comp hsub)
    have hBint : Continuous fun s : ℝ => B s * B (u - s) := hB.mul (hB.comp hsub)
    have hGsplit : G u = ∫ s in (0 : ℝ)..u, (M s * M (u - s) - B s * B (u - s)) := by
      simp only [hGdef, conv]
      rw [intervalIntegral.integral_sub (hMint.intervalIntegrable 0 u)
        (hBint.intervalIntegrable 0 u)]
    have hrefl : ∫ s in (0 : ℝ)..u, D (u - s) = F u := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => D x) u]
      simp only [sub_self, sub_zero]
      rfl
    have hD1 : Continuous fun s : ℝ => K * D s := hDc.const_mul K
    have hD2 : Continuous fun s : ℝ => K * D (u - s) := (hDc.comp hsub).const_mul K
    have hF' : ∫ s in (0 : ℝ)..u, D s = F u := rfl
    have hsplit : ∫ s in (0 : ℝ)..u, (K * D s + K * D (u - s)) = 2 * K * F u := by
      rw [intervalIntegral.integral_add (hD1.intervalIntegrable 0 u) (hD2.intervalIntegrable 0 u)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hrefl, hF']
      ring
    rw [hGsplit, ← hsplit]
    apply intervalIntegral.integral_mono_on hu.1
    · exact (hMint.sub hBint).intervalIntegrable 0 u
    · exact ((hDc.const_mul K).add ((hDc.comp hsub).const_mul K)).intervalIntegrable 0 u
    · intro s hs
      have hs0 : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hu.2⟩
      have hv0 : u - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1, hu.2]⟩
      have hpc : M s * M (u - s) - B s * B (u - s)
          ≤ K * max (M s - B s) 0 + K * max (M (u - s) - B (u - s)) 0 :=
        pointwise_conv_bound (hMb (u - s) hv0).1 (hMb (u - s) hv0).2
          (hBb s hs0).1 (hBb s hs0).2
      simp only [hDdef]
      exact hpc
  -- `I ≤ 2 a K T F` on `[0,T]`
  have hIle : ∀ t ∈ Icc 0 T, I t ≤ 2 * a * K * T * F t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hG1 : ∫ s in (0 : ℝ)..t, G s ≤ ∫ s in (0 : ℝ)..t, 2 * K * F s :=
      intervalIntegral.integral_mono_on ht0 (hGc.intervalIntegrable 0 t)
        ((continuous_const.mul hFc).intervalIntegrable 0 t)
        (fun s hs => hGbound s ⟨hs.1, hs.2.trans ht.2⟩)
    have hF1 : ∫ s in (0 : ℝ)..t, 2 * K * F s ≤ ∫ s in (0 : ℝ)..t, 2 * K * F t := by
      apply intervalIntegral.integral_mono_on ht0
        ((continuous_const.mul hFc).intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t)
      intro s hs
      have hmono : F s ≤ F t := by
        simp only [hFdef]
        exact intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
          (Filter.Eventually.of_forall fun x => hDnn x) (hDc.intervalIntegrable 0 t)
      exact mul_le_mul_of_nonneg_left hmono (by linarith)
    have hconst : ∫ s in (0 : ℝ)..t, 2 * K * F t = t * (2 * K * F t) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hnn : 0 ≤ 2 * K * F t := mul_nonneg (mul_nonneg (by norm_num) hK) (hFnn t ht0)
    have htT : t * (2 * K * F t) ≤ T * (2 * K * F t) :=
      mul_le_mul_of_nonneg_right ht.2 hnn
    have hIeq : I t = a * ∫ s in (0 : ℝ)..t, G s := rfl
    rw [hIeq]
    calc a * ∫ s in (0 : ℝ)..t, G s
        ≤ a * (T * (2 * K * F t)) := by
          apply mul_le_mul_of_nonneg_left _ ha
          linarith [hG1, hF1, hconst, htT]
      _ = 2 * a * K * T * F t := by ring
  -- `D ≤ c F` on `[0,T]` and Gronwall
  have hDle : ∀ t ∈ Icc 0 T, D t ≤ (2 * a * K * T) * ∫ s in (0 : ℝ)..t, D s := by
    intro t ht
    have hpos : 0 ≤ 2 * a * K * T * F t :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hK) hT) (hFnn t ht.1)
    have h1 : M t - B t ≤ 2 * a * K * T * F t := (hfI t ht).trans (hIle t ht)
    have h2 : D t ≤ 2 * a * K * T * F t := max_le h1 hpos
    simpa [hFdef] using h2
  have hzero := eq_zero_of_le_integral_of_nonneg (T := T) (c := 2 * a * K * T) D hDc
    (fun t _ => hDnn t) hDle
  intro t ht
  have h1 : D t = 0 := hzero t ht
  have h2 : M t - B t ≤ D t := le_max_left _ _
  linarith

/-! ## Catalan series: Cauchy product and the convolution identity `B ⋆ B = ∑ a^n C_{n+1} t^{2n+1}/(2n+1)!`. -/

/-- Coefficient `c_n = C_n a^n / (2n)!` of the Catalan series. -/
def cc (a : ℝ) (n : ℕ) : ℝ := (catalan n : ℝ) * a ^ n / ((2 * n).factorial : ℝ)

theorem cc_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ cc a n := by
  unfold cc
  have hf : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) := by positivity
  exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg ha n)) hf

theorem catalanSeries_eq (a t : ℝ) : catalanSeries a t = ∑' n : ℕ, cc a n * t ^ (2 * n) := by
  unfold catalanSeries cc
  exact tsum_congr fun n => by ring

theorem summable_catalan_term (a t : ℝ) (ha : 0 ≤ a) :
    Summable fun n : ℕ => (catalan n : ℝ) * a ^ n * t ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have hcos := Real.hasSum_cosh (2 * Real.sqrt a * t)
  refine Summable.of_nonneg_of_le ?_ (catalanSeries_term_le a t ha) hcos.summable
  intro n
  have hC : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  have htpow : 0 ≤ t ^ (2 * n) := by rw [pow_mul]; positivity
  have hf : (0 : ℝ) ≤ ((2 * n).factorial : ℝ) := by positivity
  exact div_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg ha n)) htpow) hf

theorem summable_norm_cc (a x : ℝ) (ha : 0 ≤ a) :
    Summable fun n : ℕ => ‖cc a n * x ^ (2 * n)‖ := by
  refine (summable_catalan_term a x ha).congr fun n => ?_
  have htpow : 0 ≤ x ^ (2 * n) := by rw [pow_mul]; positivity
  rw [Real.norm_of_nonneg (mul_nonneg (cc_nonneg ha n) htpow)]
  unfold cc
  ring

/-- Cauchy product of two Catalan series, indexed by antidiagonals. -/
theorem cauchy_catalanSeries (a : ℝ) (ha : 0 ≤ a) (s u : ℝ) :
    catalanSeries a s * catalanSeries a u
      = ∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * u ^ (2 * kl.2)) := by
  rw [catalanSeries_eq, catalanSeries_eq]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_cc a s ha) (summable_norm_cc a u ha)

/-- Termwise bound on `0 ≤ s ≤ t`, `0 ≤ u ≤ t`: `|c_j s^{2j} c_k u^{2k}| ≤ c_j c_k t^{2(j+k)}`. -/
theorem norm_term_le {a s u t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t)
    (hu : 0 ≤ u) (hut : u ≤ t) (j k : ℕ) :
    ‖(cc a j * s ^ (2 * j)) * (cc a k * u ^ (2 * k))‖
      ≤ cc a j * cc a k * t ^ (2 * (j + k)) := by
  have hs2 : s ^ (2 * j) ≤ t ^ (2 * j) := pow_le_pow_left₀ hs hst _
  have hu2 : u ^ (2 * k) ≤ t ^ (2 * k) := pow_le_pow_left₀ hu hut _
  have hsn : 0 ≤ s ^ (2 * j) := by rw [pow_mul]; positivity
  have hun : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
  have hcj := cc_nonneg ha j
  have hck := cc_nonneg ha k
  have hnn : 0 ≤ (cc a j * s ^ (2 * j)) * (cc a k * u ^ (2 * k)) :=
    mul_nonneg (mul_nonneg hcj hsn) (mul_nonneg hck hun)
  have ht0 : 0 ≤ t := le_trans hs hst
  rw [Real.norm_of_nonneg hnn]
  calc (cc a j * s ^ (2 * j)) * (cc a k * u ^ (2 * k))
      ≤ (cc a j * t ^ (2 * j)) * (cc a k * t ^ (2 * k)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs2 hcj) (mul_le_mul_of_nonneg_left hu2 hck)
          (mul_nonneg hck hun) (mul_nonneg hcj (pow_nonneg ht0 _))
    _ = cc a j * cc a k * t ^ (2 * (j + k)) := by ring

/-- Termwise bound summed over an antidiagonal, for `0 ≤ s ≤ t`. -/
theorem sum_term_le {a t s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))‖
      ≤ (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n) := by
  have hu : 0 ≤ t - s := by linarith
  have hut : t - s ≤ t := by linarith
  calc ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))‖
      ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          ‖(cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))‖ := norm_sum_le _ _
    _ ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          cc a kl.1 * cc a kl.2 * t ^ (2 * n) := by
        apply Finset.sum_le_sum
        intro kl hkl
        have hn := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
        have h := norm_term_le ha hs hst hu hut kl.1 kl.2
        rw [hn] at h
        exact h
    _ = (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n) :=
        (Finset.sum_mul _ _ _).symm

/-- The dominating sequence `K_n t^{2n}` is summable. -/
theorem summable_sum_bound (a t : ℝ) (ha : 0 ≤ a) :
    Summable fun n : ℕ =>
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n) := by
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm
    (summable_norm_cc a t ha) (summable_norm_cc a t ha)).of_norm
  refine h.congr fun n => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hn := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
  rw [← hn]
  ring

/-- Monomial integral of one antidiagonal term. -/
theorem integral_term (a t : ℝ) (n j k : ℕ) (hn : j + k = n) :
    ∫ s in (0 : ℝ)..t, (cc a j * s ^ (2 * j)) * (cc a k * (t - s) ^ (2 * k))
      = (a ^ n * t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
          * ((catalan j : ℝ) * (catalan k : ℝ)) := by
  subst hn
  have hfun : (fun s : ℝ => (cc a j * s ^ (2 * j)) * (cc a k * (t - s) ^ (2 * k)))
      = fun s => (cc a j * cc a k) * (s ^ (2 * j) * (t - s) ^ (2 * k)) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow_mul_sub_pow (2 * k) (2 * j) t]
  rw [show 2 * (j + k) + 1 = 2 * j + 2 * k + 1 by ring]
  unfold cc
  have h1 : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * j + 2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Integral of the antidiagonal block: `∫_0^t ∑_{j+k=n} c_j c_k s^{2j}(t-s)^{2k} ds
= a^n C_{n+1} t^{2n+1}/(2n+1)!`. -/
theorem integral_F (a t : ℝ) (n : ℕ) :
    ∫ s in (0 : ℝ)..t, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))
      = a ^ n * (catalan (n + 1) : ℝ) * t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  have hint : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      IntervalIntegrable (fun s : ℝ =>
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2)))
        MeasureTheory.volume 0 t := fun kl _ =>
    (Continuous.intervalIntegrable (by fun_prop) 0 t)
  rw [intervalIntegral.integral_finsetSum hint]
  rw [Finset.sum_congr rfl (fun kl hkl => integral_term a t n kl.1 kl.2
    (Finset.HasAntidiagonal.mem_antidiagonal.1 hkl))]
  have hc : (catalan (n + 1) : ℝ) = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (catalan kl.1 : ℝ) * (catalan kl.2 : ℝ) := by
    rw [catalan_succ']
    push_cast
    rfl
  rw [hc, ← Finset.mul_sum]
  ring

/-- Convolution identity for the Catalan series: `(B ⋆ B)(t) = ∑_n a^n C_{n+1} t^{2n+1}/(2n+1)!`
for `t ≥ 0`, by dominated convergence over the antidiagonal blocks. -/
theorem hasSum_conv_catalan (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    HasSum (fun n : ℕ => a ^ n * (catalan (n + 1) : ℝ) * t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
      (conv (catalanSeries a) (catalanSeries a) t) := by
  have hcont : ∀ n : ℕ, Continuous (fun s : ℝ =>
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))) :=
    fun n => by fun_prop
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ =>
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 t)) :=
    fun n => (hcont n).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc 0 t →
      ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2))‖
        ≤ (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n) := by
    intro n
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le ht] at hs
    exact sum_term_le ha hs.1.le hs.2 n
  have hbs : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc 0 t →
      Summable fun n : ℕ =>
        (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n) :=
    Filter.Eventually.of_forall fun _ _ => summable_sum_bound a t ha
  have hbi : IntervalIntegrable (fun _ : ℝ =>
      ∑' n : ℕ, (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, cc a kl.1 * cc a kl.2) * t ^ (2 * n))
      MeasureTheory.volume 0 t := intervalIntegrable_const
  have hlim : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc 0 t →
      HasSum (fun n : ℕ =>
          ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
            (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2)))
        (catalanSeries a s * catalanSeries a (t - s)) := by
    refine Filter.Eventually.of_forall fun s _ => ?_
    have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm
      (summable_norm_cc a s ha) (summable_norm_cc a (t - s) ha)).of_norm
    rw [cauchy_catalanSeries a ha s (t - s)]
    exact hsum.hasSum
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := t)
    (F := fun (n : ℕ) (s : ℝ) => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (cc a kl.1 * s ^ (2 * kl.1)) * (cc a kl.2 * (t - s) ^ (2 * kl.2)))
    (f := fun s : ℝ => catalanSeries a s * catalanSeries a (t - s))
    (fun (n : ℕ) (_ : ℝ) => (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        cc a kl.1 * cc a kl.2) * t ^ (2 * n))
    hmeas hbound hbs hbi hlim
  convert key using 1
  funext n
  exact (integral_F a t n).symm
  rfl

/-! ## Termwise derivative of the Catalan series and the identity `B' = a (B ⋆ B)`. -/

theorem two_mul_le_four_pow (n : ℕ) : ((2 * n : ℕ) : ℝ) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ]
    push_cast at ih
    nlinarith

/-- Summable dominating sequence for the termwise derivative, for `R ≥ 1`:
`C_n a^n (2n) R^{2n}/(2n)! ≤ (4√a R)^{2n}/(2n)!`, using `C_n ≤ 4^n` and `2n ≤ 4^n`. -/
theorem summable_deriv_bound (a R : ℝ) (ha : 0 ≤ a) (hR : 1 ≤ R) :
    Summable fun n : ℕ => cc a n * (((2 * n : ℕ) : ℝ) * R ^ (2 * n)) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hcos := Real.hasSum_cosh (4 * Real.sqrt a * R)
  refine Summable.of_nonneg_of_le ?_ ?_ hcos.summable
  · intro n
    exact mul_nonneg (cc_nonneg ha n) (mul_nonneg (by positivity) (pow_nonneg hR0 _))
  · intro n
    have hsq : Real.sqrt a ^ (2 * n) = a ^ n := by rw [pow_mul, Real.sq_sqrt ha]
    have hpow : (4 * Real.sqrt a * R) ^ (2 * n) = 4 ^ (2 * n) * a ^ n * R ^ (2 * n) := by
      calc (4 * Real.sqrt a * R) ^ (2 * n)
          = 4 ^ (2 * n) * Real.sqrt a ^ (2 * n) * R ^ (2 * n) := by ring
        _ = 4 ^ (2 * n) * a ^ n * R ^ (2 * n) := by rw [hsq]
    have hC : (catalan n : ℝ) ≤ 4 ^ n := by exact_mod_cast catalan_le_four_pow n
    have h2n : ((2 * n : ℕ) : ℝ) ≤ 4 ^ n := two_mul_le_four_pow n
    have h4 : (4 : ℝ) ^ n * 4 ^ n = 4 ^ (2 * n) := by rw [← pow_add]; ring_nf
    have hfac : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
    have hnum : (catalan n : ℝ) * (((2 * n : ℕ) : ℝ)) ≤ 4 ^ (2 * n) := by
      rw [← h4]
      exact mul_le_mul hC h2n (by positivity) (by positivity)
    have hw : (0 : ℝ) ≤ a ^ n * R ^ (2 * n) := mul_nonneg (pow_nonneg ha n) (pow_nonneg hR0 _)
    rw [hpow]
    unfold cc
    have key : (catalan n : ℝ) * a ^ n / ((2 * n).factorial : ℝ) * (((2 * n : ℕ) : ℝ) * R ^ (2 * n))
        = ((catalan n : ℝ) * (((2 * n : ℕ) : ℝ))) * (a ^ n * R ^ (2 * n))
            / ((2 * n).factorial : ℝ) := by
      field_simp
    rw [key]
    apply div_le_div_of_nonneg_right _ hfac.le
    calc ((catalan n : ℝ) * (((2 * n : ℕ) : ℝ))) * (a ^ n * R ^ (2 * n))
        ≤ 4 ^ (2 * n) * (a ^ n * R ^ (2 * n)) := mul_le_mul_of_nonneg_right hnum hw
      _ = 4 ^ (2 * n) * a ^ n * R ^ (2 * n) := by ring

/-- Termwise derivative bound: for `|x| ≤ R`, `R ≥ 1`. -/
theorem norm_deriv_term_le (a x R : ℝ) (ha : 0 ≤ a) (hx : |x| ≤ R) (hR : 1 ≤ R) (n : ℕ) :
    ‖cc a n * (((2 * n : ℕ) : ℝ) * x ^ (2 * n - 1))‖
      ≤ cc a n * (((2 * n : ℕ) : ℝ) * R ^ (2 * n)) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hc := cc_nonneg ha n
  have h2 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by positivity
  rw [norm_mul, Real.norm_of_nonneg hc, norm_mul, Real.norm_natCast, norm_pow, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ hc
  apply mul_le_mul_of_nonneg_left _ h2
  calc |x| ^ (2 * n - 1) ≤ R ^ (2 * n - 1) := pow_le_pow_left₀ (abs_nonneg x) hx _
    _ ≤ R ^ (2 * n) := pow_le_pow_right₀ hR (Nat.sub_le _ _)

/-- Termwise differentiation of the Catalan series at every real point. -/
theorem hasDerivAt_catalanSeries (a : ℝ) (ha : 0 ≤ a) (y : ℝ) :
    HasDerivAt (catalanSeries a)
      (∑' n : ℕ, cc a n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1))) y := by
  set R : ℝ := |y| + 1 with hRdef
  have hR : 1 ≤ R := by linarith [abs_nonneg y]
  have hyI : y ∈ Set.Ioo (-R) R := by
    constructor
    · linarith [neg_abs_le y, abs_nonneg y]
    · linarith [le_abs_self y, abs_nonneg y]
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℕ) (z : ℝ) => cc a n * z ^ (2 * n))
    (g' := fun (n : ℕ) (z : ℝ) => cc a n * (((2 * n : ℕ) : ℝ) * z ^ (2 * n - 1)))
    (u := fun n : ℕ => cc a n * (((2 * n : ℕ) : ℝ) * R ^ (2 * n)))
    (y₀ := y) (t := Set.Ioo (-R) R) (y := y)
    (summable_deriv_bound a R ha hR) isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => (hasDerivAt_pow (2 * n) z).const_mul (cc a n))
    (fun n z hz => norm_deriv_term_le a z R ha (abs_le.2 ⟨hz.1.le, hz.2.le⟩) hR n)
    hyI ((summable_norm_cc a y ha).of_norm) hyI
  have hfun : catalanSeries a = fun z => ∑' n : ℕ, cc a n * z ^ (2 * n) :=
    funext (catalanSeries_eq a)
  rw [hfun]
  exact hd

/-- The derivative identity `B'(t) = a (B ⋆ B)(t)` for `t ≥ 0` (the Catalan series of the report). -/
theorem hasDerivAt_catalanSeries_conv (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (hy : 0 ≤ y) :
    HasDerivAt (catalanSeries a) (a * conv (catalanSeries a) (catalanSeries a) y) y := by
  have h := hasDerivAt_catalanSeries a ha y
  have hval : (∑' n : ℕ, cc a n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)))
      = a * conv (catalanSeries a) (catalanSeries a) y := by
    rw [← (hasSum_conv_catalan a y ha hy).tsum_eq, ← tsum_mul_left]
    have hsum : Summable fun n : ℕ => cc a n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) :=
      Summable.of_norm_bounded (summable_deriv_bound a (|y| + 1) ha (by linarith [abs_nonneg y]))
        (fun n => norm_deriv_term_le a y (|y| + 1) ha (by linarith) (by linarith [abs_nonneg y]) n)
    rw [hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
    refine tsum_congr fun n => ?_
    have hfac : ((2 * (n + 1)).factorial : ℝ)
        = (((2 * n + 1 : ℕ) : ℝ) + 1) * ((2 * n + 1).factorial : ℝ) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    have hpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by positivity
    unfold cc
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, hfac]
    push_cast
    have hd : (2 * (n : ℝ) + 1 + 1) ≠ 0 := by positivity
    have hF : ((2 * n + 1).factorial : ℝ) ≠ 0 := hpos.ne'
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Continuity of the Catalan series on `ℝ`. -/
theorem continuous_catalanSeries (a : ℝ) (ha : 0 ≤ a) : Continuous (catalanSeries a) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_catalanSeries a ha y).continuousAt

/-- Value at zero: `B(0) = C_0 = 1`. -/
theorem catalanSeries_zero (a : ℝ) : catalanSeries a 0 = 1 := by
  rw [catalanSeries_eq]
  rw [tsum_eq_single 0]
  · simp [cc]
  · intro n hn
    have : (2 * n) ≠ 0 := by omega
    simp [zero_pow this]

/-! ## Assembly: the source comparison theorem `M(t) ≤ e^{2√a t}` (REG-001). -/

theorem catalanSeries_nonneg (a : ℝ) (ha : 0 ≤ a) (x : ℝ) : 0 ≤ catalanSeries a x := by
  rw [catalanSeries_eq]
  exact tsum_nonneg fun n => mul_nonneg (cc_nonneg ha n) (by rw [pow_mul]; positivity)

/-- Source REG-001 (`CC:convolution-comparison`): for `a ≥ 0` and `M` continuous on `[0,∞)` with
`M(0) = 1`, `M > 0`, differentiable on `(0,∞)` with `M'(t) ≤ a ∫_0^t M(s)M(t-s) ds` for `t > 0`,
we get `M(t) ≤ e^{2√a t}` for all `t ≥ 0`. The hypotheses are weaker than the report's
`C^1` on `[0,∞)` (derivative only on `(0,∞)`, continuity on `[0,∞)`), so this covers it. -/
theorem convolution_comparison_bound (a : ℝ) (ha : 0 ≤ a) (M M' : ℝ → ℝ)
    (hMc : ContinuousOn M (Set.Ici 0)) (hM0 : M 0 = 1)
    (hMpos : ∀ t, 0 ≤ t → 0 < M t)
    (hMd : ∀ t, 0 < t → HasDerivAt M (M' t) t)
    (hMineq : ∀ t, 0 < t → M' t ≤ a * ∫ s in (0 : ℝ)..t, M s * M (t - s)) :
    ∀ t, 0 ≤ t → M t ≤ Real.exp (2 * Real.sqrt a * t) := by
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    simp [hM0]
  -- extension of `M` to `ℝ` by `M(max x 0)`
  set Mx : ℝ → ℝ := fun x => M (max x 0) with hMxdef
  have hMxc : Continuous Mx :=
    hMc.comp_continuous (continuous_id.max continuous_const) fun x => le_max_right x 0
  have hMx_eq : ∀ x, 0 ≤ x → Mx x = M x := fun x hx => by
    simp only [hMxdef, max_eq_left hx]
  have hBc : Continuous (catalanSeries a) := continuous_catalanSeries a ha
  -- bounds on `[0,t]`
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hMxc.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hBc.continuousOn
  set K : ℝ := max (max C1 C2) 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hMb : ∀ x ∈ Set.Icc (0 : ℝ) t, 0 ≤ Mx x ∧ Mx x ≤ K := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hMx_eq x hx.1]
      exact (hMpos x hx.1).le
    · have h1 := hC1 x hx
      rw [Real.norm_eq_abs] at h1
      exact le_trans (le_trans (le_abs_self _) h1) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hBb : ∀ x ∈ Set.Icc (0 : ℝ) t, 0 ≤ catalanSeries a x ∧ catalanSeries a x ≤ K := by
    intro x hx
    refine ⟨catalanSeries_nonneg a ha x, ?_⟩
    have h1 := hC2 x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_trans (le_abs_self _) h1) (le_trans (le_max_right _ _) (le_max_left _ _))
  -- derivative of `Mx` on `(0,t)` and the convolution inequality in the extended form
  have hMxd : ∀ x ∈ Set.Ioo (0 : ℝ) t, HasDerivAt Mx (M' x) x := by
    intro x hx
    refine (hMd x hx.1).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx.1] with y hy
    exact hMx_eq y (le_of_lt hy)
  have hMxMM : ∀ x ∈ Set.Ioo (0 : ℝ) t, M' x ≤ a * conv Mx Mx x := by
    intro x hx
    have hconv : conv Mx Mx x = ∫ s in (0 : ℝ)..x, M s * M (x - s) := by
      unfold conv
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le hx.1.le] at hs
      rw [hMx_eq s hs.1, hMx_eq (x - s) (by linarith [hs.2])]
    rw [hconv]
    exact hMineq x hx.1
  have hBd : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (catalanSeries a) (a * conv (catalanSeries a) (catalanSeries a) x) x :=
    fun x hx => hasDerivAt_catalanSeries_conv a ha x hx.1.le
  have hcomp := comparison_of_convolution_inequality (T := t) (K := K) ha ht hK Mx
    (catalanSeries a) M' hMxc hBc (by rw [hMx_eq 0 le_rfl, hM0, catalanSeries_zero])
    hMb hBb hMxd hBd hMxMM
  have hMt : M t ≤ catalanSeries a t := by
    have := hcomp t ⟨ht, le_rfl⟩
    rwa [hMx_eq t ht] at this
  have hcos : catalanSeries a t ≤ Real.cosh (2 * Real.sqrt a * t) := catalanSeries_le_cosh a ha t
  have hexp : Real.cosh (2 * Real.sqrt a * t) ≤ Real.exp (2 * Real.sqrt a * t) :=
    cosh_le_exp_of_nonneg (by have := Real.sqrt_nonneg a; positivity)
  exact le_trans hMt (le_trans hcos hexp)

end

end QuantumNLS.ConvolutionComparison

/-! Axiom check for the headline declarations (compile-log evidence). -/
#print axioms QuantumNLS.ConvolutionComparison.convolution_comparison_bound
#print axioms QuantumNLS.ConvolutionComparison.hasSum_conv_catalan
#print axioms QuantumNLS.ConvolutionComparison.hasDerivAt_catalanSeries_conv
#print axioms QuantumNLS.ConvolutionComparison.continuous_catalanSeries
#print axioms QuantumNLS.ConvolutionComparison.catalanSeries_zero
#print axioms QuantumNLS.ConvolutionComparison.comparison_of_convolution_inequality
#print axioms QuantumNLS.ConvolutionComparison.catalan_le_four_pow
