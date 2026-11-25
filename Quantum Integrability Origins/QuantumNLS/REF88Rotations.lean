import Mathlib
import QuantumNLS.RephasingFlow
import QuantumNLS.ChartFrequencies

/-!
# REF88Rotations: the rough-field extension step of R-EF8C2837 (`thm:global-physical-dynamics`)

Source: `source-text/chapters/global/physical_cubic.tex`, proof paragraph "Extension to rough fields
without a rough Hamiltonian" (printed lines 177 to 214).  This module is the purely `ℓ²`-level
(soft analysis) part.  It does NOT use the physical flow, the chart, the quantum limits or REG-015.

Setting.  `E = ℓ²(ℤ;ℂ)` (`RephasingFlow.E`).  `A : ℝ → E → E` stands for `A^t = Φ S^t Φ⁻¹`.
`RoughGroup A` records exactly the facts the printed proof has established at that point:

* `A` is a jointly continuous group on `ℓ²` (printed: "jointly continuous group on `ℓ²`");
* `A` preserves each `q_n(z) = |z_n|²` (printed: "preserving each `q_n`");
* on finitely supported sequences `A^t` commutes with coordinate rotations (printed: "On finitely
  supported sequences, the preceding calculation makes it commute with every finite collection of
  coordinate rotations").  The hypothesis is stated for arbitrary angle arrays `θ` and finitely supported
  `z`; for finitely supported `z` only `θ` restricted to the support of `z` matters on both sides, so
  this is the same statement.

Printed steps and their Lean counterparts.

* "Density and continuity extend that commutation to all sequences": `RoughGroup.rot_comm`.
* "Every sequence with these moduli is a norm limit of finite rotations of `b`" (here exactly a
  rotation, `ChartFrequencies.exists_rotE_of_norm_eq`) and "the ratio `c_n(t,a)=A^t(b)_n/b_n` is the same
  at every point of that torus": `RoughGroup.ratio`, `RoughGroup.char_apply`.
* "unit modulus, continuous, `c_n(t+s,a)=c_n(t,a)c_n(s,a)`": `RoughGroup.char_*`.
* "It is therefore linear ... gives the unique real number `ν_n(a)` with `c_n(t,a)=e^{-itν_n(a)}`":
  `exists_freq_of_character` (a continuous unit-modulus character of `ℝ` is `t ↦ e^{-itν}`) and
  `RoughGroup.exists_freq`, `nuOf`.
* "If `a^j → a` in `ℓ¹` and `a_n>0` then `√a^j → √a` in `ℓ²` using `|√x-√y|² ≤ |x-y|`.  Joint continuity
  on a fixed compact time interval gives uniform convergence of the coordinate curves.  The positive
  denominators stay away from zero, so the characters converge uniformly there.  Such convergence forces
  their real frequencies to converge: if `|d| ≥ ε > 0` the maximum of `|e^{itd}-1|` over `|t| ≤ 1` is bounded
  below by a positive number depending only on `min{ε,π}`": `sqrtE_dist_le`, `freq_sep`,
  `RoughGroup.nuOf_continuousOn`.
* "A zero action gives an identically zero coordinate by conservation, with no ratio used":
  `RoughGroup.zero_coord`.
* "Unit-modulus multipliers preserve every weighted squared norm.  Finite-head and invariant-tail
  approximation proves strong continuity on each fixed-action torus": `RoughGroup.weighted_preserve`,
  `RoughGroup.weighted_continuous` (dominated convergence for the tail; works for every nonnegative
  weight, in particular for `(1+|2πn/L|)^{2s}`).

Final named theorem of this module: `QuantumNLS.REF88Rotations.rough_extension`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ENNReal Topology
open Filter

namespace QuantumNLS.REF88Rotations

open QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies

/-! ### The hypotheses -/

/-- The facts about `A^t = Φ S^t Φ⁻¹` available at the start of the printed rough-extension step. -/
structure RoughGroup (A : ℝ → E → E) : Prop where
  zero : ∀ z, A 0 z = z
  add : ∀ s t z, A (s + t) z = A s (A t z)
  cont : Continuous (fun p : ℝ × E => A p.1 p.2)
  modulus : ∀ t z n, ‖A t z n‖ = ‖z n‖
  finrot : ∀ (t : ℝ) (θ : ℤ → ℝ) (z : E), (∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0) →
    A t (rotE θ z) = rotE θ (A t z)

/-! ### Truncation and rotations -/

/-- The truncation of `z` to the labels `-K, …, K`. -/
def zTrunc (z : E) (K : ℕ) : E :=
  ∑ m ∈ Finset.Icc (-(K : ℤ)) K, lp.single (E := fun _ : ℤ => ℂ) 2 m (z m)

lemma zTrunc_apply (z : E) (K : ℕ) (n : ℤ) :
    zTrunc z K n = if n ∈ Finset.Icc (-(K : ℤ)) K then z n else 0 := by
  unfold zTrunc
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_single]
  by_cases h : n ∈ Finset.Icc (-(K : ℤ)) K
  · rw [if_pos h, Finset.sum_eq_single n]
    · simp
    · intro m _ hm; simp [Pi.single_apply, Ne.symm hm]
    · intro hn; exact absurd h hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m hm
    have : n ≠ m := fun e => h (e ▸ hm)
    simp [Pi.single_apply, this]

lemma tendsto_zTrunc (z : E) : Tendsto (zTrunc z) atTop (𝓝 z) := by
  have hs := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) z
  have hmono : Monotone (fun K : ℕ => Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
    intro a b hab m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  have hcof : Tendsto (fun K : ℕ => Finset.Icc (-(K : ℤ)) (K : ℤ)) atTop atTop :=
    Filter.tendsto_atTop_finset_of_monotone hmono (fun x => ⟨x.natAbs, by
      simp only [Finset.mem_Icc]; omega⟩)
  have h1 : Tendsto (fun s : Finset ℤ => ∑ m ∈ s,
      lp.single (E := fun _ : ℤ => ℂ) 2 m (z m)) atTop (𝓝 z) := by
    simpa [HasSum] using hs
  exact h1.comp hcof

lemma norm_rotE_sub (θ : ℤ → ℝ) (x y : E) : ‖rotE θ x - rotE θ y‖ = ‖x - y‖ := by
  apply norm_eq_of_norm_apply_eq
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply, rotE_apply]
  rw [← mul_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_rotE (θ : ℤ → ℝ) : Continuous (rotE θ) := by
  have : Isometry (rotE θ) := Isometry.of_dist_eq fun x y => by
    simp only [dist_eq_norm, norm_rotE_sub]
  exact this.continuous

lemma RoughGroup.continuous_time_slice {A : ℝ → E → E} (h : RoughGroup A) (t : ℝ) :
    Continuous (A t) :=
  h.cont.comp (Continuous.prodMk continuous_const continuous_id)

/-- Density and continuity extend the commutation with coordinate rotations from finitely supported
sequences to all sequences. -/
theorem RoughGroup.rot_comm {A : ℝ → E → E} (h : RoughGroup A) (t : ℝ) (θ : ℤ → ℝ) (z : E) :
    A t (rotE θ z) = rotE θ (A t z) := by
  have hz := tendsto_zTrunc z
  have hfin : ∀ K : ℕ, ∃ F : Finset ℤ, ∀ n, n ∉ F → zTrunc z K n = 0 := fun K =>
    ⟨Finset.Icc (-(K : ℤ)) K, fun n hn => by simp [zTrunc_apply, hn]⟩
  have h1 : Tendsto (fun K => rotE θ (zTrunc z K)) atTop (𝓝 (rotE θ z)) :=
    ((continuous_rotE θ).tendsto z).comp hz
  have l1 := ((h.continuous_time_slice t).tendsto (rotE θ z)).comp h1
  have l2 := ((continuous_rotE θ).tendsto (A t z)).comp
    (((h.continuous_time_slice t).tendsto z).comp hz)
  have heq : (A t ∘ fun K => rotE θ (zTrunc z K)) =
      (rotE θ ∘ (A t ∘ zTrunc z)) := by
    funext K
    exact h.finrot t θ (zTrunc z K) (hfin K)
  rw [heq] at l1
  exact tendsto_nhds_unique l1 l2

/-- Cross-multiplied form of "the ratio `A^t(z)_n / z_n` depends only on the actions". -/
theorem RoughGroup.ratio {A : ℝ → E → E} (h : RoughGroup A) {z w : E}
    (hzw : ∀ n, ‖z n‖ = ‖w n‖) (t : ℝ) (n : ℤ) :
    A t w n * z n = A t z n * w n := by
  obtain ⟨θ, hθ⟩ := exists_rotE_of_norm_eq hzw
  rw [hθ, h.rot_comm, rotE_apply, rotE_apply]
  ring

/-- A zero action gives an identically zero coordinate (conservation, no ratio). -/
theorem RoughGroup.zero_coord {A : ℝ → E → E} (h : RoughGroup A) (t : ℝ) (z : E) (n : ℤ)
    (hn : z n = 0) : A t z n = 0 := by
  have := h.modulus t z n
  rw [hn, norm_zero] at this
  exact norm_eq_zero.mp this

/-! ### The character of one coordinate -/

section Character
variable {A : ℝ → E → E} (h : RoughGroup A) {b : E} {n : ℤ} (hb : b n ≠ 0)

/-- `c_n(t) = A^t(b)_n / b_n`. -/
def charOf (A : ℝ → E → E) (b : E) (n : ℤ) (t : ℝ) : ℂ := A t b n / b n

include h hb

lemma RoughGroup.char_apply (t : ℝ) {w : E} (hw : ∀ m, ‖w m‖ = ‖b m‖) :
    A t w n = charOf A b n t * w n := by
  have := h.ratio (fun m => (hw m).symm) t n
  unfold charOf
  rw [div_mul_eq_mul_div, eq_div_iff hb]
  exact this

lemma RoughGroup.char_zero : charOf A b n 0 = 1 := by
  unfold charOf; rw [h.zero]; exact div_self hb

lemma RoughGroup.char_norm (t : ℝ) : ‖charOf A b n t‖ = 1 := by
  unfold charOf
  rw [norm_div, h.modulus, div_self]
  exact norm_ne_zero_iff.mpr hb

lemma RoughGroup.char_cont : Continuous (charOf A b n) := by
  unfold charOf
  have : Continuous fun t : ℝ => A t b n :=
    (pr n).continuous.comp (h.cont.comp (Continuous.prodMk continuous_id continuous_const))
  exact this.div_const _

lemma RoughGroup.char_add (s t : ℝ) :
    charOf A b n (s + t) = charOf A b n s * charOf A b n t := by
  have hw : ∀ m, ‖A t b m‖ = ‖b m‖ := fun m => h.modulus t b m
  have h1 := h.char_apply hb s hw
  have ht : A t b n = charOf A b n t * b n := by
    unfold charOf
    exact (div_mul_cancel₀ _ hb).symm
  have h2 : A (s + t) b n = charOf A b n s * charOf A b n t * b n := by
    rw [h.add, h1, ht]; ring
  calc charOf A b n (s + t) = A (s + t) b n / b n := rfl
    _ = charOf A b n s * charOf A b n t * b n / b n := by rw [h2]
    _ = _ := mul_div_cancel_right₀ _ hb

end Character

/-! ### A continuous unit-modulus character of `ℝ` is `t ↦ e^{-itν}` -/

lemma exists_freq_of_character (c : ℝ → ℂ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hmod : ∀ t, ‖c t‖ = 1) :
    ∃ ν : ℝ, ∀ t : ℝ, c t = Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) := by
  -- a short interval on which `∫ c ≠ 0`
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc.continuousAt (1 / 2) (by norm_num)
  set d : ℝ := δ / 2 with hd
  have hdpos : 0 < d := by positivity
  set a : ℂ := ∫ s in (0 : ℝ)..d, c s with ha
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) d, ‖c s - 1‖ ≤ 1 / 2 := by
    intro s hs
    rw [Set.uIoc_of_le hdpos.le] at hs
    have : dist s 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; linarith [hs.2]
    have := hδc this
    rw [dist_eq_norm, h0] at this
    exact this.le
  have hint1 : IntervalIntegrable c MeasureTheory.volume 0 d := hc.intervalIntegrable _ _
  have hdiff : ‖a - (d : ℂ)‖ ≤ 1 / 2 * |d - 0| := by
    have : a - (d : ℂ) = ∫ s in (0 : ℝ)..d, (c s - 1) := by
      rw [intervalIntegral.integral_sub hint1 (by simp)]
      simp [ha]
    rw [this]
    exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hane : a ≠ 0 := by
    intro h0'
    rw [h0'] at hdiff
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, sub_zero] at hdiff
    rw [abs_of_pos hdpos] at hdiff
    linarith
  -- `a c(t) = ∫_t^{t+d} c`
  have hFint : ∀ u : ℝ, HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, c s) (c u) u :=
    fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hrep : ∀ t : ℝ, c t = a⁻¹ * ((∫ s in (0 : ℝ)..(t + d), c s) - ∫ s in (0 : ℝ)..t, c s) := by
    intro t
    have h1 : a * c t = ∫ x in t..(t + d), c x := by
      have e1 : a * c t = ∫ s in (0 : ℝ)..d, c (s + t) := by
        rw [ha, ← intervalIntegral.integral_mul_const]
        congr 1; funext s; rw [hadd, mul_comm]
      rw [e1, intervalIntegral.integral_comp_add_right (fun x => c x) t]
      simp [add_comm]
    have h2 : (∫ s in (0 : ℝ)..(t + d), c s) - ∫ s in (0 : ℝ)..t, c s = ∫ x in t..(t + d), c x :=
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    rw [h2, ← h1]
    field_simp
  set lam : ℂ := a⁻¹ * (c d - 1) with hlam
  have hder : ∀ t : ℝ, HasDerivAt c (lam * c t) t := by
    intro t
    have h1 : HasDerivAt (fun x => ∫ s in (0 : ℝ)..(x + d), c s) (c (t + d)) t := by
      have := (hFint (t + d)).comp_add_const t d
      simpa using this
    have h2 : HasDerivAt (fun y => a⁻¹ * ((∫ s in (0 : ℝ)..(y + d), c s) -
        ∫ s in (0 : ℝ)..y, c s)) (a⁻¹ * (c (t + d) - c t)) t :=
      (h1.sub (hFint t)).const_mul a⁻¹
    have h3 : (fun y => a⁻¹ * ((∫ s in (0 : ℝ)..(y + d), c s) - ∫ s in (0 : ℝ)..y, c s)) = c := by
      funext x; exact (hrep x).symm
    rw [h3] at h2
    convert h2 using 1
    rw [hadd t d, hlam]; ring
  -- `c(t) e^{-λ t}` is constant
  have hg : ∀ t : ℝ, HasDerivAt (fun x : ℝ => c x * Complex.exp (-(lam * (x : ℂ)))) 0 t := by
    intro t
    have e0 : HasDerivAt (fun x : ℝ => lam * (x : ℂ)) lam t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul lam
    have e1 : HasDerivAt (fun x : ℝ => -(lam * (x : ℂ))) (-lam) t := e0.neg
    have e2 := (hder t).mul e1.cexp
    convert e2 using 1
    ring
  have hconst : ∀ t : ℝ, c t * Complex.exp (-(lam * (t : ℂ))) = 1 := by
    intro t
    have hdiff' : Differentiable ℝ (fun x : ℝ => c x * Complex.exp (-(lam * (x : ℂ)))) :=
      fun x => (hg x).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff' (fun x => (hg x).deriv) t 0
    simpa [h0] using this
  have hct : ∀ t : ℝ, c t = Complex.exp (lam * (t : ℂ)) := by
    intro t
    have := hconst t
    calc c t = c t * Complex.exp (-(lam * (t : ℂ))) * Complex.exp (lam * (t : ℂ)) := by
          rw [mul_assoc, ← Complex.exp_add]; simp
      _ = _ := by rw [this, one_mul]
  have hre : lam.re = 0 := by
    have := hmod 1
    rw [hct 1, Complex.norm_exp] at this
    simp only [Complex.ofReal_one, mul_one] at this
    exact Real.exp_eq_one_iff _ |>.mp this
  refine ⟨-lam.im, fun t => ?_⟩
  rw [hct t]
  congr 1
  apply Complex.ext <;> simp [hre] <;> ring

/-! ### Frequency separation -/

lemma freq_sep {ν ν' ε : ℝ} (hε : 0 < ε) (hne : ε ≤ |ν' - ν|) :
    ∃ t : ℝ, |t| ≤ 1 ∧ 2 * Real.sin (min ε Real.pi / 2) ≤
      ‖Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) -
        Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ))‖ := by
  set d : ℝ := ν' - ν with hd
  have hdpos : 0 < |d| := lt_of_lt_of_le hε hne
  set t : ℝ := min 1 (Real.pi / |d|) with ht
  have htpos : 0 < t := lt_min one_pos (div_pos Real.pi_pos hdpos)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htd : t * |d| = min |d| Real.pi := by
    rcases le_total 1 (Real.pi / |d|) with h1 | h1
    · have e : t = 1 := min_eq_left h1
      have hle : |d| ≤ Real.pi := by
        rw [le_div_iff₀ hdpos, one_mul] at h1; exact h1
      rw [e, one_mul, min_eq_left hle]
    · have e : t = Real.pi / |d| := min_eq_right h1
      have hge : Real.pi ≤ |d| := by
        rw [div_le_iff₀ hdpos, one_mul] at h1; exact h1
      rw [e, div_mul_cancel₀ _ hdpos.ne', min_eq_right hge]
  refine ⟨t, by rw [abs_of_pos htpos]; exact ht1, ?_⟩
  have hrew : Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) -
        Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((-(t * d) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    · push_cast [hd]; ring
  have hn1 : ‖Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ))‖ = 1 := by
    have : -Complex.I * ((t * ν : ℝ) : ℂ) = ((-(t * ν) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [hrew, norm_mul, hn1, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hy : min ε Real.pi ≤ t * |d| := by
    rw [htd]; exact min_le_min hne le_rfl
  have hy2 : t * |d| ≤ Real.pi := by rw [htd]; exact min_le_right _ _
  have hy0 : 0 ≤ t * |d| / 2 := by positivity
  have hsin : 0 ≤ Real.sin (t * |d| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [Real.pi_pos])
  have habs : |Real.sin (-(t * d) / 2)| = Real.sin (t * |d| / 2) := by
    rcases le_total 0 d with hd0 | hd0
    · have e : t * |d| / 2 = t * d / 2 := by rw [abs_of_nonneg hd0]
      have e2 : -(t * d) / 2 = -(t * d / 2) := by ring
      rw [e2, Real.sin_neg, abs_neg, e]
      rw [e] at hsin
      exact abs_of_nonneg hsin
    · have e : t * |d| / 2 = -(t * d) / 2 := by rw [abs_of_nonpos hd0]; ring
      rw [e]
      rw [e] at hsin
      exact abs_of_nonneg hsin
  rw [habs]
  have hmin : 0 < min ε Real.pi := lt_min hε Real.pi_pos
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · linarith [Real.pi_pos]
  · linarith
  · linarith

/-! ### The frequency `ν_n(a)` -/

section Frequency
variable {A : ℝ → E → E} (h : RoughGroup A)
include h

/-- Existence of the frequency on one torus. -/
theorem RoughGroup.exists_freq (z : E) (n : ℤ) :
    ∃ ν : ℝ, ∀ (t : ℝ) (w : E), (∀ m, ‖w m‖ = ‖z m‖) →
      A t w n = Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) * w n := by
  by_cases hn : z n = 0
  · refine ⟨0, fun t w hw => ?_⟩
    have hw0 : w n = 0 := by
      have := hw n
      rw [hn, norm_zero] at this
      exact norm_eq_zero.mp this
    rw [h.zero_coord t w n hw0, hw0, mul_zero]
  · obtain ⟨ν, hν⟩ := exists_freq_of_character (charOf A z n) (h.char_cont hn) (h.char_zero hn)
      (h.char_add hn) (h.char_norm hn)
    refine ⟨ν, fun t w hw => ?_⟩
    rw [h.char_apply hn t hw, hν t]

end Frequency

open Classical in
/-- The real frequency `ν_n(a)` attached to the action array `a` and coordinate `n`; the value is
irrelevant (and only constrained to be `0` or any frequency) when the torus of `a` has `a_n = 0`. -/
def nuOf (A : ℝ → E → E) (n : ℤ) (a : ℤ → ℝ) : ℝ :=
  if H : ∃ ν : ℝ, ∀ (t : ℝ) (w : E), act w = a →
      A t w n = Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) * w n
  then Classical.choose H else 0

lemma norm_eq_of_act_eq {z w : E} (h : act z = act w) (n : ℤ) : ‖z n‖ = ‖w n‖ := by
  have := congrFun h n
  simp only [act] at this
  exact norm_eq_of_sq_eq this

theorem RoughGroup.nuOf_spec {A : ℝ → E → E} (h : RoughGroup A) (t : ℝ) (w : E) (n : ℤ) :
    A t w n = Complex.exp (-Complex.I * ((t * nuOf A n (act w) : ℝ) : ℂ)) * w n := by
  have H : ∃ ν : ℝ, ∀ (t : ℝ) (w' : E), act w' = act w →
      A t w' n = Complex.exp (-Complex.I * ((t * ν : ℝ) : ℂ)) * w' n := by
    obtain ⟨ν, hν⟩ := h.exists_freq w n
    exact ⟨ν, fun t w' hw' => hν t w' (fun m => norm_eq_of_act_eq hw' m)⟩
  unfold nuOf
  rw [dif_pos H]
  exact (Classical.choose_spec H) t w rfl

/-- Uniqueness of the active frequency. -/
theorem RoughGroup.nuOf_unique {A : ℝ → E → E} (h : RoughGroup A) (z : E) (n : ℤ) (hn : z n ≠ 0)
    (ν' : ℝ) (hν' : ∀ t : ℝ, A t z n = Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * z n) :
    ν' = nuOf A n (act z) := by
  refine freq_eq_of_char_eq hn (fun t => ?_)
  rw [← hν' t, h.nuOf_spec t z n]

/-! ### Continuity of `ν_n` in the `ℓ¹` topology -/

/-- `√a` as an element of `ℓ²`, for `a ∈ ℓ¹`. -/
def sqrtE (a : lp (fun _ : ℤ => ℝ) 1) : E :=
  ⟨fun m => ((Real.sqrt (a m) : ℝ) : ℂ), by
    apply memℓp_gen
    have hs : Summable fun m => ‖a m‖ := by
      have := (lp.memℓp a : Memℓp a 1).summable (by norm_num)
      simpa using this
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rcases le_total 0 (a m) with h0 | h0
    · rw [Real.sq_sqrt h0]; exact le_trans (le_abs_self _) (le_of_eq (Real.norm_eq_abs _).symm)
    · rw [Real.sqrt_eq_zero_of_nonpos h0]; simp⟩

lemma sqrtE_apply (a : lp (fun _ : ℤ => ℝ) 1) (m : ℤ) :
    sqrtE a m = ((Real.sqrt (a m) : ℝ) : ℂ) := rfl

lemma act_sqrtE (a : lp (fun _ : ℤ => ℝ) 1) (ha : ∀ m, 0 ≤ a m) :
    act (sqrtE a) = fun m => a m := by
  funext m
  simp only [act, sqrtE_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (ha m)

/-- `|√x - √y|² ≤ |x - y|` gives `‖√a' - √a‖² ≤ ‖a' - a‖₁`. -/
lemma sqrtE_dist_le (a a' : lp (fun _ : ℤ => ℝ) 1) (ha : ∀ m, 0 ≤ a m) (ha' : ∀ m, 0 ≤ a' m) :
    ‖sqrtE a' - sqrtE a‖ ^ 2 ≤ ‖a' - a‖ := by
  rw [tsum_sq]
  have h1 : HasSum (fun m => ‖(a' - a) m‖) ‖a' - a‖ := by
    have := lp.hasSum_norm (p := 1) (by norm_num) (a' - a)
    simpa using this
  have h2 : Summable fun m => ‖(sqrtE a' - sqrtE a) m‖ ^ 2 := summable_sq _
  refine hasSum_le (fun m => ?_) h2.hasSum h1
  simp only [lp.coeFn_sub, Pi.sub_apply, sqrtE_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.norm_eq_abs]
  have hx := ha' m
  have hy := ha m
  have e1 := Real.sq_sqrt hx
  have e2 := Real.sq_sqrt hy
  have p1 := Real.sqrt_nonneg (a' m)
  have p2 := Real.sqrt_nonneg (a m)
  rw [le_abs]
  rcases le_total (a m) (a' m) with hxy | hxy
  · left
    have hs := Real.sqrt_le_sqrt hxy
    nlinarith [mul_nonneg p2 (sub_nonneg.mpr hs)]
  · right
    have hs := Real.sqrt_le_sqrt hxy
    nlinarith [mul_nonneg p1 (sub_nonneg.mpr hs)]

set_option maxHeartbeats 1600000 in
/-- **Active-coordinate continuity of the frequency.**  For each fixed `n`, `ν_n` is continuous on
`{a ∈ ℓ¹ : a ≥ 0, a_n > 0}` in the norm topology of `ℓ¹`. -/
theorem RoughGroup.nuOf_continuousOn {A : ℝ → E → E} (h : RoughGroup A) (n : ℤ) :
    ContinuousOn (fun a : lp (fun _ : ℤ => ℝ) 1 => nuOf A n (fun m => a m))
      {a | (∀ m, 0 ≤ a m) ∧ 0 < a n} := by
  rw [Metric.continuousOn_iff]
  intro a ha ε hε
  obtain ⟨ha0, hapos⟩ := ha
  set b : E := sqrtE a with hb
  have hact : act b = fun m => a m := act_sqrtE a ha0
  set β : ℝ := Real.sqrt (a n) with hβ
  have hβpos : 0 < β := Real.sqrt_pos.mpr hapos
  have hbn : ‖b n‖ = β := by
    rw [hb, sqrtE_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hbne : b n ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hbn; exact hβpos.ne' hbn.symm
  set δ0 : ℝ := 2 * Real.sin (min ε Real.pi / 2) with hδ0
  have hδ0pos : 0 < δ0 := by
    have : 0 < min ε Real.pi / 2 := by
      have := lt_min hε Real.pi_pos; linarith
    have h2 : min ε Real.pi / 2 < Real.pi := by
      have := min_le_right ε Real.pi; linarith [Real.pi_pos]
    have := Real.sin_pos_of_pos_of_lt_pi this h2
    rw [hδ0]; linarith
  -- the uniform-in-time continuity of `z ↦ A^t(z)_n` on `[-1,1]`
  let Fm : C(E × Set.Icc (-1 : ℝ) 1, ℂ) :=
    ⟨fun p => A p.2.1 p.1 n, (pr n).continuous.comp
      (h.cont.comp (Continuous.prodMk (continuous_subtype_val.comp continuous_snd) continuous_fst))⟩
  set r : ℝ := β * δ0 / 8 with hr
  have hrpos : 0 < r := by positivity
  have hcont := (ContinuousMap.curry Fm).continuous.continuousAt (x := b)
  obtain ⟨ρ₁, hρ₁, hρ₁c⟩ := Metric.continuousAt_iff.mp hcont r hrpos
  set ρ : ℝ := min ρ₁ (min (β / 2) r) with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ (lt_min (by positivity) hrpos)
  refine ⟨ρ ^ 2, by positivity, fun a' ha' hdist => ?_⟩
  obtain ⟨ha'0, ha'pos⟩ := ha'
  set b' : E := sqrtE a' with hb'
  have hact' : act b' = fun m => a' m := act_sqrtE a' ha'0
  have hdistb : ‖b' - b‖ < ρ := by
    have h1 := sqrtE_dist_le a a' ha0 ha'0
    rw [dist_eq_norm] at hdist
    have : ‖b' - b‖ ^ 2 < ρ ^ 2 := lt_of_le_of_lt h1 hdist
    exact lt_of_pow_lt_pow_left₀ 2 hρpos.le this
  have hρ1 : ‖b' - b‖ < ρ₁ := lt_of_lt_of_le hdistb (min_le_left _ _)
  have hρ2 : ‖b' - b‖ < β / 2 := lt_of_lt_of_le hdistb ((min_le_right _ _).trans (min_le_left _ _))
  have hρ3 : ‖b' - b‖ < r := lt_of_lt_of_le hdistb ((min_le_right _ _).trans (min_le_right _ _))
  -- the coordinate `n` of `b'` stays away from zero
  have hcoord : ‖b' n - b n‖ ≤ ‖b' - b‖ := by
    have := norm_apply_le (b' - b) n
    simpa using this
  have hb'n : β / 2 ≤ ‖b' n‖ := by
    have h3 : ‖b n‖ - ‖b' n - b n‖ ≤ ‖b' n‖ := by
      have := norm_sub_norm_le (b n) (b n - b' n)
      rw [sub_sub_cancel, norm_sub_rev (b n) (b' n)] at this
      linarith
    linarith
  have hb'ne : b' n ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb'n; linarith
  -- uniform closeness of the time-`t` coordinates
  have hunif : ∀ t : ℝ, |t| ≤ 1 → ‖A t b' n - A t b n‖ < r := by
    intro t ht
    have hd : dist (ContinuousMap.curry Fm b') (ContinuousMap.curry Fm b) < r :=
      hρ₁c (by rw [dist_eq_norm]; exact hρ1)
    have h3 : dist (A t b' n) (A t b n) < r :=
      (ContinuousMap.dist_lt_iff hrpos).mp hd ⟨t, abs_le.mp ht⟩
    rwa [dist_eq_norm] at h3
  -- the characters are uniformly close
  have hchar : ∀ t : ℝ, |t| ≤ 1 → ‖charOf A b' n t - charOf A b n t‖ < δ0 := by
    intro t ht
    unfold charOf
    rw [div_sub_div _ _ hb'ne hbne, norm_div, norm_mul, hbn]
    have hnum : ‖A t b' n * b n - b' n * A t b n‖ ≤ r * β + ‖b' - b‖ * β := by
      have e : A t b' n * b n - b' n * A t b n =
          (A t b' n - A t b n) * b n + A t b n * (b n - b' n) := by ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, hbn]
        exact mul_le_mul_of_nonneg_right (hunif t ht).le hβpos.le
      · rw [norm_mul, h.modulus, hbn, norm_sub_rev]
        calc β * ‖b' n - b n‖ ≤ β * ‖b' - b‖ := mul_le_mul_of_nonneg_left hcoord hβpos.le
          _ = ‖b' - b‖ * β := mul_comm _ _
    have hpos : 0 < ‖b' n‖ := lt_of_lt_of_le (by positivity) hb'n
    rw [div_lt_iff₀ (by positivity)]
    calc ‖A t b' n * b n - b' n * A t b n‖ ≤ r * β + ‖b' - b‖ * β := hnum
      _ < r * β + r * β := by
          have := mul_lt_mul_of_pos_right hρ3 hβpos
          linarith
      _ = δ0 * (β / 2 * β) / 2 := by rw [hr]; ring
      _ ≤ δ0 * (β / 2 * β) := by
          have : 0 < δ0 * (β / 2 * β) := by positivity
          linarith
      _ ≤ δ0 * (‖b' n‖ * β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb'n hβpos.le) hδ0pos.le
  -- conclude
  have hcharb : ∀ t : ℝ, charOf A b n t =
      Complex.exp (-Complex.I * ((t * nuOf A n (fun m => a m) : ℝ) : ℂ)) := by
    intro t
    have := h.nuOf_spec t b n
    rw [hact] at this
    unfold charOf
    rw [this]
    exact mul_div_cancel_right₀ _ hbne
  have hcharb' : ∀ t : ℝ, charOf A b' n t =
      Complex.exp (-Complex.I * ((t * nuOf A n (fun m => a' m) : ℝ) : ℂ)) := by
    intro t
    have := h.nuOf_spec t b' n
    rw [hact'] at this
    unfold charOf
    rw [this]
    exact mul_div_cancel_right₀ _ hb'ne
  show |nuOf A n (fun m => a' m) - nuOf A n (fun m => a m)| < ε
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht, hsep⟩ := freq_sep hε hcon
  have := hchar t ht
  rw [hcharb', hcharb] at this
  exact absurd (lt_of_le_of_lt hsep this) (lt_irrefl _)

/-! ### Strong continuity on fixed-action tori, weighted spaces -/

/-- Unit-modulus multipliers preserve every weighted squared norm. -/
theorem RoughGroup.weighted_preserve {A : ℝ → E → E} (h : RoughGroup A) (w : ℤ → ℝ) (t : ℝ)
    (z : E) : ∑' n, w n * ‖A t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2 := by
  congr 1; funext n; rw [h.modulus]

/-- Finite-head and invariant-tail approximation (dominated convergence): strong continuity of the
orbit in every weighted `ℓ²` norm with a nonnegative weight and finite weighted norm of the point. -/
theorem RoughGroup.weighted_continuous {A : ℝ → E → E} (h : RoughGroup A) (w : ℤ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (z : E) (hz : Summable fun n => w n * ‖z n‖ ^ 2) (t0 : ℝ) :
    Tendsto (fun t : ℝ => ∑' n, w n * ‖A t z n - A t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0) := by
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t0)
    (f := fun t n => w n * ‖A t z n - A t0 z n‖ ^ 2) (g := fun _ => (0 : ℝ))
    (bound := fun n => 4 * (w n * ‖z n‖ ^ 2)) (hz.mul_left 4) ?_ ?_
  · simpa using hlim
  · intro n
    have hc : Continuous fun t : ℝ => A t z n :=
      (pr n).continuous.comp (h.cont.comp (Continuous.prodMk continuous_id continuous_const))
    have : Tendsto (fun t : ℝ => A t z n - A t0 z n) (𝓝 t0) (𝓝 0) := by
      have := (hc.tendsto t0).sub_const (A t0 z n)
      simpa using this
    have h2 := (this.norm.pow 2).const_mul (w n)
    simpa using h2
  · refine Filter.Eventually.of_forall (fun t n => ?_)
    have h1 : ‖A t z n - A t0 z n‖ ≤ 2 * ‖z n‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [h.modulus, h.modulus]; linarith
    have h2 : ‖A t z n - A t0 z n‖ ^ 2 ≤ 4 * ‖z n‖ ^ 2 := by
      nlinarith [norm_nonneg (A t z n - A t0 z n)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw n) (sq_nonneg _))]
    nlinarith [hw n]

/-! ### The named theorem -/

/-- **Rough-field extension (printed paragraph "Extension to rough fields without a rough
Hamiltonian").**  For a jointly continuous group `A` on `ℓ²` preserving each `|z_n|²` and commuting
with coordinate rotations on finitely supported sequences:
there are real frequencies `ν n a` (`n ∈ ℤ`, `a : ℤ → ℝ`) such that

1. `A^t z_n = e^{-itν_n(|z|²)} z_n` for every `z ∈ ℓ²` and every real `t`, whenever `z_n ≠ 0`;
2. a zero coordinate stays zero;
3. `ν_n(a)` is the unique real number with this property at any point `z` of the torus of `a` with
   `z_n ≠ 0`;
4. for each `n`, `ν n` is continuous on `{a ∈ ℓ¹ : a ≥ 0, a_n > 0}` in the norm topology of `ℓ¹`;
5. every `A^t` preserves each weighted squared norm `∑ w_n |z_n|²` (`w ≥ 0`) and the orbit map
   `t ↦ A^t z` is continuous in each such weighted norm at points of finite weighted norm. -/
theorem rough_extension {A : ℝ → E → E} (h : RoughGroup A) :
    ∃ ν : ℤ → (ℤ → ℝ) → ℝ,
      (∀ (t : ℝ) (z : E) (n : ℤ), z n ≠ 0 →
        A t z n = Complex.exp (-Complex.I * ((t * ν n (act z) : ℝ) : ℂ)) * z n) ∧
      (∀ (t : ℝ) (z : E) (n : ℤ), z n = 0 → A t z n = 0) ∧
      (∀ (z : E) (n : ℤ), z n ≠ 0 → ∀ ν' : ℝ,
        (∀ t : ℝ, A t z n = Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * z n) →
          ν' = ν n (act z)) ∧
      (∀ n : ℤ, ContinuousOn (fun a : lp (fun _ : ℤ => ℝ) 1 => ν n (fun m => a m))
        {a | (∀ m, 0 ≤ a m) ∧ 0 < a n}) ∧
      (∀ (w : ℤ → ℝ) (t : ℝ) (z : E), ∑' n, w n * ‖A t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
      (∀ (w : ℤ → ℝ), (∀ n, 0 ≤ w n) → ∀ z : E, (Summable fun n => w n * ‖z n‖ ^ 2) → ∀ t0 : ℝ,
        Tendsto (fun t : ℝ => ∑' n, w n * ‖A t z n - A t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0)) := by
  refine ⟨fun n a => nuOf A n a, fun t z n _ => h.nuOf_spec t z n, h.zero_coord,
    fun z n hn ν' hν' => h.nuOf_unique z n hn ν' hν', fun n => h.nuOf_continuousOn n,
    fun w t z => h.weighted_preserve w t z, fun w hw z hz t0 => h.weighted_continuous w hw z hz t0⟩

#print axioms rough_extension

end QuantumNLS.REF88Rotations
