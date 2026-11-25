import QuantumNLS.DiagonalMultiplier

/-!
# AuditGapsS01Analytic: the analytic core of R-10EE6421 `lem:audit-gaps`

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 261-294
(`lem:audit-gaps`, `\ReportID{R-10EE6421}`), printed proof lines 270-294.

This module contains ONLY abstract `ℓ²(ι)` estimates, with no reference to the Bethe/occupation model.
It formalizes the following steps of the printed proof.

* "Integrating for `-1 ≤ t ≤ 1` gives the nonnegative function `k(x) = 4(1 - sin(x)/x)`, with `k(0) = 0`.
  It is positive away from zero, continuous, and tends to four at infinity. Hence
  `inf_{|x| ≥ ε} k(x) > 0` for every `ε > 0`":
  `kk y = ∫_{-1}^{1} (2 - 2 cos (t y)) dt` (`kk_eq`: `kk y = 4 - 4 sin y / y` for `y ≠ 0`; `kk 0 = 0`);
  `kk_lower`: `inf_{|y| ≥ η} kk y > 0`.
* "The exact diagonal multiplier makes its square `E[1_{m_a ≥ 1} |e^{it(Λ(m-e_a+e_b) - Λ(m) - δ)} - 1|²]`":
  `norm_eps_sq` gives `‖e^{itΔ} - e^{itδ}‖² = 2 - 2 cos(t(Δ - δ))`, `eps_apply_bound` bounds
  `‖T D(ε_t) ψ‖` (which is the printed square root, by `DiagonalMultiplier.norm_T_sq`) by the
  dynamic plus static residuals, from the frozen `DiagonalMultiplier.key_identity` and unitarity.
* "The integrated expectation tends to zero": `avg_bound` integrates the pointwise-in-time bound over
  `[-1, 1]` (finite subsums commute with the integral) and gets
  `∑_{m ∈ S} kk(Δ(m) - δ) ‖x m‖² ≤ 8 ε₀²` for every finite `S ⊆ D`.
* The omitted donor boundary: `diag_conc` bounds the mass of a coordinate set `Z` on which a diagonal
  bounded operator `E` vanishes by `‖E x - c x‖² / ‖c‖²` (the strong Cartesian symbol at `a = b`
  gives action concentration).

No new hypothesis about physical objects; no acceptance claim.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter Topology Complex
open scoped ComplexConjugate InnerProductSpace
open QuantumNLS.DiagonalMultiplier

namespace QuantumNLS.AuditGapsS01Analytic

/-! ### The kernel `k` -/

/-- `kk y = ∫_{-1}^{1} (2 - 2 cos (t y)) dt`, the time integral of `|e^{ity} - 1|²`. -/
def kk (y : ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, (2 - 2 * Real.cos (t * y))

theorem kk_zero : kk 0 = 0 := by
  simp [kk]

theorem kk_nonneg (y : ℝ) : 0 ≤ kk y := by
  unfold kk
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  linarith [Real.cos_le_one (t * y)]

theorem kk_eq {y : ℝ} (hy : y ≠ 0) : kk y = 4 - 4 * Real.sin y / y := by
  have h1 : ∫ t in (-1 : ℝ)..1, Real.cos (t * y) = 2 * Real.sin y / y := by
    rw [intervalIntegral.integral_comp_mul_right (fun x => Real.cos x) hy, integral_cos]
    simp only [smul_eq_mul, neg_mul, one_mul, Real.sin_neg]
    field_simp
    ring
  have hc1 : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) MeasureTheory.volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun t : ℝ => 2 * Real.cos (t * y)) MeasureTheory.volume (-1) 1 :=
    (by fun_prop : Continuous fun t : ℝ => 2 * Real.cos (t * y)).intervalIntegrable _ _
  unfold kk
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul, h1]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem kk_lower (η : ℝ) (hη : 0 < η) : ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ y : ℝ, η ≤ |y| → k₀ ≤ kk y := by
  set η' : ℝ := min η 2 with hη'
  have hη'pos : 0 < η' := lt_min hη (by norm_num)
  have hη'le : η' ≤ 2 := min_le_right _ _
  let f : ℝ → ℝ := fun s => 1 - Real.sin s / s
  have hcont : ContinuousOn f (Set.Icc η' 2) := by
    refine continuousOn_const.sub (Real.continuous_sin.continuousOn.div continuousOn_id ?_)
    intro s hs
    exact ne_of_gt (lt_of_lt_of_le hη'pos hs.1)
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨η', le_refl _, hη'le⟩ hcont
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le hη'pos hx₀.1
  have hfx₀ : 0 < f x₀ := by
    have h := (div_lt_one hx₀pos).2 (Real.sin_lt hx₀pos)
    simp only [f]
    linarith
  refine ⟨4 * min (1 / 2) (f x₀), by positivity, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, abs_zero] at hy
    linarith
  have hsym : Real.sin y / y = Real.sin |y| / |y| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sin_neg, neg_div_neg_eq]
  have hkk : kk y = 4 * f |y| := by
    rw [kk_eq hy0]
    simp only [f]
    rw [← hsym]
    field_simp
  rw [hkk]
  have hs : 0 < |y| := abs_pos.mpr hy0
  have key : min (1 / 2) (f x₀) ≤ f |y| := by
    by_cases h2 : |y| ≤ 2
    · have hmem : |y| ∈ Set.Icc η' 2 := ⟨le_trans (min_le_left _ _) hy, h2⟩
      exact le_trans (min_le_right _ _) (hmin hmem)
    · rw [not_le] at h2
      have : Real.sin |y| / |y| ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hs (by norm_num)]
        nlinarith [Real.sin_le_one |y|]
      exact le_trans (min_le_left _ _) (by simp only [f]; linarith)
  linarith

/-! ### The modulus of the rotation difference -/

theorem rot_re (a : ℝ) : (rot a).re = Real.cos a := by
  simp [rot, Complex.exp_ofReal_mul_I_re]

theorem rot_im (a : ℝ) : (rot a).im = Real.sin a := by
  simp [rot, Complex.exp_ofReal_mul_I_im]

theorem norm_rot_sub_rot_sq (a b : ℝ) : ‖rot a - rot b‖ ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, rot_re, rot_im]
  linear_combination (Real.sin_sq_add_cos_sq a) + (Real.sin_sq_add_cos_sq b) + 2 * Real.cos_sub a b

variable {ι : Type*} [DecidableEq ι]

theorem norm_eps_sq (Λ : ι → ℝ) (σ : ι → ι) (δ t : ℝ) (m : ι) :
    ‖eps Λ σ δ t m‖ ^ 2 = 2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ)) := by
  unfold eps
  rw [norm_rot_sub_rot_sq]
  congr 3
  ring

/-! ### The converse of the frozen key bound -/

section Converse
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι) (σ : ι → ι) (D : Set ι) (c : ι → ℂ)
  (T : L2 ι →L[ℂ] L2 ι)

/-- The shift-defect vector `T D(ε_t) ψ` is controlled by the dynamic residual at time `t` and the
static residual (printed: "the dynamic and static phase residuals and unitarity imply ..."). -/
theorem eps_apply_bound (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (ψ : L2 ι) (τ : ℂ) (δ t : ℝ) :
    ‖T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ)‖ ≤
      ‖T (U t ψ) - (rot (t * δ) * τ) • U t ψ‖ + ‖T ψ - τ • ψ‖ := by
  have hk := key_identity Λ U σ D c T hU hinj hT hT0 ψ τ δ t
  set A := T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ) with hA
  set B : L2 ι := rot (t * δ) • (T ψ - τ • ψ) with hB
  have h1 : ‖T (U t ψ) - (rot (t * δ) * τ) • U t ψ‖ = ‖A + B‖ := by
    rw [hk, norm_U Λ U hU]
  have h2 : ‖B‖ = ‖T ψ - τ • ψ‖ := by
    rw [hB, norm_smul, norm_rot, one_mul]
  have h3 : ‖A‖ ≤ ‖A + B‖ + ‖B‖ := by
    calc ‖A‖ = ‖(A + B) - B‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖A + B‖ + ‖B‖ := norm_sub_le _ _
  linarith

/-- Squared norm of the shift-defect vector, as the printed expectation. -/
theorem norm_sq_shift_defect (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (ψ : L2 ι) (δ t : ℝ) :
    ‖T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) ψ)‖ ^ 2 =
      ∑' m, D.indicator (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖ψ m‖ ^ 2)) m := by
  rw [norm_T_sq σ D c T hinj hT hT0]
  refine tsum_congr fun m => ?_
  by_cases hm : m ∈ D
  · simp [Set.indicator_of_mem hm, mulVec_apply, mul_pow]
  · simp [Set.indicator_of_notMem hm]

end Converse

/-! ### Time averaging -/

section Average
variable (Λ : ι → ℝ) (U : ℝ → L2 ι →L[ℂ] L2 ι) (σ : ι → ι) (D : Set ι) (c : ι → ℂ)
  (T : L2 ι →L[ℂ] L2 ι)

/-- Finite sub-sums of the time integral are controlled by the residuals, uniformly: this is the
printed "the integrated expectation tends to zero", with the integral of `‖e^{it(Δ-δ)} - 1‖²` over
`[-1, 1]` equal to `kk (Δ - δ)`. -/
theorem avg_bound (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (hc : ∀ m ∈ D, ‖c m‖ = 1)
    (x : L2 ι) (τ : ℂ) (δ ε₀ : ℝ)
    (hdyn : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖T (U t x) - (rot (t * δ) * τ) • U t x‖ ≤ ε₀)
    (hstat : ‖T x - τ • x‖ ≤ ε₀) (S : Finset ι) (hS : ∀ m ∈ S, m ∈ D) :
    ∑ m ∈ S, kk (Λ (σ m) - Λ m - δ) * ‖x m‖ ^ 2 ≤ 8 * ε₀ ^ 2 := by
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg _) hstat
  -- pointwise in time: the finite sub-sum is at most `(2 ε₀)²`
  have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ∑ m ∈ S, (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2 ≤ (2 * ε₀) ^ 2 := by
    intro t ht
    have hb := eps_apply_bound Λ U σ D c T hU hinj hT hT0 x τ δ t
    have hbd : ‖T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) x)‖ ≤ 2 * ε₀ := by
      have := hdyn t ht
      linarith
    have hsq := norm_sq_shift_defect Λ σ D c T hinj hT hT0 x δ t
    have hsum : Summable fun m => D.indicator
        (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖x m‖ ^ 2)) m := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        ((summable_sq x).mul_left 4)
      · by_cases hm : m ∈ D
        · rw [Set.indicator_of_mem hm]; positivity
        · rw [Set.indicator_of_notMem hm]
      · by_cases hm : m ∈ D
        · rw [Set.indicator_of_mem hm, hc m hm]
          have := norm_eps_le_two Λ σ δ t m
          have h4 : ‖eps Λ σ δ t m‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (eps Λ σ δ t m)]
          nlinarith [sq_nonneg ‖x m‖]
        · rw [Set.indicator_of_notMem hm]; positivity
    calc ∑ m ∈ S, (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2
        = ∑ m ∈ S, D.indicator
            (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖x m‖ ^ 2)) m := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Set.indicator_of_mem (hS m hm), hc m (hS m hm), norm_eps_sq]
          ring
      _ ≤ ∑' m, D.indicator
            (fun m => ‖c m‖ ^ 2 * (‖eps Λ σ δ t m‖ ^ 2 * ‖x m‖ ^ 2)) m :=
          hsum.sum_le_tsum S (fun m _ => by
            by_cases hm : m ∈ D
            · rw [Set.indicator_of_mem hm]; positivity
            · rw [Set.indicator_of_notMem hm])
      _ = ‖T (mulVec (eps Λ σ δ t) (norm_eps_le_two Λ σ δ t) x)‖ ^ 2 := hsq.symm
      _ ≤ (2 * ε₀) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hbd 2
  -- integrate over `[-1, 1]`
  have hcont : ∀ m : ι, Continuous fun t : ℝ =>
      (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2 := by
    intro m
    fun_prop
  have hint : ∀ m ∈ S, IntervalIntegrable (fun t : ℝ =>
      (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2) MeasureTheory.volume (-1) 1 :=
    fun m _ => (hcont m).intervalIntegrable _ _
  have hlhs : ∑ m ∈ S, kk (Λ (σ m) - Λ m - δ) * ‖x m‖ ^ 2 =
      ∫ t in (-1 : ℝ)..1, ∑ m ∈ S,
        (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2 := by
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [kk, intervalIntegral.integral_mul_const]
  rw [hlhs]
  have hle : (∫ t in (-1 : ℝ)..1, ∑ m ∈ S,
        (2 - 2 * Real.cos (t * (Λ (σ m) - Λ m - δ))) * ‖x m‖ ^ 2) ≤
      ∫ _t in (-1 : ℝ)..1, (2 * ε₀) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_finsetSum S (fun m _ => hcont m)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) ?_
    intro t ht
    exact hpt t ht
  calc _ ≤ ∫ _t in (-1 : ℝ)..1, (2 * ε₀) ^ 2 := hle
    _ = 8 * ε₀ ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- The mass of any coordinate set `Zb` of definite gap defect: `Zb ⊆ D` with `|Δ(m) - δ| ≥ η`, where
`kk ≥ k₀ > 0`, is at most `8 ε₀² / k₀`. This is the printed "the integrated expectation tends to zero,
which proves the probability claim" (one `ε`, via `inf_{|x| ≥ ε} k(x) > 0`). -/
theorem bad_mass (hU : ∀ t m, U t (e m) = phase Λ t m • e m) (hinj : Set.InjOn σ D)
    (hT : ∀ m ∈ D, T (e m) = c m • e (σ m)) (hT0 : ∀ m, m ∉ D → T (e m) = 0)
    (hc : ∀ m ∈ D, ‖c m‖ = 1)
    (x : L2 ι) (τ : ℂ) (δ ε₀ : ℝ)
    (hdyn : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖T (U t x) - (rot (t * δ) * τ) • U t x‖ ≤ ε₀)
    (hstat : ‖T x - τ • x‖ ≤ ε₀) (η k₀ : ℝ) (hk₀ : 0 < k₀)
    (hk : ∀ y : ℝ, η ≤ |y| → k₀ ≤ kk y)
    (Zb : Set ι) (hZb : ∀ m ∈ Zb, m ∈ D ∧ η ≤ |Λ (σ m) - Λ m - δ|) :
    ∑' m, Zb.indicator (fun m => ‖x m‖ ^ 2) m ≤ 8 * ε₀ ^ 2 / k₀ := by
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg _) hstat
  refine tsum_le_of_sum_le' (by positivity) fun s => ?_
  classical
  have hfilt : ∑ i ∈ s, Zb.indicator (fun m => ‖x m‖ ^ 2) i =
      ∑ i ∈ s.filter (· ∈ Zb), ‖x i‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ∈ Zb <;> simp [Set.indicator, h]
  rw [hfilt, le_div_iff₀ hk₀]
  have h1 := avg_bound Λ U σ D c T hU hinj hT hT0 hc x τ δ ε₀ hdyn hstat (s.filter (· ∈ Zb))
    (fun m hm => (hZb m (Finset.mem_filter.1 hm).2).1)
  calc (∑ i ∈ s.filter (· ∈ Zb), ‖x i‖ ^ 2) * k₀
      = ∑ i ∈ s.filter (· ∈ Zb), k₀ * ‖x i‖ ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ s.filter (· ∈ Zb), kk (Λ (σ i) - Λ i - δ) * ‖x i‖ ^ 2 :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (hk _ (hZb i (Finset.mem_filter.1 hi).2).2) (sq_nonneg _)
    _ ≤ 8 * ε₀ ^ 2 := h1

end Average

/-! ### Diagonal concentration -/

section Diagonal

theorem diag_coord (E : L2 ι →L[ℂ] L2 ι) (s : ι → ℂ) (hE : ∀ m, E (e m) = s m • e m)
    (φ : L2 ι) (k : ι) : (E φ) k = s k * φ k := by
  rw [coord_apply, tsum_eq_single k]
  · simp [hE, e_apply]; ring
  · intro m hm
    simp [hE, e_apply, Ne.symm hm]

/-- If `E` is diagonal and vanishes on the coordinate set `Z`, then the mass of `Z` is controlled by
the strong-symbol residual `‖E x - c x‖`. -/
theorem diag_conc (E : L2 ι →L[ℂ] L2 ι) (s : ι → ℂ) (hE : ∀ m, E (e m) = s m • e m)
    (Z : Set ι) (hZ : ∀ m ∈ Z, s m = 0) (c : ℂ) (x : L2 ι) (ε₁ : ℝ)
    (h : ‖E x - c • x‖ ≤ ε₁) :
    ‖c‖ ^ 2 * ∑' m, Z.indicator (fun m => ‖x m‖ ^ 2) m ≤ ε₁ ^ 2 := by
  have hsq : ‖E x - c • x‖ ^ 2 = ∑' k, ‖(s k - c) * x k‖ ^ 2 := by
    rw [norm_sq_eq_tsum]
    refine tsum_congr fun k => ?_
    congr 2
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diag_coord E s hE]
    ring
  have hsum1 : Summable fun k => ‖(s k - c) * x k‖ ^ 2 := by
    have := summable_sq (E x - c • x)
    refine this.congr fun k => ?_
    simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diag_coord E s hE]
    congr 2
    ring
  have hsum2 : Summable fun k => Z.indicator (fun m => ‖c‖ ^ 2 * ‖x m‖ ^ 2) k :=
    Summable.of_nonneg_of_le (fun k => by
        by_cases hk : k ∈ Z
        · rw [Set.indicator_of_mem hk]; positivity
        · rw [Set.indicator_of_notMem hk])
      (fun k => by
        by_cases hk : k ∈ Z
        · rw [Set.indicator_of_mem hk]
        · rw [Set.indicator_of_notMem hk]; positivity)
      ((summable_sq x).mul_left (‖c‖ ^ 2))
  have hle : ∑' k, Z.indicator (fun m => ‖c‖ ^ 2 * ‖x m‖ ^ 2) k ≤ ∑' k, ‖(s k - c) * x k‖ ^ 2 := by
    refine hsum2.tsum_le_tsum (fun k => ?_) hsum1
    by_cases hk : k ∈ Z
    · rw [Set.indicator_of_mem hk, hZ k hk, norm_mul, mul_pow]
      simp
    · rw [Set.indicator_of_notMem hk]; positivity
  have heq : ∑' k, Z.indicator (fun m => ‖c‖ ^ 2 * ‖x m‖ ^ 2) k =
      ‖c‖ ^ 2 * ∑' m, Z.indicator (fun m => ‖x m‖ ^ 2) m := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ Z <;> simp [Set.indicator, hk]
  calc ‖c‖ ^ 2 * ∑' m, Z.indicator (fun m => ‖x m‖ ^ 2) m
      = ∑' k, Z.indicator (fun m => ‖c‖ ^ 2 * ‖x m‖ ^ 2) k := heq.symm
    _ ≤ ‖E x - c • x‖ ^ 2 := hsq ▸ hle
    _ ≤ ε₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2

end Diagonal

end QuantumNLS.AuditGapsS01Analytic

#print axioms QuantumNLS.AuditGapsS01Analytic.kk_eq
#print axioms QuantumNLS.AuditGapsS01Analytic.kk_lower
#print axioms QuantumNLS.AuditGapsS01Analytic.norm_eps_sq
#print axioms QuantumNLS.AuditGapsS01Analytic.eps_apply_bound
#print axioms QuantumNLS.AuditGapsS01Analytic.avg_bound
#print axioms QuantumNLS.AuditGapsS01Analytic.bad_mass
#print axioms QuantumNLS.AuditGapsS01Analytic.kk_nonneg
#print axioms QuantumNLS.AuditGapsS01Analytic.diag_conc
