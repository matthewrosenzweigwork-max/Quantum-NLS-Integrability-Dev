import QuantumNLS.PeriodReconstructionBigO
import QuantumNLS.LabelExactPeriod

/-!
# PROP-006 `thm:B3-period-reconstruction` (label_periods.tex:308-442): eq:B3-log-reconstruction

For a sequence as in PROP-003 (`L_N ⇀ μ`, `μ` from DEF-043, `N → ∞`) and the fixed contour
`Γ = ∂([x₋, x₊] × [−h, h])` (`Gam`) with regular cutpoints as in eq:B3-two-cuts:
**`log_reconstruction`**: there is `C` with, for all large `k` and all `z ∈ Γ`,
`|ℓ_N(z) − log a_N(z) + (iκ/N) e^{izL} a_N'(z)/(a_N(z)(a_N(z)² − e^{izL}))| ≤ C/N²`.

The background `G = G_μ` is DEF-010's `cauchyTransform S.μ`; `A = e^{iκG}`, `s`, `D`, `D_N`, `a_N`,
`log a_N` are those of RC1 (`PeriodReconstructionCore` `3882a7bd…`). The hypotheses of the abstract
theorem (BO1 `rem_isBigO`) are verified here:
* `Gam`, `isCompact_Gam`; distance of `Γ` from `supp μ` and, eventually, from all roots (PROP-004
  block separation, LB1 `5e10dacd…`, and `|Im z| = h` on the horizontal sides);
* `G_μ` is differentiable and bounded near `Γ` (`hasDerivAt_cauchy`);
* `D ≠ 0` on `Γ` (`D_ne_zero_on_Gam`: positivity of `μ` off the real axis; at the two real points of
  `Γ` the equality `D = 0` would give `F(x) ∈ 2πℤ`), hence `|D| ≥ η > 0` on `Γ` by compactness;
* `iκG_N → iκG_μ` uniformly on `Γ` (`unif_conv`: weak convergence at the points of a finite net,
  with a bounded continuous extension of the Cauchy kernel, and the uniform Lipschitz bound of both
  transforms on `Γ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Complex Filter Topology Asymptotics Set

namespace QuantumNLS.PeriodReconstruction

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionBigO
  QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts QuantumNLS.EmpiricalRapidity

/-! ## 1. The contour -/

/-- `Γ = ∂([a,b] × [−h,h])` as a set. -/
def Gam (a b h : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc a b ∧ (z.im = -h ∨ z.im = h)} ∪ {z | z.im ∈ Icc (-h) h ∧ (z.re = a ∨ z.re = b)}

lemma isCompact_Gam (a b h : ℝ) : IsCompact (Gam a b h) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine IsClosed.union ?_ ?_
    · exact (isClosed_Icc.preimage continuous_re).inter
        ((isClosed_eq continuous_im continuous_const).union (isClosed_eq continuous_im continuous_const))
    · exact (isClosed_Icc.preimage continuous_im).inter
        ((isClosed_eq continuous_re continuous_const).union (isClosed_eq continuous_re continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b| + |h|)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |a| + |b| := by
      rcases hz with ⟨h1, -⟩ | ⟨-, h2 | h2⟩
      · rw [abs_le]; constructor <;> linarith [h1.1, h1.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
      · rw [h2]; linarith [abs_nonneg b]
      · rw [h2]; linarith [abs_nonneg a]
    have him : |z.im| ≤ |h| := by
      rcases hz with ⟨-, h2 | h2⟩ | ⟨h1, -⟩
      · rw [h2, abs_neg]
      · rw [h2]
      · rw [abs_le]; constructor <;> linarith [h1.1, h1.2, neg_abs_le h, le_abs_self h]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ _ := by linarith

lemma Gam_nonempty {a b h : ℝ} (hab : a ≤ b) : (Gam a b h).Nonempty :=
  ⟨(a : ℂ) + h * I, Or.inl ⟨by simp [hab], Or.inr (by simp)⟩⟩

lemma Gam_im_ne_zero_or {a b h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z ∈ Gam a b h) :
    z.im ≠ 0 ∨ (z = a ∨ z = b) := by
  by_cases him : z.im = 0
  · right
    rcases hz with ⟨-, h2 | h2⟩ | ⟨-, h2 | h2⟩
    · rw [h2] at him; linarith
    · rw [h2] at him; linarith
    · left; apply Complex.ext <;> simp [h2, him]
    · right; apply Complex.ext <;> simp [h2, him]
  · exact Or.inl him

lemma Gam_abs_im {a b h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z ∈ Gam a b h) : |z.im| ≤ h := by
  rcases hz with ⟨-, h2 | h2⟩ | ⟨h1, -⟩
  · rw [h2, abs_neg, abs_of_pos hh]
  · rw [h2, abs_of_pos hh]
  · rw [abs_le]; exact ⟨h1.1, h1.2⟩

/-- Distance from `Γ` to real points that stay `δ` away from both cutpoints. -/
lemma Gam_dist {a b h δ t : ℝ} (hh : 0 < h) (ha : δ ≤ |t - a|) (hb : δ ≤ |t - b|) {z : ℂ}
    (hz : z ∈ Gam a b h) : min δ h ≤ ‖z - t‖ := by
  rcases hz with ⟨-, h2 | h2⟩ | ⟨-, h2 | h2⟩
  · refine (min_le_right _ _).trans ((le_of_eq ?_).trans (Complex.abs_im_le_norm _))
    simp [h2, abs_of_pos hh]
  · refine (min_le_right _ _).trans ((le_of_eq ?_).trans (Complex.abs_im_le_norm _))
    simp [h2, abs_of_pos hh]
  · refine (min_le_left _ _).trans (ha.trans ((le_of_eq ?_).trans (Complex.abs_re_le_norm _)))
    simp [h2, abs_sub_comm]
  · refine (min_le_left _ _).trans (hb.trans ((le_of_eq ?_).trans (Complex.abs_re_le_norm _)))
    simp [h2, abs_sub_comm]

/-! ## 2. The Cauchy transform near `Γ` -/

section Cauchy

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma ae_mem_support : ∀ᵐ t ∂μ, t ∈ μ.support :=
  measure_eq_zero_iff_ae_notMem.1 Measure.measure_compl_support |>.mono fun _ h => not_not.1 h

lemma norm_cauchy_le {z : ℂ} {d0 : ℝ} (hd0 : 0 < d0) (hz : ∀ t ∈ μ.support, d0 ≤ ‖z - t‖) :
    ‖cauchyTransform μ z‖ ≤ 1 / d0 := by
  unfold cauchyTransform
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun t : ℝ => ((z - (t : ℂ))⁻¹ : ℂ))
    (C := 1 / d0) ((ae_mem_support μ).mono fun t ht => by
      rw [norm_inv, one_div]; exact inv_anti₀ hd0 (hz t ht))
  rwa [probReal_univ, mul_one] at this

/-- `G_μ` is complex differentiable at points at positive distance from the support. -/
lemma differentiableAt_cauchy {z : ℂ} {d0 : ℝ} (hd0 : 0 < d0)
    (hz : ∀ t ∈ μ.support, d0 ≤ ‖z - t‖) : DifferentiableAt ℂ (cauchyTransform μ) z := by
  have hball : ∀ w ∈ Metric.ball z (d0 / 2), ∀ t ∈ μ.support, d0 / 2 ≤ ‖w - t‖ := by
    intro w hw t ht
    have h1 := hz t ht
    have h2 : ‖w - z‖ < d0 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le (z - t) (z - w)
    rw [sub_sub_sub_cancel_left, norm_sub_rev z w] at this
    linarith
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => ((w - (t : ℂ))⁻¹ : ℂ)) μ := fun w =>
    ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := z)
    (F := fun w (t : ℝ) => ((w - (t : ℂ))⁻¹ : ℂ))
    (F' := fun w (t : ℝ) => -((w - (t : ℂ)) ^ 2)⁻¹) (bound := fun _ => (2 / d0) ^ 2)
    (s := Metric.ball z (d0 / 2))
    (Metric.ball_mem_nhds z (by positivity : (0 : ℝ) < d0 / 2)) (Eventually.of_forall hmeas)
    (Integrable.of_bound (hmeas z) (1 / d0) ((ae_mem_support μ).mono fun t ht => by
      rw [norm_inv, one_div]; exact inv_anti₀ hd0 (hz t ht)))
    ((measurable_const.sub Complex.measurable_ofReal).pow_const 2).inv.neg.aestronglyMeasurable
    ((ae_mem_support μ).mono fun t ht w hw => by
      have h1 := hball w hw t ht
      rw [norm_neg, norm_inv, norm_pow]
      calc (‖w - t‖ ^ 2)⁻¹ ≤ ((d0 / 2) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)
        _ = (2 / d0) ^ 2 := by field_simp)
    (integrable_const _)
    ((ae_mem_support μ).mono fun t ht w hw => by
      have h1 := hball w hw t ht
      have hne : w - t ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h1; linarith
      have h2 : HasDerivAt (fun x : ℂ => (x - t)⁻¹) (-(1 : ℂ) / (w - t) ^ 2) w :=
        ((hasDerivAt_id' w).sub_const (t : ℂ)).inv hne
      exact h2.congr_deriv (by rw [neg_div, one_div]))
  exact key.2.differentiableAt

end Cauchy

/-! ## 3. A bounded continuous extension of the Cauchy kernel -/

/-- `conj(w − t)/max(|w − t|², d₁²)`; it equals `1/(w − t)` for `|w − t| ≥ d₁`. -/
def kern (d1 : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (starRingEnd ℂ) (w - t) * ((max (normSq (w - t)) (d1 ^ 2))⁻¹ : ℝ)

lemma kern_eq {d1 : ℝ} {w : ℂ} {t : ℝ} (hd1 : 0 < d1) (h : d1 ≤ ‖w - t‖) :
    kern d1 w t = (w - t)⁻¹ := by
  have hns : d1 ^ 2 ≤ normSq (w - t) := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ hd1.le h 2
  rw [kern, max_eq_left hns, Complex.inv_def]

lemma kern_bound {d1 : ℝ} (hd1 : 0 < d1) (w : ℂ) (t : ℝ) : ‖kern d1 w t‖ ≤ 1 / d1 := by
  have hm : 0 < max (normSq (w - t)) (d1 ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  rw [kern, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_pos hm, ← div_eq_mul_inv, div_le_div_iff₀ hm hd1, one_mul]
  rcases le_total d1 ‖w - t‖ with h | h
  · calc ‖w - t‖ * d1 ≤ ‖w - t‖ * ‖w - t‖ := by gcongr
      _ = normSq (w - t) := by rw [Complex.normSq_eq_norm_sq]; ring
      _ ≤ _ := le_max_left _ _
  · calc ‖w - t‖ * d1 ≤ d1 * d1 := by gcongr
      _ = d1 ^ 2 := by ring
      _ ≤ _ := le_max_right _ _

lemma continuous_kern {d1 : ℝ} (hd1 : 0 < d1) (w : ℂ) : Continuous (kern d1 w) := by
  unfold kern
  refine ((Complex.continuous_conj.comp (continuous_const.sub Complex.continuous_ofReal))).mul
    (Complex.continuous_ofReal.comp ((Continuous.max ?_ continuous_const).inv₀ fun t =>
      (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'))
  exact Complex.continuous_normSq.comp (continuous_const.sub Complex.continuous_ofReal)

lemma integral_emp_complex {N : ℕ} (p : Fin N → ℝ) (f : ℝ → ℂ) :
    ∫ x, f x ∂(emp p) = ((N : ℝ)⁻¹ : ℂ) * ∑ j, f (p j) := by
  rw [emp, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro j _
    exact integrable_dirac (by simp)

lemma inv_sub_inv_le {z w : ℂ} {t d1 : ℝ} (hd1 : 0 < d1) (hz : d1 ≤ ‖z - t‖) (hw : d1 ≤ ‖w - t‖) :
    ‖(z - t)⁻¹ - (w - t)⁻¹‖ ≤ ‖z - w‖ / d1 ^ 2 := by
  have hz0 : z - t ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hd1 hz)
  have hw0 : w - t ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hd1 hw)
  have e : (z - t)⁻¹ - (w - t)⁻¹ = (w - z) / ((z - t) * (w - t)) := by field_simp; ring
  rw [e, norm_div, norm_mul, norm_sub_rev w z, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul hz hw hd1.le (norm_nonneg _)
  have h2 := norm_nonneg (z - w)
  nlinarith

/-! ## 4. Uniform convergence of the root Cauchy transforms on `Γ` -/

/-- `G_N → G_μ` uniformly on a compact set at positive distance from the support and from all roots. -/
theorem unif_conv {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
    {μ : ProbabilityMeasure ℝ} (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    {Γ : Set ℂ} (hΓ : IsCompact Γ) {d1 : ℝ} (hd1 : 0 < d1)
    (hsupp : ∀ z ∈ Γ, ∀ t ∈ (μ : Measure ℝ).support, d1 ≤ ‖z - t‖)
    (hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d1 ≤ ‖z - (B k).q j‖) :
    Tendsto (fun p : ℕ × ℂ => ((N p.1 : ℝ)⁻¹ : ℂ) * ∑ j, (p.2 - ((B p.1).q j : ℂ))⁻¹ -
      cauchyTransform (μ : Measure ℝ) p.2) (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_prod_principal_iff]
  set ρ := ε * d1 ^ 2 / 4 with hρ
  obtain ⟨T, hTΓ, hTf, hcov⟩ := hΓ.finite_cover_balls (show 0 < ρ by positivity)
  -- convergence at the net points
  have hpt : ∀ w ∈ T, ∀ᶠ k in atTop,
      ‖((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹ - cauchyTransform (μ : Measure ℝ) w‖ <
        ε / 2 := by
    intro w hw
    set K : BoundedContinuousFunction ℝ ℂ :=
      BoundedContinuousFunction.mkOfBound ⟨kern d1 w, continuous_kern hd1 w⟩ (2 / d1)
        (fun x y => by
          show dist (kern d1 w x) (kern d1 w y) ≤ 2 / d1
          rw [dist_eq_norm]
          have := kern_bound hd1 w x; have := kern_bound hd1 w y
          have e : (2 : ℝ) / d1 = 1 / d1 + 1 / d1 := by ring
          rw [e]; exact (norm_sub_le _ _).trans (by linarith))
    have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hconv K
    have hGμ : ∫ t, K t ∂(μ : Measure ℝ) = cauchyTransform (μ : Measure ℝ) w := by
      unfold cauchyTransform
      refine integral_congr_ae ((ae_mem_support (μ : Measure ℝ)).mono fun t ht => ?_)
      exact kern_eq hd1 (hsupp w (hTΓ hw) t ht)
    rw [hGμ] at hlim
    have hev := (Metric.tendsto_nhds.1 hlim) (ε / 2) (by positivity)
    filter_upwards [hev, hroot] with k hk hr
    have hemp : ∫ t, K t ∂(rootP (B k) (hN k) : Measure ℝ) =
        ((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹ := by
      show ∫ t, K t ∂(emp (B k).q) = _
      rw [integral_emp_complex]
      congr 1
      exact Finset.sum_congr rfl fun j _ => kern_eq hd1 (hr w (hTΓ hw) j)
    rw [hemp, dist_eq_norm] at hk
    exact hk
  have hall := (hTf.eventually_all).2 hpt
  filter_upwards [hall, hroot] with k hk hr z hz
  obtain ⟨w, hw, hzw⟩ : ∃ w ∈ T, z ∈ Metric.ball w ρ := by
    have := hcov hz; simp only [Set.mem_iUnion] at this; obtain ⟨w, hw, h⟩ := this; exact ⟨w, hw, h⟩
  have hzw' : ‖z - w‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hzw
  have hNk : (0 : ℝ) < N k := Nat.cast_pos.2 (hN k)
  -- Lipschitz bounds
  have hLN : ‖((N k : ℝ)⁻¹ : ℂ) * ∑ j, (z - ((B k).q j : ℂ))⁻¹ -
      ((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹‖ ≤ ρ / d1 ^ 2 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hNk.le]
    calc (N k : ℝ)⁻¹ * ‖∑ j, ((z - ((B k).q j : ℂ))⁻¹ - (w - ((B k).q j : ℂ))⁻¹)‖
        ≤ (N k : ℝ)⁻¹ * ∑ _j : Fin (N k), ρ / d1 ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact (inv_sub_inv_le hd1 (hr z hz j) (hr w (hTΓ hw) j)).trans
            (by gcongr)
      _ = ρ / d1 ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hLG : ‖cauchyTransform (μ : Measure ℝ) z - cauchyTransform (μ : Measure ℝ) w‖ ≤
      ρ / d1 ^ 2 := by
    unfold cauchyTransform
    have hi : ∀ v ∈ Γ, Integrable (fun t : ℝ => ((v - (t : ℂ))⁻¹ : ℂ)) (μ : Measure ℝ) :=
      fun v hv => Integrable.of_bound
        ((measurable_const.sub Complex.measurable_ofReal).inv.aestronglyMeasurable) (1 / d1)
        ((ae_mem_support (μ : Measure ℝ)).mono fun t ht => by
          rw [norm_inv, one_div]; exact inv_anti₀ hd1 (hsupp v hv t ht))
    rw [← integral_sub (hi z hz) (hi w (hTΓ hw))]
    have := norm_integral_le_of_norm_le_const (μ := (μ : Measure ℝ))
      (f := fun t : ℝ => ((z - (t : ℂ))⁻¹ : ℂ) - (w - (t : ℂ))⁻¹) (C := ρ / d1 ^ 2)
      ((ae_mem_support (μ : Measure ℝ)).mono fun t ht =>
        (inv_sub_inv_le hd1 (hsupp z hz t ht) (hsupp w (hTΓ hw) t ht)).trans (by gcongr))
    rwa [probReal_univ, mul_one] at this
  have hw' := hk w hw
  rw [dist_eq_norm, sub_zero]
  have e : ((N k : ℝ)⁻¹ : ℂ) * ∑ j, (z - ((B k).q j : ℂ))⁻¹ - cauchyTransform (μ : Measure ℝ) z =
      (((N k : ℝ)⁻¹ : ℂ) * ∑ j, (z - ((B k).q j : ℂ))⁻¹ -
        ((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹) +
      (((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹ - cauchyTransform (μ : Measure ℝ) w) -
      (cauchyTransform (μ : Measure ℝ) z - cauchyTransform (μ : Measure ℝ) w) := by ring
  rw [e]
  have hρd : ρ / d1 ^ 2 = ε / 4 := by rw [hρ]; field_simp
  calc _ ≤ ‖_ + _‖ + ‖cauchyTransform (μ : Measure ℝ) z - cauchyTransform (μ : Measure ℝ) w‖ :=
        norm_sub_le _ _
    _ ≤ ‖((N k : ℝ)⁻¹ : ℂ) * ∑ j, (z - ((B k).q j : ℂ))⁻¹ -
          ((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹‖ +
        ‖((N k : ℝ)⁻¹ : ℂ) * ∑ j, (w - ((B k).q j : ℂ))⁻¹ - cauchyTransform (μ : Measure ℝ) w‖ +
        ‖cauchyTransform (μ : Measure ℝ) z - cauchyTransform (μ : Measure ℝ) w‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-! ## 5. The background multiplier on `Γ` -/

lemma conj_cauchy (μ : Measure ℝ) (z : ℂ) :
    cauchyTransform μ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cauchyTransform μ z) := by
  unfold cauchyTransform
  rw [← integral_conj]
  congr 1; funext t; simp [map_sub, map_inv₀]

lemma norm_Af (κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ‖Af κ G z‖ = Real.exp (-(κ * (G z).im)) := by
  simp [Af, Complex.norm_exp, mul_re]

lemma norm_inv_Af (κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : ‖(Af κ G z)⁻¹‖ = Real.exp (κ * (G z).im) := by
  rw [norm_inv, norm_Af, ← Real.exp_neg, neg_neg]

lemma norm_ef (L : ℝ) (z : ℂ) : ‖ef L z‖ = Real.exp (-(L * z.im)) := by
  simp [ef, Complex.norm_exp, mul_re]

lemma sq_of_D_zero {L κ : ℝ} {G : ℂ → ℂ} {z : ℂ} (hD : Df L κ G z = 0) :
    Af κ G z ^ 2 = ef L z := by
  have hA : Af κ G z ≠ 0 := exp_ne_zero _
  unfold Df at hD
  field_simp at hD
  linear_combination hD

/-- `D ≠ 0` off the real axis: positivity of `μ`. -/
lemma D_ne_zero_of_im {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {G : ℂ → ℂ} {z : ℂ}
    (hsign : z.im * (G z).im < 0) : Df L κ G z ≠ 0 := by
  intro hD
  have h := congrArg norm (sq_of_D_zero hD)
  rw [norm_pow, norm_Af, norm_ef, ← Real.exp_nat_mul, Real.exp_eq_exp] at h
  push_cast at h
  rcases lt_or_gt_of_ne (show z.im ≠ 0 by intro h0; rw [h0, zero_mul] at hsign; linarith) with
    h1 | h1
  · have : 0 < (G z).im := by nlinarith
    nlinarith
  · have : (G z).im < 0 := by nlinarith
    nlinarith

lemma im_sign_cauchy (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
    z.im * (cauchyTransform μ z).im < 0 := by
  have hμ : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 := im_cauchyTransform_neg μ hμ ((starRingEnd ℂ) z) (by simpa using h)
    rw [conj_cauchy, Complex.conj_im] at h1
    nlinarith
  · have := im_cauchyTransform_neg μ hμ z h
    nlinarith

/-- At a real point with `F(x) ∉ 2πℤ`, `D(x) ≠ 0`. -/
lemma D_ne_zero_real {L κ : ℝ} (μ : Measure ℝ) {x : ℝ}
    (hF : ∀ m : ℤ, exteriorForce L κ μ x ≠ 2 * Real.pi * m) :
    Df L κ (cauchyTransform μ) x ≠ 0 := by
  intro hD
  have h := sq_of_D_zero hD
  have h2 : exp (2 * (I * κ * cauchyTransform μ x)) = exp (I * L * x) := by
    rw [show (2 : ℂ) * (I * κ * cauchyTransform μ x) = ((2 : ℕ) : ℂ) * (I * κ * cauchyTransform μ x)
      by norm_num, Complex.exp_nat_mul]
    exact h
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
  rw [cauchyTransform_real] at hm
  set g : ℝ := ∫ t : ℝ, (x - t)⁻¹ ∂μ
  have him := congrArg Complex.im hm
  simp only [mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im, add_im, intCast_re, intCast_im,
    re_ofNat, im_ofNat] at him
  apply hF (-m)
  unfold exteriorForce
  rw [cauchyTransform_real, ofReal_re]
  push_cast
  linarith

lemma F_not_mem {Fx : ℝ} {n : ℤ} (h1 : 2 * Real.pi * (n - 1) < Fx) (h2 : Fx < 2 * Real.pi * n) :
    ∀ m : ℤ, Fx ≠ 2 * Real.pi * m := by
  intro m hm
  rw [hm] at h1 h2
  have hpi := Real.pi_pos
  have a1 : ((n : ℝ) - 1) < m := by nlinarith
  have a2 : (m : ℝ) < n := by nlinarith
  have b1 : n - 1 < m := by exact_mod_cast a1
  have b2 : m < n := by exact_mod_cast a2
  omega

/-! ## 6. eq:B3-log-reconstruction -/

/-- **PROP-006, eq:B3-log-reconstruction**: uniformly for `z ∈ Γ`, the remainder
`ℓ_N − log a_N + (iκ/N) e^{izL} a_N'/(a_N(a_N² − e^{izL}))` is `O(N^{-2})` along any sequence of
PROP-003 (here `ℓ_N` with principal logarithms, equal to the Taylor-defined EP1 `ellN` on `Γ`). -/
theorem log_reconstruction {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h,
      ‖remf κ L N (fun k => (B k).q) (cauchyTransform S.μ) (k, z)‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2 := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hL := S.hL
  have hκ := S.hκ
  set G := cauchyTransform S.μ with hG
  set Γ := Gam xm xp h with hΓ
  have hΓc : IsCompact Γ := isCompact_Gam xm xp h
  -- distance of Γ from the support
  obtain ⟨rm, hrm, hbm⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xm
    (S.cuts_sub hxm)
  obtain ⟨rp, hrp, hbp⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xp
    (S.cuts_sub hxp)
  have hsm : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xm| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbm (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_left _ _)) ht
  have hsp : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xp| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbp (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_right _ _)) ht
  set d0 := min (min rm rp) h with hd0def
  have hd0 : 0 < d0 := by positivity
  have hsupp : ∀ z ∈ Γ, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ := fun z hz t ht =>
    Gam_dist hh (hsm t ht) (hsp t ht) hz
  -- roots
  obtain ⟨δ, hδ, hblock⟩ := label_block_seq S hμ hconv hNtop hxm hxp hlt h1 h2 h3 h4
  set d := min δ h with hddef
  have hd : 0 < d := by positivity
  have hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d ≤ ‖z - (B k).q j‖ :=
    hblock.mono fun k hk z hz j => Gam_dist hh (hk j).2.1 (hk j).2.2 hz
  -- uniform convergence
  set d1 := min d d0
  have hd1 : 0 < d1 := by positivity
  have hU0 := unif_conv hconv hΓc hd1 (fun z hz t ht => by
      rw [hμ] at ht; exact (min_le_right _ _).trans (hsupp z hz t ht))
    (hroot.mono fun k hk z hz j => (min_le_left _ _).trans (hk z hz j))
  rw [hμ] at hU0
  have hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) -
      I * κ * G p.2) (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
    have := hU0.const_mul (I * κ)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun p => ?_)
    show I * κ * (((N p.1 : ℝ)⁻¹ : ℂ) * ∑ j, (p.2 - ((B p.1).q j : ℂ))⁻¹ - G p.2) =
      (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) - I * κ * G p.2
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  -- background
  have hGd : ∀ z ∈ Γ, DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_cauchy S.μ hd0 (hsupp z hz)
  have hDz : ∀ z ∈ Γ, Df L κ G z ≠ 0 := by
    intro z hz
    rcases Gam_im_ne_zero_or hh hz with him | hreal
    · exact D_ne_zero_of_im hL hκ (im_sign_cauchy S.μ him)
    · rcases hreal with rfl | rfl
      · exact D_ne_zero_real S.μ (F_not_mem h1 h2)
      · exact D_ne_zero_real S.μ (F_not_mem (n := n + 1) (by push_cast; linarith)
          (by push_cast; linarith))
  have hDc : ∀ z ∈ Γ, ContinuousAt (Df L κ G) z := fun z hz => by
    have hA : ContinuousAt (Af κ G) z := ((hGd z hz).continuousAt.const_mul (I * κ)).cexp
    have he : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    exact hA.sub (he.div hA (exp_ne_zero _))
  have hDev : ∀ z ∈ Γ, ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0 := fun z hz =>
    (hDc z hz).eventually_ne (hDz z hz)
  obtain ⟨z0, hz0, hmin⟩ := hΓc.exists_isMinOn (Gam_nonempty hlt.le)
    (f := fun z => ‖Df L κ G z‖) (fun z hz => (hDc z hz).norm.continuousWithinAt)
  set η := ‖Df L κ G z0‖
  have hη : 0 < η := norm_pos_iff.2 (hDz z0 hz0)
  set M := max 1 (max (Real.exp (κ / d0)) (Real.exp (L * h)))
  have hM0 : 1 ≤ M := le_max_left _ _
  have hM : ∀ z ∈ Γ, ‖Af κ G z‖ ≤ M ∧ ‖(Af κ G z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
      η ≤ ‖Df L κ G z‖ := by
    intro z hz
    have hGb := norm_cauchy_le S.μ hd0 (hsupp z hz)
    have himG : |(G z).im| ≤ 1 / d0 := (Complex.abs_im_le_norm _).trans hGb
    have hk : κ * |(G z).im| ≤ κ / d0 := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left himG hκ.le
    have hzim := Gam_abs_im hh hz
    have hexp1 : Real.exp (κ / d0) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hexp2 : Real.exp (L * h) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_, hmin hz⟩
    · rw [norm_Af]
      refine (Real.exp_le_exp.2 ?_).trans hexp1
      nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
    · rw [norm_inv_Af]
      refine (Real.exp_le_exp.2 ?_).trans hexp1
      nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
    · rw [norm_ef]
      refine (Real.exp_le_exp.2 ?_).trans hexp2
      nlinarith [neg_abs_le z.im, le_abs_self z.im]
  have hbig := rem_isBigO (q := fun k => (B k).q) hκ hN hNtop hd hroot hU hGd hDev hM0 hη hM
  obtain ⟨C, hC⟩ := hbig.bound
  refine ⟨C, ?_⟩
  have := Filter.eventually_prod_principal_iff.1 hC
  filter_upwards [this] with k hk z hz
  have := hk z hz
  rwa [Real.norm_of_nonneg (sq_nonneg _)] at this

end QuantumNLS.PeriodReconstruction

#print axioms QuantumNLS.PeriodReconstruction.isCompact_Gam
#print axioms QuantumNLS.PeriodReconstruction.differentiableAt_cauchy
#print axioms QuantumNLS.PeriodReconstruction.unif_conv
#print axioms QuantumNLS.PeriodReconstruction.log_reconstruction
