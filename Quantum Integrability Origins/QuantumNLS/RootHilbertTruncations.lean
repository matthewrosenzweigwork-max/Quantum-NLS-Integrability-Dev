import Mathlib

/-!
# R-064239ED `lem:root-Hilbert-truncations` (ROOT_scalar_uniqueness.tex:11) -- POINTWISE PART ONLY

Source statement: `ρ ≥ 0`, `ρ ∈ L¹(ℝ) ∩ L^∞(ℝ)`, locally Hölder continuous; `H_ε ρ(x) = ∫_{|x-y|>ε} ρ(y)/(x-y) dy`.
(i) the principal value limit `Hρ(x)` exists at every `x`;
(ii) `H_ε ρ → Hρ` in `L²(dx)` and in `L²(ρ dx)` as `ε ↓ 0`.

PROVED HERE: (i), as `pv_exists` / `tendsto_hilbertPV` (literal hypotheses `HilbertHyp`; local Hölder
means: every `x` has a neighbourhood `s` and `C, r : ℝ≥0`, `0 < r ≤ 1`, with `HolderOnWith C r ρ s`).
Printed proof followed: split `ε<|t|<δ` / `|t|≥δ`, subtract `ρ(x)` in the symmetric integral (zero by
oddness), dominate by `C|t|^{r-1}`, tail absolutely convergent since `ρ ∈ L¹`.

NOT PROVED (gap): (ii), the Fourier/Plancherel part (needs: Plancherel identification on `L¹∩L²`,
multiplier of `1_{ε<|t|<R}/t`, uniform bound and a.e. limit `-iπ sgn ξ`, i.e. the Dirichlet integral).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace QuantumNLS.RootHilbert

/-- `H_ε ρ(x) = ∫_{|x-y|>ε} ρ(y)/(x-y) dy`. -/
def hilbertTrunc (ρ : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  ∫ y in {y : ℝ | ε < |x - y|}, ρ y / (x - y)

/-- The hypotheses of the lemma: `ρ ≥ 0`, `ρ ∈ L¹ ∩ L^∞`, locally Hölder continuous. -/
structure HilbertHyp (ρ : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  integrable : Integrable ρ volume
  linfty : MemLp ρ ⊤ volume
  holder : ∀ x : ℝ, ∃ s ∈ 𝓝 x, ∃ C r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ HolderOnWith C r ρ s

theorem hilbertTrunc_eq (ρ : ℝ → ℝ) (ε x : ℝ) :
    hilbertTrunc ρ ε x = ∫ t, {t : ℝ | ε < |t|}.indicator (fun t => ρ (x - t) / t) t := by
  have hm : MeasurableSet {y : ℝ | ε < |x - y|} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [hilbertTrunc, ← integral_indicator hm]
  rw [← integral_sub_left_eq_self
    (fun t => {t : ℝ | ε < |t|}.indicator (fun t => ρ (x - t) / t) t) volume x]
  congr 1
  funext y
  by_cases h : ε < |x - y|
  · simp [indicator, h]
  · simp [indicator, h]

theorem integral_odd_indicator (S : Set ℝ) (hS : ∀ t, t ∈ S ↔ -t ∈ S) :
    ∫ t, S.indicator (fun t => 1 / t) t = 0 := by
  have h := integral_neg_eq_self (fun t => S.indicator (fun t : ℝ => 1 / t) t) volume
  have h2 : (fun t : ℝ => S.indicator (fun t : ℝ => 1 / t) (-t)) =
      fun t => -(S.indicator (fun t : ℝ => 1 / t) t) := by
    funext t
    by_cases ht : t ∈ S
    · have : -t ∈ S := (hS t).mp ht
      simp [indicator, ht, this, one_div, inv_neg]
    · have : -t ∉ S := fun h' => ht ((hS t).mpr h')
      simp [indicator, ht, this]
  rw [h2, integral_neg] at h
  linarith

theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t : ℝ => |t| ^ r) (Ioo (-η) η) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ r) (Ioo 0 η) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hη).mpr hr
  have h2 : IntegrableOn (fun t : ℝ => |t| ^ r) (Ioo 0 η) :=
    h1.congr_fun (fun t ht => by simp [abs_of_pos ht.1]) measurableSet_Ioo
  have h2' : IntervalIntegrable (fun t : ℝ => |t| ^ r) volume 0 η := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h2
  have h3 : IntervalIntegrable (fun t : ℝ => |t| ^ r) volume 0 (-η) := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun t : ℝ => |t| ^ r) (a := 0) (b := η)).mp h2'
    simpa using this
  have h4 : IntervalIntegrable (fun t : ℝ => |t| ^ r) volume (-η) η := h3.symm.trans h2'
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at h4
  exact h4.mono_set Ioo_subset_Ioc_self

/-- **Pointwise part of R-064239ED.** For every `x`, `H_ε ρ(x)` has a limit as `ε ↓ 0`. -/
theorem pv_exists {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (x : ℝ) :
    ∃ L : ℝ, Tendsto (fun ε => hilbertTrunc ρ ε x) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨s, hs, C, r, hr0, hr1, hH⟩ := hρ.holder x
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hxs : x ∈ s := hball (Metric.mem_ball_self hδ)
  set g : ℝ → ℝ := fun t => (ρ (x - t) - ρ x) / t with hg
  set Φ : ℝ → ℝ := fun t => ρ (x - t) / t with hΦ
  set G : ℝ → ℝ := (Ioo (-δ) δ).indicator (fun t => (C : ℝ) * |t| ^ ((r : ℝ) - 1)) with hG
  have hρm : AEStronglyMeasurable (fun t => ρ (x - t)) volume :=
    (hρ.integrable.comp_sub_left x).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g volume := by
    have := (hρm.sub (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => ρ x) volume)).mul
      (measurable_inv.aestronglyMeasurable : AEStronglyMeasurable (fun t : ℝ => t⁻¹) volume)
    exact this.congr (Eventually.of_forall fun t => by simp [hg, div_eq_mul_inv])
  have hΦm : AEStronglyMeasurable Φ volume := by
    have := hρm.mul
      (measurable_inv.aestronglyMeasurable : AEStronglyMeasurable (fun t : ℝ => t⁻¹) volume)
    exact this.congr (Eventually.of_forall fun t => by simp [hΦ, div_eq_mul_inv])
  -- Hölder bound
  have hbd : ∀ t : ℝ, |t| < δ → 0 < |t| → |g t| ≤ C * |t| ^ ((r : ℝ) - 1) := by
    intro t ht ht0
    have h1 : x - t ∈ s := hball (by rw [Metric.mem_ball, Real.dist_eq]; simpa using ht)
    have h2 := hH.dist_le h1 hxs
    rw [Real.dist_eq, Real.dist_eq] at h2
    have h3 : |x - t - x| = |t| := by rw [sub_sub_cancel_left, abs_neg]
    rw [h3] at h2
    simp only [hg, abs_div]
    rw [Real.rpow_sub_one ht0.ne', ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h2 ht0.le
  have hGint : Integrable G volume := by
    rw [hG, integrable_indicator_iff measurableSet_Ioo]
    exact (integrableOn_abs_rpow (by linarith [(NNReal.coe_pos.mpr hr0)] : -1 < (r : ℝ) - 1) hδ).const_mul _
  set Lim : Set ℝ := {t | 0 < |t| ∧ |t| < δ} with hLim
  set Mset : ℝ → Set ℝ := fun ε => {t | ε < |t| ∧ |t| < δ} with hMset
  set Oset : Set ℝ := {t | δ ≤ |t|} with hOset
  have habs : Measurable (fun t : ℝ => |t|) := continuous_abs.measurable
  have hMmeas : ∀ ε, MeasurableSet (Mset ε) := fun ε =>
    (measurableSet_lt measurable_const habs).inter (measurableSet_lt habs measurable_const)
  have hOmeas : MeasurableSet Oset := measurableSet_le measurable_const habs
  have hLmeas : MeasurableSet Lim :=
    (measurableSet_lt measurable_const habs).inter (measurableSet_lt habs measurable_const)
  have hlim : Tendsto (fun ε => ∫ t, (Mset ε).indicator g t) (𝓝[>] 0)
      (𝓝 (∫ t, Lim.indicator g t)) := by
    refine tendsto_integral_filter_of_dominated_convergence G
      (Eventually.of_forall fun ε => hgm.indicator (hMmeas ε)) ?_ hGint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Mset ε
      · have hGt : G t = C * |t| ^ ((r : ℝ) - 1) := by
          rw [hG, indicator_of_mem]
          rw [mem_Ioo]; exact abs_lt.mp ht.2
        rw [indicator_of_mem ht, Real.norm_eq_abs, hGt]
        exact hbd t ht.2 (lt_trans hε ht.1)
      · rw [indicator_of_notMem ht, norm_zero]
        rw [hG]
        exact indicator_nonneg (fun t _ => by positivity) t
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Lim
      · rw [indicator_of_mem ht]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT ht.1] with ε hε
        rw [indicator_of_mem (show t ∈ Mset ε from ⟨hε.2, ht.2⟩)]
      · rw [indicator_of_notMem ht]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have : t ∉ Mset ε := fun hm => ht ⟨lt_trans hε hm.1, hm.2⟩
        rw [indicator_of_notMem this]
  have hOint : Integrable (Oset.indicator Φ) volume := by
    have hb : Integrable (fun t => δ⁻¹ * ‖ρ (x - t)‖) volume :=
      ((hρ.integrable.comp_sub_left x).norm).const_mul _
    refine hb.mono' (hΦm.indicator hOmeas) (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Oset
    · rw [indicator_of_mem ht, hΦ]
      simp only [norm_div, Real.norm_eq_abs]
      have ht' : δ ≤ |t| := ht
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ ht') (abs_nonneg _)
    · rw [indicator_of_notMem ht, norm_zero]; positivity
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), hilbertTrunc ρ ε x =
      (∫ t, (Mset ε).indicator g t) + ∫ t, Oset.indicator Φ t := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεδ : ε < δ := hε.2
    have hMint : Integrable ((Mset ε).indicator g) volume := by
      refine hGint.mono' (hgm.indicator (hMmeas ε)) (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ Mset ε
      · have hGt : G t = C * |t| ^ ((r : ℝ) - 1) := by
          rw [hG, indicator_of_mem]
          rw [mem_Ioo]; exact abs_lt.mp ht.2
        rw [indicator_of_mem ht, Real.norm_eq_abs, hGt]
        exact hbd t ht.2 (lt_trans hε0 ht.1)
      · rw [indicator_of_notMem ht, norm_zero, hG]
        exact indicator_nonneg (fun t _ => by positivity) t
    have hInv : Integrable (fun t => ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t) volume := by
      have hb : Integrable ((Ioo (-δ) δ).indicator (fun _ : ℝ => ε⁻¹)) volume := by
        rw [integrable_indicator_iff measurableSet_Ioo]
        exact integrableOn_const (by simp)
      have hm : AEStronglyMeasurable (fun t : ℝ => ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t)
          volume := by
        refine (aestronglyMeasurable_const.mul ?_)
        exact (measurable_const.div measurable_id).aestronglyMeasurable.indicator (hMmeas ε)
      refine (hb.const_mul |ρ x|).mono' hm (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ Mset ε
      · have : t ∈ Ioo (-δ) δ := by rw [mem_Ioo]; exact abs_lt.mp ht.2
        rw [indicator_of_mem ht, indicator_of_mem this, Real.norm_eq_abs, abs_mul]
        gcongr
        rw [one_div, abs_inv]
        exact inv_anti₀ hε0 ht.1.le
      · rw [indicator_of_notMem ht, mul_zero, norm_zero]
        refine mul_nonneg (abs_nonneg _) ?_
        exact indicator_nonneg (fun t _ => by positivity) t
    have hsplit : {t : ℝ | ε < |t|}.indicator Φ = fun t =>
        ((Mset ε).indicator g t + ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t) +
          Oset.indicator Φ t := by
      funext t
      by_cases h1 : ε < |t|
      · have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at h1; linarith
        by_cases h2 : |t| < δ
        · have hM : t ∈ Mset ε := ⟨h1, h2⟩
          have hO : t ∉ Oset := fun h => by have : δ ≤ |t| := h; linarith
          rw [indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from h1), indicator_of_mem hM,
            indicator_of_mem hM, indicator_of_notMem hO]
          simp only [hΦ, hg]
          field_simp
          ring
        · have hM : t ∉ Mset ε := fun h => h2 h.2
          have hO : t ∈ Oset := not_lt.mp h2
          rw [indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from h1), indicator_of_notMem hM,
            indicator_of_notMem hM, indicator_of_mem hO]
          simp
      · have hM : t ∉ Mset ε := fun h => h1 h.1
        have hO : t ∉ Oset := fun h => by
          have : δ ≤ |t| := h
          exact h1 (lt_of_lt_of_le hεδ this)
        rw [indicator_of_notMem (show t ∉ {t : ℝ | ε < |t|} from h1), indicator_of_notMem hM,
          indicator_of_notMem hM, indicator_of_notMem hO]
        simp
    have hodd : ∫ t, (Mset ε).indicator (fun t : ℝ => 1 / t) t = 0 := by
      refine integral_odd_indicator (Mset ε) (fun t => ?_)
      simp only [hMset, mem_setOf_eq, abs_neg]
    have e1 := integral_add
      (f := fun t => (Mset ε).indicator g t + ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t)
      (g := fun t => Oset.indicator Φ t)
      (hMint.add hInv : Integrable (fun t => (Mset ε).indicator g t +
        ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t) volume) hOint
    have e2 := integral_add (f := fun t => (Mset ε).indicator g t)
      (g := fun t => ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t) hMint hInv
    rw [hilbertTrunc_eq, hsplit]
    show ∫ t, ((Mset ε).indicator g t + ρ x * (Mset ε).indicator (fun t : ℝ => 1 / t) t +
      Oset.indicator Φ t) = _
    rw [e1, e2, integral_const_mul, hodd, mul_zero, add_zero]
  exact ⟨_, ((hlim.add_const (∫ t, Oset.indicator Φ t)).congr'
    (heq.mono fun ε h => h.symm))⟩

/-- The principal value `Hρ(x) = lim_{ε↓0} H_ε ρ(x)`. -/
def hilbertPV (ρ : ℝ → ℝ) (x : ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) (fun ε => hilbertTrunc ρ ε x)

theorem tendsto_hilbertPV {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (x : ℝ) :
    Tendsto (fun ε => hilbertTrunc ρ ε x) (𝓝[>] 0) (𝓝 (hilbertPV ρ x)) := by
  obtain ⟨L, hL⟩ := pv_exists hρ x
  exact tendsto_nhds_limUnder ⟨L, hL⟩

#print axioms pv_exists
#print axioms tendsto_hilbertPV

end QuantumNLS.RootHilbert
