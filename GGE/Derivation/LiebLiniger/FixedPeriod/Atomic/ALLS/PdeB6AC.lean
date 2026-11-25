import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Coeff

/-! # Track B, package 3: the product rule `|A|²` for indefinite integrals of `L¹` functions

If `A r = A s + ∫ₛʳ g` on `[s,t]` with `g ∈ L¹(s,t)`, then
`|A t|² - |A s|² = 2 Re ∫ₛᵗ conj(A r) g r dr` (`normSq_indefinite`). Proof by Fubini on the square
`(s,t]²` split along the diagonal (no differentiability is used).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

theorem integrable_conj_fun {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : Integrable g μ) : Integrable (fun q => conj (g q)) μ :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hg

theorem integral_indicator_Iic_Ioc {g : ℝ → ℂ} {s t r : ℝ} (hr : r ∈ Set.Icc s t) :
    ∫ q, (Set.Iic r).indicator g q ∂((volume : Measure ℝ).restrict (Set.Ioc s t)) =
      ∫ q in s..r, g q := by
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    intervalIntegral.integral_of_le hr.1]
  congr 2
  ext q
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2, h1.trans hr.2⟩

theorem integral_indicator_Iio_Ioc {g : ℝ → ℂ} {s t r : ℝ} (hr : r ∈ Set.Icc s t) :
    ∫ q, (Set.Iio r).indicator g q ∂((volume : Measure ℝ).restrict (Set.Ioc s t)) =
      ∫ q in s..r, g q := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    intervalIntegral.integral_of_le hr.1, integral_Ioc_eq_integral_Ioo]
  congr 2
  ext q
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2, h1.le.trans hr.2⟩

theorem intervalIntegral_conj {g : ℝ → ℂ} {s r : ℝ} (h : s ≤ r) :
    ∫ q in s..r, conj (g q) = conj (∫ q in s..r, g q) := by
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, integral_conj]

/-- The diagonal splitting identity: `I + conj I = |∫ₛᵗ g|²`, `I = ∫ₛᵗ conj(∫ₛʳ g) g(r) dr`. -/
theorem triangle_identity {g : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hg : IntegrableOn g (Set.Ioc s t)) :
    (∫ r in s..t, conj (∫ q in s..r, g q) * g r) +
        conj (∫ r in s..t, conj (∫ q in s..r, g q) * g r) =
      conj (∫ q in s..t, g q) * ∫ q in s..t, g q := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc s t) with hμ
  have hgc : Integrable (fun q => conj (g q)) μ := integrable_conj_fun hg
  set H : ℝ × ℝ → ℂ := fun p => conj (g p.1) * g p.2 with hHdef
  have hH : Integrable H (μ.prod μ) := hgc.mul_prod hg
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have htot : ∫ p, H p ∂(μ.prod μ) = conj (∫ q in s..t, g q) * ∫ q in s..t, g q := by
    rw [hHdef, integral_prod_mul (fun q => conj (g q)) g, integral_conj,
      intervalIntegral.integral_of_le hst]
  have hA : ∫ p in S, H p ∂(μ.prod μ) = ∫ r in s..t, conj (∫ q in s..r, g q) * g r := by
    rw [← integral_indicator hS, integral_prod_symm _ (hH.indicator hS),
      intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hpt : (fun q => S.indicator H (q, r)) =
        fun q => (Set.Iic r).indicator (fun q => conj (g q)) q * g r := by
      funext q
      by_cases hq : q ≤ r
      · simp [S, H, Set.indicator, hq]
      · simp [S, H, Set.indicator, hq]
    rw [hpt, integral_mul_const, integral_indicator_Iic_Ioc ⟨hr.1.le, hr.2⟩,
      intervalIntegral_conj hr.1.le]
  have hB : ∫ p in Sᶜ, H p ∂(μ.prod μ) = conj (∫ r in s..t, conj (∫ q in s..r, g q) * g r) := by
    rw [← integral_indicator hS.compl, integral_prod _ (hH.indicator hS.compl),
      intervalIntegral.integral_of_le hst, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    have hpt : (fun r => Sᶜ.indicator H (q, r)) =
        fun r => conj (g q) * (Set.Iio q).indicator g r := by
      funext r
      by_cases hr : r < q
      · simp [S, H, Set.indicator, hr, not_le.2 hr]
      · simp [S, H, Set.indicator, hr, not_lt.1 hr]
    rw [hpt, integral_const_mul, integral_indicator_Iio_Ioc ⟨hq.1.le, hq.2⟩, map_mul,
      Complex.conj_conj, mul_comm]
  rw [← hB, ← hA, integral_add_compl hS hH, htot]

/-- **Product rule for `|A|²`** of an indefinite integral of an `L¹` function. -/
theorem normSq_indefinite {g : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hg : IntegrableOn g (Set.Ioc s t))
    (A : ℝ → ℂ) (hA : ∀ r ∈ Set.Icc s t, A r = A s + ∫ q in s..r, g q) :
    ‖A t‖ ^ 2 - ‖A s‖ ^ 2 = 2 * (∫ r in s..t, conj (A r) * g r).re := by
  have hgi : IntervalIntegrable g volume s t := (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 hg
  have hcongr : (∫ r in s..t, conj (A r) * g r) =
      ∫ r in s..t, (conj (A s) * g r + conj (∫ q in s..r, g q) * g r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hst] at hr
    rw [hA r hr, map_add]
    ring
  have hI2 : IntervalIntegrable (fun r => conj (∫ q in s..r, g q) * g r) volume s t := by
    have hc : ContinuousOn (fun r => conj (∫ q in s..r, g q)) (Set.uIcc s t) :=
      Complex.continuous_conj.comp_continuousOn
        ((intervalIntegral.continuousOn_primitive_interval' hgi Set.left_mem_uIcc))
    exact hgi.continuousOn_mul hc
  have hI1 : IntervalIntegrable (fun r => conj (A s) * g r) volume s t := hgi.const_mul _
  rw [hcongr, intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
    hA t ⟨hst, le_rfl⟩]
  have key := triangle_identity hst hg
  set G := ∫ q in s..t, g q
  set I := ∫ r in s..t, conj (∫ q in s..r, g q) * g r
  have hre : 2 * I.re = (conj G * G).re := by
    have := congrArg Complex.re key
    simp only [Complex.add_re, Complex.conj_re] at this
    linarith
  rw [Complex.add_re, mul_add, hre]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.add_re, Complex.add_im]
  ring

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
