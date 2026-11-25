import NlsGge.Birkhoff.W11Equivalence38

/-! # W11 (`D:thm:equivalence`), part b: normalizers, `L¹` convergence, uniform integrability (B-free)

Source: `paper/v2.tex` l.1682-1683: "Convergence of the integrals is equivalent to `L¹` convergence: apply the
elementary identity involving `min(f_N, f_W)` and dominated convergence along almost-surely convergent
subsequences, then use the subsequence criterion. Together with probability convergence, this is also
equivalent to uniform integrability."

Abstract setting: a probability space `(α, μ)`, nonnegative integrable `f_n`, `f ≥ 0` a.e. integrable,
`f_n → f` in measure.
* `tendsto_iff_l1_W11` (W11.01): `∫ f_n → ∫ f ↔ ∫ |f_n - f| → 0`.
* `l1_iff_uniformIntegrable_W11`: `∫ |f_n - f| → 0 ↔ UniformIntegrable f_n 1 μ` (Vitali).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory Filter Topology
open scoped ENNReal

section Abstract

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
  (fn : ℕ → α → ℝ) (f : α → ℝ)

theorem abs_sub_eq_W11 (a b : ℝ) : |a - b| = a + b - 2 * (a ⊓ b) := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), inf_of_le_left h]; ring
  · rw [abs_of_nonneg (by linarith), inf_of_le_right h]; ring

theorem tendsto_integral_inf_W11 (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hconv : TendstoInMeasure μ fn atTop f) :
    Tendsto (fun n => ∫ x, fn n x ⊓ f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, hms, hae⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_integral_of_dominated_convergence f
    (fun k => ((hfn _).inf hf).aestronglyMeasurable) hf (fun k => ?_) ?_
  · filter_upwards [hf0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_inf (hfn0 _ _) hx)]
    exact inf_le_right
  · filter_upwards [hae] with x hx
    have hx' : Tendsto (fun k => fn (ns (ms k)) x) atTop (𝓝 (f x)) := hx
    have := hx'.min (tendsto_const_nhds (x := f x))
    simpa using this

/-- **W11.01.** `∫ f_n → ∫ f` iff `∫ |f_n - f| → 0`. -/
theorem tendsto_iff_l1_W11 (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hconv : TendstoInMeasure μ fn atTop f) :
    Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) ↔
      Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0) := by
  constructor
  · intro h
    have hmin := tendsto_integral_inf_W11 μ fn f hfn hf hfn0 hf0 hconv
    have e : ∀ n, ∫ x, |fn n x - f x| ∂μ =
        ∫ x, fn n x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, fn n x ⊓ f x ∂μ := by
      intro n
      have hi := (hfn n).inf hf
      have e1 : (fun x => |fn n x - f x|) = fun x => (fn n x + f x) - 2 * (fn n x ⊓ f x) :=
        funext fun x => abs_sub_eq_W11 _ _
      have hi2 : Integrable (fun x => 2 * (fn n x ⊓ f x)) μ := hi.const_mul 2
      have hi1 : Integrable (fun x => fn n x + f x) μ := (hfn n).add hf
      rw [e1, integral_sub hi1 hi2, integral_add (hfn n) hf, integral_const_mul]
    simp_rw [e]
    have := (h.add_const (∫ x, f x ∂μ)).sub (hmin.const_mul 2)
    convert this using 2
    ring
  · intro h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
    rw [Real.norm_eq_abs, ← integral_sub (hfn n) hf]
    exact abs_integral_le_integral_abs

theorem integral_abs_eq_eLpNorm_W11 (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ) (n : ℕ) :
    eLpNorm (fn n - f) 1 μ = ENNReal.ofReal (∫ x, |fn n x - f x| ∂μ) := by
  have hi : Integrable (fn n - f) μ := (hfn n).sub hf
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  have : (fun a => ‖(fn n - f) a‖) = fun x => |fn n x - f x| :=
    funext fun x => by simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [this]
  exact hi.aestronglyMeasurable

theorem tendsto_l1_iff_eLpNorm_W11 (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0) ↔
      Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0) := by
  simp_rw [integral_abs_eq_eLpNorm_W11 μ fn f hfn hf]
  constructor
  · intro h
    simpa using ENNReal.tendsto_ofReal h
  · intro h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp, ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _)]

/-- Vitali: given convergence in measure, `L¹` convergence is equivalent to uniform integrability
(`UnifIntegrable` and bounded `L¹` norm; for nonnegative `f_n` this is classical uniform integrability). -/
theorem l1_iff_uniformIntegrable_W11 (hfn : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hfn0 : ∀ n x, 0 ≤ fn n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hconv : TendstoInMeasure μ fn atTop f) :
    Tendsto (fun n => ∫ x, |fn n x - f x| ∂μ) atTop (𝓝 0) ↔ UniformIntegrable fn 1 μ := by
  have hm : ∀ n, MemLp (fn n) 1 μ := fun n => memLp_one_iff_integrable.2 (hfn n)
  have hmf : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  have hV := tendstoInMeasure_iff_tendsto_Lp_finite (μ := μ) (f := fn) (g := f) le_rfl
    ENNReal.one_ne_top hm hmf
  rw [tendsto_l1_iff_eLpNorm_W11 μ fn f hfn hf]
  constructor
  · intro h
    have hui := (hV.2 h).2
    refine ⟨hui, ?_⟩
    have hZ : Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
      exact (tendsto_iff_l1_W11 μ fn f hfn hf hfn0 hf0 hconv).2
        ((tendsto_l1_iff_eLpNorm_W11 μ fn f hfn hf).2 h)
    obtain ⟨B, hB⟩ := hZ.bddAbove_range
    refine ⟨B.toNNReal, fun n => ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hfn n)]
    have : ∫ x, ‖fn n x‖ ∂μ = ∫ x, fn n x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by
        show ‖fn n x‖ = fn n x
        rw [Real.norm_eq_abs, abs_of_nonneg (hfn0 n x)])
    rw [this]
    exact ENNReal.ofReal_le_ofReal (hB ⟨n, rfl⟩)
    exact (hfn n).aestronglyMeasurable
  · intro hu
    exact (hV.1 ⟨hconv, hu.1⟩)

end Abstract

end NlsGge.Birkhoff
end
