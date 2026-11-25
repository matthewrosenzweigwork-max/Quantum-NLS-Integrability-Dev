import NlsGge.Birkhoff.F09Limit38b

/-! # NEW-F09, file 3: the `L¹` criterion (v2 l.1788-1793)

`B`-free. If `f_n ≥ 0` are integrable, `f_n → f` in measure, `f ≥ 0` is integrable and `∫ f_n → ∫ f`, then
`∫ |f_n - f| → 0`.  Proof as in v2: along every subsequence choose a further subsequence converging a.e.;
`min(f_n, f) → f` is dominated by `f`; and
`∫|f_n - f| = ∫ f_n + ∫ f - 2 ∫ min(f_n, f)`; then the subsequence criterion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory Filter Topology
open scoped ENNReal

theorem tendsto_integral_abs_sub_of_inMeasure38 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (fN : ℕ → α → ℝ) (f : α → ℝ) (hN : ∀ n, Integrable (fN n) μ) (hf : Integrable f μ)
    (hN0 : ∀ n x, 0 ≤ fN n x) (hf0 : ∀ x, 0 ≤ f x)
    (hmeas : TendstoInMeasure μ fN atTop f)
    (hint : Tendsto (fun n => ∫ x, fN n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))) :
    Tendsto (fun n => ∫ x, |fN n x - f x| ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hm' : TendstoInMeasure μ (fun k => fN (ns k)) atTop f := fun ε hε => (hmeas ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := hm'.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  set g : ℕ → α → ℝ := fun k => fN (ns (ms k)) with hg
  have hgi : ∀ k, Integrable (g k) μ := fun k => hN _
  have hmini : ∀ k, Integrable (fun x => min (g k x) (f x)) μ := fun k => (hgi k).inf hf
  have hid : ∀ k, ∫ x, |g k x - f x| ∂μ =
      ∫ x, g k x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, min (g k x) (f x) ∂μ := by
    intro k
    have : (fun x => |g k x - f x|) = fun x => g k x + f x - 2 * min (g k x) (f x) := by
      funext x
      rcases le_total (g k x) (f x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    rw [this, integral_sub (f := fun x => g k x + f x) (g := fun x => 2 * min (g k x) (f x))
      ((hgi k).add hf) ((hmini k).const_mul 2), integral_add (hgi k) hf, integral_const_mul]
  have hmin : Tendsto (fun k => ∫ x, min (g k x) (f x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence f
      (fun k => (hmini k).aestronglyMeasurable) hf (fun k => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hN0 _ x) (hf0 x))]
      exact min_le_right _ _
    · filter_upwards [hae] with x hx
      have := hx.min (tendsto_const_nhds (x := f x))
      simpa using this
  have hgint : Tendsto (fun k => ∫ x, g k x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    hint.comp ((hns.comp hms.tendsto_atTop))
  have := (hgint.add_const (∫ x, f x ∂μ)).sub (hmin.const_mul 2)
  simp only [hg] at hid ⊢
  rw [show (0 : ℝ) = ∫ x, f x ∂μ + ∫ x, f x ∂μ - 2 * ∫ x, f x ∂μ by ring]
  exact this.congr fun k => (hid k).symm

end NlsGge.Birkhoff
end
