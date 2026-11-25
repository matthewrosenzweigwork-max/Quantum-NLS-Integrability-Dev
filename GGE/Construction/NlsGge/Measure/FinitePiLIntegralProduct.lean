import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

/-- The nonnegative integral of a finite product of coordinate functions
factors into the product of the coordinate integrals. The homogeneous factor
space keeps the measurable-space dictionary stable across `piFinSuccAbove`. -/
theorem lintegral_fin_nat_prod_eq_prod
    {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → α, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprod : Measurable (fun x : Fin (n + 1) → α => ∏ i, f i (x i)) := by
        apply Finset.univ.measurable_prod
        intro i hi
        exact (hf i).comp (measurable_pi_apply i)
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp hprod]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      have hrest : Measurable
          (fun x : Fin n → α => ∏ i : Fin n, f i.succ (x i)) := by
        apply Finset.univ.measurable_prod
        intro i hi
        exact (hf i.succ).comp (measurable_pi_apply i)
      rw [lintegral_prod_mul (hf 0).aemeasurable hrest.aemeasurable]
      rw [ih (μ := fun i => μ i.succ) (f := fun i => f i.succ)
        (hf := fun i => hf i.succ)]

end NlsGge.Measure
