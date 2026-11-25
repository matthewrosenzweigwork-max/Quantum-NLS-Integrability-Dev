import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

open scoped ENNReal

namespace NlsGge.Measure

/-- A finite product of real exponential likelihoods is one exponential of
the sum, expressed directly in `ENNReal`. -/
theorem ennreal_ofReal_exp_prod_eq_exp_sum
    {n : ℕ} (F : Fin n → ℝ) :
    (∏ i : Fin n, ENNReal.ofReal (Real.exp (F i))) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, F i)) := by
  calc
    (∏ i : Fin n, ENNReal.ofReal (Real.exp (F i))) =
        ENNReal.ofReal (∏ i : Fin n, Real.exp (F i)) := by
      symm
      exact ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => Real.exp (F i))
        (by intro i hi; positivity)
    _ = ENNReal.ofReal (Real.exp (∑ i : Fin n, F i)) := by
      rw [Real.exp_sum]

end NlsGge.Measure
