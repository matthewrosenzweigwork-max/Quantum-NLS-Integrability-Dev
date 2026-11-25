import QuantumNLS.TerraMultiRound31CoordinateHessian

/-! Finite coordinate truncations of the actual action sequence are analytic.
The convergence needed to pass to the full ℓ¹-valued Hessian is not asserted. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound31FiniteActions
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.TerraMultiRound31CoordinateHessian
variable {L κ : ℝ} [Fact (0 < L)]

def finiteActions (hκ : 0 < κ) (S : Finset ℤ) (u : L2T L) : lp (fun _ : ℤ => ℝ) 1 :=
  ∑ n ∈ S, lp.single 1 n (actionCoordinate hκ n u)

theorem finiteActions_analytic (hκ : 0 < κ) (S : Finset ℤ) (u : L2T L) :
    AnalyticAt ℝ (finiteActions hκ S) u := by
  unfold finiteActions
  apply Finset.analyticAt_fun_sum
  intro n hn
  exact (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 1 n).analyticAt _ |>.comp
    (coordinate_analytic hκ n u)

theorem finiteActions_hessian_exists (hκ : 0 < κ) (S : Finset ℤ) (u : L2T L) :
    HasFDerivAt (fderiv ℝ (finiteActions hκ S))
      (fderiv ℝ (fderiv ℝ (finiteActions hκ S)) u) u :=
  ((finiteActions_analytic hκ S u).fderiv.differentiableAt).hasFDerivAt

end QuantumNLS.TerraMultiRound31FiniteActions
#print axioms QuantumNLS.TerraMultiRound31FiniteActions.finiteActions_analytic
#print axioms QuantumNLS.TerraMultiRound31FiniteActions.finiteActions_hessian_exists
