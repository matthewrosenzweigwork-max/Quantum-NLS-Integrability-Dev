import QuantumNLS.TerraMultiRound30ActionOrigin
import QuantumNLS.DEF014Round5

/-! Unconditional second Fréchet derivatives of each actual scalar action.
This does not claim the sequence of scalar Hessians is an ℓ¹-valued Hessian. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound31CoordinateHessian
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.TerraMultiRound28PlaneSecond
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)
variable {L κ : ℝ} [Fact (0 < L)]

def actionCoordinate (hκ : 0 < κ) (n : ℤ) (u : L2T L) : ℝ := Actions hκ u n

theorem coordinate_analytic (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    AnalyticAt ℝ (actionCoordinate hκ n) u := by
  exact DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u

theorem coordinate_hessian_exists (hκ : 0 < κ) (n : ℤ) :
    HasFDerivAt (fderiv ℝ (actionCoordinate hκ n))
      (fderiv ℝ (fderiv ℝ (actionCoordinate hκ n)) (0 : L2T L)) 0 :=
  ((coordinate_analytic hκ n (0 : L2T L)).fderiv.differentiableAt).hasFDerivAt

theorem coordinate_hessian_diagonal (hκ : 0 < κ) (k n : ℤ) :
    fderiv ℝ (fderiv ℝ (actionCoordinate hκ n)) 0 (modeLp L k) (modeLp L k) =
      if n = k then 2 else 0 := by
  let v : L2T L := modeLp L k
  have hline (s : ℝ) : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (hasDerivAt_id s).smul_const v
  have hd (s : ℝ) : deriv (planeAction (L := L) hκ k n) s =
      fderiv ℝ (actionCoordinate hκ n) (s • v) v := by
    have hh := ((coordinate_analytic hκ n (s • v)).differentiableAt.hasFDerivAt).comp_hasDerivAt s (hline s)
    have heq : (fun t : ℝ => actionCoordinate hκ n (t • v)) = planeAction (L := L) hκ k n := by
      funext t
      simp [actionCoordinate, Actions, planeAction, v, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change HasDerivAt (fun t : ℝ => actionCoordinate hκ n (t • v)) _ s at hh
    rw [heq] at hh
    exact hh.deriv
  have hf : deriv (planeAction (L := L) hκ k n) =
      fun s : ℝ => fderiv ℝ (actionCoordinate hκ n) (s • v) v := by
    funext s
    exact hd s
  have hh := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp 0
    (coordinate_hessian_exists hκ n)
  have hc := hh.comp_hasDerivAt_of_eq 0 (hline 0) (by simp)
  have hc' : HasDerivAt (deriv (planeAction (L := L) hκ k n))
      (fderiv ℝ (fderiv ℝ (actionCoordinate hκ n)) 0 v v) 0 := by
    rw [hf]
    simpa [Function.comp_def] using hc
  exact hc'.unique (planeAction_second (L := L) hκ k n 0)

end QuantumNLS.TerraMultiRound31CoordinateHessian
#print axioms QuantumNLS.TerraMultiRound31CoordinateHessian.coordinate_analytic
#print axioms QuantumNLS.TerraMultiRound31CoordinateHessian.coordinate_hessian_exists
#print axioms QuantumNLS.TerraMultiRound31CoordinateHessian.coordinate_hessian_diagonal
