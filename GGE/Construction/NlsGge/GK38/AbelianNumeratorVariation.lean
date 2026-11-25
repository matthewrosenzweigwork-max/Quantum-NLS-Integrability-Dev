import NlsGge.GK38.AbelianJacobianNumerator
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The genuine entire directional variation in book Lemma14.7.
No kernel or injectivity hypothesis is used to prove its analytic realization. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

def p4NumeratorVariation38 (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) : ℂ :=
  fderiv ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) (z,s) (0,h)

namespace P4NumeratorVariation

theorem variation_entire (n : ℤ) (s h : Lib.L2Seq) :
    AnalyticOnNhd ℂ (p4NumeratorVariation38 n s h) univ := by
  let ev : ((ℂ × Lib.L2Seq) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  intro z _
  have hd := (p2FullNumerator_joint_analytic38 n (z,s) (mem_univ _)).fderiv
  have he : AnalyticAt ℂ
      (fun p : ℂ × Lib.L2Seq => ev
        (fderiv ℂ (fun q : ℂ × Lib.L2Seq => p2FullNumerator38 n q.2 q.1) p)) (z,s) :=
    (ev.analyticAt _).comp hd
  exact AnalyticAt.comp
    (g := fun p : ℂ × Lib.L2Seq => ev
      (fderiv ℂ (fun q : ℂ × Lib.L2Seq => p2FullNumerator38 n q.2 q.1) p))
    (f := fun w : ℂ => (w,s)) he (analyticAt_id.prod analyticAt_const)

theorem variation_hasDerivAt (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) :
    HasDerivAt (fun t : ℂ => p2FullNumerator38 n (s+t • h) z)
      (p4NumeratorVariation38 n s h z) 0 := by
  have hline : HasDerivAt (fun t : ℂ => (z,s+t • h)) (0,h) 0 := by
    simpa only [one_smul] using!
      (hasDerivAt_const 0 z).prodMk
        (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hf := (p2FullNumerator_joint_analytic38 n (z,s) (mem_univ _)).differentiableAt.hasFDerivAt
  have hf' : HasFDerivAt
      (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1)
      (fderiv ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) (z,s))
      (z,s+(0 : ℂ) • h) := by simpa only [zero_smul,add_zero] using hf
  exact hf'.comp_hasDerivAt 0 hline

theorem variation_unit_column (n r : ℤ) (hrn : r ≠ n)
    (s : Lib.L2Seq) (z : ℂ) :
    p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z =
      p3NumeratorColumn38 n r s z := by
  have affine : (fun t : ℂ =>
      p2FullNumerator38 n (s+t • lp.single 2 r (1 : ℂ)) z) =
      (fun t : ℂ => p2FullNumerator38 n s z+t*p3NumeratorColumn38 n r s z) :=
    funext (P3JacobianColumns.numerator_add_single n r hrn s z)
  have hd : HasDerivAt
      (fun t : ℂ => p2FullNumerator38 n s z+t*p3NumeratorColumn38 n r s z)
      (p3NumeratorColumn38 n r s z) 0 := by
    simpa only [one_mul] using!
      (((hasDerivAt_id (0 : ℂ)).mul_const (p3NumeratorColumn38 n r s z)).const_add
        (p2FullNumerator38 n s z))
  rw [← affine] at hd
  exact (variation_hasDerivAt n s _ z).unique hd

theorem variation_linear (n : ℤ) (s h k : Lib.L2Seq) (a b z : ℂ) :
    p4NumeratorVariation38 n s (a • h+b • k) z =
      a*p4NumeratorVariation38 n s h z+b*p4NumeratorVariation38 n s k z := by
  have hp : ((0,a • h+b • k) : ℂ × Lib.L2Seq) =
      a • (0,h)+b • (0,k) := by ext <;> simp
  unfold p4NumeratorVariation38
  rw [hp,map_add,map_smul,map_smul]
  rfl

end P4NumeratorVariation
end
end NlsGge.GK38
