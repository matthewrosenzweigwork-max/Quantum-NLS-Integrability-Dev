import NlsGge.GK38.AbelianComplexRealAffineIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-! SOURCE ONLY: actual derivative and oriented integral of an affine complex
line. Both interval CIs precede the identity. No derivative/contour oracle.
Exact target and English preceded proof. UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Complex_affine_line_pullback38 (f : ℂ → ℂ) (w v : ℂ) (a b : ℝ)
    (hf : ContinuousOn (fun x : ℝ => f (w+(x : ℂ)*v)) (Set.uIcc (b-a) (b+a))) :
    IntervalIntegrable (fun y : ℝ => f (w+((a*y+b : ℝ) : ℂ)*v)*
      deriv (fun t : ℝ => w+((a*t+b : ℝ) : ℂ)*v) y) volume (-1) 1 ∧
    IntervalIntegrable (fun x : ℝ => f (w+(x : ℂ)*v)) volume (b-a) (b+a) ∧
    (∫ y : ℝ in (-1 : ℝ)..1, f (w+((a*y+b : ℝ) : ℂ)*v)*
      deriv (fun t : ℝ => w+((a*t+b : ℝ) : ℂ)*v) y) =
      v*(∫ x : ℝ in (b-a)..(b+a), f (w+(x : ℂ)*v)) := by
  have hbase := p6Complex_real_affine_integral38 (fun x : ℝ => f (w+(x : ℂ)*v)) a b hf
  have hderiv (y : ℝ) : deriv (fun t : ℝ => w+((a*t+b : ℝ) : ℂ)*v) y =
      (a : ℂ)*v := by
    have hσ : HasDerivAt (fun t : ℝ => a*t+b) a y := by
      simpa using ((hasDerivAt_id y).const_mul a).add_const b
    exact ((hσ.ofReal_comp.mul_const v).const_add w).deriv
  have heq :
      (fun y : ℝ => f (w+((a*y+b : ℝ) : ℂ)*v)*
        deriv (fun t : ℝ => w+((a*t+b : ℝ) : ℂ)*v) y) =
      (fun y : ℝ => v*(f (w+((a*y+b : ℝ) : ℂ)*v)*(a : ℂ))) := by
    funext y
    rw [hderiv]
    ring
  refine ⟨?_,hbase.2.1,?_⟩
  · rw [heq]
    exact hbase.1.const_mul v
  · rw [heq,intervalIntegral.integral_const_mul,hbase.2.2]

end
end NlsGge.GK38
