import NlsGge.GK38.AbelianComplexAffineSubstitution
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! SOURCE ONLY: oriented real-coordinate substitutions with complex values.
The scale may be positive, negative or zero. BOTH genuine interval CIs precede
the integral identity. Actual square edges later realize the continuity
premise from the annular slab; the filled square need not be cut-free.
Exact target and English were recorded before proof. UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Complex_real_affine_integral38 (G : ℝ → ℂ) (a b : ℝ)
    (hG : ContinuousOn G (Set.uIcc (b-a) (b+a))) :
    IntervalIntegrable (fun y : ℝ => G (a*y+b)*(a : ℂ)) volume (-1) 1 ∧
    IntervalIntegrable G volume (b-a) (b+a) ∧
    (∫ y : ℝ in (-1 : ℝ)..1, G (a*y+b)*(a : ℂ)) =
      ∫ x : ℝ in (b-a)..(b+a), G x := by
  have hmap : MapsTo (fun y : ℝ => a*y+b) (Set.Icc (-1 : ℝ) 1)
      (Set.uIcc (b-a) (b+a)) := by
    intro y hy
    rcases le_total 0 a with ha | ha
    · rw [Set.uIcc_of_le (by linarith : b-a ≤ b+a)]
      have hl := mul_le_mul_of_nonneg_left hy.1 ha
      have hu := mul_le_mul_of_nonneg_left hy.2 ha
      constructor <;> nlinarith
    · rw [Set.uIcc_of_ge (by linarith : b+a ≤ b-a)]
      have hl := mul_le_mul_of_nonpos_left hy.1 ha
      have hu := mul_le_mul_of_nonpos_left hy.2 ha
      constructor <;> nlinarith
  have hparam : ContinuousOn (fun y : ℝ => G (a*y+b)) (Set.Icc (-1 : ℝ) 1) :=
    hG.comp (show ContinuousOn (fun y : ℝ => a*y+b) (Set.Icc (-1 : ℝ) 1)
      from by fun_prop) hmap
  have hCIy : IntervalIntegrable (fun y : ℝ => G (a*y+b)*(a : ℂ)) volume (-1) 1 :=
    (hparam.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
  have hCIx : IntervalIntegrable G volume (b-a) (b+a) := hG.intervalIntegrable
  refine ⟨hCIy,hCIx,?_⟩
  calc
    _ = (a : ℝ) • ∫ y : ℝ in (-1 : ℝ)..1, G (a*y+b) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro y hy
      simp only [Complex.real_smul,mul_comm]
    _ = _ := by
      simpa only [mul_neg_one,mul_one,neg_add_eq_sub,add_comm b a] using
        intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1) G a b

end
end NlsGge.GK38
