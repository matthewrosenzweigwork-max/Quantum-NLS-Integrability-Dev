import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Sqrt

/-! Uncompiled Scheffé bridge. The only DCT majorant is the FIXED limit row.
No common envelope for the varying rows is assumed or deduced from mass bounds. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p5Abs_sub_eq_add_sub_min38 (a b : ℝ) :
    |a-b| = a+b-2*min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem p5Nonnegative_series_strong_tendsto38 {α ι : Type*} (l : Filter α)
    (f : α → ι → ℝ) (g : ι → ℝ)
    (hf0 : ∀ x i, 0 ≤ f x i) (hg0 : ∀ i, 0 ≤ g i)
    (hfs : ∀ x, Summable (f x)) (hgs : Summable g)
    (hpoint : ∀ i, Tendsto (fun x => f x i) l (𝓝 (g i)))
    (hmass : Tendsto (fun x => ∑' i, f x i) l (𝓝 (∑' i, g i))) :
    Tendsto (fun x => ∑' i, |f x i-g i|) l (𝓝 (0 : ℝ)) := by
  have hms (x : α) : Summable (fun i => min (f x i) (g i)) :=
    hgs.of_nonneg_of_le (fun i => le_min (hf0 x i) (hg0 i)) (fun i => min_le_right _ _)
  have hmin : Tendsto (fun x => ∑' i, min (f x i) (g i)) l (𝓝 (∑' i, g i)) := by
    have hp (i : ι) : Tendsto (fun x => min (f x i) (g i)) l (𝓝 (g i)) := by
      have hc : Tendsto (fun _ : α => g i) l (𝓝 (g i)) := tendsto_const_nhds
      simpa only [min_self] using (hpoint i).min hc
    have hm := tendsto_tsum_of_dominated_convergence (f := fun x i => min (f x i) (g i))
      (g := g) hgs hp
      (Eventually.of_forall (fun x i => by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hf0 x i) (hg0 i))]
        exact min_le_right _ _))
    exact hm
  have he (x : α) : (∑' i, |f x i-g i|) =
      (∑' i, f x i)+(∑' i, g i)-2*(∑' i, min (f x i) (g i)) := by
    simp_rw [p5Abs_sub_eq_add_sub_min38]
    rw [((hfs x).add hgs).tsum_sub ((hms x).mul_left 2),
      (hfs x).tsum_add hgs,tsum_mul_left]
  have hc : Tendsto (fun _ : α => ∑' i, g i) l (𝓝 (∑' i, g i)) := tendsto_const_nhds
  have ht := (hmass.add hc).sub (hmin.const_mul 2)
  have hz : (∑' i, g i)+(∑' i, g i)-2*(∑' i, g i) = 0 := by ring
  simpa only [← he,hz] using ht

theorem p5Sqrt_sub_sq_le_abs_sub38 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a-Real.sqrt b)^2 ≤ |a-b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hpa := Real.sqrt_nonneg a
  have hpb := Real.sqrt_nonneg b
  rcases le_total a b with hab | hab
  · have hs := Real.sqrt_le_sqrt hab
    have hp := mul_nonneg hpa (sub_nonneg.mpr hs)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hs := Real.sqrt_le_sqrt hab
    have hp := mul_nonneg hpb (sub_nonneg.mpr hs)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    nlinarith

end
end NlsGge.GK38
