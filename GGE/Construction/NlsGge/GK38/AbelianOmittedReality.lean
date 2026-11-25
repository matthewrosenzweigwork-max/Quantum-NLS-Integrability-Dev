import NlsGge.GK38.XiSqLocal
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Normed.Module.Convex

/-! Actual real omitted-root factors, keeping the full complex branch construction.
UNCOMPILED prospective source. No canonical-root real value is assumed on its own cut. -/
set_option autoImplicit false
open Set Metric SummationFilter ComplexOrder
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

/-- A convex source domain containing the original sphere contains its filled disc. -/
theorem p2ClosedBall_subset_of_sphere38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    {U : Set ℂ} (hU : Convex ℝ U) (hs : sphere c r ⊆ U) :
    closedBall c r ⊆ U := by
  rw [← convexHull_sphere_eq_closedBall c hr]
  exact convexHull_min hs hU

/-- Standard roots are real off a real cut, with the actual principal branch. -/
theorem p2StdRoot_real38 (a b x : ℝ)
    (hx : (x:ℂ) ∉ segment ℝ (a:ℂ) (b:ℂ)) :
    (stdRoot38 (((a:ℂ)+b)/2) (((b:ℂ)-a)^2) x).im=0 := by
  let ρ : ℝ := 1-(((b-a)^2)/4)/(((a+b)/2-x)^2)
  have hr : (ρ:ℂ) ∈ Complex.slitPlane := by
    convert (stdRoot_slit38 (a:ℂ) (b:ℂ) (x:ℂ) hx).2 using 1
    dsimp [ρ]
    push_cast
    ring
  have hρ : 0 < ρ := Complex.ofReal_mem_slitPlane.mp hr
  have he : stdRoot38 (((a:ℂ)+b)/2) (((b:ℂ)-a)^2) x =
      (((a+b)/2-x:ℝ):ℂ)*Complex.sqrt (ρ:ℂ) := by
    dsimp [stdRoot38,ρ]
    push_cast
    rfl
  rw [he,Complex.sqrt_of_nonneg (show (0:ℂ) ≤ (ρ:ℂ) by exact_mod_cast hρ.le)]
  simp only [Complex.mul_im,Complex.ofReal_im,mul_zero,zero_mul,add_zero]

/-- Reality of every actual off-cut normalized factor, including the signed index zero. -/
theorem p2RootFactor_real38 (u : PhysicalL2) (m : ℤ) (x : ℝ)
    (hx : (x:ℂ) ∉ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    (rootFactor38 m (realSlice u,(x:ℂ))).im=0 := by
  have he := lamPlus_real u m
  rw [he.1,he.2] at hx
  have hr := p2StdRoot_real38 (actualGapLowerAllE02_38 u m)
    (actualGapUpperAllE02_38 u m) x hx
  unfold rootFactor38
  rw [(tauGamma_real38 u m).1,(tauGamma_real38 u m).2]
  have hcast :
      ((((actualGapLowerAllE02_38 u m+actualGapUpperAllE02_38 u m)/2:ℝ):ℂ)) =
        (((actualGapLowerAllE02_38 u m:ℂ)+(actualGapUpperAllE02_38 u m:ℂ))/2) := by
    push_cast
    rfl
  rw [hcast]
  push_cast
  simp only [Complex.div_im,Complex.ofReal_im,mul_zero,sub_zero,
    hr,zero_mul,zero_div]

/-- Genuine symmetric multipliability is used BEFORE mapping conjugation through the product. -/
theorem p2OmittedRoot_real38 (n : ℤ) (u : PhysicalL2) (x : ℝ)
    (hp : (realSlice u,(x:ℂ)) ∈ a5OmittedRootDomain38 n) :
    (a5OmittedRootProduct38 n (realSlice u,(x:ℂ))).im=0 := by
  have hfac : ∀ m : ℤ, (a5OmittedRootFactor38 n m (realSlice u,(x:ℂ))).im=0 := by
    intro m
    by_cases hm : m=n
    · simp only [a5OmittedRootFactor38,hm,ite_true,Complex.one_im]
    · simpa only [a5OmittedRootFactor38,hm,ite_false] using
        p2RootFactor_real38 u m x (hp.2 m hm)
  have hmul := a5OmittedRoot_multipliable38 n (realSlice u,(x:ℂ)) hp
  have hconj := hmul.map_tprod (starRingEnd ℂ) continuous_star
  have he : (fun m : ℤ => (starRingEnd ℂ) (a5OmittedRootFactor38 n m (realSlice u,(x:ℂ)))) =
      (fun m : ℤ => a5OmittedRootFactor38 n m (realSlice u,(x:ℂ))) := by
    funext m
    exact Complex.conj_eq_iff_im.mpr (hfac m)
  rw [he] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

#print axioms p2ClosedBall_subset_of_sphere38
#print axioms p2StdRoot_real38
#print axioms p2RootFactor_real38
#print axioms p2OmittedRoot_real38
end
end NlsGge.GK38
