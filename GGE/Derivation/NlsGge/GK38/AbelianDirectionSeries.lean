import NlsGge.GK38.AbelianVariationCircleBound

/-! The actual infinite directional expansion. This is density in the direction
carrier, with its genuine continuous derivative; no finite-gap potential density
or unearned logarithmic derivative identity is used. -/
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

def variationCLM (n : ℤ) (s : Lib.L2Seq) (z : ℂ) : Lib.L2Seq →L[ℂ] ℂ :=
  (fderiv ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) (z,s)).comp
    (ContinuousLinearMap.inr ℂ ℂ Lib.L2Seq)

theorem variationCLM_apply (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) :
    variationCLM n s z h = p4NumeratorVariation38 n s h z := rfl

theorem variation_omitted_unit (n : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    p4NumeratorVariation38 n s (lp.single 2 n (1 : ℂ)) z=0 := by
  have he : (fun t : ℂ => p2FullNumerator38 n
      (s+t • lp.single 2 n (1 : ℂ)) z) = fun _ => p2FullNumerator38 n s z := by
    funext t
    exact congrArg (fun q : ℂ => (-2 : ℂ)*q) (Lib.omitProd_add_single n s z t)
  have hd := variation_hasDerivAt n s (lp.single 2 n (1 : ℂ)) z
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

theorem variation_hasSum (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) :
    HasSum (fun r : ℤ => p4NumeratorVariation38 n s (lp.single 2 r (h r)) z)
      (p4NumeratorVariation38 n s h z) := by
  have hs := (lp.hasSum_single (E := fun _ : ℤ => ℂ)
    (p := (2 : ℝ≥0∞)) (by simp) h).mapL (variationCLM n s z)
  exact hs

theorem variation_section_tendsto (n : ℤ) (s h : Lib.L2Seq) (z : ℂ) :
    Tendsto (fun S : Finset ℤ => p4NumeratorVariation38 n s
      (∑ r ∈ S, lp.single 2 r (h r)) z) atTop
      (𝓝 (p4NumeratorVariation38 n s h z)) := by
  exact (variationCLM n s z).continuous.tendsto h |>.comp
    (lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)) (by simp) h)

end
end NlsGge.GK38.P4NumeratorVariation
