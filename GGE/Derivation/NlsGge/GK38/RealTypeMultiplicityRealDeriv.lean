import NlsGge.GK38.RealTypeSpectrum
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! # S6: real restriction and actual complex derivative

GK I.6/I.7. Vanishing of the imaginary restriction identifies the full derivative.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem realRestriction_deriv38 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ, (f (x : ℂ)).im = 0) (x : ℝ) :
    HasDerivAt (fun r : ℝ => (f (r : ℂ)).re) (deriv f (x : ℂ)).re x ∧
    (deriv f (x : ℂ)).im = 0 ∧
    (deriv (fun r : ℝ => (f (r : ℂ)).re) x = 0 ↔ deriv f (x : ℂ) = 0) := by
  have hd := (hf (x : ℂ)).hasDerivAt
  have hre := hd.real_of_complex
  have hi : HasDerivAt (fun r : ℝ => (f (r : ℂ)).im) (deriv f (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd.comp_ofReal
  have he : (fun r : ℝ => (f (r : ℂ)).im) = fun _ => (0 : ℝ) := funext hr
  rw [he] at hi
  have him : (deriv f (x : ℂ)).im = 0 := by simpa using hi.deriv.symm
  refine ⟨hre, him, ?_⟩
  rw [hre.deriv]
  constructor
  · intro h; exact Complex.ext (by simpa using h) (by simpa using him)
  · intro h; simp [h]

theorem rolle_complex_real38 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ, (f (x : ℂ)).im = 0) (a b : ℝ) (hab : a < b)
    (he : f (a : ℂ) = f (b : ℂ)) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ deriv f (x : ℂ) = 0 := by
  have hd := fun x => (realRestriction_deriv38 f hf hr x).1
  have hc : Continuous (fun x : ℝ => (f (x : ℂ)).re) :=
    (show Differentiable ℝ (fun x : ℝ => (f (x : ℂ)).re) from
      fun x => (hd x).differentiableAt).continuous
  obtain ⟨x, hx, hz⟩ := exists_hasDerivAt_eq_zero hab hc.continuousOn
    (congrArg Complex.re he) (fun x _ => hd x)
  refine ⟨x, hx, ?_⟩
  apply Complex.ext
  · simpa using hz
  · simpa using (realRestriction_deriv38 f hf hr x).2.1

theorem discrim_real_restriction38 (u : PhysicalL2) (x : ℝ) :
    (discrim (realSlice u) (x : ℂ)).im = 0 := by
  rw [discrim_realSlice]
  simp [Complex.mul_im, actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u x]

theorem discrim_realRestriction_deriv38 (u : PhysicalL2) (x : ℝ) :
    (discrim (realSlice u) (x : ℂ)).im = 0 ∧
    HasDerivAt (fun r : ℝ => (discrim (realSlice u) (r : ℂ)).re)
      (deriv (discrim (realSlice u)) (x : ℂ)).re x ∧
    (deriv (discrim (realSlice u)) (x : ℂ)).im = 0 := by
  have hf : Differentiable ℂ (discrim (realSlice u)) := fun z =>
    (analyticOnNhd_discrim_z (realSlice u) z (mem_univ z)).differentiableAt
  exact ⟨discrim_real_restriction38 u x,
    (realRestriction_deriv38 _ hf (discrim_real_restriction38 u) x).1,
    (realRestriction_deriv38 _ hf (discrim_real_restriction38 u) x).2.1⟩

theorem gap_discrim_endpoint_values38 (u : PhysicalL2) (n : ℤ) :
    discrim (realSlice u) (actualGapLowerAllE02_38 u n : ℂ) =
      2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) ∧
    discrim (realSlice u) (actualGapUpperAllE02_38 u n : ℂ) =
      2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  simpa only [discrim_realSlice] using
    And.intro (congrArg (fun z : ℂ => 2 * z) (actualGapEndpoint_halfTrace_all_E02_38 u n).1)
      (congrArg (fun z : ℂ => 2 * z) (actualGapEndpoint_halfTrace_all_E02_38 u n).2)

end
end NlsGge.GK38
