import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import NlsGge.Spectral.ActualPhysicalUnitAnalyticSmallBranch33V5
set_option autoImplicit false
noncomputable section
open Set
namespace NlsGge.SpectralFoundations

/-- A continuous logarithm difference with exponential one throughout a complex
upper strip has ONE integer on the whole strip. This topology prerequisite
does not supply the actual NLS logarithm or its normalization. -/
theorem complexLogarithmUpperStrip_integer_constant35
    (a : ℝ) (g : ℂ → ℂ) (hg : ContinuousOn g ({z : ℂ | a < z.im}))
    (he : ∀ Y ∈ {z : ℂ | a < z.im}, Complex.exp (g Y)=1) :
    ∃ m : ℤ, ∀ Y ∈ {z : ℂ | a < z.im}, g Y=(m : ℂ)*(2*Real.pi*Complex.I) := by
  let p : ℂ → ℝ := fun Y => (g Y).im/(2*Real.pi)
  have hπ : (2 : ℝ)*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hperiod : ∀ Y ∈ {z : ℂ | a < z.im},
      ∃ n : ℤ, g Y=(n : ℂ)*(2*Real.pi*Complex.I) := by
    intro Y hY
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((he Y hY).trans Complex.exp_zero.symm)
    exact ⟨n, by simpa only [zero_add] using hn⟩
  have hscalar : ∀ (Y : ℂ) (n : ℤ), g Y=(n : ℂ)*(2*Real.pi*Complex.I) → p Y=(n : ℝ) := by
    intro Y n hn
    dsimp [p]
    rw [hn]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero]
    field_simp [hπ] <;> ring
  have hc : ContinuousOn p ({z : ℂ | a < z.im}) :=
    (Complex.continuous_im.comp_continuousOn hg).div_const (2*Real.pi)
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hm : MapsTo p ({z : ℂ | a < z.im}) (range ((↑) : ℤ → ℝ)) := by
    intro Y hY
    obtain ⟨n, hn⟩ := hperiod Y hY
    exact ⟨n, (hscalar Y n hn).symm⟩
  obtain ⟨v, ⟨m, rfl⟩, hconst⟩ := (convex_halfSpace_im_gt a).isPreconnected.eqOn_const_of_mapsTo hd hc hm
    (show (range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)
  refine ⟨m, ?_⟩
  intro Y hY
  obtain ⟨n, hn⟩ := hperiod Y hY
  have hnm : n=m := by
    have hmcast : (n : ℝ)=(m : ℝ) := by
      simpa only [Function.const_apply] using (hscalar Y n hn).symm.trans (hconst hY)
    exact_mod_cast hmcast
  simpa only [hnm] using hn

end NlsGge.SpectralFoundations
end
