import NlsGge.Spectral.ActualPhysicalUnitFloquetMultiplierReal33V4
import NlsGge.Spectral.ActualPhysicalUnitCharacteristicEquation33V1
import NlsGge.Spectral.ActualPhysicalUnitAnalyticUnnormalizedCosine32V4
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- Actual nonreal monodromy square-root multipliers avoid the unit circle. -/
theorem actualPhysicalUnit_squareRoot_norm_ne_one33
    (u : PhysicalL2) (z s : ℂ) (hz : z.im ≠ 0)
    (hs : s^2 = actualPhysicalUnitHalfTrace32 u z ^2 - 1) :
    ‖actualPhysicalUnitHalfTrace32 u z+s‖ ≠ 1 := by
  intro hnorm
  obtain ⟨v, hv, heigen⟩ := actualPhysicalUnit_squareRoot_gives_eigenmultiplier33 u z s hs
  exact hz (actualPhysicalUnitFloquetMultiplier_im_eq_zero33 u z
    (actualPhysicalUnitHalfTrace32 u z+s) v hv hnorm heigen)

/-- The genuine rough source trace admits an analytic small Floquet root
and logarithm throughout the upper half-plane. Logarithm integer and source
high-energy normalization are deliberately not asserted here. -/
theorem exists_actualPhysicalUnitAnalyticSmallBranch33 (u : PhysicalL2) :
    ∃ s ℓ : ℂ → ℂ,
      AnalyticOnNhd ℂ s {z : ℂ | 0 < z.im} ∧
      AnalyticOnNhd ℂ ℓ {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → s z^2 = actualPhysicalUnitHalfTrace32 u z^2-1) ∧
      (∀ z : ℂ, 0 < z.im → Complex.exp (ℓ z)=actualPhysicalUnitHalfTrace32 u z+s z) ∧
      (∀ z : ℂ, 0 < z.im → ‖actualPhysicalUnitHalfTrace32 u z+s z‖ < 1) := by
  obtain ⟨s, ℓ, hs, hl, hsq, he⟩ := exists_actualPhysicalUnitAnalyticUnnormalizedBranch32 u
  have hd := (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).mono
    (show {z : ℂ | 0 < z.im} ⊆ Set.univ from Set.subset_univ _)
  have hnorm := (hd.add hs).continuousOn.norm
  have hne : ∀ z ∈ {z : ℂ | 0 < z.im}, ‖actualPhysicalUnitHalfTrace32 u z+s z‖ ≠ 1 := by
    intro z hz
    exact actualPhysicalUnit_squareRoot_norm_ne_one33 u z (s z) (ne_of_gt hz) (hsq z hz)
  rcases (convex_halfSpace_im_gt 0).isPreconnected.mapsTo_Ioi_or_Iio hnorm hne with hlarge | hsmall
  · refine ⟨fun z => -s z, fun z => -ℓ z, hs.neg, hl.neg, ?_, ?_, ?_⟩
    · intro z hz
      simpa only [neg_sq] using hsq z hz
    · intro z hz
      have hp : (actualPhysicalUnitHalfTrace32 u z+s z)*
          (actualPhysicalUnitHalfTrace32 u z-s z)=1 := by
        linear_combination -hsq z hz
      apply mul_left_cancel₀ (Complex.exp_ne_zero (ℓ z))
      calc
        Complex.exp (ℓ z)*Complex.exp (-ℓ z)=1 := by
          rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
        _ = Complex.exp (ℓ z)*(actualPhysicalUnitHalfTrace32 u z+-s z) := by
          rw [he z hz]
          simpa only [sub_eq_add_neg] using hp.symm
    · intro z hz
      have hp : (actualPhysicalUnitHalfTrace32 u z+s z)*
          (actualPhysicalUnitHalfTrace32 u z-s z)=1 := by
        linear_combination -hsq z hz
      have he' : Complex.exp (-ℓ z)=actualPhysicalUnitHalfTrace32 u z-s z := by
        apply mul_left_cancel₀ (Complex.exp_ne_zero (ℓ z))
        calc
          Complex.exp (ℓ z)*Complex.exp (-ℓ z)=1 := by
            rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
          _ = Complex.exp (ℓ z)*(actualPhysicalUnitHalfTrace32 u z-s z) := by rw [he z hz, hp]
      have hpos : 0 < (ℓ z).re := by
        apply Real.one_lt_exp_iff.mp
        simpa only [Pi.add_apply, Set.mem_Ioi, ← he z hz, Complex.norm_exp] using hlarge hz
      rw [← sub_eq_add_neg, ← he', Complex.norm_exp, Complex.neg_re]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpos)
  · exact ⟨s, ℓ, hs, hl, hsq, he, fun z hz => hsmall hz⟩

/-- Actual analytic cosine branch with positive imaginary part. It is still
unnormalized: k(z)=z+o(1), real boundary and spectral labels remain open. -/
theorem exists_actualPhysicalUnitAnalyticPositiveCosine33 (u : PhysicalL2) :
    ∃ k : ℂ → ℂ, AnalyticOnNhd ℂ k {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → Complex.cos (k z)=actualPhysicalUnitHalfTrace32 u z) ∧
      (∀ z : ℂ, 0 < z.im → 0 < (k z).im) := by
  obtain ⟨s, ℓ, hs, hl, hsq, he, hsmall⟩ := exists_actualPhysicalUnitAnalyticSmallBranch33 u
  refine ⟨fun z => -Complex.I*ℓ z, analyticOnNhd_const.mul hl, ?_, ?_⟩
  · intro z hz
    exact actualPhysicalUnitCosine_of_squareRoot_log32 u z (s z) (ℓ z) (hsq z hz) (he z hz)
  · intro z hz
    have hneg : (ℓ z).re < 0 := by
      apply Real.exp_lt_one_iff.mp
      simpa only [← he z hz, Complex.norm_exp] using hsmall z hz
    simpa [Complex.mul_im] using neg_pos.mpr hneg

end NlsGge.SpectralFoundations
end
