import NlsGge.Spectral.ActualPhysicalUnitAnalyticUnnormalizedBranch32V4
import Mathlib.Analysis.Complex.Trigonometric
set_option autoImplicit false
noncomputable section
open Set
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- Every true logarithm of delta+s, for an actual square root of
delta^2-1, gives the source cosine relation. No principal-branch choice or
asymptotic normalization is silently imposed. -/
theorem actualPhysicalUnitCosine_of_squareRoot_log32
    (u : PhysicalL2) (z s ℓ : ℂ)
    (hs : s ^ 2 = actualPhysicalUnitHalfTrace32 u z ^ 2 - 1)
    (he : Complex.exp ℓ = actualPhysicalUnitHalfTrace32 u z + s) :
    Complex.cos (-Complex.I * ℓ) = actualPhysicalUnitHalfTrace32 u z := by
  have hp : (actualPhysicalUnitHalfTrace32 u z + s) *
      (actualPhysicalUnitHalfTrace32 u z - s) = 1 := by
    linear_combination - hs
  have hm : Complex.exp (-ℓ) = actualPhysicalUnitHalfTrace32 u z - s := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero ℓ)
    calc
      Complex.exp ℓ * Complex.exp (-ℓ) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      _ = Complex.exp ℓ * (actualPhysicalUnitHalfTrace32 u z - s) := by
        rw [he, hp]
  have hplus : (-Complex.I * ℓ) * Complex.I = ℓ := by
    calc
      (-Complex.I * ℓ) * Complex.I = -(Complex.I * Complex.I) * ℓ := by ring
      _ = ℓ := by rw [Complex.I_mul_I]; ring
  have hminus : -(-Complex.I * ℓ) * Complex.I = -ℓ := by
    rw [neg_mul, hplus]
  rw [Complex.cos, hplus, hminus, he, hm]
  ring

/-- The actual unit trace admits an analytic cosine branch on the whole
upper half-plane. The branch is existential and unnormalized: the source
condition k(z)=z+o(1), slit geometry, boundary roots and labels are still open. -/
theorem exists_actualPhysicalUnitAnalyticUnnormalizedCosine32 (u : PhysicalL2) :
    ∃ k : ℂ → ℂ, AnalyticOnNhd ℂ k {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im → Complex.cos (k z) = actualPhysicalUnitHalfTrace32 u z := by
  obtain ⟨s, ℓ, hs, hl, hsq, he⟩ := exists_actualPhysicalUnitAnalyticUnnormalizedBranch32 u
  refine ⟨fun z => -Complex.I * ℓ z, analyticOnNhd_const.mul hl, ?_⟩
  intro z hz
  exact actualPhysicalUnitCosine_of_squareRoot_log32 u z (s z) (ℓ z) (hsq z hz) (he z hz)

end NlsGge.SpectralFoundations
end
