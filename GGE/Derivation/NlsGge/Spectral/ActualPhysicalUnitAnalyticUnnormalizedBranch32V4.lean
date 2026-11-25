import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import NlsGge.Spectral.ContinuousComplexLogLiftAnalytic32V3
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
noncomputable section
open Set
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

theorem actualPhysicalUpperHalfPlane_isSimplyConnected32 :
    IsSimplyConnected {z : ℂ | 0 < z.im} := by
  letI : ContractibleSpace {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩
  change SimplyConnectedSpace {z : ℂ | 0 < z.im}
  infer_instance

/-- The ACTUAL rough physical unit trace radicand has an analytic square
root on the upper half-plane. Its sign is existential and unnormalized. -/
theorem exists_actualPhysicalUnitAnalyticSquareRoot32 (u : PhysicalL2) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im → s z ^ 2 = actualPhysicalUnitHalfTrace32 u z ^ 2 - 1 := by
  have ha := (analyticOnNhd_actualPhysicalUnitBranchRadicand32 u).mono
    (show {z : ℂ | 0 < z.im} ⊆ Set.univ from subset_univ _)
  obtain ⟨ℓ, hl, he⟩ := exists_analyticComplexLogLift32
    UpperHalfPlane.isOpen_upperHalfPlaneSet actualPhysicalUpperHalfPlane_isSimplyConnected32
    ha (fun z hz => actualPhysicalUnitBranchRadicand_upperHalfPlane_nonzero32 u z hz)
  refine ⟨fun z => Complex.exp (ℓ z / 2), hl.div_const.cexp, ?_⟩
  intro z hz
  have ht : ℓ z / 2 + ℓ z / 2 = ℓ z := by ring
  rw [pow_two, ← Complex.exp_add, ht, he z hz]

/-- There is an analytic logarithm of delta+s for an actual analytic
square root of delta^2-1. Neither root sign nor logarithm integer is fixed;
the manuscript asymptotic k(z)=z+o(1), boundary labels and action estimate
remain additional obligations. This is a concrete intermediate, not E02
or NEW-E01 completion. -/
theorem exists_actualPhysicalUnitAnalyticUnnormalizedBranch32 (u : PhysicalL2) :
    ∃ s ℓ : ℂ → ℂ,
      AnalyticOnNhd ℂ s {z : ℂ | 0 < z.im} ∧
      AnalyticOnNhd ℂ ℓ {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → s z ^ 2 = actualPhysicalUnitHalfTrace32 u z ^ 2 - 1) ∧
      (∀ z : ℂ, 0 < z.im → Complex.exp (ℓ z) = actualPhysicalUnitHalfTrace32 u z + s z) := by
  obtain ⟨s, hs, hsq⟩ := exists_actualPhysicalUnitAnalyticSquareRoot32 u
  have hd := (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).mono
    (show {z : ℂ | 0 < z.im} ⊆ Set.univ from subset_univ _)
  have hn : ∀ z ∈ {z : ℂ | 0 < z.im}, actualPhysicalUnitHalfTrace32 u z + s z ≠ 0 := by
    intro z hz hzero
    have hprod : (actualPhysicalUnitHalfTrace32 u z + s z) *
        (actualPhysicalUnitHalfTrace32 u z - s z) = 1 := by
      linear_combination - hsq z hz
    rw [hzero, zero_mul] at hprod
    exact zero_ne_one hprod
  obtain ⟨ℓ, hl, he⟩ := exists_analyticComplexLogLift32
    UpperHalfPlane.isOpen_upperHalfPlaneSet actualPhysicalUpperHalfPlane_isSimplyConnected32
    (hd.add hs) hn
  exact ⟨s, ℓ, hs, hl, hsq, he⟩

end NlsGge.SpectralFoundations
end
