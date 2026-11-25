import NlsGge.GK38.PairRealBridge
import NlsGge.Birkhoff.BirkhoffAPI38

/-!
# F4 (part 3): the discriminant of a Fourier sequence (`discrimOf`, plan R5b draft (tv))

`discrimOf x hx w = Δ(realSlice (physInv38 x hx), w)`: the discriminant of the potential whose
(reflected) Fourier sequence is `x ∈ h⁰`.  Kept apart from `PairRealBridge.lean` because it imports
the Birkhoff API (`physInv38`, `seqSobolev38`).  The plan's `rotSeq` draft is not defined here:
the repository already has `rotSeq38` (`NlsGge.Birkhoff`).
-/

set_option autoImplicit false

namespace NlsGge.GK38

noncomputable section

open NlsGge.Birkhoff NlsGge.Pilot NlsGge.SpectralFoundations

/-- The discriminant of the potential whose Fourier sequence is `u` (R5b). -/
def discrimOf (u : ℤ → ℂ) (hu : u ∈ seqSobolev38 0) (w : ℂ) : ℂ :=
  discrim (realSlice (physInv38 u hu)) w

theorem discrimOf_fourierSeq38 (u : PhysicalL2) (w : ℂ) :
    discrimOf (fourierSeq38 u) (fourierSeq38_mem_zero u) w = discrim (realSlice u) w := by
  unfold discrimOf
  rw [physInv38_fourierSeq38]

theorem discrimOf_eq_halfTrace (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (w : ℂ) :
    discrimOf x hx w = 2 * actualPhysicalUnitHalfTrace32 (physInv38 x hx) w :=
  discrim_realSlice _ w

theorem analyticOnNhd_discrimOf (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    AnalyticOnNhd ℂ (discrimOf x hx) Set.univ :=
  analyticOnNhd_discrim_z _

/-- The zero sequence has the free discriminant `2 cos w`. -/
theorem discrimOf_zero (hx : (0 : ℤ → ℂ) ∈ seqSobolev38 0) (w : ℂ) :
    discrimOf 0 hx w = 2 * Complex.cos w := by
  have h : physInv38 0 hx = 0 := by
    apply fourierSeq38_injective
    rw [fourierSeq38_physInv38, fourierSeq38_zero]
  unfold discrimOf
  rw [h, realSlice_zero]
  exact discrim_zero w

end

end NlsGge.GK38
