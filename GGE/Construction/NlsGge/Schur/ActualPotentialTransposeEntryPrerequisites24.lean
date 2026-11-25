import NlsGge.Schur.ActualPotentialTransposeScalarAndBasisPrerequisites24
import NlsGge.Schur.CoveredH1ParityPairEntriesFromAE
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The inner product against a single coordinate with coefficient one
extracts that coordinate on the actual square Fourier space. -/
theorem actualPotentialTranspose_lp_single_inner_coordinate24
    (n : ℤ) (i : Bool × Sector n) (y : SectorSquare n) :
    inner ℂ (lp.single 2 i (1 : ℂ)) y = y i := by
  rw [lp.inner_single_left]
  exact actualPotentialTranspose_inner_one_left24 (y i)

/-- The actual off-diagonal paired potential has zero same-channel matrix
entries on every genuine paired Fourier basis vector. -/
theorem actualPotentialTranspose_same_channel_entry_zero24
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (b : Bool) (m l : Sector n) :
    inner ℂ (parityPairVector n (b, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (b, l))) = 0 := by
  cases b <;>
    simp [parityPairVector, mixedIndex,
      coveredH1ParityPairPotential_apply_true,
      coveredH1ParityPairPotential_apply_false,
      coveredH1ScalarParityMultiplier_coe_apply,
      PiLp.single_apply, PiLp.inner_apply, Fintype.sum_bool,
      Submodule.coe_inner]

/-- Fully reduced actual matrix entries of the two-field paired potential.
The same-channel terms vanish; the two cross channels retain their distinct
fields and exact signed Fourier indices. -/
theorem actualPotentialTranspose_pair_entry_formula24
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (b c : Bool) (m l : Sector n) :
    inner ℂ (parityPairVector n (b, m))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (c, l))) =
      if b = c then 0 else if b then
        physicalFourier u₁ ((m.val + l.val) / 2) else
        physicalFourier u₂ (-(m.val + l.val) / 2) := by
  cases b <;> cases c
  · simpa using actualPotentialTranspose_same_channel_entry_zero24
      u₁ u₂ hu₁ hu₂ n false m l
  · simpa using coveredH1ParityPairPotential_lower_entry
      u₁ u₂ hu₁ hu₂ n m l
  · simpa using coveredH1ParityPairPotential_upper_entry
      u₁ u₂ hu₁ hu₂ n m l
  · simpa using actualPotentialTranspose_same_channel_entry_zero24
      u₁ u₂ hu₁ hu₂ n true m l

/-- The tuple projections appearing after Bool case splits reduce to the
actual channel-swapped pair index. -/
@[simp] theorem actualPotentialTranspose_swapped_pair_index24
    (n : ℤ) (b : Bool) (m : Sector n) :
    (!((b, m).1), (b, m).2) = (!b, m) := by
  rfl

end NlsGge.Schur
