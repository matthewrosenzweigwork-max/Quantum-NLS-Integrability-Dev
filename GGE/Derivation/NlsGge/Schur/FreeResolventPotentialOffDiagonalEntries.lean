import NlsGge.Schur.FreeResolventPotentialMatrixEntriesAfterInnerScalar
import NlsGge.Schur.ResonantParityPairBasisAction

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

theorem resonantParityPair_repr_apply (n : ℤ) (f : ParityPair n)
    (i : Bool × Sector n) :
    parityPairRepr n (resonantParityPair n f) i =
      if i.2 = resonantIndex n then parityPairRepr n f i else 0 := by
  simp [resonantParityPair, resonantSquare_apply]

theorem freeResolventPotentialColumn_repr_apply
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz f) i =
      freeResolventCoeff n z i.2 *
        parityPairRepr n
          (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
            (resonantParityPair n f)) i := by
  simp [freeResolventPotentialColumn, freeResolventParityPair_repr_apply]

theorem resonantPotentialFreeResolventRow_repr_apply
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz f) i =
      if i.2 = resonantIndex n then
        parityPairRepr n
          (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
            (freeResolventParityPair n z hz f)) i
      else 0 := by
  simp [resonantPotentialFreeResolventRow, resonantParityPair_repr_apply]

/-- Actual DVP upper coefficient: its input column is supported only at the
resonant paired mode, and retains the first independent source field. -/
theorem freeResolventPotentialColumn_upper_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, l))) =
      if l = resonantIndex n then
        freeResolventCoeff n z m *
          physicalFourier u₁ ((m.val + l.val) / 2)
      else 0 := by
  rw [← parityPairRepr_inner, freeResolventPotentialColumn_repr_apply,
    resonantParityPair_apply_basis]
  by_cases hl : l = resonantIndex n
  · simp [hl, parityPairRepr_inner, coveredH1ParityPairPotential_upper_entry]
  · simp [hl]

/-- Actual DVP reflected lower coefficient for the independently quantified
second source field. -/
theorem freeResolventPotentialColumn_lower_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, l))) =
      if l = resonantIndex n then
        freeResolventCoeff n z m *
          physicalFourier u₂ (-(m.val + l.val) / 2)
      else 0 := by
  rw [← parityPairRepr_inner, freeResolventPotentialColumn_repr_apply,
    resonantParityPair_apply_basis]
  by_cases hl : l = resonantIndex n
  · simp [hl, parityPairRepr_inner, coveredH1ParityPairPotential_lower_entry]
  · simp [hl]

/-- Actual PVD upper coefficient: its output row is supported only at the
resonant paired mode, with the first independent source field preserved. -/
theorem resonantPotentialFreeResolventRow_upper_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, l))) =
      if m = resonantIndex n then
        physicalFourier u₁ ((m.val + l.val) / 2) *
          freeResolventCoeff n z l
      else 0 := by
  rw [← parityPairRepr_inner, resonantPotentialFreeResolventRow_repr_apply]
  by_cases hm : m = resonantIndex n
  · simp only [hm, if_pos]
    rw [freeResolventParityPair_apply_basis, map_smul, parityPairRepr_inner]
    rw [parityPair_inner_smul_right n (parityPairVector n (true, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (false, l))) (freeResolventCoeff n z l)]
    rw [coveredH1ParityPairPotential_upper_entry]
    ring
  · simp [hm]

/-- Actual PVD reflected lower coefficient, retaining the independent second
source field and its reflected sign. -/
theorem resonantPotentialFreeResolventRow_lower_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, l))) =
      if m = resonantIndex n then
        physicalFourier u₂ (-(m.val + l.val) / 2) *
          freeResolventCoeff n z l
      else 0 := by
  rw [← parityPairRepr_inner, resonantPotentialFreeResolventRow_repr_apply]
  by_cases hm : m = resonantIndex n
  · simp only [hm, if_pos]
    rw [freeResolventParityPair_apply_basis, map_smul, parityPairRepr_inner]
    rw [parityPair_inner_smul_right n (parityPairVector n (false, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (true, l))) (freeResolventCoeff n z l)]
    rw [coveredH1ParityPairPotential_lower_entry]
    ring
  · simp [hm]

end NlsGge.Schur
