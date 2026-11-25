import NlsGge.Schur.FreeResolventPotentialInnerScalar
import NlsGge.Schur.CoveredH1ParityPairEntriesFromAE

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

theorem parityPairRepr_inner (n : ℤ) (f : ParityPair n)
    (i : Bool × Sector n) :
    parityPairRepr n f i = inner ℂ (parityPairVector n i) f := by
  change (parityPairFourierBasis n).repr f i = _
  rw [HilbertBasis.repr_apply_apply]
  simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The actual free resolvent acts diagonally on the concrete paired Fourier
basis, with its resonant coefficient equal to zero. -/
theorem freeResolventParityPair_repr_apply (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralDisk n) (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n (freeResolventParityPair n z hz f) i =
      freeResolventCoeff n z i.2 * parityPairRepr n f i := by
  simp [freeResolventParityPair, freeResolventSquare_apply]

theorem freeResolventPotentialFreeResolvent_repr_apply
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (f : ParityPair n) (i : Bool × Sector n) :
    parityPairRepr n
        (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz f) i =
      freeResolventCoeff n z i.2 * parityPairRepr n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
          (freeResolventParityPair n z hz f)) i := by
  simp [freeResolventPotentialFreeResolvent, freeResolventParityPair_repr_apply]

/-- The actual free resolvent acts diagonally on the concrete paired Fourier
basis, with its resonant coefficient equal to zero. -/
theorem freeResolventParityPair_apply_basis (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralDisk n) (i : Bool × Sector n) :
    freeResolventParityPair n z hz (parityPairVector n i) =
      freeResolventCoeff n z i.2 • parityPairVector n i := by
  apply (parityPairRepr n).injective
  apply lp.ext
  funext j
  simp only [freeResolventParityPair_repr_apply, parityPairRepr_vector, map_smul]
  by_cases hji : j = i <;> simp [lp.single_apply, hji]

/-- Exact upper DVD matrix coefficient, including both free denominators and
the first independent source field. -/
theorem freeResolventPotentialFreeResolvent_upper_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, l))) =
      freeResolventCoeff n z m *
        physicalFourier u₁ ((m.val + l.val) / 2) *
          freeResolventCoeff n z l := by
  rw [← parityPairRepr_inner, freeResolventPotentialFreeResolvent_repr_apply,
    freeResolventParityPair_apply_basis]
  rw [map_smul, parityPairRepr_inner]
  rw [parityPair_inner_smul_right n (parityPairVector n (true, m))
    (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (parityPairVector n (false, l))) (freeResolventCoeff n z l)]
  rw [coveredH1ParityPairPotential_upper_entry]
  ring

/-- Exact reflected lower DVD matrix coefficient, retaining the second
independent source field and its reflected Fourier sign. -/
theorem freeResolventPotentialFreeResolvent_lower_entry
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, l))) =
      freeResolventCoeff n z m *
        physicalFourier u₂ (-(m.val + l.val) / 2) *
          freeResolventCoeff n z l := by
  rw [← parityPairRepr_inner, freeResolventPotentialFreeResolvent_repr_apply,
    freeResolventParityPair_apply_basis]
  rw [map_smul, parityPairRepr_inner]
  rw [parityPair_inner_smul_right n (parityPairVector n (false, m))
    (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (parityPairVector n (true, l))) (freeResolventCoeff n z l)]
  rw [coveredH1ParityPairPotential_lower_entry]
  ring

end NlsGge.Schur
