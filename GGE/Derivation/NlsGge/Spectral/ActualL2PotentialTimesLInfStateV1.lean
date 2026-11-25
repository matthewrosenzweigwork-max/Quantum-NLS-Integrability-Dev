import NlsGge.Analysis.NaturalCoverCoefficients
import NlsGge.Schur.SignedInterval
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- Multiplication by the actual physical L² potential, lifted to the
doubled source circle, on an L∞ state. This uses the L² × L∞ → L² Hölder
orientation required by the source equation. -/
def actualL2PotentialTimesLInf (u : PhysicalL2) :
    Lp ℂ ∞ spectralHaar →L[ℂ] SpectralScalarL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL spectralHaar 2 ∞ 2
    (naturalPhysicalCoverL2 u)

/-- The lifted L² multiplication map has the actual product as its a.e.
representative on the doubled circle. -/
theorem actualL2PotentialTimesLInf_ae (u : PhysicalL2)
    (f : Lp ℂ ∞ spectralHaar) :
    (actualL2PotentialTimesLInf u f : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => naturalPhysicalCoverL2 u x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := (2 : ℝ≥0∞))
    (naturalPhysicalCoverL2 u) f
  change (actualL2PotentialTimesLInf u f : SpectralCircle → ℂ) =ᵐ[spectralHaar]
    fun x => naturalPhysicalCoverL2 u x * f x at hm
  exact hm

/-- Exact physical representative of the potential on the actual unit source
interval, obtained from the even doubled-circle lift. -/
def actualPhysicalL2SourcePotential (u : PhysicalL2) : SourceIntervalL2 :=
  scalarParityIntervalEquiv 0
    ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩

/-- The actual source-interval potential has exactly the original physical
L² norm; the degree-two cover and parity restriction introduce no factor. -/
theorem actualPhysicalL2SourcePotential_norm (u : PhysicalL2) :
    ‖actualPhysicalL2SourcePotential u‖ = ‖u‖ := by
  rw [actualPhysicalL2SourcePotential]
  rw [(scalarParityIntervalEquiv 0).norm_map]
  exact naturalPhysicalCoverL2_norm u

/-- The actual source-interval L² potential acts on an L∞ source state by a
bounded L² multiplier, with no H¹ assumption. -/
def actualSourceL2PotentialTimesLInf (u : PhysicalL2) :
    Lp ℂ ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1)) →L[ℂ] SourceIntervalL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL
    (volume.restrict (Set.Ioc (0 : ℝ) 1)) 2 ∞ 2
      (actualPhysicalL2SourcePotential u)

/-- Its representative is the actual a.e. product on the source interval. -/
theorem actualSourceL2PotentialTimesLInf_ae (u : PhysicalL2)
    (f : Lp ℂ ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (actualSourceL2PotentialTimesLInf u f : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => actualPhysicalL2SourcePotential u x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := (2 : ℝ≥0∞))
    (actualPhysicalL2SourcePotential u) f
  change (actualSourceL2PotentialTimesLInf u f : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
    fun x => actualPhysicalL2SourcePotential u x * f x at hm
  exact hm

/-- The source-interval multiplication operator is bounded by the original
physical L² norm. -/
theorem actualSourceL2PotentialTimesLInf_norm_bound (u : PhysicalL2) :
    ‖actualSourceL2PotentialTimesLInf u‖ ≤ ‖u‖ := by
  have hop : ‖(ContinuousLinearMap.mul ℂ ℂ).holderL
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) 2 ∞ 2‖ ≤ 1 := by
    exact (ContinuousLinearMap.norm_holderL_le (ContinuousLinearMap.mul ℂ ℂ)).trans
      (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
  calc
    ‖actualSourceL2PotentialTimesLInf u‖ ≤
        ‖(ContinuousLinearMap.mul ℂ ℂ).holderL
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) 2 ∞ 2‖ *
          ‖actualPhysicalL2SourcePotential u‖ :=
      ((ContinuousLinearMap.mul ℂ ℂ).holderL
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) 2 ∞ 2).le_opNorm _
    _ ≤ 1 * ‖actualPhysicalL2SourcePotential u‖ :=
      mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = ‖u‖ := by rw [actualPhysicalL2SourcePotential_norm]; simp

end NlsGge.Schur

end
