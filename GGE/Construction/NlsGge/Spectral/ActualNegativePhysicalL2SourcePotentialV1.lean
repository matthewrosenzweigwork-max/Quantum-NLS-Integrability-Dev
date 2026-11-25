import NlsGge.Spectral.ActualPhysicalPotentialSourceConjugacyV3
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The actual interval potential agrees with the actual doubled-cover L2
representative after restriction; no pointwise representative equality is used. -/
theorem actualPhysicalL2SourcePotential_cover_ae (u : PhysicalL2) :
    (actualPhysicalL2SourcePotential u : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => naturalPhysicalCoverL2 u (t : SpectralCircle) := by
  exact scalarParityRestrictValue_ae 0
    ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩

/-- The negative physical field has the negative actual source potential
as its cover representative, almost everywhere on the true source interval. -/
theorem naturalPhysicalCoverL2_neg_source_ae (u : PhysicalL2) :
    (fun t : ℝ => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => -actualPhysicalL2SourcePotential u t := by
  have hn : (naturalPhysicalCoverL2 (-u) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => -naturalPhysicalCoverL2 u x := by
    rw [map_neg]
    exact Lp.coeFn_neg (naturalPhysicalCoverL2 u)
  have hi := spectral_ae_pullback_first_half hn
  filter_upwards [hi, actualPhysicalL2SourcePotential_cover_ae u] with t ht hu
  exact ht.trans (congrArg Neg.neg hu.symm)

/-- The sign bridge is an exact equality of the source L2 classes, not a
choice of special representatives of the rough potential. -/
theorem actualPhysicalL2SourcePotential_neg (u : PhysicalL2) :
    actualPhysicalL2SourcePotential (-u) = -actualPhysicalL2SourcePotential u := by
  apply Lp.ext
  filter_upwards [actualPhysicalL2SourcePotential_cover_ae (-u),
    naturalPhysicalCoverL2_neg_source_ae u,
    Lp.coeFn_neg (actualPhysicalL2SourcePotential u)] with t hs hn hz
  exact hs.trans (hn.trans hz.symm)

end NlsGge.Schur
end
