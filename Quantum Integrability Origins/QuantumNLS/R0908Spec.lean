import QuantumNLS.RootGapLevelSets
/-! integrator-authored trusted spec for R-0908DFDE prop:root-gap-multiplicity (Terra r157 FULL ACCEPT): headline statement(s) copied verbatim from RootGapLevelSets (QuantumNLS.RootGapLevelSets). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Set
open scoped Real ENNReal
noncomputable section
namespace QuantumNLS.R0908Spec
open QuantumNLS.RootGapLevelSets
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.PhysicalContinuousBoundary (boundary continuous_boundary boundary_limit boundary_cosine boundary_im
  gap_constancy monotone_all onto_all boundary_zero)
open QuantumNLS.RootGapLocal
open QuantumNLS.RootGapMultiplicity
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg)
open QuantumNLS.RootDensity (hfun hfun_pos_iff hfun_nonneg)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_gap_multiplicity_spec (hκ : 0 < κ) (u : L2T L) :
    (∀ z : ℂ, Dl κ u z ^ 2 - 4 = 0 → z.im = 0 ∧ analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) z ≤ 2) ∧
    (∀ x : ℝ, analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) (x : ℂ) = 2 →
      (∀ᶠ t : ℝ in 𝓝[<] x, |(Dl κ u (t : ℂ)).re| < 2) ∧ (∀ᶠ t : ℝ in 𝓝[>] x, |(Dl κ u (t : ℂ)).re| < 2)) ∧
    (∀ n : ℤ, ∃ a : ℝ, (boundary hκ u a).re = ((n : ℝ) + 1 / 2) * Real.pi) ∧
    (∀ n : ℤ, ∃ bm bp : ℝ, bm ≤ bp ∧ {x : ℝ | (boundary hκ u x).re = (n : ℝ) * Real.pi} = Icc bm bp ∧
      (∀ a a' : ℝ, (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi →
        (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi →
        a < bm ∧ bp < a' ∧ (0 < measure hκ u (Ioo a a') ↔ bm < bp)) ∧
      ((bm < bp ∧ (∀ x ∈ Ioo bm bp, 0 < dens κ u x) ∧
          analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bm : ℂ) = 1 ∧
          analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bp : ℂ) = 1) ∨
       (bm = bp ∧ analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bm : ℂ) = 2 ∧
          ∀ a a' : ℝ, (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi →
            (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi → measure hκ u (Ioo a a') = 0))) := by
  first
  | exact QuantumNLS.RootGapLevelSets.root_gap_multiplicity
  | (apply QuantumNLS.RootGapLevelSets.root_gap_multiplicity <;> assumption)

end QuantumNLS.R0908Spec
#print axioms QuantumNLS.R0908Spec.root_gap_multiplicity_spec
