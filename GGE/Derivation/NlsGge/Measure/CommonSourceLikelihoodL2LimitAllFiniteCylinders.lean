import NlsGge.Measure.CommonSourceLikelihoodL2LimitCylinderAfterEventuallyConstant

/-! The same chosen actual L2 density, not a cylinder-dependent existential.
This is a countable-coordinate cylinder globalization prerequisite; full raw
RN equality and strict positivity are separate obligations. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace NlsGge.Measure

theorem exists_actualSourceCMCommonLikelihoodL2Limit_allFiniteCylinders
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ L : Lp ℝ 2 (fullWeightSequenceGaussian c.val),
      Tendsto (commonSourceLikelihoodLpSequenceOfMemLp lower upper c
        (actualSourceCMSequence c x)
        (fun N => memLp_commonSourceLikelihoodReal c N
          (actualSourceCMSequence c x))) atTop (nhds L) ∧
      (∀ᵐ z ∂fullWeightSequenceGaussian c.val, 0 ≤ L z) ∧
      (∫ z : ℤ → ℂ, L z ∂fullWeightSequenceGaussian c.val) = 1 ∧
      ∀ (M : ℕ) (U : Finset ℤ)
        (hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M)
        (B : Set ((u : U) → ℂ)), MeasurableSet B →
        ENNReal.ofReal (∫ z in
          (fun z : ℤ → ℂ => fun u : U => z u.1) ⁻¹' B,
          L z ∂fullWeightSequenceGaussian c.val) =
          (Measure.pi (fun u : U =>
            (complexGaussian (fullWeightRate c.val u.1)).map
              (fun z : ℂ => z + actualSourceCMSequence c x u.1))) B := by
  obtain ⟨L, hconv, hnonneg, hmass⟩ :=
    exists_actualSourceCMCommonLikelihoodL2Limit_probability c x
  refine ⟨L, hconv, hnonneg, hmass, ?_⟩
  intro M U hU B hB
  obtain ⟨L', hconv', _, _, hcy⟩ :=
    exists_actualSourceCMCommonLikelihoodL2Limit_finiteCylinder_afterEventuallyConstant
      c x M U hU B hB
  have hsame : L = L' := tendsto_nhds_unique hconv hconv'
  rw [hsame]
  exact hcy

end NlsGge.Measure
