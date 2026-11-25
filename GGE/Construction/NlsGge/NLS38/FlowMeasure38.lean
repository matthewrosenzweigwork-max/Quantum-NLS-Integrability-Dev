import NlsGge.NLS38.PhysicalFlow38
import NlsGge.NLS38.MeasureDetermination38
import NlsGge.Birkhoff.S04Moments38b

/-! # GWP piece C2b: measurability of the physical flow `nlsFlowL2 t`

Plan `campaign/GWP_PLAN.md` §7 C2b.  `Measure.map` of a non-measurable map is `0`, so the
statements `(ν_Λ).map (nlsFlowL2 t) = ν_Λ` and `(μ_W).map (nlsFlowL2 t) = μ_W` (S04.07, S04.08) are
meaningful only because of `measurable_nlsFlowL2`.

On `H¹ = {u | fourierSeq38 u ∈ seqSobolev38 1}` (a measurable set) the flow is
`physIncl38 1 ∘ nlsFlowC 1 t ∘ physH38 1` (`physH38_nlsFlowL2` and `physIncl38_physH38`); off `H¹` it
is the identity (`nlsFlowL2_of_not_H1`).  `Measurable.ite` assembles the two pieces.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open MeasureTheory NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

/-- The flow agrees with `physIncl38 1 ∘ nlsFlowC ∘ physH38 1` on `H¹`. -/
theorem nlsFlowL2_eq_incl38 (t : ℝ) (u : PhysicalL2)
    (hu : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    nlsFlowL2 t u = physIncl38 1 (nlsFlowC 1 le_rfl t (physH38 1 u)) := by
  have hu' : SobolevSquareSummable ((1 : ℕ) : ℝ) (physicalFourier u) :=
    (fourierSeq38_mem_iff _ u).1 hu
  have hv : fourierSeq38 (nlsFlowL2 t u) ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff _ _).2 (nlsFlowL2_mem 1 le_rfl hu' t)
  rw [← physH38_nlsFlowL2 1 le_rfl hu t, physIncl38_physH38 1 _ hv]

theorem continuous_nlsFlowC_one38 (t : ℝ) :
    Continuous fun x : SobolevCarrier38 ((1 : ℕ) : ℝ) => nlsFlowC 1 le_rfl t x := by
  have h := continuous_nlsFlowC_uncurry 1 le_rfl
  exact h.comp (continuous_const.prodMk continuous_id)

/-- Borel measurability of `physIncl38 1 ∘ nlsFlowC 1 t ∘ physH38 1`, for any Borel structure on
the carrier. -/
theorem measurable_inclFlowH38 (t : ℝ)
    [MeasurableSpace (SobolevCarrier38 ((1 : ℕ) : ℝ))]
    [BorelSpace (SobolevCarrier38 ((1 : ℕ) : ℝ))] :
    Measurable fun u : PhysicalL2 => physIncl38 1 (nlsFlowC 1 le_rfl t (physH38 1 u)) := by
  have hι : Measurable (physIncl38 1) := (continuous_physIncl38 1).measurable
  have hF : Measurable (nlsFlowC 1 le_rfl t) := (continuous_nlsFlowC_one38 t).measurable
  exact Measurable.comp (g := physIncl38 1)
    (f := fun u : PhysicalL2 => nlsFlowC 1 le_rfl t (physH38 1 u)) hι
    (Measurable.comp (g := nlsFlowC 1 le_rfl t) (f := physH38 1) hF (measurable_physH38 1))

theorem measurable_nlsFlowL2 (t : ℝ) : Measurable (nlsFlowL2 t) := by
  classical
  let _ : MeasurableSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := ⟨rfl⟩
  have hset : MeasurableSet {u : PhysicalL2 | fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ)} :=
    (NlsGge.Birkhoff.measurableSet_seqSobolev38 _).preimage measurable_fourierSeq38
  have heq : nlsFlowL2 t = fun u : PhysicalL2 =>
      if fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) then
        physIncl38 1 (nlsFlowC 1 le_rfl t (physH38 1 u)) else u := by
    funext u
    by_cases hu : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ)
    · simp only [hu, ↓reduceIte]
      exact nlsFlowL2_eq_incl38 t u hu
    · simp only [hu, ↓reduceIte]
      refine nlsFlowL2_of_not_H1 (fun h => hu ((fourierSeq38_mem_iff _ u).2 ?_)) t
      rw [Nat.cast_one]; exact h
  rw [heq]
  exact Measurable.ite hset (measurable_inclFlowH38 t) measurable_id

/-! ## Probe: the pushforward of a probability measure is a probability measure -/

/-- Non-vacuity: `Measure.map (nlsFlowL2 t)` is not the zero measure; it preserves total mass. -/
theorem isProbabilityMeasure_map_nlsFlowL2_38 (μ : Measure PhysicalL2) [IsProbabilityMeasure μ]
    (t : ℝ) : IsProbabilityMeasure (μ.map (nlsFlowL2 t)) :=
  haveI : IsProbabilityMeasure (μ.map (nlsFlowL2 t)) :=
    ⟨by rw [Measure.map_apply (measurable_nlsFlowL2 t) MeasurableSet.univ]; simp⟩
  this

/-- The pushforward of a Dirac mass is the Dirac mass at the flowed point (not `0`). -/
theorem map_dirac_nlsFlowL2_38 (u : PhysicalL2) (t : ℝ) :
    (Measure.dirac u).map (nlsFlowL2 t) = Measure.dirac (nlsFlowL2 t u) :=
  Measure.map_dirac' (measurable_nlsFlowL2 t) u

/-- Total mass of the pushforward is `1` for every probability measure. -/
theorem map_nlsFlowL2_univ_38 (μ : Measure PhysicalL2) [IsProbabilityMeasure μ] (t : ℝ) :
    (μ.map (nlsFlowL2 t)) Set.univ = 1 := by
  rw [Measure.map_apply (measurable_nlsFlowL2 t) MeasurableSet.univ]
  simp

end NlsGge.NLS38
