import NlsGge.Birkhoff.S04Moments38

/-! # C2a: measure determination (carrier-level invariance gives the `L²` identity)

Plan `campaign/GWP_PLAN.md` §7 C2a, §10 flag 4.  Abstract in `S`: no PDE content.  If a measurable
`S : PhysicalL2 → PhysicalL2` preserves `H^m` and the carrier pushforwards `physH38 m ∘ S` and
`physH38 m` have the same `μ`-integrals against all bounded continuous `F`, then `μ.map S = μ`,
provided `μ` is carried by `H^m`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open MeasureTheory NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped BoundedContinuousFunction

/-- The continuous inclusion `h^m → h^0 ≅ L²`, `x ↦ 𝓕⁻¹ x` (the left inverse of `physH38 m` on `H^m`). -/
def physIncl38 (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) : PhysicalL2 :=
  carrierToPhys38 (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m) : ((0 : ℕ) : ℝ) ≤ (m : ℝ)) x)

theorem continuous_physIncl38 (m : ℕ) : Continuous (physIncl38 m) :=
  continuous_carrierToPhys38.comp (carrierIncl38 _).continuous

theorem fourierSeq38_physIncl38 (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) :
    fourierSeq38 (physIncl38 m x) = carrierCoe38 (m : ℝ) x := by
  unfold physIncl38 carrierToPhys38
  rw [fourierSeq38_physInv38]
  exact carrierCoe38_incl38 _ x

/-- `physIncl38 m` is a left inverse of `physH38 m` on `H^m`. -/
theorem physIncl38_physH38 (m : ℕ) (u : PhysicalL2) (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :
    physIncl38 m (physH38 m u) = u := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physIncl38, physH38_of_mem m u hu]
  rfl

/-- **C2a, `m`-general.**  A carrier-level identity gives the `L²` identity. -/
theorem map_eq_of_carrier_invariance_m (m : ℕ) (S : PhysicalL2 → PhysicalL2) (hS : Measurable S)
    (μ : Measure PhysicalL2) [IsProbabilityMeasure μ]
    (hH1 : ∀ᵐ u ∂μ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ))
    (hS1 : ∀ u, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) → fourierSeq38 (S u) ∈ seqSobolev38 (m : ℝ))
    (h : ∀ F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ,
      ∫ u, F (physH38 m (S u)) ∂μ = ∫ u, F (physH38 m u) ∂μ) : μ.map S = μ := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  have hP : Measurable (physH38 m) := measurable_physH38 m
  have hPS : Measurable (physH38 m ∘ S) := hP.comp hS
  have hι : Measurable (physIncl38 m) := (continuous_physIncl38 m).measurable
  -- carrier-level equality of pushforwards (measure determination)
  have hcar : μ.map (physH38 m ∘ S) = μ.map (physH38 m) := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun F => ?_)
    rw [integral_map hPS.aemeasurable F.continuous.aestronglyMeasurable,
      integral_map hP.aemeasurable F.continuous.aestronglyMeasurable]
    exact h F
  -- `physIncl38 m ∘ physH38 m = id` and `physIncl38 m ∘ physH38 m ∘ S = S`, `μ`-a.e.
  have e1 : (physIncl38 m ∘ physH38 m) =ᵐ[μ] id :=
    hH1.mono fun u hu => physIncl38_physH38 m u hu
  have e2 : (physIncl38 m ∘ (physH38 m ∘ S)) =ᵐ[μ] S :=
    hH1.mono fun u hu => physIncl38_physH38 m (S u) (hS1 u hu)
  calc μ.map S = μ.map (physIncl38 m ∘ (physH38 m ∘ S)) :=
        (Measure.map_congr e2).symm
    _ = (μ.map (physH38 m ∘ S)).map (physIncl38 m) := (Measure.map_map hι hPS).symm
    _ = (μ.map (physH38 m)).map (physIncl38 m) := by rw [hcar]
    _ = μ.map (physIncl38 m ∘ physH38 m) := Measure.map_map hι hP
    _ = μ.map id := Measure.map_congr e1
    _ = μ := Measure.map_id

/-- **C2a (plan §7, `m = 1`).** -/
theorem map_eq_of_carrier_invariance (S : PhysicalL2 → PhysicalL2) (hS : Measurable S)
    (μ : Measure PhysicalL2) [IsProbabilityMeasure μ]
    (hH1 : ∀ᵐ u ∂μ, fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hS1 : ∀ u, fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      fourierSeq38 (S u) ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (h : ∀ F : SobolevCarrier38 ((1 : ℕ) : ℝ) →ᵇ ℝ,
      ∫ u, F (physH38 1 (S u)) ∂μ = ∫ u, F (physH38 1 u) ∂μ) : μ.map S = μ :=
  map_eq_of_carrier_invariance_m 1 S hS μ hH1 hS1 h

/-- Converse (sanity check: the hypothesis `h` is necessary): if `S` is measurable and preserves `μ`,
then the carrier integral identity holds. -/
theorem carrier_invariance_of_map_eq (m : ℕ) (S : PhysicalL2 → PhysicalL2) (hS : Measurable S)
    (μ : Measure PhysicalL2) (hμ : μ.map S = μ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ) :
    ∫ u, F (physH38 m (S u)) ∂μ = ∫ u, F (physH38 m u) ∂μ := by
  let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
  have hG : AEStronglyMeasurable (fun u => F (physH38 m u)) μ :=
    (F.continuous.measurable.comp (measurable_physH38 m)).aestronglyMeasurable
  calc ∫ u, F (physH38 m (S u)) ∂μ = ∫ u, F (physH38 m u) ∂(μ.map S) :=
        (integral_map hS.aemeasurable (hμ ▸ hG)).symm
    _ = ∫ u, F (physH38 m u) ∂μ := by rw [hμ]

/-- Regression probe: `S = id` satisfies every hypothesis of `map_eq_of_carrier_invariance`
(so the hypotheses are satisfiable) and the conclusion is `Measure.map_id`. -/
theorem map_eq_of_carrier_invariance_id (μ : Measure PhysicalL2) [IsProbabilityMeasure μ]
    (hH1 : ∀ᵐ u ∂μ, fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : μ.map id = μ :=
  map_eq_of_carrier_invariance id measurable_id μ hH1 (fun _ h => h) (fun _ => rfl)

end NlsGge.NLS38
