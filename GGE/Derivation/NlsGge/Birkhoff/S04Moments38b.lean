import NlsGge.Birkhoff.S04Moments38

/-! # S04.01-.03 (consolidated) and S04.05: equivalence with `γ_W`, smooth support, positivity of actions

v2 `A:thm:main` proof, paragraph 1 (l.431-433): "Smooth support follows from
`A:eq:Gaussianregularity` and the inverse Birkhoff map. Positivity of all the actions follows from
equivalence with `γ_W`: each Gaussian coordinate is nonzero almost surely, and there are countably
many coordinates."

Conditional on `B : BirkhoffTop38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal BoundedContinuousFunction

theorem measurableSet_seqSobolev38 (r : ℝ) : MeasurableSet (seqSobolev38 r) := by
  have : seqSobolev38 r = {z : ℤ → ℂ | Summable (fun n : ℤ => sobolevModeWeight r n * ‖z n‖ ^ 2)} := by
    ext z
    exact mem_seqSobolev38_iff r z
  rw [this]
  exact measurableSet_sequenceSummable _ (fun n => (sobolevModeWeight_pos r n).le)

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- Cleaned `T` on `h⁰` as a map of sequences: `T` on `h⁰`, `0` elsewhere. -/
def cleanT0 (z : ℤ → ℂ) : ℤ → ℂ :=
  carrierCoe38 ((0 : ℕ) : ℝ) (Function.extend (carrierCoe38 ((0 : ℕ) : ℝ)) (B.TC 0) (fun _ => 0) z)

theorem cleanT0_of_mem (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) : B.cleanT0 z = B.T z := by
  have hz' : z ∈ seqSobolev38 ((0 : ℕ) : ℝ) := (mem_seqSobolev38_natCast_zero_iff z).2 hz
  have h : Function.extend (carrierCoe38 ((0 : ℕ) : ℝ)) (B.TC 0) (fun _ => 0) z =
      B.TC 0 (carrierMk38 ((0 : ℕ) : ℝ) z hz') :=
    (carrierCoe38_injective ((0 : ℕ) : ℝ)).extend_apply (B.TC 0) (fun _ => 0)
      (carrierMk38 ((0 : ℕ) : ℝ) z hz')
  unfold cleanT0
  rw [h]
  rfl

theorem measurable_cleanT0 : Measurable B.cleanT0 := by
  let _ : MeasurableSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((0 : ℕ) : ℝ)) := ⟨rfl⟩
  exact (continuous_carrierCoe38 _).measurable.comp
    ((measurableEmbedding_carrierCoe38 ((0 : ℕ) : ℝ)).measurable_extend
      (B.continuous_TC 0).measurable measurable_const)

end BirkhoffTop38


theorem gap_open_of_action_pos38 (u : PhysicalL2) (n : ℤ) (h : 0 < actualGapActionAllE02_38 u n) :
    actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
  by_contra hn
  have h1 : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
    le_antisymm (actualGapLower_le_upper38 u n) (not_lt.1 hn)
  have : actualGapActionAllE02_38 u n = 0 := by
    unfold actualGapActionAllE02_38
    rw [h1, intervalIntegral.integral_same, mul_zero]
  linarith

/-- Each Gaussian coordinate is a.s. nonzero: the planar Gaussian has no atom at `0`. -/
theorem ae_coord_ne_zero_complexGaussian38 (a : ℝ) (ha : 0 < a) :
    ∀ᵐ y ∂(complexGaussian a), y ≠ 0 := by
  rw [complexGaussian_density a ha]
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  exact (Set.countable_singleton (0 : ℂ)).ae_notMem volume

theorem ae_forall_coord_ne_zero38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ z ∂(fullWeightSequenceGaussian c), ∀ n : ℤ, z n ≠ 0 := by
  rw [ae_all_iff]
  intro n
  have h := ae_coord_ne_zero_complexGaussian38 _ (fullWeightRate_pos lower upper c hlower hbound hupper n)
  rw [← fullWeightSequenceGaussian_map_eval] at h
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable h


namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- The measurable set of `H¹` fields all of whose Birkhoff coordinates are nonzero. -/
def posSet38 : Set PhysicalL2 :=
  {u | fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) ∧ ∀ n : ℤ, B.cleanT0 (fourierSeq38 u) n ≠ 0}

theorem measurableSet_posSet38 : MeasurableSet B.posSet38 := by
  refine ((measurableSet_seqSobolev38 _).preimage measurable_fourierSeq38).inter ?_
  have : {u : PhysicalL2 | ∀ n : ℤ, B.cleanT0 (fourierSeq38 u) n ≠ 0} =
      ⋂ n : ℤ, (fun u : PhysicalL2 => B.cleanT0 (fourierSeq38 u) n) ⁻¹' {0}ᶜ := by
    ext u; simp
  show MeasurableSet {u : PhysicalL2 | ∀ n : ℤ, B.cleanT0 (fourierSeq38 u) n ≠ 0}
  rw [this]
  exact MeasurableSet.iInter fun n =>
    ((measurable_pi_apply n).comp (B.measurable_cleanT0.comp measurable_fourierSeq38))
      (measurableSet_singleton (0 : ℂ)).compl

/-- On `posSet38`, every action is strictly positive (`I_n = |Φ_n(u)|²`, field `action`). -/
theorem action_pos_of_mem_posSet38 {u : PhysicalL2} (hu : u ∈ B.posSet38) (n : ℤ) :
    0 < actualGapActionAllE02_38 u n := by
  obtain ⟨h1, h2⟩ := hu
  have hs : SobolevSquareSummable 1 (physicalFourier u) :=
    (fourierSeq38_mem_iff 1 u).1 (by rw [← seqSobolev38_natCast_one]; exact h1)
  rw [← B.action u hs n, ← B.cleanT0_of_mem _ (fourierSeq38_mem_zero u)]
  exact pow_pos (norm_pos_iff.2 (h2 n)) 2

section Props

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- `μ̂_W`-a.e. `z`: `Φ⁻¹ z` has all its Sobolev norms finite, lies in `posSet38`, and the
Birkhoff coordinates of `Φ⁻¹ z` are `z`. -/
theorem ae_muHatW38_good :
    ∀ᵐ z ∂(B.muHatW38 c), (∀ m : ℕ, fourierSeq38 (B.cleanΦinv z) ∈ seqSobolev38 (m : ℝ)) ∧
      B.cleanΦinv z ∈ B.posSet38 ∧ B.Φ (B.cleanΦinv z) = z := by
  have h0 : ∀ᵐ z ∂(fullWeightSequenceGaussian c),
      (∀ m : ℕ, fourierSeq38 (B.cleanΦinv z) ∈ seqSobolev38 (m : ℝ)) ∧
      B.cleanΦinv z ∈ B.posSet38 ∧ B.Φ (B.cleanΦinv z) = z := by
    filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper,
      ae_forall_coord_ne_zero38 lower upper c hlower hbound hupper] with z hz hne
    have hz0 : z ∈ seqSobolev38 0 := seqSobolev38_natCast_mono (mem_seqSobolev38_of_Omega038 c hz 1)
    have hF : ∀ m : ℕ, fourierSeq38 (B.cleanΦinv z) ∈ seqSobolev38 (m : ℝ) := fun m => by
      rw [B.fourierSeq38_cleanΦinv z hz0]
      exact B.mapsTo_Tinv m z (mem_seqSobolev38_of_Omega038 c hz m)
    refine ⟨hF, ⟨hF 1, fun n => ?_⟩, B.Φ_cleanΦinv z hz0⟩
    rw [B.cleanT0_of_mem _ (fourierSeq38_mem_zero _)]
    show B.Φ (B.cleanΦinv z) n ≠ 0
    rw [B.Φ_cleanΦinv z hz0]
    exact hne n
  exact (B.muHatW38_equivalent lower upper c hlower hbound hupper).1.ae_le h0

omit hlower hbound hupper in
theorem measurableSet_allSobolev38 :
    MeasurableSet {u : PhysicalL2 | ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)} := by
  have : {u : PhysicalL2 | ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)} =
      ⋂ m : ℕ, fourierSeq38 ⁻¹' (seqSobolev38 (m : ℝ)) := by ext u; simp
  rw [this]
  exact MeasurableSet.iInter fun m => (measurableSet_seqSobolev38 _).preimage measurable_fourierSeq38

/-- **S04.05 (smooth support in the Sobolev sense, v2 l.432).** `μ_W`-a.e. field lies in `H^m`
for every `m ∈ ℕ`. -/
theorem ae_muW38_allSobolev :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u) := by
  have h : ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) :=
    (ae_map_iff B.measurable_cleanΦinv.aemeasurable measurableSet_allSobolev38).2 (by
      filter_upwards [B.ae_muHatW38_good lower upper c hlower hbound hupper] with z hz using hz.1)
  filter_upwards [h] with u hu m
  exact (fourierSeq38_mem_iff _ u).1 (hu m)

/-- **S04.05 (positivity, v2 l.432-433).** `μ_W`-a.e. field has `I_n(u) > 0` for every `n ∈ ℤ`
(`I_n` the actual gap action), equivalently every gap `g_n(u)` is open. -/
theorem ae_muW38_actions_pos :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n ∧
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
  have h : ∀ᵐ u : PhysicalL2 ∂(B.muW38 c), u ∈ B.posSet38 :=
    (ae_map_iff B.measurable_cleanΦinv.aemeasurable B.measurableSet_posSet38).2 (by
      filter_upwards [B.ae_muHatW38_good lower upper c hlower hbound hupper] with z hz using hz.2.1)
  filter_upwards [h] with u hu n
  exact ⟨B.action_pos_of_mem_posSet38 hu n,
    gap_open_of_action_pos38 u n (B.action_pos_of_mem_posSet38 hu n)⟩

/-- **S04.05 ("not supported on finite-gap fields").** `μ_W`-a.e. field has infinitely many open
gaps (indeed all of them), so it is not a finite-gap field. -/
theorem ae_muW38_not_finiteGap :
    ∀ᵐ u : PhysicalL2 ∂(B.muW38 c),
      ¬ {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite := by
  filter_upwards [B.ae_muW38_actions_pos lower upper c hlower hbound hupper] with u hu hfin
  have : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} = Set.univ :=
    Set.eq_univ_of_forall fun n => (hu n).2
  rw [this] at hfin
  exact Set.infinite_univ hfin

end Props

/-- `ν_Λ` is supported on smooth fields: `ν_Λ`-a.e. field lies in every `H^m`. -/
theorem ae_nu38_allSobolev (c : ℕ → ℝ) (Λ : Finset ℤ) :
    ∀ᵐ u : PhysicalL2 ∂(B.nu38 c Λ), ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u) := by
  have h : ∀ᵐ u : PhysicalL2 ∂(B.nu38 c Λ), ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) :=
    (ae_map_iff (B.measurable_finiteGapField38 Λ).aemeasurable measurableSet_allSobolev38).2
      (Filter.Eventually.of_forall (fun w m => by
        rw [finiteGapField38, B.fourierSeq38_cleanΦinv _ (seqSobolev38_natCast_mono (m := 0)
          (finiteSupport_mem_seqSobolev38 _ _ (by
            rw [← projFin38_extZero38 Λ w]; exact finite_support_projFin38 Λ _)))]
        exact B.mapsTo_Tinv m _ (finiteSupport_mem_seqSobolev38 _ _ (by
          rw [← projFin38_extZero38 Λ w]; exact finite_support_projFin38 Λ _))))
  filter_upwards [h] with u hu m
  exact (fourierSeq38_mem_iff _ u).1 (hu m)

end BirkhoffTop38

end NlsGge.Birkhoff
