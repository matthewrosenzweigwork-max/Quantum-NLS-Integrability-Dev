import NlsGge.Birkhoff.S03Measure38c
import NlsGge.Definitions.BorelL2

/-! # S03, part 4: measurability of the remainder and the limiting measures `Z_W, μ̂_W, μ_W`

v2 lines 397-411 (`A:eq:limitmeasure`), conditional on `B : BirkhoffTop38`.

* `Rbar38`: `R_W(Φ⁻¹ z)` on the full-measure set `Ω₀` and `0` on its (null) complement ("values on
  the exceptional null set may be chosen arbitrarily", v2 l.406).
* Its measurability is proved explicitly (limit of measurable finite partial sums).
* `Z_W`, `μ̂_W = Z_W⁻¹ e^{-R_W(Φ⁻¹ z)} γ_W` and `μ_W = (Φ⁻¹)_# μ̂_W` are defined; `0 < Z_W ≤ 1`,
  `μ̂_W` is a probability measure equivalent to `γ_W`, and `μ_W` is a probability measure on the
  project's Borel `PhysicalL2` (instance `NlsGge.Pilot.physicalL2MeasurableSpace`).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal

/-- The standard exhaustion `Λ_N = {-N, …, N}`. -/
def stdExh38 (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem isExhaustion_stdExh38 : IsExhaustion38 stdExh38 :=
  ⟨fun a b hab => Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab),
    fun n => ⟨n.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- The `n`-th remainder summand, written as a function of the Birkhoff coordinates `z`
(through the cleaned carrier inverse, hence measurable in `z`). -/
def summandZ38 (c : ℕ → ℝ) (n : ℤ) (z : ℤ → ℂ) : ℝ :=
  gapFn38 c n (B.cleanTinvC 1 z) - fullWeightRate c n * ‖z n‖ ^ 2

theorem summandZ38_eq (c : ℕ → ℝ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    B.summandZ38 c n z = remainderSummand38 c (B.cleanΦinv z) n := by
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv z)) := by
    simpa using B.sobolev_cleanΦinv38 1 z hz
  unfold summandZ38 remainderSummand38
  rw [B.action_cleanΦinv38 z hz n, gapIntegral38_eq_gapFn38 c _ hs n,
    B.cleanTinvC_of_mem 1 z hz]
  congr 2
  exact carrierExt38 (by
    show B.Tinv z = fourierSeq38 (B.cleanΦinv z)
    exact (B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz)).symm)

theorem measurable_summandZ38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (n : ℤ) :
    Measurable (B.summandZ38 c n) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := ⟨rfl⟩
  unfold summandZ38
  exact ((continuous_gapFn38 c hW n).measurable.comp (B.measurable_cleanTinvC 1)).sub
    (((measurable_pi_apply n).norm.pow_const 2).const_mul _)

/-- `R_W(Φ⁻¹ z)` on `Ω₀`; the arbitrary value `0` on the `γ_W`-null complement. -/
def Rbar38 (c : ℕ → ℝ) (z : ℤ → ℂ) : ℝ :=
  by classical exact if z ∈ Omega038 c then remainder38 c (B.cleanΦinv z) else 0

theorem Rbar38_of_mem (c : ℕ → ℝ) {z : ℤ → ℂ} (hz : z ∈ Omega038 c) :
    B.Rbar38 c z = remainder38 c (B.cleanΦinv z) := by
  unfold Rbar38; simp only [hz, ↓reduceIte]

theorem Rbar38_of_not_mem (c : ℕ → ℝ) {z : ℤ → ℂ} (hz : z ∉ Omega038 c) : B.Rbar38 c z = 0 := by
  unfold Rbar38; simp only [hz, ↓reduceIte]

theorem Rbar38_nonneg (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℤ → ℂ) :
    0 ≤ B.Rbar38 c z := by
  by_cases hz : z ∈ Omega038 c
  · rw [B.Rbar38_of_mem c hz]
    exact (B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper z hz
      isExhaustion_stdExh38).2.2.2.2
  · rw [B.Rbar38_of_not_mem c hz]

/-- Explicit measurability: `R̄_W` is the everywhere limit of the measurable partial sums
`1_{Ω₀} ∑_{|n|≤M} summandZ`. -/
theorem measurable_Rbar38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    Measurable (B.Rbar38 c) := by
  classical
  have hW := weight_continuous38 hlower hbound hupper
  have hΩ := measurableSet_Omega038 lower upper c hlower hbound hupper
  refine measurable_of_tendsto_metrizable (f := fun M : ℕ => fun z : ℤ → ℂ =>
    if z ∈ Omega038 c then ∑ n ∈ stdExh38 M, B.summandZ38 c n z else 0) (fun M => ?_) ?_
  · exact Measurable.ite hΩ (Finset.measurable_sum _ (fun n _ => B.measurable_summandZ38 c hW n))
      measurable_const
  · rw [tendsto_pi_nhds]
    intro z
    by_cases hz : z ∈ Omega038 c
    · simp only [hz, ↓reduceIte]
      rw [B.Rbar38_of_mem c hz]
      have hz1 := mem_seqSobolev38_of_Omega038 c hz 1
      obtain ⟨hsum, -, -, -, -⟩ := B.remainder_tendsto_pathwise38 lower upper c hlower hbound hupper
        z hz isExhaustion_stdExh38
      have hs : Summable (fun n : ℤ => B.summandZ38 c n z) :=
        hsum.congr (fun n => (B.summandZ38_eq c z hz1 n).symm)
      have h : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, B.summandZ38 c n z) atTop
          (𝓝 (∑' n : ℤ, B.summandZ38 c n z)) := hs.hasSum
      have e : ∑' n : ℤ, B.summandZ38 c n z = remainder38 c (B.cleanΦinv z) :=
        tsum_congr (fun n => B.summandZ38_eq c z hz1 n)
      rw [← e]
      exact h.comp isExhaustion_stdExh38.tendsto_atTop
    · simp only [hz, ↓reduceIte]
      rw [B.Rbar38_of_not_mem c hz]
      exact tendsto_const_nhds

/-! ### `Z_W`, `μ̂_W`, `μ_W` (v2 `A:eq:limitmeasure`) -/

/-- `Z_W = ∫ e^{-R_W(Φ⁻¹ z)} dγ_W(z)`. -/
def ZW38 (c : ℕ → ℝ) : ℝ := ∫ z, Real.exp (-(B.Rbar38 c z)) ∂(fullWeightSequenceGaussian c)

/-- `μ̂_W = Z_W⁻¹ e^{-R_W(Φ⁻¹ z)} γ_W`, as a density measure on the Birkhoff-coordinate space. -/
def muHatW38 (c : ℕ → ℝ) : Measure (ℤ → ℂ) :=
  (fullWeightSequenceGaussian c).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-(B.Rbar38 c z)) / B.ZW38 c))

/-- `μ_W = (Φ⁻¹)_# μ̂_W`, on the project's Borel `PhysicalL2`; the push-forward is by the cleaned
inverse, which is the actual `Φ⁻¹` on the support (see `ae_cleanΦinv_eq_Φinv38`). -/
def muW38 (c : ℕ → ℝ) : Measure PhysicalL2 := (B.muHatW38 c).map B.cleanΦinv

section Props

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

omit hlower hbound hupper in
theorem exp_neg_Rbar38_pos (z : ℤ → ℂ) : 0 < Real.exp (-(B.Rbar38 c z)) := Real.exp_pos _

theorem exp_neg_Rbar38_le_one (z : ℤ → ℂ) : Real.exp (-(B.Rbar38 c z)) ≤ 1 := by
  have := B.Rbar38_nonneg lower upper c hlower hbound hupper z
  rw [Real.exp_le_one_iff]; linarith

theorem measurable_exp_neg_Rbar38 : Measurable (fun z => Real.exp (-(B.Rbar38 c z))) :=
  Real.measurable_exp.comp (B.measurable_Rbar38 lower upper c hlower hbound hupper).neg

theorem integrable_exp_neg_Rbar38 :
    Integrable (fun z => Real.exp (-(B.Rbar38 c z))) (fullWeightSequenceGaussian c) :=
  Integrable.of_bound (B.measurable_exp_neg_Rbar38 lower upper c hlower hbound hupper).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper z)

/-- **`0 < Z_W ≤ 1`** (v2 l.411). -/
theorem ZW38_pos_le_one : 0 < B.ZW38 c ∧ B.ZW38 c ≤ 1 := by
  constructor
  · unfold ZW38
    rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le)
      (B.integrable_exp_neg_Rbar38 lower upper c hlower hbound hupper)]
    have : Function.support (fun z => Real.exp (-(B.Rbar38 c z))) = Set.univ :=
      Set.eq_univ_of_forall fun z => (Real.exp_pos _).ne'
    rw [this]; simp
  · unfold ZW38
    calc ∫ z, Real.exp (-(B.Rbar38 c z)) ∂(fullWeightSequenceGaussian c)
        ≤ ∫ _z, (1 : ℝ) ∂(fullWeightSequenceGaussian c) :=
          integral_mono (B.integrable_exp_neg_Rbar38 lower upper c hlower hbound hupper)
            (integrable_const _) (fun z => B.exp_neg_Rbar38_le_one lower upper c hlower hbound hupper z)
      _ = 1 := by simp

theorem measurable_density38 :
    Measurable (fun z => ENNReal.ofReal (Real.exp (-(B.Rbar38 c z)) / B.ZW38 c)) :=
  ((B.measurable_exp_neg_Rbar38 lower upper c hlower hbound hupper).div_const _).ennreal_ofReal

/-- `μ̂_W` is a probability measure. -/
theorem isProbabilityMeasure_muHatW38 : IsProbabilityMeasure (B.muHatW38 c) := by
  refine ⟨?_⟩
  have hZ := (B.ZW38_pos_le_one lower upper c hlower hbound hupper).1
  unfold muHatW38
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((B.integrable_exp_neg_Rbar38 lower upper c hlower hbound hupper).div_const _)
      (Filter.Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hZ.le),
    integral_div]
  change ENNReal.ofReal (B.ZW38 c / B.ZW38 c) = 1
  rw [div_self hZ.ne']; simp

/-- `γ_W ≪ μ̂_W` and `μ̂_W ≪ γ_W`: the two measures are equivalent (v2 l.411). -/
theorem muHatW38_equivalent :
    B.muHatW38 c ≪ fullWeightSequenceGaussian c ∧ fullWeightSequenceGaussian c ≪ B.muHatW38 c := by
  have hZ := (B.ZW38_pos_le_one lower upper c hlower hbound hupper).1
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  exact withDensity_absolutelyContinuous'
    (B.measurable_density38 lower upper c hlower hbound hupper).aemeasurable
    (Filter.Eventually.of_forall fun z => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact div_pos (Real.exp_pos _) hZ)

/-- On the support `Ω₀` of `γ_W` (hence `μ̂_W`-a.e.), `Φ⁻¹` is the actual inverse: the cleaned
inverse equals `Φinv`, and `Φ(Φ⁻¹ z) = z`. -/
theorem ae_cleanΦinv_eq_Φinv38 :
    ∀ᵐ z ∂(B.muHatW38 c), ∃ hz : z ∈ seqSobolev38 0,
      B.cleanΦinv z = B.Φinv z hz ∧ B.Φ (B.cleanΦinv z) = z := by
  have h0 : ∀ᵐ z ∂(fullWeightSequenceGaussian c), ∃ hz : z ∈ seqSobolev38 0,
      B.cleanΦinv z = B.Φinv z hz ∧ B.Φ (B.cleanΦinv z) = z := by
    filter_upwards [ae_mem_Omega038 lower upper c hlower hbound hupper] with z hz
    have hz0 : z ∈ seqSobolev38 0 := seqSobolev38_natCast_mono (mem_seqSobolev38_of_Omega038 c hz 1)
    exact ⟨hz0, B.cleanΦinv_of_mem z hz0, B.Φ_cleanΦinv z hz0⟩
  exact (B.muHatW38_equivalent lower upper c hlower hbound hupper).1.ae_le h0

/-- `μ_W` is a probability measure on `PhysicalL2` (Borel σ-algebra of the project's instance). -/
theorem isProbabilityMeasure_muW38 : IsProbabilityMeasure (B.muW38 c) := by
  have := B.isProbabilityMeasure_muHatW38 lower upper c hlower hbound hupper
  refine ⟨?_⟩
  unfold muW38
  rw [Measure.map_apply B.measurable_cleanΦinv MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

end Props

end BirkhoffTop38

end NlsGge.Birkhoff
end
