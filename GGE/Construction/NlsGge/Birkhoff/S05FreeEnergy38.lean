import NlsGge.Measure.GibbsVariational38
import NlsGge.Birkhoff.S03Measure38d

/-! # S05 (v2 `A:eq:freeenergy`, l.457-475), part 1: the Gibbs variational characterization of
`μ̂_W` in Birkhoff variables, conditional on `B : BirkhoffTop38`

Source: `paper/v2.tex` l.457-475, blueprint `S05.01`-`S05.04`.

Objects (all from S03):
* `γ_W = fullWeightSequenceGaussian c` on `ℤ → ℂ` (product σ-algebra), a probability measure;
* `R̄_W = B.Rbar38 c`, i.e. `z ↦ R_W(Φ⁻¹ z)` on the `γ_W`-full measurable set `Ω₀`, and the
  arbitrary value `0` off it (v2 l.406); `R̄_W` is measurable and `≥ 0` everywhere;
* `Z_W = B.ZW38 c = ∫ e^{-R̄_W} dγ_W`, `μ̂_W = B.muHatW38 c = Z_W⁻¹ e^{-R̄_W} γ_W`.

Free energy (S05.01): `F(ρ) = Ent(ρ ∣ γ_W) + ∫ R̄_W dρ ∈ [0,∞]` where `Ent = InformationTheory.klDiv`
(`= ∞` unless `ρ ≪ γ_W` and the log-likelihood ratio is `ρ`-integrable; for probability measures
the log-likelihood ratio has an integrable negative part, so this is exactly the usual extended
relative entropy, finite iff `ρ ≪ γ_W` and `∫ log dρ/dγ_W dρ < ∞`) and the second term is the extended
nonnegative integral `∫⁻ ofReal R̄_W dρ`.  `F` does not depend on the values of `R̄_W` on the
`γ_W`-null set `Ω₀ᶜ`: if `F(ρ) < ∞` then `ρ ≪ γ_W` (`freeEnergy_ne_top_ac38`) and `R̄_W` agrees
`ρ`-a.e. with `remainder38 c ∘ cleanΦinv` (`ae_Rbar_eq_remainder_of_ac38`).

All Φ-free statements are in `NlsGge.Measure.GibbsVariational38` (abstract `γ`, `R`); here they are
instantiated.  `B` enters only through `Rbar38` and its measurability and nonnegativity.
-/

set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace NlsGge.Birkhoff

open MeasureTheory InformationTheory NlsGge.Measure NlsGge.Pilot
open scoped ENNReal

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

/-- **S05.01. The free energy** `F(ρ) = Ent(ρ ∣ γ_W) + ∫ R_W(Φ⁻¹ z) dρ(z)` (v2 `A:eq:freeenergy`)
of a measure `ρ` on the Birkhoff coordinates `ℤ → ℂ`, valued in `[0,∞]`.  Convention: the entropy
is `+∞` when `ρ` is not absolutely continuous w.r.t. `γ_W` (or its log-likelihood ratio is not
integrable); the second term is the nonnegative extended integral. -/
def freeEnergyW38 (c : ℕ → ℝ) (ρ : Measure (ℤ → ℂ)) : ℝ≥0∞ :=
  klDiv ρ (fullWeightSequenceGaussian c) + ∫⁻ z, ENNReal.ofReal (B.Rbar38 c z) ∂ρ

theorem freeEnergyW38_eq (c : ℕ → ℝ) (ρ : Measure (ℤ → ℂ)) :
    B.freeEnergyW38 c ρ = freeEnergy38 (fullWeightSequenceGaussian c) (B.Rbar38 c) ρ := rfl

/-- `Z_W` of S03 is the Gibbs partition function of `(γ_W, R̄_W)`. -/
theorem ZW38_eq_gibbsPartition38 :
    B.ZW38 c = gibbsPartition38 (fullWeightSequenceGaussian c) (B.Rbar38 c) := rfl

/-- `F(ρ) < ∞` forces `ρ ≪ γ_W`: a measure that is not absolutely continuous has `Ent = +∞`. -/
theorem freeEnergy_ne_top_ac38 (ρ : Measure (ℤ → ℂ)) (h : B.freeEnergyW38 c ρ ≠ ∞) :
    ρ ≪ fullWeightSequenceGaussian c := by
  by_contra hna
  exact h (by simp [freeEnergyW38, klDiv_of_not_ac hna])

include hlower hbound hupper

/-- `μ̂_W = Z_W⁻¹ e^{-R̄_W} γ_W` is the Gibbs law `γ_W.tilted (-R̄_W)` (v2 `A:eq:limitmeasure`). -/
theorem muHatW38_eq_gibbsLaw38 :
    B.muHatW38 c = gibbsLaw38 (fullWeightSequenceGaussian c) (B.Rbar38 c) := by
  rw [gibbsLaw38_eq_withDensity (fullWeightSequenceGaussian c) (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper)]
  unfold muHatW38
  congr 1
  funext z
  rw [← ZW38_eq_gibbsPartition38 B c, div_eq_inv_mul]

/-- The remainder entering `F` is the genuine `R_W(Φ⁻¹ z)` for `ρ`-almost every `z` whenever
`ρ ≪ γ_W`; its values on the exceptional `γ_W`-null set are irrelevant. -/
theorem ae_Rbar_eq_remainder_of_ac38 (ρ : Measure (ℤ → ℂ))
    (hρ : ρ ≪ fullWeightSequenceGaussian c) :
    ∀ᵐ z ∂ρ, z ∈ Omega038 c ∧ B.Rbar38 c z = remainder38 c (B.cleanΦinv z) := by
  have h : ∀ᵐ z ∂(fullWeightSequenceGaussian c), z ∈ Omega038 c :=
    ae_mem_Omega038 lower upper c hlower hbound hupper
  filter_upwards [hρ.ae_le h] with z hz
  exact ⟨hz, B.Rbar38_of_mem c hz⟩

/-- **Independence of the null-set convention (v2 l.406).** If `R'` agrees with `R̄_W` outside a
`γ_W`-null set, then `Ent(ρ ∣ γ_W) + ∫ R' dρ = F(ρ)` for every measure `ρ` (for `ρ` not
absolutely continuous both sides are `+∞`; otherwise the integrals agree). -/
theorem freeEnergyW38_congr_null (R' : (ℤ → ℂ) → ℝ)
    (hR' : ∀ᵐ z ∂(fullWeightSequenceGaussian c), R' z = B.Rbar38 c z) (ρ : Measure (ℤ → ℂ)) :
    klDiv ρ (fullWeightSequenceGaussian c) + ∫⁻ z, ENNReal.ofReal (R' z) ∂ρ =
      B.freeEnergyW38 c ρ := by
  by_cases hac : ρ ≪ fullWeightSequenceGaussian c
  · unfold freeEnergyW38
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hac.ae_le hR'] with z hz
    rw [hz]
  · simp [freeEnergyW38, klDiv_of_not_ac hac]

/-- **S05.02 (chain identity, extended form).** If `F(ρ) < ∞` for a probability measure `ρ`, then
`F(ρ) = Ent(ρ ∣ μ̂_W) + (-log Z_W)` in `[0,∞]`, i.e.
`Ent(ρ ∣ μ̂_W) = Ent(ρ ∣ γ_W) + ∫ R_W(Φ⁻¹ z) dρ + log Z_W`, all terms finite. -/
theorem freeEnergyW38_chain (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
    (h : B.freeEnergyW38 c ρ ≠ ∞) :
    B.freeEnergyW38 c ρ = klDiv ρ (B.muHatW38 c) + ENNReal.ofReal (-Real.log (B.ZW38 c)) := by
  rw [B.muHatW38_eq_gibbsLaw38 lower upper c hlower hbound hupper]
  exact freeEnergy38_chain (fullWeightSequenceGaussian c) (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper) ρ h

/-- **S05.02 (chain identity, real form; v2 l.464-467).** If `F(ρ) < ∞` then all three terms are
finite (`ρ ≪ γ_W`, the log-likelihood ratio and `R̄_W` are `ρ`-integrable) and
`Ent(ρ ∣ μ̂_W) = Ent(ρ ∣ γ_W) + ∫ R_W(Φ⁻¹ z) dρ(z) + log Z_W`. -/
theorem freeEnergyW38_chain_real (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
    (h : B.freeEnergyW38 c ρ ≠ ∞) :
    ρ ≪ fullWeightSequenceGaussian c ∧
    Integrable (llr ρ (fullWeightSequenceGaussian c)) ρ ∧
    Integrable (B.Rbar38 c) ρ ∧
    klDiv ρ (B.muHatW38 c) ≠ ∞ ∧
    (klDiv ρ (B.muHatW38 c)).toReal =
      (klDiv ρ (fullWeightSequenceGaussian c)).toReal + ∫ z, B.Rbar38 c z ∂ρ +
        Real.log (B.ZW38 c) := by
  have h1 : klDiv ρ (fullWeightSequenceGaussian c) ≠ ∞ := fun e => h (by simp [freeEnergyW38, e])
  have h2 : ∫⁻ z, ENNReal.ofReal (B.Rbar38 c z) ∂ρ ≠ ∞ := fun e => h (by simp [freeEnergyW38, e])
  have hI := integrable_of_freeEnergy_ne_top38 (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper) ρ h2
  obtain ⟨hac, hK⟩ := klDiv_ne_top_iff.mp h1
  rw [B.muHatW38_eq_gibbsLaw38 lower upper c hlower hbound hupper]
  obtain ⟨hne, hre⟩ := toReal_klDiv_gibbs38 (fullWeightSequenceGaussian c) (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper) ρ hac hK hI
  exact ⟨hac, hK, hI, hne, hre⟩

/-- **S05.03.** `R̄_W` is `μ̂_W`-integrable and `∫ R_W(Φ⁻¹ z) dμ̂_W ≤ 1/(e Z_W) < ∞`
(from `r e^{-r} ≤ e^{-1}`, `r ≥ 0`). -/
theorem integral_Rbar_muHatW38_le :
    Integrable (B.Rbar38 c) (B.muHatW38 c) ∧
    ∫ z, B.Rbar38 c z ∂(B.muHatW38 c) ≤ 1 / (Real.exp 1 * B.ZW38 c) := by
  rw [B.muHatW38_eq_gibbsLaw38 lower upper c hlower hbound hupper]
  exact ⟨integrable_gibbsLaw38 _ _ (B.measurable_Rbar38 lower upper c hlower hbound hupper)
      (B.Rbar38_nonneg lower upper c hlower hbound hupper),
    integral_gibbsLaw38_le _ _ (B.measurable_Rbar38 lower upper c hlower hbound hupper)
      (B.Rbar38_nonneg lower upper c hlower hbound hupper)⟩

/-- **S05.03.** `μ̂_W` has finite free energy, equal to `-log Z_W`. -/
theorem freeEnergyW38_muHatW38 :
    B.freeEnergyW38 c (B.muHatW38 c) = ENNReal.ofReal (-Real.log (B.ZW38 c)) ∧
    B.freeEnergyW38 c (B.muHatW38 c) ≠ ∞ := by
  have e : B.freeEnergyW38 c (B.muHatW38 c) = ENNReal.ofReal (-Real.log (B.ZW38 c)) := by
    rw [B.muHatW38_eq_gibbsLaw38 lower upper c hlower hbound hupper]
    exact freeEnergy38_gibbs (fullWeightSequenceGaussian c) (B.Rbar38 c)
      (B.measurable_Rbar38 lower upper c hlower hbound hupper)
      (B.Rbar38_nonneg lower upper c hlower hbound hupper)
  exact ⟨e, by rw [e]; exact ENNReal.ofReal_ne_top⟩

/-- **S05.04, lower bound.** Every probability measure `ρ` has `-log Z_W ≤ F(ρ)` (relative entropy is
nonnegative; for `F(ρ) = ∞` there is nothing to prove). -/
theorem freeEnergyW38_ge (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ] :
    ENNReal.ofReal (-Real.log (B.ZW38 c)) ≤ B.freeEnergyW38 c ρ :=
  freeEnergy38_ge (fullWeightSequenceGaussian c) (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper) ρ

/-- **S05.04, equality case.** `F(ρ) = -log Z_W` iff `ρ = μ̂_W` (relative entropy vanishes exactly when
the measures agree). -/
theorem freeEnergyW38_eq_iff (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ] :
    B.freeEnergyW38 c ρ = ENNReal.ofReal (-Real.log (B.ZW38 c)) ↔ ρ = B.muHatW38 c := by
  rw [B.muHatW38_eq_gibbsLaw38 lower upper c hlower hbound hupper]
  exact freeEnergy38_eq_iff (fullWeightSequenceGaussian c) (B.Rbar38 c)
    (B.measurable_Rbar38 lower upper c hlower hbound hupper)
    (B.Rbar38_nonneg lower upper c hlower hbound hupper) ρ

/-- **S05, the Gibbs variational characterization (v2 `A:eq:freeenergy`, l.458-475).**
In Birkhoff variables `μ̂_W` is the unique minimizer over probability measures `ρ` on `ℤ → ℂ` of
`F(ρ) = Ent(ρ ∣ γ_W) + ∫ R_W(Φ⁻¹ z) dρ(z) ∈ [0,∞]`, and the minimum is `-log Z_W`:
1. `μ̂_W` is a probability measure with finite free energy `F(μ̂_W) = -log Z_W`;
2. `-log Z_W ≤ F(ρ)` for every probability measure `ρ`;
3. `F(ρ) = -log Z_W` only for `ρ = μ̂_W` (so a probability measure with `F(ρ) = ∞` is never a
   minimizer);
4. `∫ R_W(Φ⁻¹ z) dμ̂_W ≤ 1/(e Z_W)`;
5. the chain identity for every probability measure of finite free energy. -/
theorem S05_variational_38 :
    IsProbabilityMeasure (B.muHatW38 c) ∧
    B.freeEnergyW38 c (B.muHatW38 c) = ENNReal.ofReal (-Real.log (B.ZW38 c)) ∧
    B.freeEnergyW38 c (B.muHatW38 c) ≠ ∞ ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      ENNReal.ofReal (-Real.log (B.ZW38 c)) ≤ B.freeEnergyW38 c ρ) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      (B.freeEnergyW38 c ρ = ENNReal.ofReal (-Real.log (B.ZW38 c)) ↔ ρ = B.muHatW38 c)) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → B.freeEnergyW38 c ρ = ∞ →
      B.freeEnergyW38 c ρ ≠ ENNReal.ofReal (-Real.log (B.ZW38 c))) ∧
    ∫ z, B.Rbar38 c z ∂(B.muHatW38 c) ≤ 1 / (Real.exp 1 * B.ZW38 c) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → B.freeEnergyW38 c ρ ≠ ∞ →
      B.freeEnergyW38 c ρ =
        klDiv ρ (B.muHatW38 c) + ENNReal.ofReal (-Real.log (B.ZW38 c))) := by
  refine ⟨B.isProbabilityMeasure_muHatW38 lower upper c hlower hbound hupper,
    (B.freeEnergyW38_muHatW38 lower upper c hlower hbound hupper).1,
    (B.freeEnergyW38_muHatW38 lower upper c hlower hbound hupper).2,
    fun ρ hρ => ?_, fun ρ hρ => ?_, fun ρ hρ h => ?_,
    (B.integral_Rbar_muHatW38_le lower upper c hlower hbound hupper).2,
    fun ρ hρ h => ?_⟩
  · have := hρ
    exact B.freeEnergyW38_ge lower upper c hlower hbound hupper ρ
  · have := hρ
    exact B.freeEnergyW38_eq_iff lower upper c hlower hbound hupper ρ
  · rw [h]; exact ENNReal.top_ne_ofReal
  · have := hρ
    exact B.freeEnergyW38_chain lower upper c hlower hbound hupper ρ h

end BirkhoffTop38

end NlsGge.Birkhoff
