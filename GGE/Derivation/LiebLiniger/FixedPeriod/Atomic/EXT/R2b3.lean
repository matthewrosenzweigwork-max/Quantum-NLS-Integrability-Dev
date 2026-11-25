import LiebLiniger.FixedPeriod.Atomic.EXT.R2b2
import NlsGge.Sobolev.SourceWeighted
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # The actual physical finite-gap Gibbs tilt

The reference is the form-derived physical Liouville measure of R2b2.
Gibbs normalization is literally normalization of its energy-weighted measure.
Positive finite integrability is established from the actual S04 partition
bounds before inverse-mass cancellation or Gibbs transport is used.
-/
set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Measure
open NlsGge.ThirdConsultation.PDE

/-- Gibbs law is literally the energy-weighted reference measure divided by
its total mass. Every subsequent cancellation involving an actual ensemble
uses the positive finite mass established below. -/
def gibbsLaw38 {α : Type*} [MeasurableSpace α] (μ : Measure α) (E : α → ℝ) : Measure α :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (-E x)) ∂μ)⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-E x)))

variable {lower upper : ℝ}

/-- Integrability of the actual finite-plane energy density, earned from
the existing positive S04 coordinate partition theorem. -/
theorem actual_coordinate_energy_integrable38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    Integrable (fun w => Real.exp (-energyW38 c.val
      (actualBirkhoffTop38.finiteGapField38 Λ w))) (finiteComplexVolume Λ) := by
  apply Integrable.of_integral_ne_zero
  exact (actualBirkhoffTop38.ZcalΛ38_pos_le lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ).1.ne'

/-- Nonnegative integral equals the strictly positive finite S04 coordinate
partition; integrability is proved before converting between integrals. -/
theorem actual_coordinate_energy_mass38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (-energyW38 c.val
      (actualBirkhoffTop38.finiteGapField38 Λ w))) ∂finiteComplexVolume Λ) =
        ENNReal.ofReal (actualBirkhoffTop38.ZcalΛ38 c.val Λ) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (actual_coordinate_energy_integrable38 c Λ)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- The coordinate energy-weighted mass is strictly positive and finite
under exactly the bounded positive source coefficient assumptions. -/
theorem actual_coordinate_energy_mass_pos_finite38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    0 < (∫⁻ w, ENNReal.ofReal (Real.exp (-energyW38 c.val
        (actualBirkhoffTop38.finiteGapField38 Λ w))) ∂finiteComplexVolume Λ) ∧
      (∫⁻ w, ENNReal.ofReal (Real.exp (-energyW38 c.val
        (actualBirkhoffTop38.finiteGapField38 Λ w))) ∂finiteComplexVolume Λ) < ∞ := by
  rw [actual_coordinate_energy_mass38]
  exact ⟨ENNReal.ofReal_pos.mpr
    (actualBirkhoffTop38.ZcalΛ38_pos_le lower upper c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ).1,
    ENNReal.ofReal_lt_top⟩

/-- The actual energy density is integrable against the form-derived
physical coordinate Liouville measure. -/
theorem actual_pullPhys_energy_integrable38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    Integrable (fun w => Real.exp (-energyW38 c.val
      (actualBirkhoffTop38.finiteGapField38 Λ w))) (muPullPhys Λ) := by
  rw [muPullPhys_eq]
  exact (actual_coordinate_energy_integrable38 c Λ).smul_measure ENNReal.ofReal_ne_top

/-- The actual energy density is integrable on the entire actual range,
viewed as an ambient physical L² measure. -/
theorem actual_physical_energy_integrable38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    Integrable (fun u => Real.exp (-energyW38 c.val u))
      (inducedFiniteGapPhysicalLiouville38 Λ) := by
  rw [inducedFiniteGapPhysicalLiouville38_eq_map]
  exact (actual_finiteGapField_measurableEmbedding Λ).integrable_map_iff.2
    (actual_pullPhys_energy_integrable38 c Λ)

/-- The absolute physical partition function uses the actual energy and
physical Liouville reference, rather than changing the published coordinate
partition convention. -/
def physicalPartition38 (c : ℕ → ℝ) (Λ : Finset ℤ) : ℝ :=
  ∫ u, Real.exp (-energyW38 c u) ∂inducedFiniteGapPhysicalLiouville38 Λ

/-- Exact factor accounting: the physical absolute partition is 2^|Λ|
times the published ordinary-coordinate partition. -/
theorem physicalPartition38_eq (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    physicalPartition38 c.val Λ =
      (2 : ℝ) ^ Λ.card * actualBirkhoffTop38.ZcalΛ38 c.val Λ := by
  have hi := actual_physical_energy_integrable38 c Λ
  unfold physicalPartition38
  rw [inducedFiniteGapPhysicalLiouville38_eq_map,
    (actual_finiteGapField_measurableEmbedding Λ).integral_map,
    muPullPhys_eq, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
  rfl

/-- Positivity and the finite source upper bound for the physical absolute
partition, with no extra coefficient or cutoff restriction. -/
theorem physicalPartition38_pos_le (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    0 < physicalPartition38 c.val Λ ∧
      physicalPartition38 c.val Λ ≤ (2 : ℝ) ^ Λ.card *
        ∏ i : Λ, (Real.pi / rateΛ38 c.val Λ i) := by
  rw [physicalPartition38_eq c Λ]
  obtain ⟨h₁,h₂⟩ := actualBirkhoffTop38.ZcalΛ38_pos_le lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ
  exact ⟨mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) h₁,
    mul_le_mul_of_nonneg_left h₂ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)⟩

/-- The actual physical energy-weighted mass equals the nonnegative
version of its absolute partition, after integrability has been earned. -/
theorem actual_physical_energy_mass38 (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    (∫⁻ u, ENNReal.ofReal (Real.exp (-energyW38 c.val u))
      ∂inducedFiniteGapPhysicalLiouville38 Λ) =
        ENNReal.ofReal (physicalPartition38 c.val Λ) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (actual_physical_energy_integrable38 c Λ)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- Positive finite physical tilted mass, before Gibbs cancellation. -/
theorem actual_physical_energy_mass_pos_finite38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    0 < (∫⁻ u, ENNReal.ofReal (Real.exp (-energyW38 c.val u))
        ∂inducedFiniteGapPhysicalLiouville38 Λ) ∧
      (∫⁻ u, ENNReal.ofReal (Real.exp (-energyW38 c.val u))
        ∂inducedFiniteGapPhysicalLiouville38 Λ) < ∞ := by
  rw [actual_physical_energy_mass38]
  exact ⟨ENNReal.ofReal_pos.mpr (physicalPartition38_pos_le c Λ).1, ENNReal.ofReal_lt_top⟩

section Transport
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Energy weighting commutes with a measurable embedding. The embedding
allows a weight measurable only on its actual range; no off-range extension
or globally measurable replacement of the physical energy is introduced. -/
theorem withDensity_map_embedding38 {f : α → β} (hf : MeasurableEmbedding f)
    (μ : Measure α) (w : β → ℝ≥0∞) :
    (μ.map f).withDensity w = (μ.withDensity (w ∘ f)).map f := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply hf.measurable hs,
    withDensity_apply _ (hf.measurable hs),
    ← lintegral_indicator hs, hf.lintegral_map,
    ← lintegral_indicator (hf.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ s <;> simp [Set.indicator, hx]

/-- Literal normalization commutes with measurable embedding transport.
This identity uses no cancellation of a zero or infinite tilted mass. -/
theorem gibbsLaw38_map_embedding {f : α → β} (hf : MeasurableEmbedding f)
    (μ : Measure α) (E : β → ℝ) :
    gibbsLaw38 (μ.map f) E = (gibbsLaw38 μ (E ∘ f)).map f := by
  unfold gibbsLaw38
  rw [hf.lintegral_map, withDensity_map_embedding38 hf,
    Measure.map_smul _ hf.measurable.aemeasurable]
  rfl

/-- A strictly positive finite scalar cancels in a Gibbs normalization.
The positive finite tilted mass is explicit, and is discharged by the actual
partition theorems above when this algebraic lemma is used below. -/
theorem gibbsLaw38_smul (μ : Measure α) (E : α → ℝ) (r : ℝ≥0∞)
    (hr₀ : r ≠ 0) (hrTop : r ≠ ∞)
    (hZ : 0 < (∫⁻ x, ENNReal.ofReal (Real.exp (-E x)) ∂μ) ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp (-E x)) ∂μ) < ∞) :
    gibbsLaw38 (r • μ) E = gibbsLaw38 μ E := by
  unfold gibbsLaw38
  rw [lintegral_smul_measure, withDensity_smul_measure, smul_smul]
  congr 1
  rw [smul_eq_mul, ENNReal.mul_inv (Or.inr hZ.2.ne) (Or.inr hZ.1.ne'),
    mul_right_comm, ENNReal.inv_mul_cancel hr₀ hrTop, one_mul]

end Transport

/-- Normalization of the actual ordinary-coordinate energy tilt is exactly
the existing S04 coordinate canonical law, with its published partition. -/
theorem actual_coordinate_gibbs_eq_nuHat38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    gibbsLaw38 (finiteComplexVolume Λ)
      (fun w => energyW38 c.val (actualBirkhoffTop38.finiteGapField38 Λ w)) =
        actualBirkhoffTop38.nuHat38 c.val Λ := by
  have hZ := (actualBirkhoffTop38.ZcalΛ38_pos_le lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ).1
  have hm := actual_coordinate_energy_mass_pos_finite38 c Λ
  unfold gibbsLaw38
  rw [actual_coordinate_energy_mass38]
  unfold BirkhoffTop38.nuHat38
  rw [← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]
  rfl

/-- The physical coordinate Liouville scalar cancels after the positive
finite energy-weighted mass has been proved. -/
theorem actual_pullPhys_gibbs_eq_nuHat38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    gibbsLaw38 (muPullPhys Λ)
      (fun w => energyW38 c.val (actualBirkhoffTop38.finiteGapField38 Λ w)) =
        actualBirkhoffTop38.nuHat38 c.val Λ := by
  rw [muPullPhys_eq, gibbsLaw38_smul _ _ _
    (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)).ne'
    ENNReal.ofReal_ne_top (actual_coordinate_energy_mass_pos_finite38 c Λ)]
  exact actual_coordinate_gibbs_eq_nuHat38 c Λ

/-- The actual energy Gibbs tilt of the induced PHYSICAL symplectic volume
is exactly the existing S04 field law. The full source coefficient bounds
supply all positivity and finiteness; no additional hypothesis is used. -/
theorem actual_finiteGap_canonical_gibbs (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    gibbsLaw38 (inducedFiniteGapPhysicalLiouville38 Λ) (energyW38 c.val) =
      actualBirkhoffTop38.nu38 c.val Λ := by
  have hm := actual_physical_energy_mass_pos_finite38 c Λ
  rw [inducedFiniteGapPhysicalLiouville38_eq_map,
    gibbsLaw38_map_embedding (actual_finiteGapField_measurableEmbedding Λ)]
  change (gibbsLaw38 (muPullPhys Λ)
    (fun w => energyW38 c.val (actualBirkhoffTop38.finiteGapField38 Λ w))).map
      (actualBirkhoffTop38.finiteGapField38 Λ) = _
  rw [actual_pullPhys_gibbs_eq_nuHat38]
  rfl

/-- The physical Gibbs coordinate law retains the exact existing relative
Gaussian density and relative normalizer. -/
theorem actual_pullPhys_gibbs_eq_relative38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    gibbsLaw38 (muPullPhys Λ)
      (fun w => energyW38 c.val (actualBirkhoffTop38.finiteGapField38 Λ w)) =
        (gammaΛ38 c.val Λ).withDensity (fun w => ENNReal.ofReal
          (Real.exp (-actualBirkhoffTop38.Rbar38 c.val (extZero38 Λ w)) /
            actualBirkhoffTop38.ZΛ38 c.val Λ)) := by
  rw [actual_pullPhys_gibbs_eq_nuHat38]
  exact actualBirkhoffTop38.nuHat38_eq_relative lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ

/-- The literal physical Gibbs normalization defines a probability law. -/
theorem actual_finiteGap_gibbs_probability38 (c : BoundedCoefficients lower upper)
    (Λ : Finset ℤ) :
    IsProbabilityMeasure
      (gibbsLaw38 (inducedFiniteGapPhysicalLiouville38 Λ) (energyW38 c.val)) := by
  rw [actual_finiteGap_canonical_gibbs]
  exact actualBirkhoffTop38.isProbabilityMeasure_nu38 lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) Λ

end LiebLiniger.FixedPeriod.EXT
