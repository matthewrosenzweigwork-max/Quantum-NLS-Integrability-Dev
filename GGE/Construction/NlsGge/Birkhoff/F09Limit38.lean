import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Hierarchy.ExponentialH2Moment38

/-! # NEW-F09 (`F:cor:limit`, v2 l.1702-1722), file 1: the finite-section law `ν_{W,N}` and its bridge to `E_s`

Source: `paper/v2.tex` l.932-938 (`eq:fullbare`, `F:eq:relativeZ`), l.1695-1700 (`F:eq:weights`).
This file is `B`-free. It defines the full-energy Fourier-plane law

`ν_{W,N} = 𝒵_{W,N}⁻¹ e^{-E_W(z)} ∏_{|n|≤N} d²z_n`, pushed to `L²(𝕋)` by the plane embedding `planeL2 N`,

(`nuWN38`, with `E_W = fullEnergy38`, `𝒵_{W,N} = fullPartition38`, `Z_N = relativePartition38`) and proves the
bridge to the `E_s` formulation of W07/W10:

`∫ G dν_{W,N} = Z_N⁻¹ ∫_{E_s} G(𝓕⁻¹P_N x) f_N(x) dγ_W(x)`

for every `G : L² → ℝ` with `G ∘ planeL2 N` measurable (`integral_nuWN38_Es`), in particular for every
`G` whose restriction to `𝓕⁻¹E_s` is continuous (`measurable_comp_planeL2_of_cont38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Law

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

/-- **`ν_{W,N}` (v2 `eq:fullbare`).** `dν_{W,N} = 𝒵_{W,N}⁻¹ e^{-E_W(u)} ∏_{|n|≤N} d²û(n)` on the Fourier plane
`ℂ^{2N+1}` (ordinary product Lebesgue measure `planeVolume N`, all modes `|n| ≤ N` including `n = 0`),
transported to `L²(𝕋)` by the plane embedding `u = ∑_{|n|≤N} z_n e^{2πinx}`. -/
def nuWN38 (N : ℕ) : Measure PhysicalL2 :=
  ENNReal.ofReal (1 / fullPartition38 c N) •
    (((planeVolume N).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)))).map (planeL2 N))

theorem measurableEmbedding_planeL2_38 (N : ℕ) : MeasurableEmbedding (planeL2 N) := by
  have : PolishSpace (FourierPlane N) := inferInstance
  exact (continuous_planeL2 N).measurableEmbedding (planeL2_injective N)

theorem isProbabilityMeasure_nuWN38 (N : ℕ) : IsProbabilityMeasure (nuWN38 c N) := by
  have hint := integrable_exp_neg_fullEnergy38 c N
  have hZ := fullPartition38_pos c N
  refine ⟨?_⟩
  unfold nuWN38
  rw [Measure.smul_apply, Measure.map_apply (measurableEmbedding_planeL2_38 N).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le), smul_eq_mul,
    ← ENNReal.ofReal_mul (one_div_pos.2 hZ).le, one_div]
  have : ∫ x, Real.exp (-fullEnergy38 c N x) ∂(planeVolume N) = fullPartition38 c N := rfl
  rw [this, inv_mul_cancel₀ hZ.ne', ENNReal.ofReal_one]

/-- The Lebesgue form of the integral against `ν_{W,N}`. -/
theorem integral_nuWN38_plane (N : ℕ) (G : PhysicalL2 → ℝ)
    (hG : AEStronglyMeasurable (fun z => G (planeL2 N z)) (planeVolume N)) :
    ∫ u, G u ∂(nuWN38 c N) =
      (1 / fullPartition38 c N) * ∫ z, G (planeL2 N z) * Real.exp (-fullEnergy38 c N z) ∂(planeVolume N) := by
  have hZ := fullPartition38_pos c N
  have hemb := measurableEmbedding_planeL2_38 N
  have hden : Measurable (fun z : FourierPlane N => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z))) :=
    (continuous_fullEnergy38 c N).neg.rexp.measurable.ennreal_ofReal
  have hG' : AEStronglyMeasurable (fun z => G (planeL2 N z))
      ((planeVolume N).withDensity (fun z => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)))) :=
    hG.mono_ac (withDensity_absolutelyContinuous _ _)
  unfold nuWN38
  rw [integral_smul_measure, ENNReal.toReal_ofReal (one_div_pos.2 hZ).le, smul_eq_mul]
  congr 1
  rw [hemb.integral_map, integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  ring

theorem planeGaussPDF_mul_fFourier38 (N : ℕ) (z : FourierPlane N) :
    Real.exp (-fullEnergy38 c N z) = (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) *
      ((∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
          Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2)) * fFourier38 c N z) := by
  have h := fFourier_tilt_pointwise38 c c 0 (by funext j; simp [NlsGge.AblowitzLadik.alTiltCoeff38]) N z
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  rw [h, ← mul_assoc]
  have hpos : ∀ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) ≠ 0 :=
    fun i => (fullWeightRate_pos38 c _).ne'
  have : (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) *
      ∏ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) / Real.pi = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    have := Real.pi_pos.ne'
    field_simp [hpos i]
  rw [this, one_mul]

/-- The Gaussian form: `∫ G dν_{W,N} = Z_N⁻¹ ∫ G(planeL2 z) f_N^F(z) dγ_N(z)`. -/
theorem integral_nuWN38_gauss (N : ℕ) (G : PhysicalL2 → ℝ)
    (hG : AEStronglyMeasurable (fun z => G (planeL2 N z)) (planeVolume N)) :
    ∫ u, G u ∂(nuWN38 c N) = (1 / relativePartition38 c N) *
      ∫ z, G (planeL2 N z) * fFourier38 c N z ∂(fullWeightFourierGaussian N c.val) := by
  have hlo := c.property.1
  have hden := fullWeightFourierGaussian_density lower upper c.val hlo (coef_bound38 c)
    (coef_upper38 c) N
  have hpdfm : Measurable (fun z : FourierPlane N => ENNReal.ofReal
      (∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2))) :=
    (measurable_fullWeightFourierGaussianPDF N c.val).ennreal_ofReal
  have hP := freeNormalizer38_pos c N
  have hpdf0 : ∀ z : FourierPlane N, 0 ≤ ∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
      Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) := fun z =>
    Finset.prod_nonneg fun i _ => mul_nonneg
      (div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le) (Real.exp_pos _).le
  rw [integral_nuWN38_plane c N G hG]
  have e1 : ∫ z, G (planeL2 N z) * Real.exp (-fullEnergy38 c N z) ∂(planeVolume N) =
      (freeNormalizer38 c N) * ∫ z, G (planeL2 N z) * fFourier38 c N z ∂(fullWeightFourierGaussian N c.val) := by
    rw [hden, integral_withDensity_eq_integral_toReal_smul hpdfm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hpdf0 z), smul_eq_mul]
    rw [planeGaussPDF_mul_fFourier38 c N z]
    unfold freeNormalizer38
    ring
  rw [e1]
  unfold relativePartition38
  have hZ := fullPartition38_pos c N
  field_simp

end Law

end NlsGge.Birkhoff
end
