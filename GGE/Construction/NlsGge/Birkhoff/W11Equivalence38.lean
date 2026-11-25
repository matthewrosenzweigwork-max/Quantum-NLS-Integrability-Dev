import NlsGge.Birkhoff.W10Localized38i
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.S04Moments38b
import NlsGge.Birkhoff.F09Limit38

/-! # W11 (`D:thm:equivalence`, v2 l.1671-1691), part a: the finite-energy laws and the `H²` tail

Source: `paper/v2.tex` l.1666-1670 (`eq:remainingtight`), l.925-935 (`eq:fullbare`), l.1671-1691.

* `nuWN38 c N` (defined in `F09Limit38.lean`): the full-energy Fourier law `ν_{W,N}` of `eq:fullbare` as a genuine `Measure` on `L²`:
  `ν_{W,N} = (planeL2 N)_# (𝒵_{W,N}⁻¹ e^{-E_W(z)} d(planeVolume N)(z))`, with the complete charge series
  `E_W = fullEnergy38` and the ordinary complex Lebesgue volume.
* `h2SqENN38 u = ‖u‖²_{H²} ∈ [0,∞]` (the Fourier convention `Σ⟨n⟩⁴|𝓕u_n|²`, nonnegative extended-real sum)
  and `h2Tail38 R = {u : ‖u‖_{H²} > R}` (for `R ≥ 0`).
* Bridge to the common Gaussian representation: `(P_N-image of f_N γ_W) = Z_N ν_{W,N}`.
* `1 - χ_R ≤ 1_{‖u‖_{H²}>R}` and `χ_R = 0` on `{‖u‖_{H²} > 2R}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section H2

/-- `‖u‖²_{H²} = Σ_n ⟨n⟩⁴ |(𝓕u)_n|²` in `[0,∞]` (v2's Fourier Sobolev convention; `𝓕` is a reflection so
this is the `H²` norm of `u`; same order `(1+1 : ℕ)` as `chiR38`). -/
def h2SqENN38 (u : PhysicalL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n * ‖fourierSeq38 u n‖ ^ 2)

/-- `{u : ‖u‖_{H²} > R}` (for `R ≥ 0`; includes every `u ∉ H²`). -/
def h2Tail38 (R : ℝ) : Set PhysicalL2 := {u | ENNReal.ofReal (R ^ 2) < h2SqENN38 u}

theorem measurable_h2SqENN38 : Measurable h2SqENN38 := by
  unfold h2SqENN38
  refine Measurable.ennreal_tsum fun n => ?_
  refine ENNReal.measurable_ofReal.comp ?_
  have : Measurable (fun u : PhysicalL2 => fourierSeq38 u n) :=
    (measurable_pi_apply n).comp measurable_fourierSeq38
  exact (this.norm.pow_const 2).const_mul _

theorem measurableSet_h2Tail38 (R : ℝ) : MeasurableSet (h2Tail38 R) :=
  measurableSet_lt measurable_const measurable_h2SqENN38

theorem h2Tail38_anti {R R' : ℝ} (h0 : 0 ≤ R) (h : R ≤ R') : h2Tail38 R' ⊆ h2Tail38 R := by
  intro u hu
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by nlinarith)) hu

theorem h2SqENN38_of_mem (u : PhysicalL2) (h : fourierSeq38 u ∈ seqSobolev38 (((1 + 1 : ℕ)) : ℝ)) :
    h2SqENN38 u = ENNReal.ofReal (‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) h‖ ^ 2) := by
  have hs := carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ) (carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) h)
  unfold h2SqENN38
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))
    (by simpa using hs.summable)]
  rw [← hs.tsum_eq]
  simp

theorem mem_of_h2SqENN38_ne_top (u : PhysicalL2) (h : h2SqENN38 u ≠ ⊤) :
    fourierSeq38 u ∈ seqSobolev38 (((1 + 1 : ℕ)) : ℝ) := by
  rw [mem_seqSobolev38_iff]
  have h' : Summable (fun n : ℤ => ENNReal.ofReal (sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n *
      ‖fourierSeq38 u n‖ ^ 2)) := ENNReal.summable
  unfold h2SqENN38 at h
  have := (ENNReal.summable_toReal h)
  refine this.congr fun n => ?_
  exact ENNReal.toReal_ofReal (mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))

/-- `1 - χ_R ≤ 1_{‖u‖_{H²} > R}`: off the tail, `χ_R = 1`. -/
theorem chiR38_eq_one_of_not_tail {χ : ℝ → ℝ} (hχ : CutoffProfile38 χ) {R : ℝ} (hR : 0 < R)
    {u : PhysicalL2} (hu : u ∉ h2Tail38 R) : chiR38 χ R u = 1 := by
  have hu' : h2SqENN38 u ≤ ENNReal.ofReal (R ^ 2) := not_lt.1 hu
  have hmem := mem_of_h2SqENN38_ne_top u (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu')
  rw [h2SqENN38_of_mem u hmem, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hu'
  unfold chiR38
  simp only [hmem, ↓reduceDIte]
  have : ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) hmem‖ ≤ R :=
    abs_le_of_sq_le_sq' (by simpa using hu') hR.le |>.2
  exact hχ.eq_one _ (div_nonneg (norm_nonneg _) hR.le) ((div_le_one hR).2 this)

theorem chiR38_eq_zero_of_mem_tail {χ : ℝ → ℝ} (hχ : CutoffProfile38 χ) {R : ℝ} (hR : 0 < R)
    {u : PhysicalL2} (hu : u ∈ h2Tail38 (2 * R)) : chiR38 χ R u = 0 := by
  unfold chiR38
  split_ifs with hmem
  · have hu : ENNReal.ofReal ((2 * R) ^ 2) < h2SqENN38 u := hu
    rw [h2SqENN38_of_mem u hmem] at hu
    have hu' : (2 * R) ^ 2 < ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) hmem‖ ^ 2 :=
      ((ENNReal.ofReal_lt_ofReal_iff').1 hu).1
    have h2 : 2 * R < ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (fourierSeq38 u) hmem‖ :=
      lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hu'
    exact hχ.eq_zero _ (by rw [le_div_iff₀ hR]; linarith)
  · rfl

end H2


section Law

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

/- `nuWN38 c N` (v2 `eq:fullbare`) is defined in `F09Limit38.lean` (identical definition:
`ofReal (1/𝒵_{W,N}) • (planeL2 N)_#((planeVolume N).withDensity (e^{-E_W}))`). -/

theorem measurable_expNegEnergy38 (N : ℕ) :
    Measurable (fun z : FourierPlane N => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z))) :=
  ((continuous_fullEnergy38 c N).neg.rexp).measurable.ennreal_ofReal

theorem lintegral_nuWN38 (N : ℕ) (φ : PhysicalL2 → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ u, φ u ∂(nuWN38 c N) = ENNReal.ofReal (1 / fullPartition38 c N) *
      ∫⁻ w, φ (planeL2 N w) * ENNReal.ofReal (Real.exp (-fullEnergy38 c N w)) ∂(planeVolume N) := by
  unfold nuWN38
  rw [lintegral_smul_measure, lintegral_map hφ (continuous_planeL2 N).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_expNegEnergy38 c N)
      (show Measurable (fun a => φ (planeL2 N a)) from hφ.comp (continuous_planeL2 N).measurable)]
  simp only [smul_eq_mul, Pi.mul_apply]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [mul_comm]

theorem planeMeasurable_planeOfSeq38 (N : ℕ) : Measurable (planeOfSeq38 N) := by
  unfold planeOfSeq38 reflectPlane
  exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).neg.comp
    (measurable_pi_iff.2 fun j => measurable_pi_apply _)

theorem prodRatio38 (N : ℕ) :
    relativePartition38 c N * (1 / fullPartition38 c N) =
      ∏ i : Fin (2 * N + 1), (fullWeightRate c.val (modeIndex N i) / Real.pi) := by
  have hZ := (fullPartition38_pos c N).ne'
  unfold relativePartition38 freeNormalizer38
  have h1 : ∏ i : Fin (2 * N + 1), (Real.pi / fullWeightRate c.val (modeIndex N i)) =
      (∏ i : Fin (2 * N + 1), (fullWeightRate c.val (modeIndex N i) / Real.pi))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (inv_div _ _).symm
  rw [h1]
  have hP : (∏ i : Fin (2 * N + 1), (fullWeightRate c.val (modeIndex N i) / Real.pi)) ≠ 0 :=
    (Finset.prod_pos fun i _ => div_pos (fullWeightRate_pos38 c _) Real.pi_pos).ne'
  field_simp

variable (s : ℝ)

/-- **Bridge to the common Gaussian representation.** For measurable `φ ≥ 0` on `L²`:
`∫ φ(𝓕⁻¹P_N x) f_N(x) dγ_W = Z_N ∫ φ dν_{W,N}`. -/
theorem lintegral_bridge38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) (φ : PhysicalL2 → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ x, φ (physOfE38 c s (projE38 c s N x)) * ENNReal.ofReal (fN38 c s N x)
        ∂(fullWeightedSequenceGaussian c s) =
      ENNReal.ofReal (relativePartition38 c N) * ∫⁻ u, φ u ∂(nuWN38 c N) := by
  set G : (ℤ → ℂ) → ℝ≥0∞ := fun z => φ (planeL2 N (planeOfSeq38 N z)) *
    ENNReal.ofReal (fNseq38 c N z) with hG
  have hm : Measurable (planeOfSeq38 N) := planeMeasurable_planeOfSeq38 N
  have hG' : Measurable G :=
    (hφ.comp ((continuous_planeL2 N).measurable.comp hm)).mul
      (measurable_fNseq38 c N).ennreal_ofReal
  have hA : ∫⁻ x, φ (physOfE38 c s (projE38 c s N x)) * ENNReal.ofReal (fN38 c s N x)
        ∂(fullWeightedSequenceGaussian c s) =
      ∫⁻ x, G (coordE c s x) ∂(fullWeightedSequenceGaussian c s) := by
    refine lintegral_congr fun x => ?_
    simp only [hG, physOfE38_projE38_W07, fN38_eq_fNseq]
  rw [hA, lintegral_comp_coordE c s hs hG'.aemeasurable]
  -- to the plane
  set H : FourierPlane N → ℝ≥0∞ := fun w => φ (planeL2 N w) * ENNReal.ofReal (fFourier38 c N w)
    with hH
  have hFc : Continuous (fFourier38 c N) :=
    Real.continuous_exp.comp (((continuous_fullEnergy38 c N).neg).add
      (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((continuous_norm.comp (continuous_apply i)).pow 2)))
  have hH' : Measurable H :=
    (hφ.comp (continuous_planeL2 N).measurable).mul
      (hFc.measurable.ennreal_ofReal)
  have hGH : G = H ∘ planeOfSeq38 N := rfl
  have e1 : ∫⁻ z, G z ∂(fullWeightSequenceGaussian c.val) =
      ∫⁻ w, H w ∂(fullWeightFourierGaussian N c.val) := by
    rw [← map_planeOfSeq38 c N, lintegral_map hH' hm]; rfl
  rw [e1,
    fullWeightFourierGaussian_density lower upper c.val c.property.1 (coef_bound38 c)
      (coef_upper38 c) N,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_fullWeightFourierGaussianPDF N c.val).ennreal_ofReal hH']
  rw [lintegral_nuWN38 c N φ hφ, ← mul_assoc, ← ENNReal.ofReal_mul (relativePartition38_pos c N).le,
    prodRatio38 c N, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  have h := fFourier_tilt_pointwise38 c c 0 (by rw [alTiltCoeff38_zero]) N w
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  simp only [Pi.mul_apply, hH]
  rw [show ENNReal.ofReal (∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi)) *
      (φ (planeL2 N w) * ENNReal.ofReal (Real.exp (-fullEnergy38 c N w))) =
      φ (planeL2 N w) * (ENNReal.ofReal (∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi)) *
        ENNReal.ofReal (Real.exp (-fullEnergy38 c N w))) by ring,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ =>
      div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le), ← h,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => mul_nonneg
      (div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le) (Real.exp_pos _).le)]
  ring


/-- `P_N` read as a self-map of `E_s = FullWeightedHilbert c s` (type with a measurable space). -/
def projFW38 (N : ℕ) (x : FullWeightedHilbert c s) : FullWeightedHilbert c s := projE38 c s N x

theorem continuous_projFW38 (N : ℕ) : Continuous (projFW38 c s N) :=
  (projE38 c s N).continuous

theorem measurable_physProj38 (N : ℕ) :
    Measurable (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x)) :=
  (continuous_physFW06_38 c s).measurable.comp (continuous_projFW38 c s N).measurable

/-- `ν_{W,N}` through the common Gaussian representation:
`ν_{W,N} = Z_N⁻¹ (𝓕⁻¹P_N)_#(f_N γ_W)`. -/
theorem nuWN38_eq_map (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    nuWN38 c N = ENNReal.ofReal (1 / relativePartition38 c N) •
      ((fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (fN38 c s N x))).map
        (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x)) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hZ := relativePartition38_pos c N
  have hf : Measurable (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x)) :=
    (measurable_fN38 c s N).ennreal_ofReal
  rw [lintegral_smul_measure, lintegral_map hφ (measurable_physProj38 c s N),
    lintegral_withDensity_eq_lintegral_mul _ hf (show Measurable
      (fun a : FullWeightedHilbert c s => φ (physOfE38 c s (projE38 c s N a))) from
        hφ.comp (measurable_physProj38 c s N))]
  simp only [Pi.mul_apply, smul_eq_mul]
  have := lintegral_bridge38 c s hs N φ hφ
  have e : ∫⁻ x, ENNReal.ofReal (fN38 c s N x) * φ (physOfE38 c s (projE38 c s N x))
        ∂(fullWeightedSequenceGaussian c s) =
      ∫⁻ x, φ (physOfE38 c s (projE38 c s N x)) * ENNReal.ofReal (fN38 c s N x)
        ∂(fullWeightedSequenceGaussian c s) :=
    lintegral_congr fun x => mul_comm _ _
  rw [e, this, ← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.2 hZ).le, one_div_mul_cancel hZ.ne',
    ENNReal.ofReal_one, one_mul]

/-- A function on `L²` continuous on `𝓕⁻¹E_s` is `ν_{W,N}`-a.e. strongly measurable. -/
theorem aestronglyMeasurable_nuWN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) :
    AEStronglyMeasurable F (nuWN38 c N) := by
  rw [nuWN38_eq_map c s hs N]
  refine AEStronglyMeasurable.smul_measure ?_ _
  have hmp : (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x)) =
      (physFW06_38 c s) ∘ (projFW38 c s N) := rfl
  rw [hmp, ← Measure.map_map (continuous_physFW06_38 c s).measurable
    (continuous_projFW38 c s N).measurable,
    (measurableEmbedding_physFW06_38 c s).aestronglyMeasurable_map_iff]
  have hF' : Continuous (fun y : FullWeightedHilbert c s => F (physOfE38 c s y)) := hF
  exact hF'.aestronglyMeasurable


/-- `ν_{W,N}` is concentrated on `𝓕⁻¹E_s` (indeed on trigonometric polynomials). -/
theorem ae_mem_range_nuWN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    ∀ᵐ u ∂(nuWN38 c N), u ∈ Set.range (physOfE38 c s) := by
  rw [nuWN38_eq_map c s hs N]
  refine Measure.ae_smul_measure ?_ _
  have hr : MeasurableSet (Set.range (physOfE38 c s)) :=
    (measurableEmbedding_physFW06_38 c s).measurableSet_range
  refine (ae_map_iff (measurable_physProj38 c s N).aemeasurable hr).2 ?_
  exact Filter.Eventually.of_forall fun x => ⟨projE38 c s N x, rfl⟩

/-- **Integral against `ν_{W,N}` in the common representation.** For `F` continuous on `𝓕⁻¹E_s`:
`∫ F dν_{W,N} = Z_N⁻¹ ∫ F(𝓕⁻¹P_N x) f_N(x) dγ_W(x)`. -/
theorem integral_nuWN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) :
    ∫ u, F u ∂(nuWN38 c N) = (1 / relativePartition38 c N) *
      ∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s) := by
  have hZ := relativePartition38_pos c N
  have hf : AEMeasurable (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x))
      (fullWeightedSequenceGaussian c s) := (measurable_fN38 c s N).ennreal_ofReal.aemeasurable
  have hF' : Continuous (fun y : FullWeightedHilbert c s => F (physOfE38 c s y)) := hF
  have hmp : (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x)) =
      (physFW06_38 c s) ∘ (projFW38 c s N) := rfl
  have hasm : AEStronglyMeasurable F (((fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (fN38 c s N x))).map
        (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x))) := by
    rw [hmp, ← Measure.map_map (continuous_physFW06_38 c s).measurable
      (continuous_projFW38 c s N).measurable,
      (measurableEmbedding_physFW06_38 c s).aestronglyMeasurable_map_iff]
    exact hF'.aestronglyMeasurable
  rw [nuWN38_eq_map c s hs N, integral_smul_measure,
    ENNReal.toReal_ofReal (one_div_pos.2 hZ).le, smul_eq_mul,
    integral_map (measurable_physProj38 c s N).aemeasurable hasm,
    integral_withDensity_eq_integral_toReal_smul₀ hf
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (fN38_pos c s N x).le, smul_eq_mul]
  ring

/-- `F` bounded and `𝓕⁻¹E_s`-continuous is `ν_{W,N}`-integrable. -/
theorem integrable_nuWN38_W11 (hs : (1 : ℝ) / 2 < s) (N : ℕ) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (M : ℝ) (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Integrable F (nuWN38 c N) := by
  have := isProbabilityMeasure_nuWN38 c N
  refine Integrable.of_bound (aestronglyMeasurable_nuWN38 c s hs N F hF) M ?_
  filter_upwards [ae_mem_range_nuWN38 c s hs N] with u hu
  obtain ⟨y, rfl⟩ := hu
  exact hM y

end Law

end NlsGge.Birkhoff
end
