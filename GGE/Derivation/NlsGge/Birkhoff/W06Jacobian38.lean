import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.S03Measure38d
import NlsGge.Ramer.RamerTheorem

/-! # W06 (`D:thm:Ramer`, v2 l.1521-1543), part 1: instantiation of Ramer's theorem on `E_s`

Source: `paper/v2.tex` l.1521-1543. Conditional on `B : BirkhoffInput38` and
`O : OneSmoothingInput38 B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights Filter Topology
open scoped ENNReal Real

section Incl

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

theorem cmModeWeight_le_two_fullModeWeight_zero38 (n : ℤ) :
    cmModeWeight c n ≤ 2 * fullModeWeight c 0 n := by
  unfold cmModeWeight fullModeWeight
  simp [Real.rpow_zero]

/-- The identity on Fourier sequences, `E_0 → H = ActualCM c` (the Cameron-Martin space; `E_0 = H`
by `mem_seqE38_zero_iff_cm`). -/
def cmOfE0_38 : ECarrier38 c 0 →L[ℝ] NlsGge.Ramer.ActualCM c :=
  weightedRealComparisonContinuous (fullModeWeight c 0) (cmModeWeight c) 2 (by norm_num)
    (cmModeWeight_le_two_fullModeWeight_zero38 c)

theorem cmCoord_cmOfE0_38 (y : ECarrier38 c 0) (n : ℤ) :
    NlsGge.Ramer.cmCoord (cmOfE0_38 c y) n = eCoe38 c 0 y n := rfl

end Incl


namespace BirkhoffInput38

variable {lower upper : ℝ} (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- `K = T - Id : E_s → H` (v2: "`K : E → H`"), `E_s → E_0 = H`, for `s ≤ 1`. -/
def KW06_38 (hs : s ≤ 1) : ECarrier38 c s → NlsGge.Ramer.ActualCM c :=
  fun x => cmOfE0_38 c (eMap38 c s 0 (fun y => B.T y - y) (B.differences_mem_E0_38 O c hs).1 x)

/-- `T⁻¹ - Id : E_s → H`. -/
def KinvW06_38 (hs : s ≤ 1) : ECarrier38 c s → NlsGge.Ramer.ActualCM c :=
  fun x => cmOfE0_38 c (eMap38 c s 0 (fun y => B.Tinv y - y) (B.differences_mem_E0_38 O c hs).2 x)

theorem cmCoord_KW06_38 (hs1 : s ≤ 1) (x : ECarrier38 c s) (n : ℤ) :
    NlsGge.Ramer.cmCoord (B.KW06_38 O c hs1 x) n = B.T (eCoe38 c s x) n - eCoe38 c s x n := rfl

theorem cmCoord_KinvW06_38 (hs1 : s ≤ 1) (x : ECarrier38 c s) (n : ℤ) :
    NlsGge.Ramer.cmCoord (B.KinvW06_38 O c hs1 x) n = B.Tinv (eCoe38 c s x) n - eCoe38 c s x n := rfl

theorem analytic_KW06_38 (hs : s ≤ 1) : AnalyticOnNhd ℝ (B.KW06_38 O c hs) Set.univ := by
  have h := (B.analytic_differences_E0_38 O c hs).1
  exact ((cmOfE0_38 c).analyticOnNhd _).comp h (fun _ _ => Set.mem_univ _)

theorem analytic_KinvW06_38 (hs : s ≤ 1) : AnalyticOnNhd ℝ (B.KinvW06_38 O c hs) Set.univ := by
  have h := (B.analytic_differences_E0_38 O c hs).2
  exact ((cmOfE0_38 c).analyticOnNhd _).comp h (fun _ _ => Set.mem_univ _)

theorem eCoe_inclE_38 (hs : (1 : ℝ) / 2 < s) (h : NlsGge.Ramer.ActualCM c) (n : ℤ) :
    eCoe38 c s (NlsGge.Ramer.inclE c s hs h) n = NlsGge.Ramer.cmCoord h n := rfl

theorem hT_W06_38 (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) (x : ECarrier38 c s) :
    B.weightedHomeoE38 O c s x =
      x + (show ECarrier38 c s from NlsGge.Ramer.inclE c s hs (B.KW06_38 O c hs1 x)) := by
  refine eExt38 c s (funext fun n => ?_)
  rw [B.weightedHomeoE38_apply O c s x, eAdd_apply38, eCoe_inclE_38, cmCoord_KW06_38]
  ring

theorem hTs_W06_38 (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) (y : ECarrier38 c s) :
    (B.weightedHomeoE38 O c s).symm y =
      y + (show ECarrier38 c s from NlsGge.Ramer.inclE c s hs (B.KinvW06_38 O c hs1 y)) := by
  refine eExt38 c s (funext fun n => ?_)
  rw [B.weightedHomeoE38_symm_apply O c s y, eAdd_apply38, eCoe_inclE_38, cmCoord_KinvW06_38]
  ring

end BirkhoffInput38


/-! ## The physical embedding `𝓕⁻¹ : E_s → L²` and the pointwise identities -/

section Embedding

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem sobolevModeWeight_zero38 (n : ℤ) : sobolevModeWeight 0 n = 1 := by
  simp [sobolevModeWeight]

theorem norm_sq_physOfE38_sub_le (x y : ECarrier38 c s) :
    ‖physOfE38 c s x - physOfE38 c s y‖ ^ 2 ≤
      sourceSobolevBound lower upper 0 s c.property.1 * ‖x - y‖ ^ 2 := by
  have h2 := (mem_seqE38_iff c s _).1 (eCoe38_mem c s (x - y))
  have hdom : ∀ n : ℤ, ‖eCoe38 c s (x - y) n‖ ^ 2 ≤
      sourceSobolevBound lower upper 0 s c.property.1 *
        (fullModeWeight c s n * ‖eCoe38 c s (x - y) n‖ ^ 2) := by
    intro n
    have := sourceSobolevBound_dominates lower upper 0 s c.property.1 c n
    rw [sobolevModeWeight_zero38] at this
    rw [← mul_assoc]
    calc ‖eCoe38 c s (x - y) n‖ ^ 2 = 1 * ‖eCoe38 c s (x - y) n‖ ^ 2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have e : ∀ n : ℤ, fourierSeq38 (physOfE38 c s x - physOfE38 c s y) n =
      eCoe38 c s (x - y) n := by
    intro n
    rw [fourierSeq38_sub]
    show fourierSeq38 (physOfE38 c s x) n - fourierSeq38 (physOfE38 c s y) n = _
    rw [fourierSeq38_physOfE38, fourierSeq38_physOfE38]
    rfl
  rw [norm_sq_eq_tsum_fourierSeq38, norm_sq_eCarrier38, ← tsum_mul_left]
  simp only [e]
  exact Summable.tsum_le_tsum hdom (Summable.of_nonneg_of_le (fun n => sq_nonneg _) hdom
    (h2.mul_left _)) (h2.mul_left _)

theorem continuous_physOfE38 : Continuous (physOfE38 c s) := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨Real.sqrt (sourceSobolevBound lower upper 0 s c.property.1),
      Real.sqrt_nonneg _⟩) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have h := norm_sq_physOfE38_sub_le c s x y
  show ‖physOfE38 c s x - physOfE38 c s y‖ ≤ Real.sqrt _ * ‖x - y‖
  rw [← Real.sqrt_sq (norm_nonneg (physOfE38 c s x - physOfE38 c s y)),
    ← Real.sqrt_sq (norm_nonneg (x - y)),
    ← Real.sqrt_mul (sourceSobolevBound_nonneg _ _ _ _ _)]
  exact Real.sqrt_le_sqrt h

theorem physOfE38_injective : Function.Injective (physOfE38 c s) := by
  intro x y h
  apply eExt38 c s
  rw [← fourierSeq38_physOfE38, ← fourierSeq38_physOfE38 c s y, h]

theorem polishSpace_ECarrier38 : PolishSpace (ECarrier38 c s) := by
  have : TopologicalSpace.SeparableSpace (ECarrier38 c s) :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (FullWeightedHilbert c s))
  have : CompleteSpace (ECarrier38 c s) := inferInstance
  have : SecondCountableTopology (ECarrier38 c s) :=
    UniformSpace.secondCountable_of_separable (ECarrier38 c s)
  infer_instance

theorem measurableEmbedding_physOfE38 [MeasurableSpace (ECarrier38 c s)]
    [BorelSpace (ECarrier38 c s)] : MeasurableEmbedding (physOfE38 c s) := by
  have := polishSpace_ECarrier38 c s
  exact (continuous_physOfE38 c s).measurableEmbedding (physOfE38_injective c s)

end Embedding

section Pointwise

variable {lower upper : ℝ} (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) (s : ℝ)

theorem T_mem_Omega0_38 (O : OneSmoothingInput38 B) (hs : s ≤ 3 / 4) (x : ECarrier38 c s) :
    B.T (eCoe38 c s x) ∈ Omega038 c.val := by
  have hE := B.T_mem_E38 O c s _ (eCoe38_mem c s x)
  refine ⟨fun m => (mem_seqSobolev38_iff _ _).1 (seqE38_subset_seqSobolev38 c s m hE), ?_⟩
  have h2 := (mem_seqE38_iff c s _).1 hE
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (h2.mul_left ((1 : ℝ) ^ (2 * s - 3 / 2)))
  · exact mul_nonneg (tailWeight38_nonneg lower upper c.val c.property.1 (coef_bound38 c)
      (coef_upper38 c) n) (sq_nonneg _)
  · exact tailWeight_mul_le38 c s hs 1 one_pos n (japaneseBracket_one_le n) _

theorem cleanΦinv_T_38 (x : ECarrier38 c s) :
    B.cleanΦinv (B.T (eCoe38 c s x)) = physOfE38 c s x := by
  have hz : B.T (eCoe38 c s x) ∈ seqSobolev38 0 :=
    B.T_mem_zero (seqE38_subset_seqSobolev38 c s 0 (eCoe38_mem c s x))
  rw [B.cleanΦinv_of_mem _ hz]
  apply fourierSeq38_injective
  rw [B.fourierSeq38_Φinv, fourierSeq38_physOfE38]
  exact B.left_inv _ (seqE38_subset_seqSobolev38 c s 0 (eCoe38_mem c s x))

theorem Rbar_T_38 (O : OneSmoothingInput38 B) (hs : s ≤ 3 / 4) (x : ECarrier38 c s) :
    B.Rbar38 c.val (B.T (eCoe38 c s x)) = remainder38 c.val (physOfE38 c s x) := by
  rw [B.Rbar38_of_mem _ (T_mem_Omega0_38 B c s O hs x), cleanΦinv_T_38 B c s x]

end Pointwise


/-! ## W06 part 2: the Ramer density and the transfer to the full Fourier Gaussian -/

section Main

open NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant Metric

variable {lower upper : ℝ} (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  (c : BoundedCoefficients lower upper) (s : ℝ)

/-- v2's "locally defined Gaussian divergence" clauses (the second and third clauses of
`NlsGge.Ramer.ramer_eq_Ramercommon`): `δK` is, `γ_W`-a.e. on every ball where `K` agrees with a
field `G` having a closed divergence `η`, equal to `η`; and such local representatives exist. -/
def RamerDivergence38 (K : FullWeightedHilbert c s → ActualCM c) (δK : (ℤ → ℂ) → ℝ) : Prop :=
  (∀ x₀ : FullWeightedHilbert c s, ∃ r > 0,
    ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (ball x₀ r) ∧
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) ∧
  (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
      (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
      ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
        NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r → δK z = η z)

/-- v2 `D:eq:J`: `J_T = |det₂(Id + D_H K)| exp(-δK - ½‖K‖²_H)`, for `K = T - Id` (here
`‖K x‖² = ‖K x‖_H²` is the Cameron-Martin norm of `ActualCM c`, and `δK` is evaluated at the
coordinate sequence of `x`). -/
def JW06_38 (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (δK : (ℤ → ℂ) → ℝ) (x : FullWeightedHilbert c s) : ℝ :=
  |det2 (hsDerivH c s hs K x)| * Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2)

/-- v2 `D:eq:fullFourierdensity`: `f_W(x) = e^{-R_W(𝓕⁻¹ x)} J_T(x)` on `E_s`. -/
def fW06_38 (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (δK : (ℤ → ℂ) → ℝ) (x : FullWeightedHilbert c s) : ℝ :=
  Real.exp (-(remainder38 c.val (physOfE38 c s x))) * JW06_38 c s hs K δK x

/-- The W04 homeomorphism `T`, read on `E_s = FullWeightedHilbert c s` (the same type as `ECarrier38`). -/
def TW06_38 : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s :=
  B.weightedHomeoE38 O c s

/-- **W06.03.** Ramer's theorem (E05, `ramer_eq_Ramercommon`) instantiated on `E_s` with `T` the W04
weighted homeomorphism and `K = T - Id`, `K' = T⁻¹ - Id` into the Cameron-Martin space. -/
theorem ramer_W06_38 (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    ∃ δK : (ℤ → ℂ) → ℝ, RamerDivergence38 c s (B.KW06_38 O c hs1) δK ∧
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
        (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
          (fun x => ENNReal.ofReal (JW06_38 c s hs (B.KW06_38 O c hs1) δK x)) ∧
      (∀ x, 0 < JW06_38 c s hs (B.KW06_38 O c hs1) δK x) ∧
      Integrable (JW06_38 c s hs (B.KW06_38 O c hs1) δK)
        (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
      ∫ x, JW06_38 c s hs (B.KW06_38 O c hs1) δK x
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 := by
  obtain ⟨δK, h2, h3, hmap, hpos, hint, hone, -⟩ :=
    NlsGge.Ramer.ramer_eq_Ramercommon c s hs (TW06_38 B O c s) (B.KW06_38 O c hs1)
      (B.KinvW06_38 O c hs1) (fun x => B.hT_W06_38 O c hs hs1 x)
      (fun y => B.hTs_W06_38 O c hs hs1 y) (B.analytic_KW06_38 O c hs1)
      (B.analytic_KinvW06_38 O c hs1)
  exact ⟨δK, ⟨h2, h3⟩, hmap, hpos, hint, hone⟩

/-- `𝓕⁻¹ : E_s → L²` on `FullWeightedHilbert c s` (the same map as `physOfE38`). -/
def physFW06_38 (x : FullWeightedHilbert c s) : PhysicalL2 := physOfE38 c s x

theorem continuous_physFW06_38 : Continuous (physFW06_38 c s) := continuous_physOfE38 c s

theorem coordE_TW06_38 (y : FullWeightedHilbert c s) :
    coordE c s (TW06_38 B O c s y) = B.T (coordE c s y) :=
  B.weightedHomeoE38_apply O c s y

/-- Change of variables for `(T⁻¹)_# γ_W = J γ_W`. -/
theorem lintegral_comp_T_W06_38 (J : FullWeightedHilbert c s → ℝ)
    (hmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (J x)))
    (hJ : AEMeasurable (fun x => ENNReal.ofReal (J x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s))
    (H : FullWeightedHilbert c s → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x, H x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ y, ENNReal.ofReal (J y) * H (TW06_38 B O c s y)
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  set T := TW06_38 B O c s with hT
  have hHT : Measurable (H ∘ T) := hH.comp T.continuous.measurable
  have h1 : ∫⁻ x, H x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ x, (H ∘ T) (T.symm x) ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
    simp [Function.comp]
  rw [h1, ← lintegral_map hHT T.symm.continuous.measurable, hmap,
    lintegral_withDensity_eq_lintegral_mul₀ hJ hHT.aemeasurable]
  rfl

/-- **W06.04 (measure form of `D:eq:fullFourierdensity`).** For any `J` with
`(T⁻¹)_# γ_W = J γ_W` (and `J` a.e. measurable), the finite-gap limit law is
`μ_W = Z_W⁻¹ (𝓕⁻¹)_# (f_W γ_W)` with `f_W = e^{-R_W(𝓕⁻¹ x)} J`. -/
theorem muW38_eq_map_W06 (O : OneSmoothingInput38 B) (hs : (1 : ℝ) / 2 < s) (hs' : s ≤ 3 / 4)
    (J : FullWeightedHilbert c s → ℝ)
    (hmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (J x)))
    (hJ : AEMeasurable (fun x => ENNReal.ofReal (J x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)) :
    B.muW38 c.val = ENNReal.ofReal (1 / B.ZW38 c.val) •
      ((NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x))).map
        (physFW06_38 c s) := by
  have hRm := B.measurable_Rbar38 lower upper c.val c.property.1 (coef_bound38 c) (coef_upper38 c)
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hem : Measurable (physFW06_38 c s) := (continuous_physFW06_38 c s).measurable
  ext S hS
  have hP : MeasurableSet (B.cleanΦinv ⁻¹' S) := B.measurable_cleanΦinv hS
  set g : (ℤ → ℂ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(B.Rbar38 c.val z)) / B.ZW38 c.val) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Real.measurable_exp.comp hRm.neg).div_const _
  have hHm : Measurable (fun x : FullWeightedHilbert c s =>
      (B.cleanΦinv ⁻¹' S).indicator g (coordE c s x)) :=
    (hgm.indicator hP).comp (measurable_coordE c s)
  -- left side
  have hL : B.muW38 c.val S = ∫⁻ y, ENNReal.ofReal (J y) *
      (B.cleanΦinv ⁻¹' S).indicator g (coordE c s (TW06_38 B O c s y))
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
    rw [BirkhoffTop38.muW38, Measure.map_apply B.measurable_cleanΦinv hS, BirkhoffTop38.muHatW38,
      withDensity_apply _ hP, ← lintegral_indicator hP,
      ← lintegral_comp_coordE c s hs (hgm.indicator hP).aemeasurable]
    exact lintegral_comp_T_W06_38 B O c s J hmap hJ _ hHm
  rw [hL, Measure.smul_apply, Measure.map_apply hem hS,
    withDensity_apply _ (hem hS), smul_eq_mul, ← lintegral_indicator (hem hS),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  rw [coordE_TW06_38]
  have hmem : B.T (coordE c s y) = B.T (eCoe38 c s y) := rfl
  rw [hmem]
  by_cases hy : physOfE38 c s y ∈ S
  · have hy' : B.T (eCoe38 c s y) ∈ B.cleanΦinv ⁻¹' S := by
      show B.cleanΦinv (B.T (eCoe38 c s y)) ∈ S
      rw [cleanΦinv_T_38 B c s y]; exact hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem (show y ∈ physFW06_38 c s ⁻¹' S from hy)]
    simp only [hg]
    rw [Rbar_T_38 B c s O hs' y]
    have hJ0 : 0 ≤ (1 / B.ZW38 c.val) := (one_div_pos.2 hZ).le
    rw [← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul' (div_pos (Real.exp_pos _) hZ).le]
    congr 1
    ring
  · have hy' : B.T (eCoe38 c s y) ∉ B.cleanΦinv ⁻¹' S := by
      show B.cleanΦinv (B.T (eCoe38 c s y)) ∉ S
      rw [cleanΦinv_T_38 B c s y]; exact hy
    rw [Set.indicator_of_notMem hy',
      Set.indicator_of_notMem (show y ∉ physFW06_38 c s ⁻¹' S from hy)]
    simp

/-- A function on `E_s` transported to physical fields: `u ↦ g(𝓕 u)` when `𝓕 u ∈ E_s`, else `0`
(the complement of `𝓕⁻¹ E_s` is `γ_W^𝐅`-null, so the junk value is immaterial). -/
def physFun38 (g : FullWeightedHilbert c s → ℝ) (u : PhysicalL2) : ℝ := by
  classical exact if h : fourierSeq38 u ∈ seqE38 c s then g (toE38 c s ⟨u, h⟩) else 0

theorem physFun38_physOfE38 (g : FullWeightedHilbert c s → ℝ) (x : FullWeightedHilbert c s) :
    physFun38 c s g (physFW06_38 c s x) = g x := by
  have key : ∀ y : ECarrier38 c s, fourierSeq38 (physOfE38 c s y) ∈ seqE38 c s := fun y => by
    rw [fourierSeq38_physOfE38]; exact eCoe38_mem c s y
  have h : fourierSeq38 (physFW06_38 c s x) ∈ seqE38 c s := key x
  unfold physFun38
  simp only [h, ↓reduceDIte]
  congr 1
  exact eExt38 c s (by
    show fourierSeq38 (physOfE38 c s x) = eCoe38 c s x
    exact fourierSeq38_physOfE38 c s x)

theorem ofReal_lintegral_eq_W06 (O : OneSmoothingInput38 B) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (J : FullWeightedHilbert c s → ℝ)
    (hmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (J x)))
    (hJ : AEMeasurable (fun x => ENNReal.ofReal (J x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x)
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = ENNReal.ofReal (B.ZW38 c.val) := by
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hmu := muW38_eq_map_W06 B c s O hs hs'.le J hmap hJ
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have hem : Measurable (physFW06_38 c s) := (continuous_physFW06_38 c s).measurable
  have h1 : B.muW38 c.val Set.univ = 1 := measure_univ
  rw [hmu, Measure.smul_apply, Measure.map_apply hem MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul] at h1
  have h2 : ENNReal.ofReal (B.ZW38 c.val) * ENNReal.ofReal (1 / B.ZW38 c.val) = 1 := by
    rw [← ENNReal.ofReal_mul hZ.le, mul_one_div_cancel hZ.ne', ENNReal.ofReal_one]
  calc _ = ENNReal.ofReal (B.ZW38 c.val) * (ENNReal.ofReal (1 / B.ZW38 c.val) * _) := by
        rw [← mul_assoc, h2, one_mul]
    _ = _ := by rw [h1, mul_one]

theorem measurableEmbedding_physFW06_38 : MeasurableEmbedding (physFW06_38 c s) := by
  have : PolishSpace (FullWeightedHilbert c s) := polishSpace_ECarrier38 c s
  exact (continuous_physFW06_38 c s).measurableEmbedding (physOfE38_injective c s)

/-- Quasi-invariance of `γ_W` under `T` and `T⁻¹` from `(T⁻¹)_# γ_W = J γ_W`, `J > 0`. -/
theorem quasiInvariant_W06_38 (O : OneSmoothingInput38 B) (J : FullWeightedHilbert c s → ℝ)
    (hmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (J x)))
    (hJ : AEMeasurable (fun x => ENNReal.ofReal (J x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)) (hpos : ∀ x, 0 < J x) :
    ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s) ≪
        NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
      NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
        (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s)) ∧
    ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm ≪
        NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
      NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
        (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm) := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  set T := TW06_38 B O c s with hT
  have h1 : γ.map T.symm ≪ γ := by rw [hmap]; exact withDensity_absolutelyContinuous _ _
  have h2 : γ ≪ γ.map T.symm := by
    rw [hmap]
    refine withDensity_absolutelyContinuous' hJ (Filter.Eventually.of_forall fun x => ?_)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos x
  have hTm : Measurable T := T.continuous.measurable
  have hback : (γ.map T.symm).map T = γ := by
    rw [Measure.map_map hTm T.symm.continuous.measurable]
    have : (T ∘ T.symm) = id := funext fun x => T.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨⟨?_, ?_⟩, h1, h2⟩
  · have := h2.map hTm
    rwa [hback] at this
  · have := h1.map hTm
    rwa [hback] at this

/-- **W06.04-W06.05.** Density formula `D:eq:fullFourierdensity`, the integral `Z_W = ∫ f_W dγ_W`,
and the equivalence of `μ_W` with the full Fourier Gaussian `γ_W^𝐅 = (𝓕⁻¹)_# γ_W`. -/
theorem density_W06_38 (O : OneSmoothingInput38 B) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (J : FullWeightedHilbert c s → ℝ)
    (hmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (J x)))
    (hJi : Integrable J (NlsGge.Measure.fullWeightedSequenceGaussian c s))
    (hpos : ∀ x, 0 < J x) :
    (∀ x, 0 < Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) ∧
    Integrable (fun x => Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
    ∫ x, Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = B.ZW38 c.val ∧
    B.muW38 c.val = ENNReal.ofReal (1 / B.ZW38 c.val) •
      ((NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x))).map
        (physFW06_38 c s) ∧
    B.muW38 c.val = ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s)).withDensity
      (fun u => ENNReal.ofReal (1 / B.ZW38 c.val *
        physFun38 c s (fun x => Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) u)) ∧
    (B.muW38 c.val ≪ (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ∧
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ≪ B.muW38 c.val) := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (J x)) γ := hJi.aemeasurable.ennreal_ofReal
  have hcont : Continuous (fun x : FullWeightedHilbert c s => remainder38 c.val (physOfE38 c s x)) :=
    B.continuous_remainder_physOfE38 c s O hs'
  set f : FullWeightedHilbert c s → ℝ :=
    fun x => Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x with hf
  have hfpos : ∀ x, 0 < f x := fun x => mul_pos (Real.exp_pos _) (hpos x)
  have hfm : AEStronglyMeasurable f γ :=
    ((hcont.neg.rexp).aestronglyMeasurable).mul hJi.aestronglyMeasurable
  have hlint : ∫⁻ x, ENNReal.ofReal (f x) ∂γ = ENNReal.ofReal (B.ZW38 c.val) :=
    ofReal_lintegral_eq_W06 B c s O hs hs' J hmap hJ
  have hfi : Integrable f γ := by
    refine ⟨hfm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (hfpos x).le), hlint]
    exact ENNReal.ofReal_lt_top
  have hmu := muW38_eq_map_W06 B c s O hs hs'.le J hmap hJ
  have hem : Measurable (physFW06_38 c s) := (continuous_physFW06_38 c s).measurable
  have hemb := measurableEmbedding_physFW06_38 c s
  refine ⟨hfpos, hfi, ?_, hmu, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (hfpos x).le) hfm,
      hlint, ENNReal.toReal_ofReal hZ.le]
  · -- the density with respect to `γ_W^𝐅`
    rw [hmu]
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hem hS, withDensity_apply _ (hem hS),
      withDensity_apply _ hS, smul_eq_mul, ← lintegral_indicator (hem hS),
      ← lintegral_indicator hS, hemb.lintegral_map, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    by_cases hy : physFW06_38 c s y ∈ S
    · rw [Set.indicator_of_mem (show y ∈ physFW06_38 c s ⁻¹' S from hy),
        Set.indicator_of_mem hy, physFun38_physOfE38 c s f y]
      rw [← ENNReal.ofReal_mul (one_div_pos.2 hZ).le]
    · rw [Set.indicator_of_notMem (show y ∉ physFW06_38 c s ⁻¹' S from hy),
        Set.indicator_of_notMem hy]
      simp
  · have hZ0 : ENNReal.ofReal (1 / B.ZW38 c.val) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact one_div_pos.2 hZ
    have hFac : γ.withDensity (fun x => ENNReal.ofReal (f x)) ≪ γ :=
      withDensity_absolutelyContinuous _ _
    have hFac' : γ ≪ γ.withDensity (fun x => ENNReal.ofReal (f x)) := by
      refine withDensity_absolutelyContinuous' hfm.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hfpos x
    rw [hmu]
    refine ⟨(Measure.smul_absolutelyContinuous).trans (hFac.map hem), ?_⟩
    exact (hFac'.map hem).trans (Measure.absolutelyContinuous_smul hZ0)

theorem le_one_of_lt_three_quarters_W06_38 {s : ℝ} (hs' : s < 3 / 4) : s ≤ 1 := by linarith

/-- `γ_W^𝐅 = (𝓕⁻¹)_# γ_W` computed from the product Gaussian on sequences:
`(𝓕⁻¹ ∘ R_s)_# γ_W^{seq}` with `R_s` the realization of a sequence in `E_s`. -/
theorem gammaF_eq_W06_38 :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (physFW06_38 c s ∘ NlsGge.Measure.fullWeightedSequenceRealization c s) := by
  unfold NlsGge.Measure.fullWeightedSequenceGaussian
  rw [Measure.map_map (continuous_physFW06_38 c s).measurable
    (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s)]

/-- **W06 (v2 `D:thm:Ramer`, l.1521-1543), conditional on `B : BirkhoffInput38` and
`O : OneSmoothingInput38 B`, for `1/2 < s < 3/4`.**
`γ = fullWeightedSequenceGaussian c s` is the full-weight Gaussian `γ_W` on `E_s`; `T` is the W04
homeomorphism, `K = T - Id : E_s → H = ActualCM c` (so `‖K x‖` is the Cameron-Martin norm).
There is a Gaussian divergence `δK` (locally defined, `RamerDivergence38`) such that, with
`J_T = |det₂(Id + D_H K)| exp(-δK - ½‖K‖²_H)`:
* `(T⁻¹)_# γ_W = J_T γ_W`, `J_T > 0`, `∫ J_T dγ_W = 1`, and `T`, `T⁻¹` are quasi-invariant;
* with `f_W(x) = e^{-R_W(𝓕⁻¹ x)} J_T(x)`: `f_W > 0`, `f_W` is `γ_W`-integrable with
  `∫ f_W dγ_W = Z_W` (the S04 constant `ZW38`), `μ_W = Z_W⁻¹ (𝓕⁻¹)_#(f_W γ_W)` and, equivalently,
  `dμ_W(u) = Z_W⁻¹ f_W(𝓕 u) dγ_W^𝐅(u)` (`physFun38` is `f_W ∘ 𝓕`, extended by `0` off
  `𝓕⁻¹ E_s`, a `γ_W^𝐅`-null set);
* `μ_W` and the full Fourier Gaussian `γ_W^𝐅 = (𝓕⁻¹)_# γ_W` are mutually absolutely continuous. -/
theorem W06_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (JW06_38 c s hs
              (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x)) ∧
        (∀ x, 0 < JW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x) ∧
        Integrable (JW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, JW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s) ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s)) ∧
        ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm ≪
            NlsGge.Measure.fullWeightedSequenceGaussian c s ∧
          NlsGge.Measure.fullWeightedSequenceGaussian c s ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm)) ∧
      ((∀ x, 0 < fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x) ∧
        Integrable (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK)
          (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
        ∫ x, fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = B.ZW38 c.val ∧
        B.muW38 c.val = ENNReal.ofReal (1 / B.ZW38 c.val) •
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (fW06_38 c s hs
              (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x))).map
            (physFW06_38 c s) ∧
        B.muW38 c.val =
          ((NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s)).withDensity
            (fun u => ENNReal.ofReal (1 / B.ZW38 c.val *
              physFun38 c s (fW06_38 c s hs
                (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) u)) ∧
        (B.muW38 c.val ≪
            (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ∧
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (physFW06_38 c s) ≪
            B.muW38 c.val)) := by
  obtain ⟨δK, hdiv, hmap, hpos, hint, hone⟩ :=
    ramer_W06_38 B O c s hs (le_one_of_lt_three_quarters_W06_38 hs')
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (JW06_38 c s hs
      (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := hint.aemeasurable.ennreal_ofReal
  exact ⟨δK, hdiv, ⟨hmap, hpos, hint, hone,
    (quasiInvariant_W06_38 B c s O _ hmap hJ hpos)⟩,
    density_W06_38 B c s O hs hs' _ hmap hint hpos⟩

end Main

end NlsGge.Birkhoff
