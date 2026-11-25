import NlsGge.Birkhoff.F05Identity38e

/-! # F05, file f: the measure identity `dμ_m = Z_m⁻¹ e^{-V_m} dγ_m^F` and `∫ e^{-V_m} dγ_m^F = Z_m`

Transport of `(T⁻¹)_# γ_m = e^{-D_m} γ_m` (file e) through the substitution of the defining
finite-gap law (v2 `B:eq:mumeasures`), and total masses (F05.06).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General NlsGge.Ramer
  NlsGge.Analysis.RegularizedDeterminant Filter Topology
open scoped ENNReal

section Final

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

theorem measurable_physE05 : Measurable (physE05 (m := m) (β := β) hm hβ) :=
  (continuous_physE05 hm hβ).measurable

/-- `γ_m^F = (𝓕⁻¹)_# γ_m^E`. -/
theorem gammaFM38_eq05 :
    gammaFM38 m β = (S05 m β hm hβ).γE.map (physE05 hm hβ) := by
  have h := F05Setting_γE m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)
  have h' : (S05 m β hm hβ).γE =
      ((gammaM38 m β).map (gaussianRealization38 m)).map (F05Equiv m β hm
        (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)) := h
  rw [h', Measure.map_map (measurable_physE05 hm hβ)
    (F05Equiv m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _))
      (hβ m le_rfl)).continuous.measurable]
  unfold gammaFM38
  congr 1
  funext y
  show FinvH38 m y = FinvH38 m (ofCarrier38 _ (toCarrier38 _ ((F05Equiv m β hm
    (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)).symm
    (F05Equiv m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) y))))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- `Φ⁻¹ z = 𝓕⁻¹ (T⁻¹ (R z))` for `z ∈ h^{m-1}`. -/
theorem PhiInvX_eq05 (z : ℤ → ℂ) (hz : (S05 m β hm hβ).memE z) :
    B.PhiInvX38 m z = physE05 hm hβ ((T05 B hm hβ).symm ((S05 m β hm hβ).R z)) := by
  have hz' : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := by
    rw [mem_seqSobolev38_iff]
    exact (F05_memE_iff m β hm (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _))
      (hβ m le_rfl) z).1 hz
  have hR : (S05 m β hm hβ).R z = Eq05 m β hm hβ (carrierMk38 _ z hz') := by
    apply (S05 m β hm hβ).E_ext
    intro n
    rw [(S05 m β hm hβ).coord_R hz, coord_Eq05]
    rfl
  rw [hR, T05_symm_apply]
  unfold BirkhoffInput38.PhiInvX38 physE05
  rw [B.cleanTinvC_of_mem _ z hz', LinearIsometryEquiv.symm_apply_apply]
  rfl


include O hm hβ in
/-- **F05 (measure form).** `μ_m = Z_m⁻¹ e^{-V_m} γ_m^F`, as measures on `H^{m-1}`. -/
theorem muM38_eq05 :
    muM38 B m β = (gammaFM38 m β).withDensity
      (fun u => ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-(Vm38 m β u)))) := by
  set Z := ZM38 B m β with hZdef
  have hZ := (B.ZM38_pos_le_one hm hβ).1
  have hRc := continuous_Rm38 hm hβ
  have hVc := continuous_Vm38 hm hβ
  set g : Hm1 m → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(Rm38 m β u)) / Z) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hRc.measurable.neg).div_const _)
  have hphi := measurable_physE05 hm hβ
  have hT := (T05 B hm hβ).symm.continuous.measurable
  have hRm := (S05 m β hm hβ).measurable_R
  ext A hA
  have hP : MeasurableSet (B.PhiInvX38 m ⁻¹' A) := B.measurable_PhiInvX38 m hA
  -- step 1: unfold the definition of `μ_m`
  have s1 : muM38 B m β A = ∫⁻ z, A.indicator g (B.PhiInvX38 m z) ∂(gammaM38 m β) := by
    rw [muM38, Measure.map_apply (B.measurable_PhiInvX38 m) hA, muHatM38,
      withDensity_apply _ hP, ← lintegral_indicator hP]
    refine lintegral_congr fun z => ?_
    by_cases hz : B.PhiInvX38 m z ∈ A
    · rw [Set.indicator_of_mem (show z ∈ B.PhiInvX38 m ⁻¹' A from hz),
        Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (show z ∉ B.PhiInvX38 m ⁻¹' A from hz),
        Set.indicator_of_notMem hz]
  -- step 2: replace `Φ⁻¹ z` by `𝓕⁻¹ T⁻¹ R z` almost surely
  have s2 : ∫⁻ z, A.indicator g (B.PhiInvX38 m z) ∂(gammaM38 m β) =
      ∫⁻ z, A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm ((S05 m β hm hβ).R z)))
        ∂(S05 m β hm hβ).γ := by
    refine lintegral_congr_ae ?_
    filter_upwards [(S05 m β hm hβ).ae_memE] with z hz
    rw [PhiInvX_eq05 B hm hβ z hz]
  have hfm : Measurable (fun y : (S05 m β hm hβ).E => A.indicator g (physE05 hm hβ y)) :=
    (hgm.indicator hA).comp hphi
  -- step 3: change variables `x = R z`, then `y = T⁻¹ x`
  have s3 : ∫⁻ z, A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm ((S05 m β hm hβ).R z)))
      ∂(S05 m β hm hβ).γ = ∫⁻ y, A.indicator g (physE05 hm hβ y)
        ∂((S05 m β hm hβ).γE.map (T05 B hm hβ).symm) := by
    have e1 : ∫⁻ y, A.indicator g (physE05 hm hβ y) ∂((S05 m β hm hβ).γE.map (T05 B hm hβ).symm) =
        ∫⁻ x, A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm x)) ∂(S05 m β hm hβ).γE :=
      lintegral_map hfm hT
    have e2 : ∫⁻ x, A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm x)) ∂(S05 m β hm hβ).γE =
        ∫⁻ z, A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm ((S05 m β hm hβ).R z)))
          ∂(S05 m β hm hβ).γ :=
      lintegral_map (f := fun x => A.indicator g (physE05 hm hβ ((T05 B hm hβ).symm x)))
        (hfm.comp hT) hRm
    exact e2.symm.trans e1.symm
  have hDm : Measurable (fun x : (S05 m β hm hβ).E => ENNReal.ofReal (Real.exp (-(D05 hm hβ x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (continuous_D05 hm hβ).measurable.neg)
  have s4 : ∫⁻ y, A.indicator g (physE05 hm hβ y)
      ∂((S05 m β hm hβ).γE.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(D05 hm hβ x))))) =
      ∫⁻ y, ENNReal.ofReal (Real.exp (-(D05 hm hβ y))) * A.indicator g (physE05 hm hβ y)
        ∂(S05 m β hm hβ).γE :=
    lintegral_withDensity_eq_lintegral_mul _ hDm hfm
  rw [s1, s2, s3, ramer_density05 B O hm hβ, s4]
  -- step 4: pointwise algebra and the density w.r.t. `γ_m^F`
  have hdm : Measurable (fun u : Hm1 m => ENNReal.ofReal (Z⁻¹ * Real.exp (-(Vm38 m β u)))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp hVc.measurable.neg))
  have s5 : ((gammaFM38 m β).withDensity
      (fun u => ENNReal.ofReal (Z⁻¹ * Real.exp (-(Vm38 m β u))))) A =
      ∫⁻ y, A.indicator (fun u => ENNReal.ofReal (Z⁻¹ * Real.exp (-(Vm38 m β u))))
        (physE05 hm hβ y) ∂(S05 m β hm hβ).γE := by
    rw [withDensity_apply _ hA, gammaFM38_eq05 hm hβ, ← lintegral_indicator hA]
    exact lintegral_map (hdm.indicator hA) hphi
  rw [s5]
  refine lintegral_congr fun y => ?_
  by_cases hy : physE05 hm hβ y ∈ A
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [hg]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    unfold D05
    have e : Real.exp (-(Vm38 m β (physE05 hm hβ y) - Rm38 m β (physE05 hm hβ y))) *
        Real.exp (-(Rm38 m β (physE05 hm hβ y))) = Real.exp (-(Vm38 m β (physE05 hm hβ y))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← e]
    field_simp
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    simp


include hm hβ in
theorem isProbabilityMeasure_gammaFM38 : IsProbabilityMeasure (gammaFM38 m β) := by
  rw [gammaFM38_eq05 hm hβ]
  have : IsProbabilityMeasure (S05 m β hm hβ).γE := by
    unfold RamerSetting.γE
    have : IsProbabilityMeasure (S05 m β hm hβ).γ := by
      show IsProbabilityMeasure (gammaM38 m β)
      infer_instance
    infer_instance
  infer_instance

include O hm hβ in
/-- **F05 (v2 `B:cor:identity`), conditional on `B`, `O`.**  With `γ_m^F = (𝓕⁻¹)_# γ_m`:
`0 < Z_m ≤ 1`, `e^{-V_m}` is `γ_m^F`-integrable with `∫ e^{-V_m} dγ_m^F = Z_m` (integrability is a
conclusion), and `dμ_m = Z_m⁻¹ e^{-V_m} dγ_m^F`. -/
theorem F05_identity38 :
    (0 < ZM38 B m β ∧ ZM38 B m β ≤ 1) ∧
    Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u)) ∂(gammaFM38 m β) = ZM38 B m β ∧
    muM38 B m β = (gammaFM38 m β).withDensity
      (fun u => ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-(Vm38 m β u)))) := by
  have hZ := B.ZM38_pos_le_one hm hβ
  have hmu := muM38_eq05 B O hm hβ
  have hprob := B.isProbabilityMeasure_muM38 hm hβ
  have hVc := continuous_Vm38 hm hβ
  set Z := ZM38 B m β with hZdef
  have hmeas : Measurable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) :=
    Real.measurable_exp.comp hVc.measurable.neg
  have h1 : ∫⁻ u, ENNReal.ofReal (Z⁻¹ * Real.exp (-(Vm38 m β u))) ∂(gammaFM38 m β) = 1 := by
    have := measure_univ (μ := muM38 B m β)
    rw [hmu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have h2 : ∫⁻ u, ENNReal.ofReal (Real.exp (-(Vm38 m β u))) ∂(gammaFM38 m β) =
      ENNReal.ofReal Z := by
    have e : ∀ u : Hm1 m, ENNReal.ofReal (Z⁻¹ * Real.exp (-(Vm38 m β u))) =
        ENNReal.ofReal Z⁻¹ * ENNReal.ofReal (Real.exp (-(Vm38 m β u))) := fun u =>
      ENNReal.ofReal_mul (inv_nonneg.2 hZ.1.le)
    simp only [e] at h1
    rw [lintegral_const_mul (f := fun u : Hm1 m => ENNReal.ofReal (Real.exp (-(Vm38 m β u)))) _
      (ENNReal.measurable_ofReal.comp hmeas)] at h1
    have hZ0 : ENNReal.ofReal Z⁻¹ ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hZ.1
    have h3 : ENNReal.ofReal Z * ENNReal.ofReal Z⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hZ.1.le, mul_inv_cancel₀ hZ.1.ne', ENNReal.ofReal_one]
    calc _ = ENNReal.ofReal Z * (ENNReal.ofReal Z⁻¹ * ∫⁻ u, ENNReal.ofReal (Real.exp (-(Vm38 m β u)))
          ∂(gammaFM38 m β)) := by rw [← mul_assoc, h3, one_mul]
      _ = _ := by rw [h1, mul_one]
  have hint : Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le), h2]
    exact ENNReal.ofReal_lt_top
  refine ⟨hZ, hint, ?_, hmu⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
    hmeas.aestronglyMeasurable, h2, ENNReal.toReal_ofReal hZ.1.le]

end Final

end NlsGge.Birkhoff
