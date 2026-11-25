import NlsGge.ThirdConsultation.AL.Basic

/-! # SG08 (record L08): common-reference reweighting (paper/v2.tex l.2264-2267, `D:eq:ALcommonweight`)

Under the coupling `D_h U_h = P_N U`, the lattice weight on the common full Gaussian is
`F_h(U) = f_h(D_h⁻¹ P_N U)`.  We prove, at all sufficiently fine meshes, the Gaussian transport
`(D_h⁻¹ P_N)_# γ_W = γ_h`, the weighted-law identity, its test-function form, the partition
identity `∫ F_h dγ_W = Z_h > 0`, and the normalized-law identity.
The statement of `alCommonReweighting38` is the reviewed frozen statement (STATEMENTS_SG08_B018.md). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open MeasureTheory Filter NlsGge.Measure
open scoped ENNReal

/-- Lattice Fourier coordinates of an integer-indexed coefficient sequence: the `ZMod (2N+1)`
coordinate `k` reads the integer frequency `k.valMinAbs ∈ [-N, N]`. -/
def alLatticeCoord38 (N : ℕ) (u : ℤ → ℂ) : ZMod (2 * N + 1) → ℂ :=
  fun k => u k.valMinAbs

/-- `D_h⁻¹ P_N`, read in the lattice Fourier coordinates of `γ_h`. -/
def alCommonTransport38 (c : ℕ → ℝ) (N : ℕ) (u : ℤ → ℂ) : ZMod (2 * N + 1) → ℂ :=
  alLatticeCoord38 N (alCorrInvCoef38 c N u)

section SG08Lemmas

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem alRateCont_pos_SG08 (hA : AdmissibleWeight38 lower upper c) (k : ℤ) :
    0 < alRateCont38 c k :=
  (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)

theorem admitted_of_admissible_SG08 (hA : AdmissibleWeight38 lower upper c) :
    NlsGge.Pilot.AdmittedCoefficients lower upper c :=
  ⟨hA.1, (hA.2.1 0).trans (hA.2.2 0), fun j => ⟨hA.2.1 j, hA.2.2 j⟩⟩

theorem valMinAbs_abs_le_SG08 (N : ℕ) (k : ZMod (2 * N + 1)) : |k.valMinAbs| ≤ (N : ℤ) := by
  have := valMinAbs_mem_Icc38 N k
  rw [Finset.mem_Icc] at this
  rw [abs_le]; exact this

theorem measurable_alCommonTransport_SG08 (c : ℕ → ℝ) (N : ℕ) :
    Measurable (alCommonTransport38 c N) := by
  unfold alCommonTransport38 alLatticeCoord38 alCorrInvCoef38
  fun_prop

theorem measurable_alUCoef_SG08 (c : ℕ → ℝ) : Measurable (alUCoef38 c) := by
  unfold alUCoef38
  fun_prop

/-- (3): the coupled continuum field has the common full Gaussian law. -/
theorem alUCoef_law_SG08 (hA : AdmissibleWeight38 lower upper c) :
    alFreeLaw38.map (alUCoef38 c) = fullWeightSequenceGaussian c := by
  unfold alFreeLaw38 fullWeightSequenceGaussian countableComplexGaussian
  have := Measure.infinitePi_map_pi (μ := fun _ : ℤ => complexGaussian (1 : ℝ))
    (f := fun k (z : ℂ) => (((Real.sqrt (alRateCont38 c k))⁻¹ : ℝ) : ℂ) * z)
    (fun k => by fun_prop)
  have hfun : alUCoef38 c = fun g k => (((Real.sqrt (alRateCont38 c k))⁻¹ : ℝ) : ℂ) * g k := by
    funext g k
    rw [alUCoef38, div_eq_inv_mul, Complex.ofReal_inv]
  rw [hfun, this]
  congr 1
  funext k
  rw [complexGaussian_scale38 _ (alRateCont_pos_SG08 hA k)]
  rfl

/-- (4): the coupled lattice field has the lattice Gaussian law `γ_h`. -/
theorem alUhLattice_law_SG08 (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) :
    alFreeLaw38.map (fun g => alLatticeCoord38 N (alUhCoef38 c N g)) =
      alGauss38 (L := 2 * N + 1) c (alMeshStep38 N) := by
  classical
  set U : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hU
  let e : ZMod (2 * N + 1) ≃ U :=
    { toFun := fun k => ⟨k.valMinAbs, valMinAbs_mem_Icc38 N k⟩
      invFun := fun u => ((u : ℤ) : ZMod (2 * N + 1))
      left_inv := fun k => ZMod.coe_valMinAbs k
      right_inv := fun u => by
        apply Subtype.ext
        have hu : (u : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := u.2
        rw [Finset.mem_Icc] at hu
        exact valMinAbs_intCast38 N u hu.1 hu.2 }
  have h1 := countableComplexGaussian_map_finiteRestriction (fun _ : ℤ => (1 : ℝ)) U
  have h2 := measurePreserving_arrowCongr' (fun u : U => complexGaussian ((fun _ : ℤ => (1 : ℝ)) u.1))
    (fun _ : ZMod (2 * N + 1) => complexGaussian 1) e.symm (MeasurableEquiv.refl ℂ)
    (fun u => MeasurePreserving.id _)
  set cc : ZMod (2 * N + 1) → ℝ := fun k => (Real.sqrt (alRateFree38 c N k.valMinAbs))⁻¹ with hcc
  have hcomp : (fun g => alLatticeCoord38 N (alUhCoef38 c N g)) =
      (fun y : ZMod (2 * N + 1) → ℂ => fun k => ((cc k : ℝ) : ℂ) * y k) ∘
      (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)) ∘ U.restrict := by
    funext g k
    have hk := valMinAbs_abs_le_SG08 N k
    show (if |k.valMinAbs| ≤ (N : ℤ) then
        g k.valMinAbs / (Real.sqrt (alRateFree38 c N k.valMinAbs) : ℂ) else 0) =
      (((Real.sqrt (alRateFree38 c N k.valMinAbs))⁻¹ : ℝ) : ℂ) * g k.valMinAbs
    simp only [hk, ↓reduceIte]
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  have hmeas1 : Measurable (fun y : ZMod (2 * N + 1) → ℂ => fun k => ((cc k : ℝ) : ℂ) * y k) := by
    fun_prop
  rw [hcomp, ← Measure.map_map hmeas1
    ((MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable.comp
      (Finset.measurable_restrict U)),
    ← Measure.map_map (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable
      (Finset.measurable_restrict U)]
  unfold alFreeLaw38
  rw [h1, h2.map_eq, Measure.pi_map_pi (fun k => by fun_prop)]
  unfold alGauss38
  congr 1
  funext k
  have hk := hpos k.valMinAbs (valMinAbs_abs_le_SG08 N k)
  rw [← alRateFree38_eq_alRate38, ← complexGaussian_scale38 _ hk]

/-- `D_h⁻¹` only reads the plane modes, so `D_h⁻¹ U = D_h⁻¹ P_N U`. -/
theorem alCorrInv_U_eq_PNU_SG08 (N : ℕ) (g : ℤ → ℂ) :
    alCorrInvCoef38 c N (alUCoef38 c g) = alCorrInvCoef38 c N (alPNUCoef38 c N g) := by
  funext k
  by_cases hk : |k| ≤ (N : ℤ)
  · simp only [alCorrInvCoef38, alPNUCoef38, hk, ↓reduceIte]
  · simp [alCorrInvCoef38, alCorrInvMul38, hk]

/-- The coupling: `D_h⁻¹ P_N U = U_h` in lattice coordinates. -/
theorem alCommonTransport_coupling_SG08 (hA : AdmissibleWeight38 lower upper c) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) :
    alCommonTransport38 c N ∘ alUCoef38 c = fun g => alLatticeCoord38 N (alUhCoef38 c N g) := by
  funext g
  simp only [Function.comp_apply, alCommonTransport38]
  rw [alCorrInv_U_eq_PNU_SG08, alCorrInv_PNU_coef38 hA N hpos g]

/-- (6): Gaussian transport `(D_h⁻¹ P_N)_# γ_W = γ_h`. -/
theorem alCommonTransport_law_SG08 (hA : AdmissibleWeight38 lower upper c) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) :
    (fullWeightSequenceGaussian c).map (alCommonTransport38 c N) =
      alGauss38 (L := 2 * N + 1) c (alMeshStep38 N) := by
  rw [← alUCoef_law_SG08 hA, Measure.map_map (measurable_alCommonTransport_SG08 c N)
    (measurable_alUCoef_SG08 c), alCommonTransport_coupling_SG08 hA N hpos,
    alUhLattice_law_SG08 N hpos]

theorem map_withDensity_comp_SG08 {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) (Φ : α → γ) (h : γ → ℝ≥0∞) (hΦ : Measurable Φ) (hh : Measurable h) :
    (μ.withDensity (fun z => h (Φ z))).map Φ = (μ.map Φ).withDensity h := by
  ext s hs
  rw [Measure.map_apply hΦ hs, withDensity_apply _ (hΦ hs), withDensity_apply _ hs,
    Measure.restrict_map hΦ hs, lintegral_map hh hΦ]

theorem alCommonWeight_nonneg_SG08 (N : ℕ) (u : ℤ → ℂ) :
    0 ≤ NlsGge.ThirdConsultation.AL.alCommonWeight c N u := by
  unfold NlsGge.ThirdConsultation.AL.alCommonWeight alReweight38
  split_ifs <;> positivity

theorem eventually_lower_inv_lt_SG08 (lower : ℝ) :
    ∀ᶠ N : ℕ in atTop, lower⁻¹ < ((2 * N + 1 : ℕ) : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop lower⁻¹] with N hN
  push_cast
  have : (0 : ℝ) ≤ N := N.cast_nonneg
  linarith

theorem alMeshStep_eq_inv_SG08 (N : ℕ) : alMeshStep38 N = (((2 * N + 1 : ℕ) : ℕ) : ℝ)⁻¹ := by
  unfold alMeshStep38
  push_cast
  rw [one_div]

end SG08Lemmas

/-- **SG08 common-reference reweighting.** For all sufficiently fine meshes `h = 1/(2N+1)`:
the lattice weight on the common full Gaussian `γ_W` is `F_h = f_h ∘ D_h⁻¹ P_N`, the
transported common Gaussian is exactly `γ_h`, the transported `F_h`-reweighted common Gaussian
is the `f_h`-reweighted `γ_h` (equivalently against every nonnegative measurable test), the
partition integrals agree, and the normalized laws agree. -/
theorem alCommonReweighting38 {lower upper : ℝ} {c : ℕ → ℝ}
    (hA : AdmissibleWeight38 lower upper c) :
    ∀ᶠ N : ℕ in atTop,
      (∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) ∧
      (∀ u : ℤ → ℂ, NlsGge.ThirdConsultation.AL.alCommonWeight c N u =
        alReweight38 c (alMeshStep38 N) (alCommonTransport38 c N u)) ∧
      (∀ g : ℤ → ℂ, NlsGge.ThirdConsultation.AL.alCommonWeight c N (alUCoef38 c g) =
        alReweight38 c (alMeshStep38 N) (alLatticeCoord38 N (alUhCoef38 c N g))) ∧
      alFreeLaw38.map (alUCoef38 c) = fullWeightSequenceGaussian c ∧
      alFreeLaw38.map (fun g => alLatticeCoord38 N (alUhCoef38 c N g)) =
        alGauss38 (L := 2 * N + 1) c (alMeshStep38 N) ∧
      Measurable (alCommonTransport38 c N) ∧
      Measurable (NlsGge.ThirdConsultation.AL.alCommonWeight c N) ∧
      (∀ u : ℤ → ℂ, 0 ≤ NlsGge.ThirdConsultation.AL.alCommonWeight c N u) ∧
      (fullWeightSequenceGaussian c).map (alCommonTransport38 c N) =
        alGauss38 (L := 2 * N + 1) c (alMeshStep38 N) ∧
      ((fullWeightSequenceGaussian c).withDensity
          (fun u => ENNReal.ofReal (NlsGge.ThirdConsultation.AL.alCommonWeight c N u))).map
            (alCommonTransport38 c N) =
        (alGauss38 (L := 2 * N + 1) c (alMeshStep38 N)).withDensity
          (fun û => ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û)) ∧
      (∀ Φ : (ZMod (2 * N + 1) → ℂ) → ℝ≥0∞, Measurable Φ →
        ∫⁻ u, ENNReal.ofReal (NlsGge.ThirdConsultation.AL.alCommonWeight c N u) *
            Φ (alCommonTransport38 c N u) ∂(fullWeightSequenceGaussian c) =
          ∫⁻ û, ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û) * Φ û
            ∂(alGauss38 (L := 2 * N + 1) c (alMeshStep38 N))) ∧
      Integrable (NlsGge.ThirdConsultation.AL.alCommonWeight c N)
        (fullWeightSequenceGaussian c) ∧
      ∫ u, NlsGge.ThirdConsultation.AL.alCommonWeight c N u ∂(fullWeightSequenceGaussian c) =
        alZ38 (L := 2 * N + 1) c (alMeshStep38 N) ∧
      0 < ∫ u, NlsGge.ThirdConsultation.AL.alCommonWeight c N u ∂(fullWeightSequenceGaussian c) ∧
      IsProbabilityMeasure
        ((ENNReal.ofReal (∫ u, NlsGge.ThirdConsultation.AL.alCommonWeight c N u
            ∂(fullWeightSequenceGaussian c)))⁻¹ •
          (fullWeightSequenceGaussian c).withDensity
            (fun u => ENNReal.ofReal (NlsGge.ThirdConsultation.AL.alCommonWeight c N u))) ∧
      ((ENNReal.ofReal (∫ u, NlsGge.ThirdConsultation.AL.alCommonWeight c N u
            ∂(fullWeightSequenceGaussian c)))⁻¹ •
          (fullWeightSequenceGaussian c).withDensity
            (fun u => ENNReal.ofReal (NlsGge.ThirdConsultation.AL.alCommonWeight c N u))).map
          (alCommonTransport38 c N) =
        (ENNReal.ofReal (alZ38 (L := 2 * N + 1) c (alMeshStep38 N)))⁻¹ •
          (alGauss38 (L := 2 * N + 1) c (alMeshStep38 N)).withDensity
            (fun û => ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û)) := by
  have hAd := admitted_of_admissible_SG08 hA
  filter_upwards [alRateFree_pos_eventually38 hA, eventually_lower_inv_lt_SG08 lower]
    with N hpos hL
  have hh0 : 0 < alMeshStep38 N := alMeshStep_pos38 N
  have hT := measurable_alCommonTransport_SG08 c N
  have hfm : Measurable (alReweight38 (L := 2 * N + 1) c (alMeshStep38 N)) :=
    meas_alReweight38 hAd hh0
  have hbund := alGaussianNormalizer_bundled38 (L := 2 * N + 1) hAd (alMeshStep_eq_inv_SG08 N) hL
  have hint : Integrable (alReweight38 (L := 2 * N + 1) c (alMeshStep38 N))
      (alGauss38 (L := 2 * N + 1) c (alMeshStep38 N)) := hbund.2.2.2.2.1
  have hZ : 0 < alZ38 (L := 2 * N + 1) c (alMeshStep38 N) := hbund.2.2.2.2.2.2.1
  have h6 := alCommonTransport_law_SG08 hA N hpos
  have hcoup := alCommonTransport_coupling_SG08 hA N hpos
  have hFeq : NlsGge.ThirdConsultation.AL.alCommonWeight c N =
      alReweight38 c (alMeshStep38 N) ∘ alCommonTransport38 c N := rfl
  have hFm : Measurable (NlsGge.ThirdConsultation.AL.alCommonWeight c N) := by
    rw [hFeq]; exact hfm.comp hT
  have h7 : ((fullWeightSequenceGaussian c).withDensity
          (fun u => ENNReal.ofReal (NlsGge.ThirdConsultation.AL.alCommonWeight c N u))).map
            (alCommonTransport38 c N) =
        (alGauss38 (L := 2 * N + 1) c (alMeshStep38 N)).withDensity
          (fun û => ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û)) := by
    rw [← h6]
    exact map_withDensity_comp_SG08 _ _ (fun û => ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û))
      hT (ENNReal.measurable_ofReal.comp hfm)
  have hFint : Integrable (NlsGge.ThirdConsultation.AL.alCommonWeight c N)
      (fullWeightSequenceGaussian c) := by
    rw [hFeq]
    rw [← h6] at hint
    exact (integrable_map_measure hfm.aestronglyMeasurable hT.aemeasurable).mp hint
  have hFZ : ∫ u, NlsGge.ThirdConsultation.AL.alCommonWeight c N u ∂(fullWeightSequenceGaussian c) =
      alZ38 (L := 2 * N + 1) c (alMeshStep38 N) := by
    unfold alZ38
    rw [← h6, integral_map hT.aemeasurable hfm.aestronglyMeasurable]
    rfl
  refine ⟨hpos, fun u => rfl, fun g => ?_, alUCoef_law_SG08 hA, alUhLattice_law_SG08 N hpos, hT,
    hFm, alCommonWeight_nonneg_SG08 N, h6, h7, ?_, hFint, hFZ, hFZ ▸ hZ, ?_, ?_⟩
  · exact congrArg (alReweight38 c (alMeshStep38 N)) (congrFun hcoup g)
  · intro Φ hΦ
    rw [← h6, lintegral_map (f := fun û => ENNReal.ofReal (alReweight38 c (alMeshStep38 N) û) * Φ û)
      ((ENNReal.measurable_ofReal.comp hfm).mul hΦ) hT]
    rfl
  · constructor
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hFint
        (Filter.Eventually.of_forall (alCommonWeight_nonneg_SG08 N)),
      smul_eq_mul, hFZ, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top]
  · rw [Measure.map_smul, h7, hFZ]
    exact hT.aemeasurable

end NlsGge.AblowitzLadik
