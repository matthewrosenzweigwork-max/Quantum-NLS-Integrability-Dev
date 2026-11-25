import NlsGge.Hierarchy.ALFiniteMeasure38

/-! ORIGINAL record L03, clause B084.C03 (paper/v2.tex 2008-2016, `D:eq:ALf`).

Statement `alEta_map_dft38` is the independently reviewed (SOL-STMTL-20261111,
APPROVABLE_AS_STATED) frozen command of `AuthOrig-20261111/STATEMENTS_L03_L04.md`, copied
byte-for-byte from the elaborated probe `probe-AllSAOrigL0304Probe.lean`.

Import (the only one needed): `NlsGge.Hierarchy.ALFiniteMeasure38`, which provides `alEta38`,
`alWeighted38`, `alIntegrand38`, `alPartition_bounds38`, `integrable_alReweight38`,
`alIntegrand_synth38`, and (through `NlsGge.Hierarchy.ALGaussianNormalizer38`) `integral_synth38`,
`integral_gauss_pi38`, `alGaussianNormalizer38`, `alGauss38`, `alReweight38`, `alZ38`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open MeasureTheory NlsGge.Pilot

section L03Helpers

variable {L : ℕ} [NeZero L]

theorem l03_alReweight_nonneg (c : ℕ → ℝ) (h : ℝ) (û : ZMod L → ℂ) :
    0 ≤ alReweight38 (L := L) c h û := by
  classical
  unfold alReweight38
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem l03_measurable_dft : Measurable (fun α : ZMod L → ℂ => ZMod.dft α) :=
  (LinearMap.continuous_of_finiteDimensional
    (ZMod.dft : (ZMod L → ℂ) ≃ₗ[ℂ] (ZMod L → ℂ)).toLinearMap).measurable

/-- The weighted Liouville measure is Lebesgue measure with density `alIntegrand38`. -/
theorem l03_alWeighted_eq {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    alWeighted38 L c h =
      (volume : Measure (ZMod L → ℂ)).withDensity
        (fun α => ENNReal.ofReal (alIntegrand38 (L := L) c h α)) := by
  classical
  have hE := meas_alEnergyInd38 (L := L) hc hh
  unfold alWeighted38 alLiouvilleMeasure38
  rw [← withDensity_mul _ (f := fun α => ENNReal.ofReal (alRho38 α))
      (g := fun α => ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α)))
      (ENNReal.measurable_ofReal.comp measurable_alRho38)
      (ENNReal.measurable_ofReal.comp hE.neg.exp),
    ← withDensity_indicator measurableSet_alDisk38]
  congr 1
  funext α
  by_cases hα : IsALField38 α
  · have hmem : α ∈ alDisk38 L := hα
    rw [Set.indicator_of_mem hmem, Pi.mul_apply]
    have hρ : 0 ≤ alRho38 α := Finset.prod_nonneg fun j _ => inv_nonneg.2 (by
      have := hα j; nlinarith [norm_nonneg (α j)])
    rw [← ENNReal.ofReal_mul hρ]
    unfold alIntegrand38 alEnergyInd38
    simp only [hα, ite_true]
    rw [mul_comm]; rfl
  · have hmem : α ∉ alDisk38 L := hα
    rw [Set.indicator_of_notMem hmem]
    unfold alIntegrand38
    simp [hα]

/-- `η_h` of a measurable set as a Lebesgue integral of the Liouville integrand. -/
theorem l03_alEta_apply {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h)
    {A : Set (ZMod L → ℂ)} (hA : MeasurableSet A) :
    alEta38 L c h A =
      ENNReal.ofReal ((alPartition38 L c h)⁻¹ * ∫ α in A, alIntegrand38 (L := L) c h α) := by
  have hint := alIntegrand_integrable38 (L := L) hc hh
  have hP := (alPartition_bounds38 (L := L) hc hh).2.2.1
  unfold alEta38
  rw [Measure.smul_apply, l03_alWeighted_eq hc hh, withDensity_apply _ hA, smul_eq_mul,
    ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Filter.Eventually.of_forall (alIntegrand_nonneg38 c h)),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hP.le)]

/-- Change of variables `α = 𝓕⁻¹ û` and Gaussian density on a DFT preimage. -/
theorem l03_setIntegral_preimage {c : ℕ → ℝ} {h : ℝ} (hh : h = (L : ℝ)⁻¹)
    (ha : ∀ ν : ℤ, 0 < alRate38 c h ν) {S : Set (ZMod L → ℂ)} (hS : MeasurableSet S) :
    ∫ α in (fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S, alIntegrand38 (L := L) c h α =
      h ^ L * (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) *
        ∫ û in S, alReweight38 (L := L) c h û ∂(alGauss38 (L := L) c h) := by
  classical
  have hpre : MeasurableSet ((fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S) :=
    l03_measurable_dft hS
  rw [← integral_indicator hpre, integral_synth38]
  have hJ : ((L : ℝ) ^ L)⁻¹ = h ^ L := by rw [hh, inv_pow]
  rw [hJ]
  have hpt : ∀ û : ZMod L → ℂ,
      ((fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S).indicator (alIntegrand38 (L := L) c h)
        (ZMod.dft.symm û) =
      Real.exp (-∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2) *
        S.indicator (alReweight38 (L := L) c h) û := by
    intro û
    by_cases hû : û ∈ S
    · have hm : ZMod.dft.symm û ∈ (fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S := by
        simp only [Set.mem_preimage, LinearEquiv.apply_symm_apply]; exact hû
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hû, alIntegrand_synth38]
    · have hm : ZMod.dft.symm û ∉ (fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S := by
        simp only [Set.mem_preimage, LinearEquiv.apply_symm_apply]; exact hû
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hû, mul_zero]
  simp_rw [hpt]
  have hG := integral_gauss_pi38 (fun k : ZMod L => alRate38 c h k.valMinAbs)
    (fun k => ha _) (S.indicator (alReweight38 (L := L) c h))
  have hprod : (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero (ha _).ne' Real.pi_ne_zero
  have hinv : (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) =
      (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [inv_div]
  rw [← integral_indicator hS]
  unfold alGauss38
  rw [hG, hinv]
  field_simp

end L03Helpers

/-- B084.C03 (paper/v2.tex 2008-2016, `D:eq:ALf`): the full-weight AL law `η_h`, pushed forward to
the Fourier coordinates `û = 𝓕 α` of the interpolant, is the normalized reweighting of `γ_h` by
`f_h = 1_{disk} e^{-R_h}`, as measures and on every measurable set. -/
theorem alEta_map_dft38 {L : ℕ} [NeZero L] {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : h = (L : ℝ)⁻¹)
    (ha : ∀ ν : ℤ, 0 < alRate38 c h ν) :
    0 < alPartition38 L c h ∧
    0 < alZ38 (L := L) c h ∧
    Integrable (alReweight38 (L := L) c h) (alGauss38 (L := L) c h) ∧
    Measure.map (fun α : ZMod L → ℂ => ZMod.dft α) (alEta38 L c h) =
      ENNReal.ofReal (alZ38 (L := L) c h)⁻¹ •
        (alGauss38 (L := L) c h).withDensity
          (fun û => ENNReal.ofReal (alReweight38 (L := L) c h û)) ∧
    ∀ S : Set (ZMod L → ℂ), MeasurableSet S →
      alEta38 L c h ((fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S) =
        ENNReal.ofReal ((alZ38 (L := L) c h)⁻¹ *
          ∫ û in S, alReweight38 (L := L) c h û ∂(alGauss38 (L := L) c h)) := by

  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hP := (alPartition_bounds38 (L := L) hc hh0).2.2.1
  have hK : 0 < h ^ L * ∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs :=
    mul_pos (pow_pos hh0 _) (Finset.prod_pos fun k _ => div_pos Real.pi_pos (ha _))
  have hid := alGaussianNormalizer38 (L := L) c hh ha
  have hZ : 0 < alZ38 (L := L) c h := by
    by_contra hZ
    push Not at hZ
    have := mul_nonpos_of_nonneg_of_nonpos hK.le hZ
    linarith
  have hfi := integrable_alReweight38 (L := L) hc hh0 ha
  have hset : ∀ S : Set (ZMod L → ℂ), MeasurableSet S →
      alEta38 L c h ((fun α : ZMod L → ℂ => ZMod.dft α) ⁻¹' S) =
        ENNReal.ofReal ((alZ38 (L := L) c h)⁻¹ *
          ∫ û in S, alReweight38 (L := L) c h û ∂(alGauss38 (L := L) c h)) := by
    intro S hS
    have hK2 : (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero Real.pi_ne_zero (ha _).ne'
    have hhL : h ^ L ≠ 0 := pow_ne_zero _ hh0.ne'
    rw [l03_alEta_apply hc hh0 (l03_measurable_dft hS), l03_setIntegral_preimage hh ha hS, hid]
    congr 1
    field_simp
  refine ⟨hP, hZ, hfi, ?_, hset⟩
  ext S hS
  rw [Measure.map_apply l03_measurable_dft hS, hset S hS, Measure.smul_apply,
    withDensity_apply _ hS, smul_eq_mul,
    ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
      (Filter.Eventually.of_forall (l03_alReweight_nonneg c h)),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hZ.le)]

end NlsGge.AblowitzLadik
