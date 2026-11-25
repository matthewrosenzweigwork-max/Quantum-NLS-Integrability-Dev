import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Hm1Prop

/-! # Track B, step B3 (review items R1 / M1 / G4): the `H⁻¹` Duhamel integrand is defined
and integrable BEFORE any Duhamel identity is asserted

Statement-independent. Slabs are `[a,b] × 𝕋` with `volume.restrict (Icc a b) ⊗ spatialMeasure`
(`slab_eq`: the same measure as the restriction of the product measure to `Icc a b ×ˢ univ`).

* `integrable_cubic_slab`: `U ∈ L⁴(slab) ⇒ 2|U|²U ∈ L¹(slab)` (finite measure).
* For any `F ∈ L¹(slab)`: a.e. slice integrability (`ae_integrable_slice`); the `H⁻¹`-valued map
  `r ↦ fnToHm1 (F(r,·))` is a.e.-strongly measurable and Bochner integrable on `[a,b]`, and so is
  the Duhamel integrand `r ↦ e^{i(t-r)∂ₓ²}(-i · fnToHm1 (F(r,·)))` (`integrable_duhamel_slab`).
* If `F ∈ L¹` on every slab `[-T,T] × 𝕋`: the Duhamel integrand is interval integrable between
  ANY two base times (`intervalIntegrable_duhamel`), and its oriented Bochner integral has the
  coefficients `∫_s^{s'} e^{-i(t-r)(2πn)²} (-i) F̂(r)(n) dr` of the scalar Fourier integrals
  (`carrierCoe38_duhamel_integral`): the Bochner and the Fourier-defined Duhamel terms agree.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

theorem isProbabilityMeasure_spatialMeasure : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

attribute [local instance] isProbabilityMeasure_spatialMeasure

theorem slab_eq (a b : ℝ) :
    ((volume : Measure ℝ).prod spatialMeasure).restrict (Set.Icc a b ×ˢ Set.univ) =
      ((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := spatialMeasure)
    (Set.Icc a b) Set.univ
  rw [Measure.restrict_univ] at h
  exact h.symm

theorem isFiniteMeasure_slab (a b : ℝ) :
    IsFiniteMeasure (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  infer_instance

theorem norm_two_complex : ‖(2 : ℂ)‖ = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
  norm_num

/-- `U ∈ L⁴([a,b] × 𝕋) ⇒ 2|U|²U ∈ L¹([a,b] × 𝕋)`. -/
theorem integrable_cubic_slab {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hU : MemLp U 4
      (((volume : Measure ℝ).prod spatialMeasure).restrict (Set.Icc a b ×ˢ Set.univ))) :
    Integrable (fun p => 2 * ((‖U p‖ ^ 2 : ℝ) : ℂ) * U p)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
  rw [slab_eq] at hU
  have := isFiniteMeasure_slab a b
  have h4 : Integrable (fun p => ‖U p‖ ^ 4)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
    have h := hU.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using h
  refine Integrable.mono' ((h4.const_mul 2).add (integrable_const (2 : ℝ))) ?_
    (ae_of_all _ fun p => ?_)
  · exact (by fun_prop : Continuous fun z : ℂ => 2 * ((‖z‖ ^ 2 : ℝ) : ℂ) * z).comp_aestronglyMeasurable
      hU.aestronglyMeasurable
  · have hy := norm_nonneg (U p)
    show ‖2 * ((‖U p‖ ^ 2 : ℝ) : ℂ) * U p‖ ≤ 2 * ‖U p‖ ^ 4 + 2
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_two_complex]
    nlinarith [mul_nonneg (mul_nonneg hy hy) (sq_nonneg (‖U p‖ - 1)), sq_nonneg (‖U p‖ ^ 2 - 1 / 2)]

/-- An `L¹` slab function has integrable slices for a.e. time of the slab. -/
theorem ae_integrable_slice {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Icc a b →
      Integrable (fun x => F (r, x)) spatialMeasure :=
  (ae_restrict_iff' measurableSet_Icc).1 hF.prod_right_ae

/-- The `H⁻¹`-valued slice map of an `L¹` slab function is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_fnToHm1_slice {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure)) :
    AEStronglyMeasurable (fun r => fnToHm1 (fun x => F (r, x)))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  refine aestronglyMeasurable_of_carrierCoe (-1) _ (fun n => ?_)
  have h1 : AEStronglyMeasurable (fun p : ℝ × PhysicalCircle => fourier (-n) p.2 • F p)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) :=
    ((map_continuous (fourier (-n))).comp continuous_snd).aestronglyMeasurable.smul hF.1
  have hm := h1.integral_prod_right'
  refine hm.congr ?_
  filter_upwards [hF.prod_right_ae] with r hr
  rw [carrierCoe38_fnToHm1 hr]
  rfl

/-- The `H⁻¹`-valued slice map of an `L¹` slab function is Bochner integrable on the slab. -/
theorem integrable_fnToHm1_slice {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure)) :
    Integrable (fun r => fnToHm1 (fun x => F (r, x)))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
  Integrable.mono' (hF.integral_norm_prod_left.const_mul hm1Const)
    (aestronglyMeasurable_fnToHm1_slice hF) (ae_of_all _ fun _ => norm_fnToHm1_le _)

theorem norm_negIMul (r : ℝ) (x : SobolevCarrier38 r) : ‖negIMul r x‖ = ‖x‖ :=
  norm_unitMul r (fun _ => -Complex.I) (fun _ => by simp) x

theorem aestronglyMeasurable_duhamel_pair {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure))
    (t : ℝ) :
    AEStronglyMeasurable
      (fun r => ((t - r : ℝ), negIMul (-1) (fnToHm1 (fun x => F (r, x)))))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
  (by fun_prop : Continuous fun r : ℝ => t - r).aestronglyMeasurable.prodMk
    ((negIMul (-1)).continuous.comp_aestronglyMeasurable (aestronglyMeasurable_fnToHm1_slice hF))

theorem aestronglyMeasurable_duhamel_slab {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure))
    (t : ℝ) :
    AEStronglyMeasurable
      (fun r => freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x)))))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  have h := (continuous_freeProp (-1)).comp_aestronglyMeasurable
    (aestronglyMeasurable_duhamel_pair hF t)
  exact h

theorem norm_duhamel_term (t r : ℝ) (y : SobolevCarrier38 (-1)) :
    ‖freeProp (-1) (t - r) (negIMul (-1) y)‖ = ‖y‖ := by
  rw [norm_freeProp, norm_negIMul]

/-- The Duhamel integrand `r ↦ e^{i(t-r)∂ₓ²}(-i F(r))` is Bochner integrable in `H⁻¹` on a slab. -/
theorem integrable_duhamel_slab {F : ℝ × PhysicalCircle → ℂ} {a b : ℝ}
    (hF : Integrable F (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure))
    (t : ℝ) :
    Integrable (fun r => freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x)))))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
  Integrable.mono' (integrable_fnToHm1_slice hF).norm (aestronglyMeasurable_duhamel_slab hF t)
    (ae_of_all _ fun r => le_of_eq (norm_duhamel_term t r _))

/-- If `F ∈ L¹` on every slab `[-T,T] × 𝕋`, the Duhamel integrand is interval integrable between
any two times. -/
theorem intervalIntegrable_duhamel {F : ℝ × PhysicalCircle → ℂ}
    (hF : ∀ T : ℝ,
      Integrable F (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod spatialMeasure))
    (t s s' : ℝ) :
    IntervalIntegrable
      (fun r => freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) volume s s' := by
  set T := max |s| |s'|
  have h := integrable_duhamel_slab (hF T) t
  have hs := abs_le.mp (le_max_left |s| |s'|)
  have hs' := abs_le.mp (le_max_right |s| |s'|)
  refine IntegrableOn.intervalIntegrable (IntegrableOn.mono_set h ?_)
  exact Set.uIcc_subset_Icc ⟨hs.1, hs.2⟩ ⟨hs'.1, hs'.2⟩

/-- Bochner = Fourier: the coefficients of the oriented `H⁻¹` Bochner Duhamel integral are the
scalar Duhamel integrals of the ordinary Fourier coefficients of the slices. -/
theorem carrierCoe38_duhamel_integral {F : ℝ × PhysicalCircle → ℂ}
    (hF : ∀ T : ℝ,
      Integrable F (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod spatialMeasure))
    (t s s' : ℝ) (n : ℤ) :
    carrierCoe38 (-1)
        (∫ r in s..s', freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => F (r, x))))) n =
      ∫ r in s..s', freePhase (t - r) n * (-Complex.I * physicalFourier (fun x => F (r, x)) n) := by
  rw [carrierCoe38_intervalIntegral (-1) (intervalIntegrable_duhamel hF t s s')]
  set T := max |s| |s'|
  have hs := abs_le.mp (le_max_left |s| |s'|)
  have hs' := abs_le.mp (le_max_right |s| |s'|)
  have hsub : Set.uIoc s s' ⊆ Set.Icc (-T) T :=
    Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc ⟨hs.1, hs.2⟩ ⟨hs'.1, hs'.2⟩)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_integrable_slice (hF T)] with r hr hmem
  rw [carrierCoe38_freeProp, carrierCoe38_negIMul, carrierCoe38_fnToHm1 (hr (hsub hmem))]

/-- Coefficients of the free evolution of an `L²` datum in `H⁻¹`. -/
theorem carrierCoe38_freeProp_l2ToHm1 (t : ℝ) (u : PhysicalL2) (n : ℤ) :
    carrierCoe38 (-1) (freeProp (-1) t (l2ToHm1 u)) n = freePhase t n * physicalFourier u n := rfl

end LiebLiniger.FixedPeriod.ALLS.PdeB
