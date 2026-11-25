import Mathlib
import NlsGge.Atomic.PeriodPi
import NlsGge.Atomic.IntervalZSAction

/-! Period-π to period-one unitary rescaling, literal H¹ domain transport, endpoint traces,
and the Zakharov–Shabat action identity. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace NlsGge.Atomic.DM001

open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.PeriodPi

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
abbrev UnitL2 := NlsGge.Schur.SourceIntervalL2
abbrev PiL2 := NlsGge.Atomic.PeriodPi.SourceIntervalL2

/-- The globally defined affine measurable equivalence underlying the restricted map. -/
def piScaleHomeomorph : ℝ ≃ₜ ℝ :=
  Homeomorph.mulLeft₀ Real.pi (ne_of_gt Real.pi_pos)

def piScaleMeasurableEquiv : ℝ ≃ᵐ ℝ := piScaleHomeomorph.toMeasurableEquiv

@[simp] lemma piScaleHomeomorph_symm_apply (x : ℝ) :
    piScaleHomeomorph.symm x = x / Real.pi := by
  simp [piScaleHomeomorph, Homeomorph.mulLeft₀_symm_apply, div_eq_mul_inv, mul_comm]

@[simp] lemma piScaleMeasurableEquiv_symm_apply (x : ℝ) :
    piScaleMeasurableEquiv.symm x = x / Real.pi := by
  simp [piScaleMeasurableEquiv]

lemma piScale_preimage :
    piScaleMeasurableEquiv ⁻¹' Ioc (0 : ℝ) Real.pi = Ioc (0 : ℝ) 1 := by
  ext x
  change (0 < Real.pi * x ∧ Real.pi * x ≤ Real.pi) ↔ (0 < x ∧ x ≤ 1)
  constructor
  · rintro ⟨hx0, hx1⟩
    constructor
    · by_contra hnot
      have hxle : x ≤ 0 := le_of_not_gt hnot
      have hmul : Real.pi * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        Real.pi_pos.le hxle
      linarith
    · exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mp (by simpa using hx1)
  · rintro ⟨hx0, hx1⟩
    constructor
    · exact mul_pos Real.pi_pos hx0
    · simpa using mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le

/-- `t ↦ πt` sends raw unit-interval volume to normalized period-π volume. -/
lemma measurePreserving_piScale :
    MeasurePreserving piScaleMeasurableEquiv unitMeasure normalizedMeasure := by
  refine ⟨piScaleMeasurableEquiv.measurable, ?_⟩
  have hrestrict := piScaleMeasurableEquiv.restrict_map volume (Ioc (0 : ℝ) Real.pi)
  rw [piScale_preimage] at hrestrict
  change (volume.restrict (Ioc (0 : ℝ) 1)).map piScaleMeasurableEquiv = normalizedMeasure
  rw [← hrestrict]
  change (Measure.map (fun x : ℝ => Real.pi * x) volume).restrict
      (Ioc (0 : ℝ) Real.pi) = normalizedMeasure
  rw [Real.map_volume_mul_left (ne_of_gt Real.pi_pos)]
  simp [normalizedMeasure, Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr Real.pi_pos)]

/-- The inverse affine map preserves the corresponding normalized measures. -/
lemma measurePreserving_piScale_symm :
    MeasurePreserving piScaleMeasurableEquiv.symm normalizedMeasure unitMeasure :=
  MeasurePreserving.symm piScaleMeasurableEquiv measurePreserving_piScale

/-- Actual pullback on the L² classes; this is the normalized unitary candidate. -/
def rescaleLp : PiL2 →ₗᵢ[ℂ] UnitL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ piScaleMeasurableEquiv measurePreserving_piScale

/-- The inverse pullback on the L² classes. -/
def inverseRescaleLp : UnitL2 →ₗᵢ[ℂ] PiL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ piScaleMeasurableEquiv.symm measurePreserving_piScale_symm

def inverseRescaleValue (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x / Real.pi)

def inverseRescaleDerivative (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (Real.pi⁻¹ : ℂ) * g (x / Real.pi)

lemma inverseRescaleLp_ae (f : UnitL2) :
    (inverseRescaleLp f : ℝ → ℂ) =ᵐ[normalizedMeasure]
      inverseRescaleValue (f : ℝ → ℂ) := by
  have h := Lp.coeFn_compMeasurePreserving f measurePreserving_piScale_symm
  filter_upwards [h] with x hx
  simpa [inverseRescaleLp, inverseRescaleValue, piScaleMeasurableEquiv,
    piScaleHomeomorph, Function.comp_def, div_eq_mul_inv, mul_comm] using hx

lemma derivativeInverseRescaleLp_ae (g : UnitL2) :
    ((Real.pi⁻¹ : ℂ) • inverseRescaleLp g : PiL2) =ᵐ[normalizedMeasure]
      inverseRescaleDerivative (g : ℝ → ℂ) := by
  filter_upwards [Lp.coeFn_smul (Real.pi⁻¹ : ℂ) (inverseRescaleLp g),
    inverseRescaleLp_ae g] with x hmul hcomp
  calc
    ((Real.pi⁻¹ : ℂ) • inverseRescaleLp g : PiL2) x =
        (Real.pi⁻¹ : ℂ) * (inverseRescaleLp g : ℝ → ℂ) x := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hmul
    _ = inverseRescaleDerivative (g : ℝ → ℂ) x := by rw [hcomp]; rfl

lemma inverse_rescale_rescale (f : PiL2) : inverseRescaleLp (rescaleLp f) = f := by
  change Lp.compMeasurePreserving piScaleMeasurableEquiv.symm measurePreserving_piScale_symm
      (Lp.compMeasurePreserving piScaleMeasurableEquiv measurePreserving_piScale f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_piScale
    measurePreserving_piScale_symm]
  simp

lemma rescale_inverse_rescale (f : UnitL2) : rescaleLp (inverseRescaleLp f) = f := by
  change Lp.compMeasurePreserving piScaleMeasurableEquiv measurePreserving_piScale
      (Lp.compMeasurePreserving piScaleMeasurableEquiv.symm measurePreserving_piScale_symm f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_piScale_symm
    measurePreserving_piScale]
  simp

/-- The actual normalized L² unitary equivalence `f ↦ f(π·)`. -/
def unitaryRescale : PiL2 ≃ₗᵢ[ℂ] UnitL2 :=
  LinearIsometryEquiv.ofLinearIsometry rescaleLp inverseRescaleLp.toLinearMap
    (LinearMap.ext fun f => rescale_inverse_rescale f)
    (LinearMap.ext fun f => inverse_rescale_rescale f)

/-- A real smooth test on `(0,1)` pulls back to one compactly supported in `(0,π)`. -/
def piTest (ψ : ℝ → ℝ) : ℝ → ℝ := fun x => ψ (x / Real.pi)

lemma piTest_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (piTest ψ) := by
  exact hψ.comp (by fun_prop)

lemma piTest_compact {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (piTest ψ) := by
  let e : ℝ ≃ₜ ℝ := piScaleHomeomorph
  have he : piTest ψ = ψ ∘ e.symm := by
    funext x
    simp [piTest, e, div_eq_mul_inv, mul_comm]
  rw [he]
  exact hψ.comp_homeomorph e.symm

lemma piTest_tsupport {ψ : ℝ → ℝ} (hψ : tsupport ψ ⊆ Ioo (0 : ℝ) 1) :
    tsupport (piTest ψ) ⊆ Ioo (0 : ℝ) Real.pi := by
  let e : ℝ ≃ₜ ℝ := piScaleHomeomorph
  have he : piTest ψ = ψ ∘ e.symm := by
    funext x
    simp [piTest, e, div_eq_mul_inv, mul_comm]
  rw [he, tsupport_comp_eq_preimage ψ e.symm]
  intro x hx
  have hx' : e.symm x ∈ Ioo (0 : ℝ) 1 := hψ hx
  have hxe : x = e (e.symm x) := (e.apply_symm_apply x).symm
  rw [hxe]
  rcases hx' with ⟨hx0, hx1⟩
  change 0 < Real.pi * e.symm x ∧ Real.pi * e.symm x < Real.pi
  constructor
  · exact mul_pos Real.pi_pos hx0
  · calc
      Real.pi * e.symm x < Real.pi * 1 := mul_lt_mul_of_pos_left hx1 Real.pi_pos
      _ = Real.pi := by ring

lemma deriv_piTest (ψ : ℝ → ℝ) (x : ℝ) :
    deriv (piTest ψ) x = Real.pi⁻¹ * deriv ψ (x / Real.pi) := by
  rw [show piTest ψ = fun x => ψ (Real.pi⁻¹ * x) by
    funext y
    simp [piTest, div_eq_mul_inv, mul_comm]]
  rw [deriv_comp_mul_left]
  simp [div_eq_mul_inv, mul_comm]

/-- Literal distributional derivative transports with the chain-rule factor π. -/
theorem weakDerivative_rescale {f g : ℝ → ℂ}
    (hfg : NlsGge.Atomic.PeriodPi.HasWeakDerivative f g) :
    NlsGge.Atomic.Interval.HasWeakDerivative (rescaleValue f) (rescaleDerivative g) := by
  intro ψ hψd hψc hψs
  let F : ℝ → ℂ := fun x => f x * ((deriv (piTest ψ) x : ℝ) : ℂ)
  let G : ℝ → ℂ := fun x => g x * (piTest ψ x : ℂ)
  have hleftPoint (t : ℝ) :
      (Real.pi : ℂ) * F (Real.pi * t) =
        rescaleValue f t * ((deriv ψ t : ℝ) : ℂ) := by
    dsimp [F]
    rw [deriv_piTest]
    simp only [rescaleValue]
    have harg : (Real.pi * t) / Real.pi = t := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hrightPoint (t : ℝ) :
      (Real.pi : ℂ) * G (Real.pi * t) =
        rescaleDerivative g t * (ψ t : ℂ) := by
    dsimp [G, rescaleDerivative]
    have harg : (Real.pi * t) / Real.pi = t := by
      field_simp [Real.pi_ne_zero]
    simp only [piTest, harg]
    ring
  have hleft :
      (∫ t in (0 : ℝ)..1,
        rescaleValue f t * ((deriv ψ t : ℝ) : ℂ)) =
      (∫ x in (0 : ℝ)..Real.pi, F x) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (Real.pi : ℂ) * F (Real.pi * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hleftPoint t).symm
      _ = (Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, F (Real.pi * t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..Real.pi, F x := by
        simpa only [Complex.real_smul, mul_zero, mul_one] using
          (intervalIntegral.smul_integral_comp_mul_left (f := F)
            (a := (0 : ℝ)) (b := (1 : ℝ)) Real.pi)
  have hright :
      (∫ t in (0 : ℝ)..1, rescaleDerivative g t * (ψ t : ℂ)) =
      (∫ x in (0 : ℝ)..Real.pi, G x) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (Real.pi : ℂ) * G (Real.pi * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hrightPoint t).symm
      _ = (Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, G (Real.pi * t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ x in (0 : ℝ)..Real.pi, G x := by
        simpa only [Complex.real_smul, mul_zero, mul_one] using
          (intervalIntegral.smul_integral_comp_mul_left (f := G)
            (a := (0 : ℝ)) (b := (1 : ℝ)) Real.pi)
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi,
        f x * ((deriv (piTest ψ) x : ℝ) : ℂ) := by
          simpa [F] using hleft
    _ = -(∫ x in (0 : ℝ)..Real.pi, g x * (piTest ψ x : ℂ)) :=
          hfg (piTest ψ) (piTest_contDiff hψd) (piTest_compact hψc)
            (piTest_tsupport hψs)
    _ = -(∫ t in (0 : ℝ)..1, rescaleDerivative g t * (ψ t : ℂ)) := by
          rw [← hright]

/-- Replacing weak-graph representatives on a null set does not change the literal test identity. -/
lemma weakDerivative_congr_ae {f f' g g' : ℝ → ℂ}
    (hf : f =ᵐ[unitMeasure] f') (hg : g =ᵐ[unitMeasure] g')
    (hfg : NlsGge.Atomic.Interval.HasWeakDerivative f g) :
    NlsGge.Atomic.Interval.HasWeakDerivative f' g' := by
  intro ψ hψd hψc hψs
  have hf' : f' =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] f := by
    simpa [unitMeasure, uIoc_of_le zero_le_one] using hf.symm
  have hg' : g =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] g' := by
    simpa [unitMeasure, uIoc_of_le zero_le_one] using hg
  calc
    (∫ x in (0 : ℝ)..1, f' x * ((deriv ψ x : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..1, f x * ((deriv ψ x : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hf'] with x hx
          rw [hx]
    _ = -(∫ x in (0 : ℝ)..1, g x * (ψ x : ℂ)) := hfg ψ hψd hψc hψs
    _ = -(∫ x in (0 : ℝ)..1, g' x * (ψ x : ℂ)) := by
          congr 1
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hg'] with x hx
          rw [hx]

lemma weakDerivative_congr_ae_pi {f f' g g' : ℝ → ℂ}
    (hf : f =ᵐ[normalizedMeasure] f') (hg : g =ᵐ[normalizedMeasure] g')
    (hfg : NlsGge.Atomic.PeriodPi.HasWeakDerivative f g) :
    NlsGge.Atomic.PeriodPi.HasWeakDerivative f' g' := by
  intro ψ hψd hψc hψs
  have hscale : ENNReal.ofReal (Real.pi⁻¹) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr Real.pi_pos)
  have hfRaw : f' =ᵐ[volume.restrict (Ioc (0 : ℝ) Real.pi)] f := by
    have h := (Measure.ae_ennreal_smul_measure_iff
      (c := ENNReal.ofReal (Real.pi⁻¹)) hscale).mp hf.symm
    filter_upwards [h] with x hx
    exact hx
  have hgRaw : g =ᵐ[volume.restrict (Ioc (0 : ℝ) Real.pi)] g' := by
    have h := (Measure.ae_ennreal_smul_measure_iff
      (c := ENNReal.ofReal (Real.pi⁻¹)) hscale).mp hg
    filter_upwards [h] with x hx
    exact hx
  have hf' : f' =ᵐ[volume.restrict (uIoc (0 : ℝ) Real.pi)] f := by
    simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hfRaw
  have hg' : g =ᵐ[volume.restrict (uIoc (0 : ℝ) Real.pi)] g' := by
    simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hgRaw
  calc
    (∫ x in (0 : ℝ)..Real.pi, f' x * ((deriv ψ x : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..Real.pi, f x * ((deriv ψ x : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hf'] with x hx
          rw [hx]
    _ = -(∫ x in (0 : ℝ)..Real.pi, g x * (ψ x : ℂ)) := hfg ψ hψd hψc hψs
    _ = -(∫ x in (0 : ℝ)..Real.pi, g' x * (ψ x : ℂ)) := by
          congr 1
          apply intervalIntegral.integral_congr_ae_restrict
          filter_upwards [hg'] with x hx
          rw [hx]

def unitTest (ψ : ℝ → ℝ) : ℝ → ℝ := fun t => ψ (Real.pi * t)

lemma unitTest_contDiff {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (unitTest ψ) := hψ.comp (by fun_prop)

lemma unitTest_compact {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (unitTest ψ) := by
  exact hψ.comp_homeomorph piScaleHomeomorph

lemma unitTest_tsupport {ψ : ℝ → ℝ}
    (hψ : tsupport ψ ⊆ Ioo (0 : ℝ) Real.pi) :
    tsupport (unitTest ψ) ⊆ Ioo (0 : ℝ) 1 := by
  rw [show unitTest ψ = ψ ∘ piScaleHomeomorph by rfl,
    tsupport_comp_eq_preimage ψ piScaleHomeomorph]
  intro t ht
  have hπt := hψ ht
  change 0 < Real.pi * t ∧ Real.pi * t < Real.pi at hπt
  constructor
  · exact (mul_pos_iff_of_pos_left Real.pi_pos).mp hπt.1
  · have h' : Real.pi * t < Real.pi * 1 := by simpa using hπt.2
    exact (mul_lt_mul_iff_of_pos_left Real.pi_pos).mp h'

lemma deriv_unitTest (ψ : ℝ → ℝ) (t : ℝ) :
    deriv (unitTest ψ) t = Real.pi * deriv ψ (Real.pi * t) := by
  rw [show unitTest ψ = fun t => ψ (Real.pi * t) by rfl, deriv_comp_mul_left]
  simp

/-- The affine inverse transports the literal unit weak graph to the literal π weak graph. -/
theorem weakDerivative_inverseRescale {f g : ℝ → ℂ}
    (hfg : NlsGge.Atomic.Interval.HasWeakDerivative f g) :
    NlsGge.Atomic.PeriodPi.HasWeakDerivative
      (inverseRescaleValue f) (inverseRescaleDerivative g) := by
  intro ψ hψd hψc hψs
  let F : ℝ → ℂ := fun x => inverseRescaleValue f x * ((deriv ψ x : ℝ) : ℂ)
  let G : ℝ → ℂ := fun x => inverseRescaleDerivative g x * (ψ x : ℂ)
  have hχd := unitTest_contDiff hψd
  have hχc := unitTest_compact hψc
  have hχs := unitTest_tsupport hψs
  have hleftPoint (t : ℝ) :
      (Real.pi : ℂ) * F (Real.pi * t) =
        f t * ((deriv (unitTest ψ) t : ℝ) : ℂ) := by
    dsimp [F, inverseRescaleValue]
    rw [deriv_unitTest]
    have harg : (Real.pi * t) / Real.pi = t := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    push_cast
    ring
  have hrightPoint (t : ℝ) :
      (Real.pi : ℂ) * G (Real.pi * t) = g t * (unitTest ψ t : ℂ) := by
    dsimp [G, inverseRescaleDerivative, unitTest]
    have harg : (Real.pi * t) / Real.pi = t := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hleft :
      (∫ x in (0 : ℝ)..Real.pi, F x) =
        ∫ t in (0 : ℝ)..1, f t * ((deriv (unitTest ψ) t : ℝ) : ℂ) := by
    calc
      _ = (Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, F (Real.pi * t) := by
        simpa only [Complex.real_smul, mul_zero, mul_one] using
          (intervalIntegral.smul_integral_comp_mul_left (f := F)
            (a := (0 : ℝ)) (b := (1 : ℝ)) Real.pi).symm
      _ = ∫ t in (0 : ℝ)..1, (Real.pi : ℂ) * F (Real.pi * t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hleftPoint t
  have hright :
      (∫ x in (0 : ℝ)..Real.pi, G x) =
        ∫ t in (0 : ℝ)..1, g t * (unitTest ψ t : ℂ) := by
    calc
      _ = (Real.pi : ℂ) * ∫ t in (0 : ℝ)..1, G (Real.pi * t) := by
        simpa only [Complex.real_smul, mul_zero, mul_one] using
          (intervalIntegral.smul_integral_comp_mul_left (f := G)
            (a := (0 : ℝ)) (b := (1 : ℝ)) Real.pi).symm
      _ = ∫ t in (0 : ℝ)..1, (Real.pi : ℂ) * G (Real.pi * t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hrightPoint t
  calc
    _ = ∫ x in (0 : ℝ)..Real.pi, F x := by rfl
    _ = ∫ t in (0 : ℝ)..1, f t * ((deriv (unitTest ψ) t : ℝ) : ℂ) := hleft
    _ = -(∫ t in (0 : ℝ)..1, g t * (unitTest ψ t : ℂ)) :=
      hfg (unitTest ψ) hχd hχc hχs
    _ = -(∫ x in (0 : ℝ)..Real.pi, G x) := by rw [hright]

lemma rescaleLp_ae (f : PiL2) :
    (rescaleLp f : ℝ → ℂ) =ᵐ[unitMeasure] rescaleValue (f : ℝ → ℂ) := by
  have hmap : rescaleLp f =
      Lp.compMeasurePreserving piScaleMeasurableEquiv measurePreserving_piScale f := rfl
  rw [hmap]
  change (Lp.compMeasurePreserving piScaleMeasurableEquiv measurePreserving_piScale f :
    ℝ → ℂ) =ᵐ[unitMeasure] fun t => (f : ℝ → ℂ) (Real.pi * t)
  exact Lp.coeFn_compMeasurePreserving f measurePreserving_piScale

lemma derivativeRescaleLp_ae (g : PiL2) :
    (((Real.pi : ℂ) • rescaleLp g : UnitL2) : ℝ → ℂ) =ᵐ[unitMeasure]
      rescaleDerivative (g : ℝ → ℂ) := by
  filter_upwards [Lp.coeFn_smul (Real.pi : ℂ) (rescaleLp g), rescaleLp_ae g]
    with t hmul hcomp
  calc
    ((Real.pi : ℂ) • rescaleLp g : UnitL2) t =
        (Real.pi : ℂ) * (rescaleLp g : ℝ → ℂ) t := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hmul
    _ = rescaleDerivative (g : ℝ → ℂ) t := by rw [hcomp]; rfl

/-- The literal weak graph transports to the existing unit H¹ graph with derivative factor π. -/
def rescaleH1 (f : NlsGge.Atomic.PeriodPi.H1) : NlsGge.Atomic.Interval.H1 where
  value := rescaleLp f.value
  derivative := (Real.pi : ℂ) • rescaleLp f.derivative
  weak := weakDerivative_congr_ae (rescaleLp_ae f.value).symm
    (derivativeRescaleLp_ae f.derivative).symm (weakDerivative_rescale f.weak)

abbrev UnitH1Pair := Bool → NlsGge.Atomic.Interval.H1
abbrev PiH1Pair := Bool → NlsGge.Atomic.PeriodPi.H1

/-- The actual inverse affine map transports the unit H¹ graph back to the π interval. -/
def inverseRescaleH1 (f : NlsGge.Atomic.Interval.H1) : NlsGge.Atomic.PeriodPi.H1 where
  value := inverseRescaleLp f.value
  derivative := (Real.pi⁻¹ : ℂ) • inverseRescaleLp f.derivative
  weak := weakDerivative_congr_ae_pi (inverseRescaleLp_ae f.value).symm
    (derivativeInverseRescaleLp_ae f.derivative).symm
    (weakDerivative_inverseRescale f.weak)

def inverseRescaleH1Pair (f : UnitH1Pair) : PiH1Pair := fun b => inverseRescaleH1 (f b)

theorem rescale_inverseRescaleH1 (f : NlsGge.Atomic.Interval.H1) :
    rescaleH1 (inverseRescaleH1 f) = f := by
  cases f with
  | mk value derivative weak =>
    simp only [rescaleH1, inverseRescaleH1]
    have hv := rescale_inverse_rescale value
    have hd := rescale_inverse_rescale derivative
    simp [hv, hd, smul_smul, Complex.ofReal_inv, Real.pi_ne_zero]

theorem inverseRescale_rescaleH1 (f : NlsGge.Atomic.PeriodPi.H1) :
    inverseRescaleH1 (rescaleH1 f) = f := by
  cases f with
  | mk value derivative weak =>
    simp only [rescaleH1, inverseRescaleH1]
    have hv := inverse_rescale_rescale value
    have hd := inverse_rescale_rescale derivative
    have hd' : inverseRescaleLp ((Real.pi : ℂ) • rescaleLp derivative) =
        (Real.pi : ℂ) • derivative := by
      rw [map_smul, inverse_rescale_rescale]
    have hder : (Real.pi⁻¹ : ℂ) • inverseRescaleLp
        ((Real.pi : ℂ) • rescaleLp derivative) = derivative := by
      calc
        _ = (Real.pi⁻¹ : ℂ) • ((Real.pi : ℂ) • derivative) := by rw [hd']
        _ = derivative := by
          rw [smul_smul]
          congr 1
          norm_num [Complex.ofReal_inv, Real.pi_ne_zero]
    simp only [NlsGge.Atomic.PeriodPi.H1.mk.injEq]
    exact ⟨hv, hder⟩

abbrev PiPairL2 := NlsGge.Atomic.PeriodPi.SourcePairL2
abbrev UnitPairL2 := NlsGge.Schur.SourcePairL2

/-- Componentwise normalized rescaling on the actual Bool sum-of-squares carriers. -/
def unitaryRescalePair : PiPairL2 ≃ₗᵢ[ℂ] UnitPairL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool => unitaryRescale)

@[simp] theorem unitaryRescalePair_apply (f : PiPairL2) :
    unitaryRescalePair f = WithLp.toLp 2 (fun b => unitaryRescale (f b)) := rfl

def rescaleH1Pair (f : PiH1Pair) : Bool → NlsGge.Atomic.Interval.H1 :=
  fun b => rescaleH1 (f b)

/-- Restriction of the affine inverse to the closed intervals, for canonical representatives. -/
def piToUnitIcc (x : Icc (0 : ℝ) Real.pi) : Icc (0 : ℝ) 1 :=
  ⟨x.1 / Real.pi, ⟨div_nonneg x.2.1 (le_of_lt Real.pi_pos),
    (div_le_iff₀ Real.pi_pos).2 (by nlinarith [x.2.2])⟩⟩

def piToUnitIccContinuous : C(Icc (0 : ℝ) Real.pi, Icc (0 : ℝ) 1) :=
  ⟨piToUnitIcc, Continuous.subtype_mk (by fun_prop)
    (fun x => (piToUnitIcc x).property)⟩

/-- Canonical π-interval representative obtained from LIB-026's unit-interval representative. -/
def representativePi (f : NlsGge.Atomic.PeriodPi.H1) :
    C(Icc (0 : ℝ) Real.pi, ℂ) :=
  ⟨fun x => NlsGge.Atomic.LIB026.representative (rescaleH1 f) (piToUnitIcc x),
    (NlsGge.Atomic.LIB026.representative (rescaleH1 f)).continuous.comp
      piToUnitIccContinuous.continuous⟩

def representativePiExtend (f : NlsGge.Atomic.PeriodPi.H1) : ℝ → ℂ :=
  Set.IccExtend (le_of_lt Real.pi_pos) (representativePi f)

def unitRepresentativeExtend (f : NlsGge.Atomic.PeriodPi.H1) : ℝ → ℂ :=
  Set.IccExtend zero_le_one (NlsGge.Atomic.LIB026.representative (rescaleH1 f))

def tracePiLeft (f : NlsGge.Atomic.PeriodPi.H1) : ℂ :=
  representativePi f ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩

def tracePiRight (f : NlsGge.Atomic.PeriodPi.H1) : ℂ :=
  representativePi f ⟨Real.pi, ⟨Real.pi_pos.le, le_rfl⟩⟩

lemma tracePiLeft_eq_unit (f : NlsGge.Atomic.PeriodPi.H1) :
    tracePiLeft f = NlsGge.Atomic.LIB026.traceLeft (rescaleH1 f) := by
  change NlsGge.Atomic.LIB026.representative (rescaleH1 f)
      (piToUnitIcc ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩) =
    NlsGge.Atomic.LIB026.representative (rescaleH1 f) ⟨0, by norm_num⟩
  congr 1
  apply Subtype.ext
  simp [piToUnitIcc]

lemma tracePiRight_eq_unit (f : NlsGge.Atomic.PeriodPi.H1) :
    tracePiRight f = NlsGge.Atomic.LIB026.traceRight (rescaleH1 f) := by
  change NlsGge.Atomic.LIB026.representative (rescaleH1 f)
      (piToUnitIcc ⟨Real.pi, ⟨Real.pi_pos.le, le_rfl⟩⟩) =
    NlsGge.Atomic.LIB026.representative (rescaleH1 f) ⟨1, by norm_num⟩
  congr 1
  apply Subtype.ext
  simp [piToUnitIcc]

lemma tracePiLeft_inverse (f : NlsGge.Atomic.Interval.H1) :
    tracePiLeft (inverseRescaleH1 f) = NlsGge.Atomic.LIB026.traceLeft f := by
  rw [tracePiLeft_eq_unit, rescale_inverseRescaleH1]

lemma tracePiRight_inverse (f : NlsGge.Atomic.Interval.H1) :
    tracePiRight (inverseRescaleH1 f) = NlsGge.Atomic.LIB026.traceRight f := by
  rw [tracePiRight_eq_unit, rescale_inverseRescaleH1]

lemma representativePiExtend_eq_of_mem (f : NlsGge.Atomic.PeriodPi.H1)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) Real.pi) :
    representativePiExtend f x =
      unitRepresentativeExtend f (piScaleMeasurableEquiv.symm x) := by
  have hxPi : x ∈ Icc (0 : ℝ) Real.pi := ⟨hx.1.le, hx.2⟩
  have hxUnit : piScaleMeasurableEquiv.symm x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have hform : piScaleMeasurableEquiv.symm x = x / Real.pi := by
        simp [piScaleMeasurableEquiv, piScaleHomeomorph, div_eq_mul_inv, mul_comm]
      rw [hform]
      exact div_nonneg hx.1.le (le_of_lt Real.pi_pos)
    · have hform : piScaleMeasurableEquiv.symm x = x / Real.pi := by
        simp [piScaleMeasurableEquiv, piScaleHomeomorph, div_eq_mul_inv, mul_comm]
      rw [hform, div_le_iff₀ Real.pi_pos]
      nlinarith [hx.2]
  have hsub : piToUnitIcc ⟨x, hxPi⟩ = ⟨piScaleMeasurableEquiv.symm x, hxUnit⟩ := by
    apply Subtype.ext
    simp [piToUnitIcc, piScaleMeasurableEquiv, piScaleHomeomorph,
      div_eq_mul_inv, mul_comm]
  rw [representativePiExtend, Set.IccExtend_of_mem (le_of_lt Real.pi_pos)
    (representativePi f) hxPi,
    unitRepresentativeExtend, Set.IccExtend_of_mem zero_le_one
      (NlsGge.Atomic.LIB026.representative (rescaleH1 f)) hxUnit]
  change NlsGge.Atomic.LIB026.representative (rescaleH1 f) (piToUnitIcc ⟨x, hxPi⟩) = _
  rw [hsub]

lemma representativePiExtend_ae (f : NlsGge.Atomic.PeriodPi.H1) :
    representativePiExtend f =ᵐ[normalizedMeasure] (f.value : ℝ → ℂ) := by
  have hdom : ∀ᵐ x ∂normalizedMeasure, x ∈ Ioc (0 : ℝ) Real.pi := by
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  have hrepUnit : unitRepresentativeExtend f =ᵐ[unitMeasure]
      (rescaleLp f.value : ℝ → ℂ) := by
    simpa [unitRepresentativeExtend, rescaleH1, unitMeasure] using
      NlsGge.Atomic.LIB026.representative_ae (rescaleH1 f)
  have hpull : (fun x => unitRepresentativeExtend f (piScaleMeasurableEquiv.symm x)) =ᵐ[
      normalizedMeasure] fun x => rescaleLp f.value (piScaleMeasurableEquiv.symm x) := by
    simpa [Function.comp_def] using
      measurePreserving_piScale_symm.quasiMeasurePreserving.ae_eq_comp hrepUnit
  have hcomp : (inverseRescaleLp (rescaleLp f.value) : ℝ → ℂ) =ᵐ[normalizedMeasure]
      fun x => rescaleLp f.value (piScaleMeasurableEquiv.symm x) := by
    change (Lp.compMeasurePreserving piScaleMeasurableEquiv.symm
      measurePreserving_piScale_symm (rescaleLp f.value) : ℝ → ℂ) =ᵐ[normalizedMeasure] _
    exact Lp.coeFn_compMeasurePreserving (rescaleLp f.value) measurePreserving_piScale_symm
  have hback : (fun x => rescaleLp f.value (piScaleMeasurableEquiv.symm x)) =ᵐ[
      normalizedMeasure] (f.value : ℝ → ℂ) := by
    calc
      (fun x => rescaleLp f.value (piScaleMeasurableEquiv.symm x)) =ᵐ[normalizedMeasure]
          (inverseRescaleLp (rescaleLp f.value) : ℝ → ℂ) := hcomp.symm
      _ =ᵐ[normalizedMeasure] (f.value : ℝ → ℂ) :=
          Lp.ext_iff.mp (inverse_rescale_rescale f.value)
  have hpiRep : representativePiExtend f =ᵐ[normalizedMeasure]
      fun x => unitRepresentativeExtend f (piScaleMeasurableEquiv.symm x) := by
    filter_upwards [hdom] with x hx
    exact representativePiExtend_eq_of_mem f hx
  exact hpiRep.trans (hpull.trans hback)

def IsPeriodicBoundary (f : PiH1Pair) : Prop :=
  ∀ b, tracePiRight (f b) = tracePiLeft (f b)

def IsAntiperiodicBoundary (f : PiH1Pair) : Prop :=
  ∀ b, tracePiRight (f b) = -tracePiLeft (f b)

lemma periodicBoundary_rescale (f : PiH1Pair) (h : IsPeriodicBoundary f) :
    ∀ b, NlsGge.Atomic.LIB026.traceRight (rescaleH1 (f b)) =
      NlsGge.Atomic.LIB026.traceLeft (rescaleH1 (f b)) := by
  intro b
  rw [← tracePiRight_eq_unit, ← tracePiLeft_eq_unit]
  exact h b

lemma antiperiodicBoundary_rescale (f : PiH1Pair) (h : IsAntiperiodicBoundary f) :
    ∀ b, NlsGge.Atomic.LIB026.traceRight (rescaleH1 (f b)) =
      -NlsGge.Atomic.LIB026.traceLeft (rescaleH1 (f b)) := by
  intro b
  rw [← tracePiRight_eq_unit, ← tracePiLeft_eq_unit]
  exact h b

lemma periodicBoundary_iff (f : PiH1Pair) : IsPeriodicBoundary f ↔
    ∀ b, NlsGge.Atomic.LIB026.traceRight (rescaleH1 (f b)) =
      NlsGge.Atomic.LIB026.traceLeft (rescaleH1 (f b)) := by
  constructor
  · exact periodicBoundary_rescale f
  · intro h b
    rw [tracePiRight_eq_unit, tracePiLeft_eq_unit]
    exact h b

lemma antiperiodicBoundary_iff (f : PiH1Pair) : IsAntiperiodicBoundary f ↔
    ∀ b, NlsGge.Atomic.LIB026.traceRight (rescaleH1 (f b)) =
      -NlsGge.Atomic.LIB026.traceLeft (rescaleH1 (f b)) := by
  constructor
  · exact antiperiodicBoundary_rescale f
  · intro h b
    rw [tracePiRight_eq_unit, tracePiLeft_eq_unit]
    exact h b

open NlsGge.Atomic.Interval

/-- The period-one potential obtained by the actual normalized pullback and scale. -/
def scaledPotential (v : PiPairL2) : UnitPairL2 :=
  (Real.pi : ℂ) • unitaryRescalePair v

lemma scaledPotential_ae (v : PiPairL2) (b : Bool) :
    (scaledPotential v b : ℝ → ℂ) =ᵐ[unitMeasure]
      fun t => (Real.pi : ℂ) * (v b : ℝ → ℂ) (Real.pi * t) := by
  have hcomponent : (scaledPotential v b : UnitL2) =
      (Real.pi : ℂ) • unitaryRescale (v b) := by
    change ((Real.pi : ℂ) • unitaryRescalePair v) b = _
    rw [unitaryRescalePair_apply]
    rfl
  filter_upwards [Lp.coeFn_smul (Real.pi : ℂ) (unitaryRescale (v b)),
    rescaleLp_ae (v b)] with t hsm hcomp
  have hu : unitaryRescale (v b) = rescaleLp (v b) := rfl
  have hcomponentFn := congrArg (fun u : UnitL2 => u t) hcomponent
  calc
    (scaledPotential v b : ℝ → ℂ) t =
        ((Real.pi : ℂ) • unitaryRescale (v b) : UnitL2) t := hcomponentFn
    _ = (Real.pi : ℂ) • (unitaryRescale (v b) : ℝ → ℂ) t := hsm
    _ = (Real.pi : ℂ) * (rescaleLp (v b) : ℝ → ℂ) t := by
      rw [hu]
      simp [Pi.smul_apply, smul_eq_mul]
    _ = (Real.pi : ℂ) * (v b : ℝ → ℂ) (Real.pi * t) := by rw [hcomp]; rfl

/-- The literal π-periodic interval Dirac expression, using its canonical H¹ representative.
This is independent of the unit-period action and imposes no boundary condition. -/
def piZSExpression (v : PiPairL2) (f : PiH1Pair) (b : Bool) (x : ℝ) : ℂ :=
  (if b then Complex.I else -Complex.I) * (f b).derivative x +
    (v b) x * representativePiExtend (f (!b)) x

lemma representativePi_memLp_top (f : PiH1Pair) (b : Bool) :
    MemLp (representativePiExtend (f b)) ∞ normalizedMeasure := by
  have hcontinuous : Continuous (representativePiExtend (f b)) :=
    (representativePi (f b)).continuous.Icc_extend'
  apply memLp_top_of_bound hcontinuous.aestronglyMeasurable
    (‖(f b).value‖ + Real.pi * ‖(f b).derivative‖)
  have hdom : ∀ᵐ x ∂normalizedMeasure, x ∈ Ioc (0 : ℝ) Real.pi := by
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _
  filter_upwards [hdom] with x hx
  rw [representativePiExtend_eq_of_mem (f b) hx]
  have hxform : piScaleMeasurableEquiv.symm x = x / Real.pi := by
    simp [piScaleMeasurableEquiv, piScaleHomeomorph, div_eq_mul_inv, mul_comm]
  have hxUnit : piScaleMeasurableEquiv.symm x ∈ Icc (0 : ℝ) 1 := by
    rw [hxform]
    exact ⟨div_nonneg hx.1.le (le_of_lt Real.pi_pos),
      (div_le_iff₀ Real.pi_pos).2 (by change x ≤ 1 * Real.pi; nlinarith [hx.2])⟩
  rw [unitRepresentativeExtend, Set.IccExtend_of_mem zero_le_one
    (NlsGge.Atomic.LIB026.representative (rescaleH1 (f b))) hxUnit]
  have hunit := NlsGge.Atomic.LIB026.representative_norm_le
    (rescaleH1 (f b)) ⟨piScaleMeasurableEquiv.symm x, hxUnit⟩
  have hnormVal : ‖rescaleLp (f b).value‖ = ‖(f b).value‖ :=
    rescaleLp.norm_map _
  have hnormDeriv : ‖(Real.pi : ℂ) • rescaleLp (f b).derivative‖ =
      Real.pi * ‖(f b).derivative‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      rescaleLp.norm_map]
  calc
    ‖NlsGge.Atomic.LIB026.representative (rescaleH1 (f b))
        ⟨piScaleMeasurableEquiv.symm x, hxUnit⟩‖ ≤
        ‖(rescaleH1 (f b)).value‖ + ‖(rescaleH1 (f b)).derivative‖ := hunit
    _ = ‖(f b).value‖ + Real.pi * ‖(f b).derivative‖ := by
      simp only [rescaleH1]
      rw [hnormVal, hnormDeriv]

/-- The raw period-π Dirac expression belongs to the actual normalized L² carrier. -/
lemma piZSExpression_memLp (v : PiPairL2) (f : PiH1Pair) (b : Bool) :
    MemLp (piZSExpression v f b) 2 normalizedMeasure := by
  by_cases hb : b
  · simp [piZSExpression, hb]
    exact ((Lp.memLp (f true).derivative).const_mul Complex.I).add
      ((Lp.memLp (v true)).mul (representativePi_memLp_top f false))
  · simp [piZSExpression, hb]
    exact ((Lp.memLp (f false).derivative).const_mul (-Complex.I)).add
      ((Lp.memLp (v false)).mul (representativePi_memLp_top f true))

/-- The π-periodic interval action, built from the literal differential expression. -/
def piZSApply (v : PiPairL2) (f : PiH1Pair) : PiPairL2 :=
  WithLp.toLp 2 (fun b => (piZSExpression_memLp v f b).toLp (piZSExpression v f b))

lemma piZSApply_ae (v : PiPairL2) (f : PiH1Pair) (b : Bool) :
    (fun x => piZSApply v f b x) =ᵐ[normalizedMeasure] piZSExpression v f b :=
  (piZSExpression_memLp v f b).coeFn_toLp

lemma representativePi_comp_scale_ae (f : NlsGge.Atomic.PeriodPi.H1) :
    (fun t => representativePiExtend f (Real.pi * t)) =ᵐ[unitMeasure]
      fun t => (f.value : ℝ → ℂ) (Real.pi * t) := by
  have h := measurePreserving_piScale.quasiMeasurePreserving.ae_eq_comp
    (representativePiExtend_ae f)
  simpa [Function.comp_def, piScaleMeasurableEquiv, piScaleHomeomorph] using h

lemma unitZSExpression_rescale_ae (v : PiPairL2) (f : PiH1Pair) (b : Bool) :
    (zsExpression (scaledPotential v)
      (fun c x => (rescaleH1Pair f c).value x)
      (fun c x => (rescaleH1Pair f c).derivative x) b) =ᵐ[unitMeasure]
        fun t => (Real.pi : ℂ) * piZSExpression v f b (Real.pi * t) := by
  have hp := scaledPotential_ae v b
  have hd := derivativeRescaleLp_ae (f b).derivative
  have hv := rescaleLp_ae (f (!b)).value
  have hr := representativePi_comp_scale_ae (f (!b))
  filter_upwards [hp, hd, hv, hr] with t hp hd hv hr
  dsimp [zsExpression, piZSExpression, scaledPotential, rescaleH1Pair,
    rescaleH1, unitaryRescalePair] at *
  rw [hp, hd, hv, hr]
  simp only [rescaleDerivative, rescaleValue]
  ring

lemma piZSApply_comp_scale_ae (v : PiPairL2) (f : PiH1Pair) (b : Bool) :
    (fun t => piZSApply v f b (Real.pi * t)) =ᵐ[unitMeasure]
      fun t => piZSExpression v f b (Real.pi * t) := by
  have h := measurePreserving_piScale.quasiMeasurePreserving.ae_eq_comp
    (piZSApply_ae v f b)
  simpa [Function.comp_def, piScaleMeasurableEquiv, piScaleHomeomorph] using h

/-- The genuine unit-period Zakharov–Shabat action intertwines with the literal π-period action.
The latter was constructed independently from its differential expression and L² proof. -/
theorem dirac_period_rescaling (v : PiPairL2) (f : PiH1Pair) :
    zsApply (scaledPotential v) (rescaleH1Pair f) =
      (Real.pi : ℂ) • unitaryRescalePair (piZSApply v f) := by
  apply PiLp.ext
  intro b
  change (zsApply (scaledPotential v) (rescaleH1Pair f) b) =
    (Real.pi : ℂ) • unitaryRescale (piZSApply v f b)
  apply Lp.ext_iff.mpr
  have hleft := zsApply_ae (scaledPotential v) (rescaleH1Pair f) b
  have hright := rescaleLp_ae (piZSApply v f b)
  have hpi := piZSApply_comp_scale_ae v f b
  have hformula := unitZSExpression_rescale_ae v f b
  have hunit := Lp.coeFn_smul (Real.pi : ℂ) (unitaryRescale (piZSApply v f b))
  have hu : unitaryRescale (piZSApply v f b) = rescaleLp (piZSApply v f b) := rfl
  filter_upwards [hleft, hright, hpi, hformula, hunit]
    with t hleft hright hpi hformula hunit
  calc
    (zsApply (scaledPotential v) (rescaleH1Pair f) b) t =
        zsExpression (scaledPotential v)
          (fun c x => (rescaleH1Pair f c).value x)
          (fun c x => (rescaleH1Pair f c).derivative x) b t := hleft
    _ = (Real.pi : ℂ) * piZSExpression v f b (Real.pi * t) := hformula
    _ = (Real.pi : ℂ) * (piZSApply v f b) (Real.pi * t) := by rw [← hpi]
    _ = (Real.pi : ℂ) * (rescaleLp (piZSApply v f b) : ℝ → ℂ) t := by
      rw [hright]
      rfl
    _ = (Real.pi : ℂ) • (rescaleLp (piZSApply v f b) : ℝ → ℂ) t := by
      simp [Pi.smul_apply, smul_eq_mul]
    _ = (Real.pi : ℂ) • (unitaryRescale (piZSApply v f b) : ℝ → ℂ) t := by rw [← hu]
    _ = ((Real.pi : ℂ) • unitaryRescale (piZSApply v f b) : UnitL2) t := hunit.symm

end NlsGge.Atomic.DM001
