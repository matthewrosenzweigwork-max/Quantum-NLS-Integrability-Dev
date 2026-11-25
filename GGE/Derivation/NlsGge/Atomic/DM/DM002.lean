/- DM-002 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/DM002_N08_PROOF01.lean.txt = proof development/DM002_FULL_01.lean.txt (nodes 01-07, 09; author proof development) plus node 08 (author proof development),
   byte-identical (a script diff against FULL_01 shows only 5 added import lines and the appended node-08 block). Independent review: proof development/DM-002_REVIEW01.md (statement identity with the supplemental design for all 19 theorems and 19 definitions, compile + closure probe).
   Target NlsGge/Atomic/DM/DM002.lean (namespace NlsGge.Atomic.DM002, helper namespace N08). -/
import Mathlib
import NlsGge.Atomic.DM.DM001
import NlsGge.Atomic.LIB.LIB001
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.LIB.LIB033
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumMonotoneE02_38
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.PairAnalyticDet
import NlsGge.Spectral.ComplexACPointwiseTestIntegrationByPartsV2
import NlsGge.Atomic.LIB.LIB026

set_option autoImplicit false

/-! DM-002 stage 1 (proof development, AUTHOR; not self-reviewed): nodes DM002.01-DM002.03, DM002.06, DM002.07, DM002.09. -/

/-! OMITTED design node (not proved here): DM002.08 `dm_endpoint_eigenvectors`.
It needs a new adapter from the sector-n physical eigenvectors
(`actualSourceEigenvalue_iff_halfTrace_E02_38`) to interval H1 pairs with the label boundary
condition; the main theorem DM002.09 `dirac_rescale_spectral_data` does not use it.
`labelBoundary` (DM002.06) is defined below for use by that omitted node. -/

open MeasureTheory NlsGge.Atomic.DM001 NlsGge.Atomic.Interval
open NlsGge.Pilot NlsGge.SpectralFoundations
open scoped ENNReal Topology

namespace NlsGge.Atomic.DM002

noncomputable section

def piCoeff (f : PiL2) (k : ℤ) : ℂ :=
  fourierCoeffOn Real.pi_pos (f : ℝ → ℂ) k

def unitCoeff (f : UnitL2) (k : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (f : ℝ → ℂ) k

def IsPiRealType (v : PiPairL2) : Prop :=
  v false = star (v true)

abbrev PiRealPotential := {v : PiPairL2 // IsPiRealType v}

/-! ### DM002.01 -/

theorem memLp_pi (f : PiL2) :
    MemLp (f : ℝ → ℂ) 2 (volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) := by
  have h : MemLp (f : ℝ → ℂ) 2
      (ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) := Lp.memLp f
  have hle : volume.restrict (Set.Ioc (0 : ℝ) Real.pi) ≤
      ENNReal.ofReal Real.pi • (ENNReal.ofReal (Real.pi⁻¹) • volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) := by
    refine le_of_eq ?_
    rw [smul_smul, ← ENNReal.ofReal_mul Real.pi_pos.le, mul_inv_cancel₀ Real.pi_ne_zero,
      ENNReal.ofReal_one, one_smul]
  exact h.of_measure_le_smul ENNReal.ofReal_ne_top hle

theorem norm_exp_neg_two_I (k : ℤ) (x : ℝ) :
    ‖Complex.exp (-2 * Complex.I * (k : ℂ) * x)‖ = 1 := by
  have e : (-2 : ℂ) * Complex.I * (k : ℂ) * x = ((-2 * k * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

theorem piCoeff_integrable (f : PiL2) (k : ℤ) :
  IntervalIntegrable
    (fun x : ℝ => Complex.exp (-2 * Complex.I * (k : ℂ) * x) * f x)
    volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
  have hL := memLp_pi f
  have hint : Integrable (f : ℝ → ℂ) (volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) :=
    hL.integrable (by norm_num)
  refine hint.norm.mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-2 * Complex.I * (k : ℂ) * x))).aestronglyMeasurable).mul
      hL.aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [norm_mul, norm_exp_neg_two_I, one_mul]

theorem fourier_neg_pi_apply (k : ℤ) (x : ℝ) :
    fourier (-k) (x : AddCircle (Real.pi - 0)) = Complex.exp (-2 * Complex.I * (k : ℂ) * x) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [sub_zero]
  field_simp

theorem piCoeff_integral (f : PiL2) (k : ℤ) :
  piCoeff f k = (Real.pi : ℂ)⁻¹ *
    ∫ x in (0 : ℝ)..Real.pi,
      Complex.exp (-2 * Complex.I * (k : ℂ) * x) * f x := by
  unfold piCoeff
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_neg_pi_apply]
  rw [Complex.real_smul]
  simp only [smul_eq_mul, sub_zero, one_div]
  push_cast
  rfl

theorem fourier_neg_unit_apply (k : ℤ) (x : ℝ) :
    fourier (-k) (x : AddCircle (1 - 0 : ℝ)) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  rw [sub_zero]
  ring

theorem unitCoeff_integral (f : UnitL2) (k : ℤ) :
    unitCoeff f k = ∫ x in (0 : ℝ)..1,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * x) * f x := by
  unfold unitCoeff
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_neg_unit_apply]
  simp

theorem unitCoeff_memℓp (f : UnitL2) : Memℓp (unitCoeff f) 2 := by
  have hL : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := Lp.memLp f
  have h := hasSum_sq_fourierCoeffOn (a := 0) (b := 1) zero_lt_one hL
  refine (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 ?_
  have hs : Summable (fun i : ℤ => ‖unitCoeff f i‖ ^ 2) := h.summable
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

/-! ### DM002.02 -/

noncomputable def unitPhysical (f : UnitL2) : PhysicalL2 :=
  physicalFourierL2.symm ⟨unitCoeff f, unitCoeff_memℓp f⟩

def scaledPhysicalPair (v : PiPairL2) :
    NlsGge.Atomic.KST001.PeriodicPair :=
  (unitPhysical (scaledPotential v true),
   unitPhysical (scaledPotential v false))

theorem unitPhysical_fourier (f : UnitL2) (k : ℤ) :
  physicalFourier (unitPhysical f) k = unitCoeff f k := by
  rw [← physicalFourierL2_apply]
  unfold unitPhysical
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem measurePreserving_mk_unit :
    MeasurePreserving (fun t : ℝ => (t : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume : Measure (AddCircle (1 : ℝ))) := by
  have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
  simpa using h

theorem ae_unit_of_ae_haar {p : AddCircle (1 : ℝ) → Prop}
    (h : ∀ᵐ x ∂(AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))), p x) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), p ((t : ℝ) : AddCircle (1 : ℝ)) := by
  have hv : ∀ᵐ x ∂(volume : Measure (AddCircle (1 : ℝ))), p x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  exact measurePreserving_mk_unit.quasiMeasurePreserving.ae hv

theorem unitPhysical_interval_ae (f : UnitL2) :
  (fun t : ℝ => unitPhysical f (t : AddCircle (1 : ℝ))) =ᵐ[
    volume.restrict (Set.Ioc (0 : ℝ) 1)] (f : ℝ → ℂ) := by
  have hL : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Set.Ioc (0 : ℝ) (0 + 1))) := by
    simpa using (Lp.memLp f)
  have hh : MemLp (AddCircle.liftIoc (1 : ℝ) 0 (f : ℝ → ℂ)) 2 AddCircle.haarAddCircle :=
    hL.memLp_liftIoc.haarAddCircle
  let g : PhysicalL2 := hh.toLp _
  have hg : unitPhysical f = g := by
    apply physicalFourierL2.injective
    apply lp.ext
    funext k
    rw [physicalFourierL2_apply, physicalFourierL2_apply, unitPhysical_fourier]
    show unitCoeff f k = fourierCoeff (g : AddCircle (1 : ℝ) → ℂ) k
    have hg' : fourierCoeff (g : AddCircle (1 : ℝ) → ℂ) k =
        fourierCoeff (AddCircle.liftIoc (1 : ℝ) 0 (f : ℝ → ℂ)) k :=
      congrFun (fourierCoeff_congr_ae hh.coeFn_toLp) k
    have hb : ∀ (b : ℝ) (hb : b = 1) (h1 : (0 : ℝ) < b),
        fourierCoeffOn h1 (f : ℝ → ℂ) k = unitCoeff f k := by
      intro b hb
      subst hb
      intro h1
      rfl
    rw [hg', fourierCoeff_liftIoc_eq]
    exact (hb (0 + 1) (by norm_num) _).symm
  rw [hg]
  have hae := ae_unit_of_ae_haar
    (p := fun x => g x = AddCircle.liftIoc (1 : ℝ) 0 (f : ℝ → ℂ) x) hh.coeFn_toLp
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht]
  exact AddCircle.liftIoc_coe_apply (by simpa using hmem)

theorem unitCoeff_star (f : UnitL2) (k : ℤ) :
    unitCoeff (star f) k = star (unitCoeff f (-k)) := by
  unfold unitCoeff
  have hae : ((star f : UnitL2) : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => star ((f : ℝ → ℂ) x) := Lp.coeFn_star f
  rw [congrFun (fourierCoeffOn_congr_ae zero_lt_one hae) k]
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [Complex.real_smul, one_div, sub_zero, inv_one, Complex.ofReal_one, one_mul, smul_eq_mul]
  rw [Complex.star_def, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  funext x
  simp only [map_mul, fourier_neg, neg_neg, Complex.conj_conj]

theorem unitPhysical_star (f : UnitL2) :
  unitPhysical (star f) = star (unitPhysical f) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext k
  rw [physicalFourierL2_apply, physicalFourierL2_apply, NlsGge.Schur.physicalFourier_star38,
    unitPhysical_fourier, unitPhysical_fourier, unitCoeff_star]

/-! ### DM002.03 -/

theorem piCoeff_rescale (f : PiL2) (k : ℤ) :
  unitCoeff (unitaryRescale f) k = piCoeff f k := by
  rw [unitCoeff_integral, piCoeff_integral]
  have hae := rescaleLp_ae f
  have hu : (unitaryRescale f : UnitL2) = rescaleLp f := rfl
  have h1 : ∫ x in (0 : ℝ)..1,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * x) * (unitaryRescale f : UnitL2) x =
      ∫ x in (0 : ℝ)..1, Complex.exp (-2 * Complex.I * (k : ℂ) * ((Real.pi * x : ℝ) : ℂ)) *
        (f : ℝ → ℂ) (Real.pi * x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [hae] with t ht
    rw [hu, ht]
    have e : -(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) * (t : ℂ) =
        -2 * Complex.I * (k : ℂ) * ((Real.pi * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e]
    rfl
  rw [h1]
  have h2 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => Complex.exp (-2 * Complex.I * (k : ℂ) * (x : ℂ)) * (f : ℝ → ℂ) x)
    Real.pi_ne_zero
  simp only [mul_zero, mul_one] at h2
  rw [h2, Complex.real_smul]
  push_cast
  rfl

theorem unitCoeff_smul (c : ℂ) (f : UnitL2) (k : ℤ) :
    unitCoeff (c • f) k = c * unitCoeff f k := by
  unfold unitCoeff
  have hae : ((c • f : UnitL2) : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => c * (f : ℝ → ℂ) x := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa using hx
  rw [congrFun (fourierCoeffOn_congr_ae zero_lt_one hae) k]
  exact congrFun (funext fun k => fourierCoeffOn.const_mul (f : ℝ → ℂ) c k zero_lt_one) k

theorem scaledPotential_comp (v : PiPairL2) (b : Bool) :
    scaledPotential v b = (Real.pi : ℂ) • unitaryRescale (v b) := by
  change ((Real.pi : ℂ) • unitaryRescalePair v) b = _
  rw [unitaryRescalePair_apply]
  rfl

theorem scaledPotential_unitCoeff (v : PiPairL2) (b : Bool) (k : ℤ) :
    unitCoeff (scaledPotential v b) k = (Real.pi : ℂ) * piCoeff (v b) k := by
  rw [scaledPotential_comp, unitCoeff_smul, piCoeff_rescale]

theorem scaledPotential_fourier (v : PiPairL2) (k : ℤ) :
  NlsGge.Atomic.KST001.periodTwoPairCoeff (scaledPhysicalPair v) (2 * k) =
    ((Real.pi : ℂ) * piCoeff (v true) k,
     (Real.pi : ℂ) * piCoeff (v false) k) := by
  rw [NlsGge.Atomic.KST001.periodOne_pair_even_coeff]
  simp only [scaledPhysicalPair, unitPhysical_fourier, scaledPotential_unitCoeff]

theorem piCoeff_star (f : PiL2) (k : ℤ) :
  piCoeff (star f) k = star (piCoeff f (-k)) := by
  rw [piCoeff_integral, piCoeff_integral]
  have hae : ((star f : PiL2) : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) Real.pi)]
      fun x => star ((f : ℝ → ℂ) x) := by
    have h := Lp.coeFn_star f
    have hc : ENNReal.ofReal (Real.pi⁻¹) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have h' : ((star f : PiL2) : ℝ → ℂ) =ᵐ[ENNReal.ofReal (Real.pi⁻¹) •
        volume.restrict (Set.Ioc (0 : ℝ) Real.pi)] fun x => star ((f : ℝ → ℂ) x) := h
    exact (Measure.absolutelyContinuous_smul hc).ae_le h'
  have hint : ∫ x in (0 : ℝ)..Real.pi,
      Complex.exp (-2 * Complex.I * (k : ℂ) * x) * ((star f : PiL2) : ℝ → ℂ) x =
      ∫ x in (0 : ℝ)..Real.pi,
        Complex.exp (-2 * Complex.I * (k : ℂ) * x) * star ((f : ℝ → ℂ) x) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le Real.pi_pos.le]
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hint, Complex.star_def, map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp
  · congr 1
    funext x
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    have h2 : (starRingEnd ℂ) 2 = 2 := by simpa using Complex.conj_ofReal 2
    simp [map_neg, map_mul, h2] <;> ring

theorem star_pi_smul_real (x : UnitL2) :
    star ((Real.pi : ℂ) • x) = (Real.pi : ℂ) • star x := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((Real.pi : ℂ) • x), Lp.coeFn_smul (Real.pi : ℂ) x,
    Lp.coeFn_smul (Real.pi : ℂ) (star x), Lp.coeFn_star x] with t h1 h2 h3 h4
  simp only [Pi.star_apply] at h1 h4
  simp only [Pi.smul_apply] at h2 h3
  rw [h1, h2, h3, h4]
  simp [smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, mul_comm]

theorem unitaryRescale_star (f : PiL2) :
    unitaryRescale (star f) = star (unitaryRescale f) := by
  apply Lp.ext
  have h1 := rescaleLp_ae (star f)
  have h2 : (fun t : ℝ => ((star f : PiL2) : ℝ → ℂ) (Real.pi * t)) =ᵐ[unitMeasure]
      fun t => star ((f : ℝ → ℂ) (Real.pi * t)) :=
    measurePreserving_piScale.quasiMeasurePreserving.ae (Lp.coeFn_star f)
  filter_upwards [h1, h2, rescaleLp_ae f, Lp.coeFn_star (unitaryRescale f)] with t a b c d
  have hu1 : (unitaryRescale (star f) : UnitL2) = rescaleLp (star f) := rfl
  have hu2 : (unitaryRescale f : UnitL2) = rescaleLp f := rfl
  rw [hu1, a]
  show ((star f : PiL2) : ℝ → ℂ) (Real.pi * t) = ((star (unitaryRescale f) : UnitL2) : ℝ → ℂ) t
  rw [b, d]
  show star ((f : ℝ → ℂ) (Real.pi * t)) = star ((unitaryRescale f : UnitL2) t)
  rw [hu2, c]
  rfl

theorem pi_realType_iff (v : PiPairL2) :
  IsPiRealType v ↔ IsRealType (scaledPotential v) := by
  unfold IsPiRealType IsRealType
  rw [scaledPotential_comp, scaledPotential_comp]
  constructor
  · intro h
    rw [h, unitaryRescale_star, star_pi_smul_real]
  · intro h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h' : unitaryRescale (v false) = star (unitaryRescale (v true)) := by
      have h3 := h
      rw [star_pi_smul_real] at h3
      exact smul_right_injective _ hπ h3
    rw [← unitaryRescale_star] at h'
    exact unitaryRescale.injective h'

theorem unit_ext_of_coeff (f g : UnitL2) (h : ∀ k, unitCoeff f k = unitCoeff g k) : f = g := by
  have hp : unitPhysical f = unitPhysical g := by
    apply physicalFourierL2.injective
    apply lp.ext
    funext k
    rw [physicalFourierL2_apply, physicalFourierL2_apply, unitPhysical_fourier, unitPhysical_fourier]
    exact h k
  apply Lp.ext
  filter_upwards [unitPhysical_interval_ae f, unitPhysical_interval_ae g] with t h1 h2
  rw [← h1, ← h2, hp]

theorem pi_realType_fourier_iff (v : PiPairL2) :
  IsPiRealType v ↔
    ∀ k : ℤ, piCoeff (v false) k = star (piCoeff (v true) (-k)) := by
  constructor
  · intro h k
    unfold IsPiRealType at h
    rw [h, piCoeff_star]
  · intro h
    unfold IsPiRealType
    apply unitaryRescale.injective
    apply unit_ext_of_coeff
    intro k
    rw [piCoeff_rescale, h k, ← piCoeff_star, ← piCoeff_rescale]

/-! ### DM002.06, DM002.07 -/

def dmBoundaryPhase (v : PiRealPotential) (x : ℝ) : ℝ :=
  actualQuasimomentumRealPartE02_38 (scaledPhysicalPair v.val).1
    (Real.pi * x) / Real.pi

def dmGapSet (v : PiRealPotential) (n : ℤ) : Set ℝ :=
  {x : ℝ | dmBoundaryPhase v x = (n : ℝ)}

def dmLower (v : PiRealPotential) (n : ℤ) : ℝ :=
  sInf (dmGapSet v n)

def dmUpper (v : PiRealPotential) (n : ℤ) : ℝ :=
  sSup (dmGapSet v n)

def dmGap (v : PiRealPotential) (n : ℤ) : ℝ :=
  dmUpper v n - dmLower v n

def kstGap (v : PiRealPotential) (n : ℤ) : ℝ :=
  actualGapUpperAllE02_38 (scaledPhysicalPair v.val).1 n -
    actualGapLowerAllE02_38 (scaledPhysicalPair v.val).1 n

theorem dmGapSet_image (v : PiRealPotential) (n : ℤ) :
  (fun x : ℝ => Real.pi * x) '' dmGapSet v n =
    actualGapLevelSetE02_38 (scaledPhysicalPair v.val).1 n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : actualQuasimomentumRealPartE02_38 (scaledPhysicalPair v.val).1 (Real.pi * x) /
        Real.pi = (n : ℝ) := hx
    show actualQuasimomentumRealPartE02_38 (scaledPhysicalPair v.val).1 (Real.pi * x) =
      (n : ℝ) * Real.pi
    rw [div_eq_iff Real.pi_ne_zero] at hx'
    exact hx'
  · intro hy
    refine ⟨y / Real.pi, ?_, by field_simp⟩
    have hy' : actualQuasimomentumRealPartE02_38 (scaledPhysicalPair v.val).1 y =
        (n : ℝ) * Real.pi := hy
    show actualQuasimomentumRealPartE02_38 (scaledPhysicalPair v.val).1 (Real.pi * (y / Real.pi)) /
      Real.pi = (n : ℝ)
    rw [show Real.pi * (y / Real.pi) = y by field_simp, hy', mul_div_assoc,
      div_self Real.pi_ne_zero, mul_one]

theorem dmGapSet_interval (v : PiRealPotential) (n : ℤ) :
  (dmGapSet v n).Nonempty ∧
    BddBelow (dmGapSet v n) ∧ BddAbove (dmGapSet v n) ∧
    dmGapSet v n = Set.Icc (dmLower v n) (dmUpper v n) := by
  obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_of_monotone_E02_38 (scaledPhysicalPair v.val).1
    (monotone_actualQuasimomentumRealPartE02_38 _) n
  have himg := dmGapSet_image v n
  have hpos : 0 < Real.pi := Real.pi_pos
  -- preimage description
  have hmem : ∀ x : ℝ, x ∈ dmGapSet v n ↔ Real.pi * x ∈
      Set.Icc (actualGapLowerAllE02_38 (scaledPhysicalPair v.val).1 n)
        (actualGapUpperAllE02_38 (scaledPhysicalPair v.val).1 n) := by
    intro x
    rw [← hIcc, ← himg]
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have : y = x := mul_left_cancel₀ hpos.ne' hxy
      rw [← this]
      exact hy
  set lo := actualGapLowerAllE02_38 (scaledPhysicalPair v.val).1 n with hlo
  set hi := actualGapUpperAllE02_38 (scaledPhysicalPair v.val).1 n with hhi
  have hset : dmGapSet v n = Set.Icc (lo / Real.pi) (hi / Real.pi) := by
    ext x
    rw [hmem x, Set.mem_Icc, Set.mem_Icc, div_le_iff₀ hpos, le_div_iff₀ hpos, mul_comm x Real.pi,
      mul_comm Real.pi x]
  have hloHi : lo ≤ hi := by
    obtain ⟨y, hy⟩ := hne
    have := (hIcc ▸ hy : y ∈ Set.Icc lo hi)
    exact this.1.trans this.2
  have hle : lo / Real.pi ≤ hi / Real.pi := div_le_div_of_nonneg_right hloHi hpos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hset]; exact ⟨lo / Real.pi, Set.left_mem_Icc.mpr hle⟩
  · rw [hset]; exact bddBelow_Icc
  · rw [hset]; exact bddAbove_Icc
  · rw [hset]
    unfold dmLower dmUpper
    rw [hset, csInf_Icc hle, csSup_Icc hle]

open scoped Pointwise in
theorem dm_lower_eq (v : PiRealPotential) (n : ℤ) :
    actualGapLowerAllE02_38 (scaledPhysicalPair v.val).1 n = Real.pi * dmLower v n := by
  have himg := dmGapSet_image v n
  unfold actualGapLowerAllE02_38 dmLower
  rw [← himg]
  have : (fun x : ℝ => Real.pi * x) '' dmGapSet v n = Real.pi • dmGapSet v n := by
    ext y
    simp [Set.mem_smul_set]
  rw [this, Real.sInf_smul_of_nonneg Real.pi_pos.le, smul_eq_mul]

open scoped Pointwise in
theorem dm_upper_eq (v : PiRealPotential) (n : ℤ) :
    actualGapUpperAllE02_38 (scaledPhysicalPair v.val).1 n = Real.pi * dmUpper v n := by
  have himg := dmGapSet_image v n
  unfold actualGapUpperAllE02_38 dmUpper
  rw [← himg]
  have : (fun x : ℝ => Real.pi * x) '' dmGapSet v n = Real.pi • dmGapSet v n := by
    ext y
    simp [Set.mem_smul_set]
  rw [this, Real.sSup_smul_of_nonneg Real.pi_pos.le, smul_eq_mul]

/-! ### DM002.09 -/

theorem dirac_rescale_spectral_data (v : PiRealPotential) :
  (∀ k : ℤ,
    NlsGge.Atomic.KST001.periodTwoPairCoeff (scaledPhysicalPair v.val) (2 * k) =
      ((Real.pi : ℂ) * piCoeff (v.val true) k,
       (Real.pi : ℂ) * piCoeff (v.val false) k)) ∧
  (∀ n : ℤ,
    actualGapLowerAllE02_38 (scaledPhysicalPair v.val).1 n =
      Real.pi * dmLower v n ∧
    actualGapUpperAllE02_38 (scaledPhysicalPair v.val).1 n =
      Real.pi * dmUpper v n ∧
    kstGap v n = Real.pi * dmGap v n) ∧
  IsRealType (scaledPotential v.val) ∧
  (∀ k : ℤ, piCoeff (v.val false) k = star (piCoeff (v.val true) (-k))) := by
  refine ⟨scaledPotential_fourier v.val, fun n => ⟨dm_lower_eq v n, dm_upper_eq v n, ?_⟩,
    (pi_realType_iff v.val).mp v.property, (pi_realType_fourier_iff v.val).mp v.property⟩
  unfold kstGap dmGap
  rw [dm_lower_eq, dm_upper_eq]
  ring

/-! ### DM002.04 -/

open NlsGge.Atomic.LIB033

def piDomain (bc : ZSBoundaryCondition) : Submodule ℂ PiPairL2 :=
  (zsDomain bc).comap unitaryRescalePair.toLinearEquiv.toLinearMap

def piDomainRescale (bc : ZSBoundaryCondition) :
    piDomain bc →ₗ[ℂ] zsDomain bc where
  toFun f := ⟨unitaryRescalePair f, f.property⟩
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

def piDirac (v : PiPairL2) (bc : ZSBoundaryCondition) :
    PiPairL2 →ₗ.[ℂ] PiPairL2 where
  domain := piDomain bc
  toFun := (Real.pi : ℂ)⁻¹ •
    unitaryRescalePair.symm.toLinearEquiv.toLinearMap.comp
      ((zsRealization (scaledPotential v) bc).toFun.comp (piDomainRescale bc))

def piH1Value (f : PiH1Pair) : PiPairL2 :=
  WithLp.toLp 2 (fun b => (f b).value)

def piBoundary (bc : ZSBoundaryCondition) (f : PiH1Pair) : Prop :=
  HasZSBoundaryCondition bc (rescaleH1Pair f)

theorem h1PairValue_rescale (f : PiH1Pair) :
    h1PairValue (rescaleH1Pair f) = unitaryRescalePair (piH1Value f) := rfl

theorem piDomain_literal (bc : ZSBoundaryCondition) (x : PiPairL2) :
  x ∈ piDomain bc ↔
    ∃ f : PiH1Pair, piBoundary bc f ∧ piH1Value f = x := by
  constructor
  · intro hx
    obtain ⟨g, hg, hgx⟩ := hx
    refine ⟨inverseRescaleH1Pair g, ?_, ?_⟩
    · have h : rescaleH1Pair (inverseRescaleH1Pair g) = g := by
        funext b
        exact rescale_inverseRescaleH1 (g b)
      unfold piBoundary
      rw [h]
      exact hg
    · apply PiLp.ext
      intro b
      have h1 : (h1PairValue g) b = unitaryRescale (x b) := by
        rw [hgx]
        rfl
      have h2 : (g b).value = unitaryRescale (x b) := h1
      change inverseRescaleLp (g b).value = x b
      rw [h2]
      exact inverse_rescale_rescale (x b)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨rescaleH1Pair f, hf, ?_⟩
    exact h1PairValue_rescale f

theorem piDirac_literal (v : PiPairL2) (bc : ZSBoundaryCondition)
    (f : PiH1Pair) (hf : piBoundary bc f) :
  ∃ hx : piH1Value f ∈ (piDirac v bc).domain,
    piDirac v bc ⟨piH1Value f, hx⟩ = piZSApply v f := by
  have hx : piH1Value f ∈ (piDirac v bc).domain :=
    (piDomain_literal bc _).mpr ⟨f, hf, rfl⟩
  refine ⟨hx, ?_⟩
  have hsub : (⟨unitaryRescalePair (piH1Value f), hx⟩ :
      (zsRealization (scaledPotential v) bc).domain) =
      ⟨h1PairValue (rescaleH1Pair f), ⟨rescaleH1Pair f, hf, rfl⟩⟩ :=
    Subtype.ext (h1PairValue_rescale f).symm
  have h3 : (zsRealization (scaledPotential v) bc).toFun
      ⟨h1PairValue (rescaleH1Pair f), ⟨rescaleH1Pair f, hf, rfl⟩⟩ =
        zsApply (scaledPotential v) (rescaleH1Pair f) :=
    zsRealization_apply _ _ _ hf
  have h4 : (zsRealization (scaledPotential v) bc).toFun
      ⟨unitaryRescalePair (piH1Value f), hx⟩ =
        zsApply (scaledPotential v) (rescaleH1Pair f) :=
    (congrArg (zsRealization (scaledPotential v) bc).toFun hsub).trans h3
  have hdef : piDirac v bc ⟨piH1Value f, hx⟩ =
      (Real.pi : ℂ)⁻¹ • unitaryRescalePair.symm
        ((zsRealization (scaledPotential v) bc).toFun ⟨unitaryRescalePair (piH1Value f), hx⟩) := rfl
  rw [hdef, h4, dirac_period_rescaling]
  rw [map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul]

/-! ### DM002.05 -/

def rootSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ.[ℂ] E) (z : ℂ) : ℕ → Submodule ℂ E
  | 0 => ⊥
  | m + 1 =>
      ((rootSpace A z m).comap
        (A.toFun - z • A.domain.subtype)).map A.domain.subtype

theorem rootSpace_map_of_intertwine {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (U : E ≃ₗ[ℂ] F)
    (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F) (c z w : ℂ) (hc : c ≠ 0) (hw : w = c * z)
    (hdom : ∀ x : E, x ∈ A.domain ↔ U x ∈ B.domain)
    (hact : ∀ (x : E) (hx : x ∈ A.domain),
      B.toFun ⟨U x, (hdom x).mp hx⟩ = c • U (A.toFun ⟨x, hx⟩)) (m : ℕ) :
    (rootSpace A z m).map U.toLinearMap = rootSpace B w m := by
  have key : ∀ x : A.domain,
      (B.toFun - w • B.domain.subtype) ⟨U x, (hdom x).mp x.property⟩ =
        c • U ((A.toFun - z • A.domain.subtype) x) := by
    intro x
    have h : B.toFun ⟨U x, (hdom x).mp x.property⟩ = c • U (A.toFun x) :=
      hact x x.property
    show B.toFun ⟨U x, (hdom x).mp x.property⟩ - w • U x =
      c • U (A.toFun x - z • (x : E))
    rw [h]
    simp only [map_sub, map_smul, smul_sub, smul_smul, hw]
  induction m with
  | zero => simp [rootSpace]
  | succ m ih =>
    ext u
    constructor
    · intro hu
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      have hx' := Submodule.mem_comap.mp hx
      show U.toLinearMap (x : E) ∈ Submodule.map B.domain.subtype
        (Submodule.comap (B.toFun - w • B.domain.subtype) (rootSpace B w m))
      refine Submodule.mem_map.mpr ⟨⟨U x, (hdom x).mp x.property⟩, Submodule.mem_comap.mpr ?_, rfl⟩
      rw [key x, ← ih]
      exact Submodule.smul_mem _ c (Submodule.mem_map_of_mem hx')
    · intro hu
      obtain ⟨x', hx, rfl⟩ := Submodule.mem_map.mp hu
      have hx' := Submodule.mem_comap.mp hx
      have hmem : (U.symm x' : E) ∈ A.domain := by
        rw [hdom]
        simpa using x'.property
      let xA : A.domain := ⟨U.symm (x' : F), hmem⟩
      have hxe : (⟨U (xA : E), (hdom xA).mp xA.property⟩ : B.domain) = x' :=
        Subtype.ext (U.apply_symm_apply (x' : F))
      have hk := key xA
      rw [hxe] at hk
      have h1 : c • U ((A.toFun - z • A.domain.subtype) xA) ∈ rootSpace B w m := by
        rw [← hk]
        exact hx'
      have h2 : U ((A.toFun - z • A.domain.subtype) xA) ∈ rootSpace B w m :=
        (Submodule.smul_mem_iff _ hc).mp h1
      rw [← ih] at h2
      obtain ⟨t, ht, e⟩ := Submodule.mem_map.mp h2
      have e' : t = (A.toFun - z • A.domain.subtype) xA := U.injective e
      refine Submodule.mem_map.mpr ⟨(xA : E), ?_, U.apply_symm_apply (x' : F)⟩
      show (xA : E) ∈ Submodule.map A.domain.subtype
        (Submodule.comap (A.toFun - z • A.domain.subtype) (rootSpace A z m))
      refine Submodule.mem_map.mpr ⟨xA, Submodule.mem_comap.mpr ?_, rfl⟩
      rw [← e']
      exact ht

theorem pi_rootSpace_map (v : PiPairL2) (bc : ZSBoundaryCondition)
    (z : ℂ) (m : ℕ) :
  (rootSpace (piDirac v bc) z m).map
      unitaryRescalePair.toLinearEquiv.toLinearMap =
    rootSpace (zsRealization (scaledPotential v) bc)
      ((Real.pi : ℂ) * z) m := by
  refine rootSpace_map_of_intertwine unitaryRescalePair.toLinearEquiv (piDirac v bc)
    (zsRealization (scaledPotential v) bc) (Real.pi : ℂ) z _
    (by exact_mod_cast Real.pi_ne_zero) rfl (fun x => Iff.rfl) ?_ m
  intro x hx
  have hdef : (piDirac v bc).toFun ⟨x, hx⟩ =
      (Real.pi : ℂ)⁻¹ • unitaryRescalePair.symm
        ((zsRealization (scaledPotential v) bc).toFun ⟨unitaryRescalePair x, hx⟩) := rfl
  rw [hdef]
  show _ = (Real.pi : ℂ) • unitaryRescalePair _
  rw [map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul]
  rfl

theorem pi_rootSpace_rank (v : PiPairL2) (bc : ZSBoundaryCondition)
    (z : ℂ) (m : ℕ) :
  Module.rank ℂ (rootSpace (piDirac v bc) z m) =
    Module.rank ℂ
      (rootSpace (zsRealization (scaledPotential v) bc)
        ((Real.pi : ℂ) * z) m) := by
  have h := LinearEquiv.rank_eq
    (Submodule.equivMapOfInjective unitaryRescalePair.toLinearEquiv.toLinearMap
      unitaryRescalePair.toLinearEquiv.injective (rootSpace (piDirac v bc) z m))
  rw [pi_rootSpace_map] at h
  exact h

def labelBoundary (n : ℤ) : ZSBoundaryCondition :=
  if n % 2 = 0 then .periodic else .antiperiodic

end

end NlsGge.Atomic.DM002


/- ===== BEGIN_N08 (proof development) ===== -/
open MeasureTheory NlsGge.Atomic.DM001 NlsGge.Atomic.Interval
open NlsGge.Pilot NlsGge.SpectralFoundations
open scoped ENNReal Topology

namespace NlsGge.Atomic.DM002

noncomputable section

namespace N08

/-- linear algebra: trace `2s`, determinant `1`, `s² = 1` give an eigenvector for `s`. -/
theorem exists_eigvec_of_trace_det (M : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (hs : s * s = 1)
    (htr : M.trace = 2 * s) (hdet : M.det = 1) :
    ∃ a : Fin 2 → ℂ, a ≠ 0 ∧ M.mulVec a = s • a := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  set N : Matrix (Fin 2) (Fin 2) ℂ := M - s • (1 : Matrix (Fin 2) (Fin 2) ℂ) with hN
  have hNN : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    · linear_combination (M 0 0) * htr - hdet + hs
    · linear_combination (M 0 1) * htr
    · linear_combination (M 1 0) * htr
    · linear_combination (M 1 1) * htr - hdet + hs
  have hNmul : ∀ a : Fin 2 → ℂ, N.mulVec a = M.mulVec a - s • a := by
    intro a
    simp [hN, Matrix.sub_mulVec, Matrix.smul_mulVec]
  by_cases hw : N.mulVec ![1, 0] = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · have := hNmul ![1, 0]
      rw [hw] at this
      exact sub_eq_zero.mp this.symm
  · refine ⟨N.mulVec ![1, 0], hw, ?_⟩
    have h0 : N.mulVec (N.mulVec ![1, 0]) = 0 := by
      rw [Matrix.mulVec_mulVec, hNN]; simp
    have := hNmul (N.mulVec ![1, 0])
    rw [h0] at this
    exact sub_eq_zero.mp this.symm

theorem e02Pot_ae_unitPhysical (f : UnitL2) :
    (fun t : ℝ => NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f) (t : NlsGge.Schur.SpectralCircle)) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] (f : ℝ → ℂ) := by
  have hH : ∀ᵐ x ∂(NlsGge.Schur.spectralHaar),
      NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f) x =
        unitPhysical f (NlsGge.Analysis.naturalPhysicalCover x) :=
    NlsGge.Analysis.naturalPhysicalCoverL2_ae _
  have hv : ∀ᵐ x ∂(volume : Measure NlsGge.Schur.SpectralCircle),
      NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f) x =
        unitPhysical f (NlsGge.Analysis.naturalPhysicalCover x) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure hH _
  have h2 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 2)),
      NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f) (t : NlsGge.Schur.SpectralCircle) =
        unitPhysical f (NlsGge.Analysis.naturalPhysicalCover (t : NlsGge.Schur.SpectralCircle)) := by
    have hmp := AddCircle.measurePreserving_mk (2 : ℝ) 0
    simp only [zero_add] at hmp
    exact hmp.quasiMeasurePreserving.ae hv
  have h1 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      NlsGge.Analysis.naturalPhysicalCoverL2 (unitPhysical f) (t : NlsGge.Schur.SpectralCircle) =
        unitPhysical f (NlsGge.Analysis.naturalPhysicalCover (t : NlsGge.Schur.SpectralCircle)) := by
    refine (ae_mono (Measure.restrict_mono (Set.Ioc_subset_Ioc_right (by norm_num)) le_rfl)) h2
  filter_upwards [h1, unitPhysical_interval_ae f] with t ht ht2
  rw [ht, NlsGge.Analysis.naturalPhysicalCover_coe]
  exact ht2


section B

/-- index of the Bool component in the `Fin 2` solution vector (`true` is the upper one). -/
def kk (b : Bool) : Fin 2 := if b then 0 else 1

/-- the derivative profile `(σ_b)⁻¹ (x f_b − φ_b f_{!b})` of an eigen-solution. -/
def dfun (φ : UnitPairL2) (x : ℂ) (F : ℝ → Fin 2 → ℂ) (b : Bool) (t : ℝ) : ℂ :=
  (if b then -Complex.I else Complex.I) * (x * F t (kk b) - φ b t * F t (kk (!b)))

theorem sigma_dfun (b : Bool) (x A B p dA : ℂ)
    (h : dA = (if b then -Complex.I else Complex.I) * (x * A - p * B)) :
    (if b then Complex.I else -Complex.I) * dA + p * B = x * A := by
  subst h
  cases b <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
    linear_combination (-(x * A - p * B)) * Complex.I_mul_I

theorem h1_of_solution (φ : UnitPairL2) (x : ℂ) (F : ℝ → Fin 2 → ℂ)
    (hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => F t i) 0 1)
    (hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ b : Bool,
      HasDerivAt (fun s => F s (kk b)) (dfun φ x F b t) t) :
    ∃ g : H1Pair,
      (∀ b, NlsGge.Atomic.LIB026.traceLeft (g b) = F 0 (kk b)) ∧
      (∀ b, NlsGge.Atomic.LIB026.traceRight (g b) = F 1 (kk b)) ∧
      (∀ b, (⇑(g b).value) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => F t (kk b)) ∧
      zsApply φ g = x • h1PairValue g := by
  have hcont : ∀ i, ContinuousOn (fun t => F t i) (Set.Icc (0 : ℝ) 1) := fun i => by
    simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using (hac i).continuousOn
  have hbdd : ∀ i, ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F t i‖ ≤ B := fun i =>
    isCompact_Icc.exists_bound_of_continuousOn (hcont i)
  have hmeas : ∀ i, AEStronglyMeasurable (fun t => F t i)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun i =>
    ((hcont i).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  have htop : ∀ i, MemLp (fun t => F t i) ∞ (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun i => by
    obtain ⟨B, hB⟩ := hbdd i
    refine memLp_top_of_bound (hmeas i) B ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ⟨ht.1.le, ht.2⟩
  have hL2 : ∀ i, MemLp (fun t => F t i) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun i => (htop i).mono_exponent le_top
  have hdL2 : ∀ b : Bool, MemLp (dfun φ x F b) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun b => by
    have h1 : MemLp (fun t => φ b t * F t (kk (!b))) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (Lp.memLp (φ b)).mul (htop (kk (!b)))
    exact (((hL2 (kk b)).const_mul x).sub h1).const_mul _
  let vL : Bool → NlsGge.Schur.SourceIntervalL2 := fun b => (hL2 (kk b)).toLp _
  let dL : Bool → NlsGge.Schur.SourceIntervalL2 := fun b => (hdL2 b).toLp _
  have hv : ∀ b, (⇑(vL b)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t => F t (kk b) :=
    fun b => (hL2 (kk b)).coeFn_toLp
  have hd : ∀ b, (⇑(dL b)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] dfun φ x F b :=
    fun b => (hdL2 b).coeFn_toLp
  have hdint : ∀ b, IntervalIntegrable (dfun φ x F b) volume 0 1 := fun b =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((hdL2 b).integrable (by norm_num))
  have hweak : ∀ b, HasWeakDerivative (⇑(vL b)) (⇑(dL b)) := by
    intro b ψ hψs hψc hψU
    have hψd (y : ℝ) : HasDerivAt (fun y => (ψ y : ℂ)) ((deriv ψ y : ℝ) : ℂ) y :=
      ((hψs.differentiable (by simp)) y).hasDerivAt.ofReal_comp
    have hψdi : IntervalIntegrable (fun y => ((deriv ψ y : ℝ) : ℂ)) volume 0 1 :=
      (Complex.continuous_ofReal.comp (hψs.continuous_deriv (by simp))).intervalIntegrable _ _
    have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hψU h).1.false)
    have hψ1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl (1 : ℝ)) (hψU h).2)
    have hd0 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ (0 : ℝ) := by simp [ae_iff]
    have hder' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIcc (0 : ℝ) 1 →
        HasDerivAt (fun s => F s (kk b)) (dfun φ x F b t) t := by
      filter_upwards [hder, hd0] with t ht ht0 hmem
      rw [Set.uIcc_of_le zero_le_one] at hmem
      exact ht ⟨lt_of_le_of_ne hmem.1 (Ne.symm ht0), hmem.2⟩ b
    have hibp := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
      (hac (kk b)) (hdint b) hder' (fun y _ => hψd y) hψdi
    simp only [hψ0, hψ1, Complex.ofReal_zero, mul_zero, sub_self, zero_sub] at hibp
    have e1 : (∫ y in (0 : ℝ)..1, (vL b) y * ((deriv ψ y : ℝ) : ℂ)) =
        ∫ y in (0 : ℝ)..1, F y (kk b) * ((deriv ψ y : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      have := (ae_restrict_iff' measurableSet_Ioc).mp (hv b)
      filter_upwards [this] with y hy hyI
      rw [Set.uIoc_of_le zero_le_one] at hyI
      rw [hy hyI]
    have e2 : (∫ y in (0 : ℝ)..1, (dL b) y * (ψ y : ℂ)) =
        ∫ y in (0 : ℝ)..1, dfun φ x F b y * (ψ y : ℂ) := by
      apply intervalIntegral.integral_congr_ae
      have := (ae_restrict_iff' measurableSet_Ioc).mp (hd b)
      filter_upwards [this] with y hy hyI
      rw [Set.uIoc_of_le zero_le_one] at hyI
      rw [hy hyI]
    rw [e1, e2]
    exact hibp
  let g : H1Pair := fun b => ⟨vL b, dL b, hweak b⟩
  let Fc : Bool → C(Set.Icc (0 : ℝ) 1, ℂ) := fun b =>
    ⟨fun t => F t.1 (kk b), (hcont (kk b)).restrict⟩
  have hrep : ∀ b, NlsGge.Atomic.LIB026.representative (g b) = Fc b := by
    intro b
    symm
    apply NlsGge.Atomic.LIB026.representative_eq_of_ae
    filter_upwards [hv b, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    show Set.IccExtend zero_le_one (Fc b) t = (vL b) t
    rw [h1, Set.IccExtend_of_mem zero_le_one (Fc b) ⟨h2.1.le, h2.2⟩]
    rfl
  refine ⟨g, fun b => ?_, fun b => ?_, fun b => hv b, ?_⟩
  · unfold NlsGge.Atomic.LIB026.traceLeft
    rw [hrep b]; rfl
  · unfold NlsGge.Atomic.LIB026.traceRight
    rw [hrep b]; rfl
  · apply PiLp.ext
    intro b
    apply Lp.ext
    have hsm := Lp.coeFn_smul x (vL b)
    filter_upwards [zsApply_ae φ g b, hsm, hv b, hv (!b), hd b] with t h1 h2 h3 h4 h5
    have e : ((x • h1PairValue g) b : NlsGge.Schur.SourceIntervalL2) = x • vL b := rfl
    rw [e, h2]
    rw [h1]
    show (if b then Complex.I else -Complex.I) * (dL b) t + φ b t * (vL (!b)) t = x • (vL b) t
    rw [h3, h4, smul_eq_mul]
    exact sigma_dfun b x (F t (kk b)) (F t (kk (!b))) (φ b t) ((dL b) t) (by rw [h5]; rfl)

end B

section C

def Upot (u : PhysicalL2) : ℝ → ℂ :=
  fun t => NlsGge.Analysis.naturalPhysicalCoverL2 u (t : NlsGge.Schur.SpectralCircle)

def Dy (u : PhysicalL2) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  actualComplexZsDysonTsum (Upot u) z t

theorem exists_unit_eigenpair (φ : UnitPairL2) (hφ : IsRealType φ) (u₀ : PhysicalL2)
    (hP : Upot u₀ =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (φ true : ℝ → ℂ))
    (x : ℝ) (s : ℂ) (hs : s * s = 1) (htr : (Dy u₀ x 1).trace = 2 * s) :
    ∃ g : H1Pair, h1PairValue g ≠ 0 ∧
      (∀ b : Bool, NlsGge.Atomic.LIB026.traceRight (g b) =
        s * NlsGge.Atomic.LIB026.traceLeft (g b)) ∧
      zsApply φ g = (x : ℂ) • h1PairValue g := by
  obtain ⟨hinit, hAC, hODE⟩ : Dy u₀ x 0 = 1 ∧
      (∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => Dy u₀ x t i j) 0 2) ∧
      (∀ i j : Fin 2, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIcc (0 : ℝ) 2 →
        HasDerivAt (fun s => Dy u₀ x s i j)
          ((zsCoefficientComplex (Upot u₀) x t * Dy u₀ x t) i j) t) :=
    actualPhysicalL2ZsDysonTsum_is_AC_fundamental u₀ (x : ℂ)
  have hdet : (Dy u₀ x 1).det = 1 := by
    have h := NlsGge.GK38.det_monodromyPair (NlsGge.GK38.realSlice u₀) (x : ℂ)
    rw [NlsGge.GK38.monodromyPair_realSlice] at h
    exact h
  obtain ⟨a, ha0, haM⟩ := exists_eigvec_of_trace_det (Dy u₀ x 1) s hs htr hdet
  let F : ℝ → Fin 2 → ℂ := fun t => (Dy u₀ x t).mulVec a
  have hFi : ∀ t i, F t i = Dy u₀ x t i 0 * a 0 + Dy u₀ x t i 1 * a 1 := by
    intro t i
    fin_cases i <;> simp [F, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsub : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 2 := by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hac : ∀ i, AbsolutelyContinuousOnInterval (fun t => F t i) 0 1 := by
    intro i
    have h0 := ((hAC i 0).mono hsub).const_smul (a 0)
    have h1 := ((hAC i 1).mono hsub).const_smul (a 1)
    have := h0.add h1
    convert this using 1
    funext t
    rw [hFi]
    simp [smul_eq_mul, mul_comm]
  have hstar : (⇑(φ false)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => star (φ true t) := by
    rw [hφ]; exact Lp.coeFn_star _
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 →
      (Upot u₀ t = φ true t ∧ φ false t = star (φ true t)) := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hP, hstar] with t ha hb
    exact ⟨ha, hb⟩
  have hAll : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i j : Fin 2, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => Dy u₀ x s i j)
        ((zsCoefficientComplex (Upot u₀) x t * Dy u₀ x t) i j) t := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact hODE i j
  have hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0 : ℝ) 1 → ∀ b : Bool,
      HasDerivAt (fun s => F s (kk b)) (dfun φ (x : ℂ) F b t) t := by
    filter_upwards [h1, hAll] with t ht hall ht'
    have hmem : t ∈ Set.uIcc (0 : ℝ) 2 := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact ⟨ht'.1.le, by linarith [ht'.2]⟩
    obtain ⟨hU, hφf⟩ := ht ht'
    have hD : ∀ i : Fin 2, HasDerivAt (fun s => F s i)
        (zsCoefficientComplex (Upot u₀) x t i 0 * F t 0 +
          zsCoefficientComplex (Upot u₀) x t i 1 * F t 1) t := by
      intro i
      have e0 := (hall i 0 hmem).mul_const (a 0)
      have e1 := (hall i 1 hmem).mul_const (a 1)
      have := e0.add e1
      have hfun : (fun s => F s i) = fun s => Dy u₀ x s i 0 * a 0 + Dy u₀ x s i 1 * a 1 := by
        funext s; exact hFi s i
      rw [hfun]
      convert this using 1
      rw [hFi t 0, hFi t 1]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e00 : zsCoefficientComplex (Upot u₀) x t 0 0 = -Complex.I * x := by simp [zsCoefficientComplex]
    have e01 : zsCoefficientComplex (Upot u₀) x t 0 1 = Complex.I * Upot u₀ t := by simp [zsCoefficientComplex]
    have e10 : zsCoefficientComplex (Upot u₀) x t 1 0 = -Complex.I * star (Upot u₀ t) := by simp [zsCoefficientComplex]
    have e11 : zsCoefficientComplex (Upot u₀) x t 1 1 = Complex.I * x := by simp [zsCoefficientComplex]
    intro b
    cases b
    · have hd : dfun φ (x : ℂ) F false t =
          zsCoefficientComplex (Upot u₀) x t 1 0 * F t 0 + zsCoefficientComplex (Upot u₀) x t 1 1 * F t 1 := by
        simp only [dfun, kk, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_true, if_false]
        rw [e10, e11, hφf, hU]
        ring
      show HasDerivAt (fun s => F s 1) (dfun φ (x : ℂ) F false t) t
      rw [hd]
      exact hD 1
    · have hd : dfun φ (x : ℂ) F true t =
          zsCoefficientComplex (Upot u₀) x t 0 0 * F t 0 + zsCoefficientComplex (Upot u₀) x t 0 1 * F t 1 := by
        simp only [dfun, kk, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_true, if_false]
        rw [e00, e01, hU]
        ring
      show HasDerivAt (fun s => F s 0) (dfun φ (x : ℂ) F true t) t
      rw [hd]
      exact hD 0
  obtain ⟨g, hL, hR, hv, heig⟩ := h1_of_solution φ (x : ℂ) F hac hder
  have hF0 : ∀ b, F 0 (kk b) = a (kk b) := by
    intro b
    show ((Dy u₀ x 0).mulVec a) (kk b) = a (kk b)
    rw [hinit, Matrix.one_mulVec]
  have hF1 : ∀ b, F 1 (kk b) = s * a (kk b) := by
    intro b
    have := congrFun haM (kk b)
    simpa [F] using this
  refine ⟨g, ?_, ?_, heig⟩
  · intro hz
    have key : ∀ b : Bool, a (kk b) = 0 := by
      intro b
      have hb : (g b).value = 0 := by
        have := congrArg (fun p : NlsGge.Schur.SourcePairL2 => p b) hz
        simpa [h1PairValue] using this
      have hrep : NlsGge.Atomic.LIB026.representative (g b) = 0 := by
        symm
        apply NlsGge.Atomic.LIB026.representative_eq_of_ae
        rw [hb]
        filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)),
          ae_restrict_mem measurableSet_Ioc] with t ht1 ht2
        rw [ht1]
        show Set.IccExtend zero_le_one (0 : C(Set.Icc (0 : ℝ) 1, ℂ)) t = 0
        rw [Set.IccExtend_of_mem zero_le_one _ ⟨ht2.1.le, ht2.2⟩]
        rfl
      have h0 := hL b
      unfold NlsGge.Atomic.LIB026.traceLeft at h0
      rw [hrep, hF0 b] at h0
      exact h0.symm
    apply ha0
    funext i
    fin_cases i
    · exact key true
    · exact key false
  · intro b
    rw [hR b, hL b, hF1 b, hF0 b]

end C

end N08

theorem cos_label_sign (n : ℤ) :
    (n % 2 = 0 → (Real.cos ((n : ℝ) * Real.pi) : ℂ) = 1) ∧
    (¬ n % 2 = 0 → (Real.cos ((n : ℝ) * Real.pi) : ℂ) = -1) := by
  constructor
  · intro h
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = 2 * m := ⟨n / 2, by omega⟩
    have : ((2 * m : ℤ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
    simp
  · intro h
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have : ((2 * m + 1 : ℤ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) + Real.pi := by
      push_cast; ring
    rw [this, Real.cos_int_mul_two_pi_add_pi]
    simp

theorem cos_label_sq (n : ℤ) : (Real.cos ((n : ℝ) * Real.pi) : ℂ) * (Real.cos ((n : ℝ) * Real.pi) : ℂ) = 1 := by
  by_cases h : n % 2 = 0
  · rw [(cos_label_sign n).1 h]; norm_num
  · rw [(cos_label_sign n).2 h]; norm_num

theorem endpoint_eigenvector_of (v : PiRealPotential) (n : ℤ) (y c : ℝ)
    (hy : actualPhysicalUnitHalfTrace32 (scaledPhysicalPair v.val).1 (y : ℂ) =
      (Real.cos ((n : ℝ) * Real.pi) : ℂ))
    (hc : y = Real.pi * c) :
    ∃ f : PiH1Pair, piH1Value f ≠ 0 ∧ piBoundary (labelBoundary n) f ∧
      piZSApply v.val f = (c : ℂ) • piH1Value f := by
  have hφ : IsRealType (scaledPotential v.val) := (pi_realType_iff v.val).mp v.property
  have hP : N08.Upot (scaledPhysicalPair v.val).1 =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      ((scaledPotential v.val true : UnitL2) : ℝ → ℂ) :=
    N08.e02Pot_ae_unitPhysical (scaledPotential v.val true)
  have htr : (N08.Dy (scaledPhysicalPair v.val).1 y 1).trace =
      2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
    have : actualPhysicalUnitHalfTrace32 (scaledPhysicalPair v.val).1 (y : ℂ) =
        (N08.Dy (scaledPhysicalPair v.val).1 y 1).trace / 2 := rfl
    rw [this] at hy
    linear_combination 2 * hy
  obtain ⟨g, hg0, hgb, hgeig⟩ := N08.exists_unit_eigenpair (scaledPotential v.val) hφ
    (scaledPhysicalPair v.val).1 hP y _ (cos_label_sq n) htr
  let f : PiH1Pair := inverseRescaleH1Pair g
  have hres : rescaleH1Pair f = g := by
    funext b
    exact rescale_inverseRescaleH1 (g b)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨f, ?_, ?_, ?_⟩
  · intro h0
    apply hg0
    have := h1PairValue_rescale f
    rw [hres, h0, map_zero] at this
    exact this
  · unfold piBoundary
    rw [hres]
    unfold labelBoundary
    split_ifs with h
    · show ∀ b : Bool, _ = _
      intro b
      rw [hgb b, (cos_label_sign n).1 h, one_mul]
    · show ∀ b : Bool, _ = _
      intro b
      rw [hgb b, (cos_label_sign n).2 h, neg_one_mul]
  · have h1 := dirac_period_rescaling v.val f
    have h3' : h1PairValue g = unitaryRescalePair (piH1Value f) := by
      rw [← hres]; exact h1PairValue_rescale f
    rw [hres, hgeig, h3'] at h1
    have h2 : (Real.pi : ℂ) • unitaryRescalePair (piZSApply v.val f) =
        (Real.pi : ℂ) • unitaryRescalePair ((c : ℂ) • piH1Value f) := by
      rw [← h1, map_smul, hc]
      rw [← smul_assoc, smul_eq_mul]
      push_cast
      rfl
    have h3 := smul_right_injective _ hπ h2
    exact unitaryRescalePair.injective h3

theorem dm_endpoint_eigenvectors (v : PiRealPotential) (n : ℤ) :
    (∃ f : PiH1Pair, piH1Value f ≠ 0 ∧
      piBoundary (labelBoundary n) f ∧
      piZSApply v.val f = (dmLower v n : ℂ) • piH1Value f) ∧
    (∃ f : PiH1Pair, piH1Value f ≠ 0 ∧
      piBoundary (labelBoundary n) f ∧
      piZSApply v.val f = (dmUpper v n : ℂ) • piH1Value f) := by
  obtain ⟨hl, hu⟩ := actualGapEndpoint_halfTrace_all_E02_38 (scaledPhysicalPair v.val).1 n
  exact ⟨endpoint_eigenvector_of v n _ (dmLower v n) hl (dm_lower_eq v n),
    endpoint_eigenvector_of v n _ (dmUpper v n) hu (dm_upper_eq v n)⟩


end

end NlsGge.Atomic.DM002

/- ===== END_N08 ===== -/
