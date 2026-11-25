import NlsGge.Schur.SourceInterval
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

/-- Actual translation sends the second source half to the first half measure. -/
theorem sourceSecondHalfShift_preserving : MeasurePreserving
    (fun x : ℝ => x - 1) (volume.restrict (Set.Ioc (1 : ℝ) 2))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hp := (measurePreserving_add_right (volume : Measure ℝ) (-1 : ℝ)).restrict_preimage
    (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
  have hs : (fun x : ℝ => x + (-1 : ℝ)) ⁻¹' Set.Ioc (0 : ℝ) 1 = Set.Ioc (1 : ℝ) 2 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  simpa only [hs, sub_eq_add_neg] using hp

/-- Explicit signed function on the doubled real interval. -/
def sourceSignedHalfValue (n : ℤ) (u : SourceIntervalL2) (x : ℝ) : ℂ :=
  if x ≤ 1 then u x else spectralSign n * u (x - 1)

/-- Both measured halves give actual membership before constructing a circle class. -/
theorem sourceSignedHalf_memLp (n : ℤ) (u : SourceIntervalL2) :
    MemLp (sourceSignedHalfValue n u) 2 (volume.restrict (Set.Ioc (0 : ℝ) 2)) := by
  have hfirstSet : Set.Iic (1 : ℝ) ∩ Set.Ioc (0 : ℝ) 2 = Set.Ioc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hx1, hx0, hx2⟩
      exact ⟨hx0, hx1⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨hx1, hx0, hx1.trans (by norm_num)⟩
  have hsecondSet : (Set.Iic (1 : ℝ))ᶜ ∩ Set.Ioc (0 : ℝ) 2 = Set.Ioc (1 : ℝ) 2 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hx1, hx0, hx2⟩
      exact ⟨lt_of_not_ge hx1, hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨not_le.mpr hx1, (by norm_num : (0 : ℝ) < 1).trans hx1, hx2⟩
  have hf : MemLp u 2 ((volume.restrict (Set.Ioc (0 : ℝ) 2)).restrict (Set.Iic (1 : ℝ))) := by
    rw [Measure.restrict_restrict measurableSet_Iic, hfirstSet]
    exact Lp.memLp u
  have hg : MemLp (fun x : ℝ => spectralSign n * u (x - 1)) 2
      ((volume.restrict (Set.Ioc (0 : ℝ) 2)).restrict (Set.Iic (1 : ℝ))ᶜ) := by
    rw [Measure.restrict_restrict measurableSet_Iic.compl, hsecondSet]
    simpa only [Function.comp_def] using
      ((Lp.memLp u).comp_measurePreserving sourceSecondHalfShift_preserving).const_mul
        (spectralSign n)
  change MemLp ((Set.Iic (1 : ℝ)).piecewise u
    (fun x : ℝ => spectralSign n * u (x - 1))) 2 (volume.restrict (Set.Ioc (0 : ℝ) 2))
  exact MemLp.piecewise measurableSet_Iic hf hg

/-- Actual lift of the explicitly constructed signed function. -/
def sourceSignedCircleValue (n : ℤ) (u : SourceIntervalL2) : SpectralCircle → ℂ :=
  AddCircle.liftIoc (2 : ℝ) 0 (sourceSignedHalfValue n u)

theorem sourceSignedCircle_memLp (n : ℤ) (u : SourceIntervalL2) :
    MemLp (sourceSignedCircleValue n u) 2 spectralHaar := by
  have hf : MemLp (sourceSignedHalfValue n u) 2
      (volume.restrict (Set.Ioc (0 : ℝ) (0 + 2))) := by
    simpa only [zero_add] using sourceSignedHalf_memLp n u
  have hp : MemLp (AddCircle.liftIoc (2 : ℝ) 0 (sourceSignedHalfValue n u)) 2
      (volume : Measure SpectralCircle) := hf.memLp_liftIoc
  exact hp.haarAddCircle

/-- The constructed lifted function has pointwise parity, including endpoint representatives. -/
theorem sourceSignedCircle_halfShift (n : ℤ) (u : SourceIntervalL2) (x : SpectralCircle) :
    sourceSignedCircleValue n u (x + ((1 : ℝ) : SpectralCircle)) =
      spectralSign n * sourceSignedCircleValue n u x := by
  let r : ℝ := (AddCircle.equivIoc (2 : ℝ) 0 x).val
  have hr : 0 < r ∧ r ≤ 2 := by
    simpa only [r, zero_add, Set.mem_Ioc] using (AddCircle.equivIoc (2 : ℝ) 0 x).property
  have hx : (r : SpectralCircle) = x := AddCircle.coe_equivIoc
  have hr0 : r ∈ Set.Ioc (0 : ℝ) (0 + 2) := by simpa only [zero_add, Set.mem_Ioc] using hr
  rw [← hx]
  by_cases hle : r ≤ 1
  · have hr1 : r + 1 ∈ Set.Ioc (0 : ℝ) (0 + 2) := by
      constructor <;> linarith [hr.1, hr.2]
    have hgt : ¬r + 1 ≤ 1 := by linarith [hr.1]
    simp only [sourceSignedCircleValue]
    rw [← AddCircle.coe_add, AddCircle.liftIoc_coe_apply hr1, AddCircle.liftIoc_coe_apply hr0]
    simp only [sourceSignedHalfValue, ite_eq_right hgt, ite_eq_left hle, add_sub_cancel_right]
  · have hminus : r - 1 ∈ Set.Ioc (0 : ℝ) (0 + 2) := by
      constructor <;> linarith [hr.1, hr.2]
    have hminus_le : r - 1 ≤ 1 := by linarith [hr.2]
    have ht : ((r - 1 : ℝ) : SpectralCircle) = ((r + 1 : ℝ) : SpectralCircle) := by
      have he : r + 1 = (r - 1) + 2 := by ring
      rw [he, AddCircle.coe_add_period]
    simp only [sourceSignedCircleValue]
    rw [← AddCircle.coe_add, ← ht,
      AddCircle.liftIoc_coe_apply hminus, AddCircle.liftIoc_coe_apply hr0]
    simp only [sourceSignedHalfValue, ite_eq_left hminus_le, ite_eq_right hle]
    rw [← mul_assoc, spectralSign_mul_self, one_mul]

def scalarParityExtendValue (n : ℤ) (u : SourceIntervalL2) : SpectralScalarL2 :=
  (sourceSignedCircle_memLp n u).toLp (sourceSignedCircleValue n u)

theorem scalarParityExtendValue_ae (n : ℤ) (u : SourceIntervalL2) :
    scalarParityExtendValue n u =ᵐ[spectralHaar] sourceSignedCircleValue n u :=
  (sourceSignedCircle_memLp n u).coeFn_toLp

/-- Membership in the actual parity kernel is proved before forming its subtype. -/
theorem scalarParityExtendValue_mem (n : ℤ) (u : SourceIntervalL2) :
    scalarParityExtendValue n u ∈ scalarParity n := by
  rw [mem_scalarParity]
  apply Lp.ext
  have hshift := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp
    (scalarParityExtendValue_ae n u)
  filter_upwards [halfTranslation_ae (scalarParityExtendValue n u), hshift,
    scalarParityExtendValue_ae n u,
    Lp.coeFn_smul (spectralSign n) (scalarParityExtendValue n u)] with x ht hs hu hout
  dsimp only [Function.comp_def] at hs
  rw [ht, hout]
  change scalarParityExtendValue n u (x + ((1 : ℝ) : SpectralCircle)) =
    spectralSign n * scalarParityExtendValue n u x
  rw [hs, hu, sourceSignedCircle_halfShift]

def scalarParityExtend (n : ℤ) (u : SourceIntervalL2) : scalarParity n :=
  ⟨scalarParityExtendValue n u, scalarParityExtendValue_mem n u⟩

/-- The actual constructed extension restricts to the arbitrary source class a.e. -/
theorem scalarParityRestrict_extend (n : ℤ) (u : SourceIntervalL2) :
    scalarParityRestrict n (scalarParityExtend n u) = u := by
  apply Lp.ext
  have hex := spectral_ae_pullback_first_half (scalarParityExtendValue_ae n u)
  filter_upwards [scalarParityRestrictValue_ae n (scalarParityExtend n u), hex,
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hres hext hx
  change scalarParityRestrictValue n (scalarParityExtend n u) x = u x
  rw [hres]
  change scalarParityExtendValue n u (x : SpectralCircle) = u x
  rw [hext]
  have hxd : x ∈ Set.Ioc (0 : ℝ) (0 + 2) := by
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  rw [sourceSignedCircleValue, AddCircle.liftIoc_coe_apply hxd]
  simp only [sourceSignedHalfValue, ite_eq_left hx.2]

theorem scalarParityRestrict_surjective (n : ℤ) :
    Function.Surjective (scalarParityRestrict n) :=
  fun u => ⟨scalarParityExtend n u, scalarParityRestrict_extend n u⟩

/-- The source interval equivalence is derived from actual constructed surjectivity. -/
def scalarParityIntervalEquiv (n : ℤ) : scalarParity n ≃ₗᵢ[ℂ] SourceIntervalL2 :=
  LinearIsometryEquiv.ofSurjective (scalarParityRestrict n) (scalarParityRestrict_surjective n)

end NlsGge.Schur
