import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1
import NlsGge.Spectral.FullImaginaryScalarResolventProbeV2
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace NlsGge.Schur

/-- The full imaginary-axis coefficient on every signed source mode. Unlike
`freeResolventCoeff`, this has no resonant-zero branch. -/
def sourceFullImaginaryResolventCoeff {n : ℤ} (y : ℝ) (m : Sector n) : ℂ :=
  (Complex.I * (y : ℂ) - spectralCenter m.val)⁻¹

lemma spectralCenter_eq_ofReal_pi_mul {n : ℤ} (m : Sector n) :
    spectralCenter m.val = ((Real.pi * (m.val : ℝ) : ℝ) : ℂ) := by
  simp only [spectralCenter, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

lemma sourceFullImaginaryResolvent_denominator_ne_zero
    {n : ℤ} (y : ℝ) (hy : 0 < y) (m : Sector n) :
    Complex.I * (y : ℂ) - spectralCenter m.val ≠ 0 := by
  simpa only [spectralCenter_eq_ofReal_pi_mul] using
    NlsGge.Pilot.FullImaginaryScalarResolventProbeV2.imaginary_sub_real_ne_zero
      (y := y) (a := Real.pi * (m.val : ℝ)) hy

lemma sourceFullImaginaryResolvent_denominator_mul_coeff
    {n : ℤ} (y : ℝ) (hy : 0 < y) (m : Sector n) :
    (Complex.I * (y : ℂ) - spectralCenter m.val) *
      sourceFullImaginaryResolventCoeff y m = 1 := by
  have hden := sourceFullImaginaryResolvent_denominator_ne_zero y hy m
  unfold sourceFullImaginaryResolventCoeff
  field_simp [hden]

lemma sourceFullImaginaryResolventCoeff_norm_le_one
    {n : ℤ} (y : ℝ) (hy : 1 ≤ y) (m : Sector n) :
    ‖sourceFullImaginaryResolventCoeff y m‖ ≤ 1 := by
  have hypos : 0 < y := by linarith
  have hsq :=
    NlsGge.Pilot.FullImaginaryScalarResolventProbeV2.normSq_imaginary_sub_real_inv_le
      (y := y) (a := Real.pi * (m.val : ℝ)) hypos
  have hsq' :
      ‖sourceFullImaginaryResolventCoeff y m‖ ^ 2 ≤ (y ^ 2)⁻¹ := by
    calc
      ‖sourceFullImaginaryResolventCoeff y m‖ ^ 2 =
          Complex.normSq (sourceFullImaginaryResolventCoeff y m) :=
        (Complex.normSq_eq_norm_sq _).symm
      _ ≤ (y ^ 2)⁻¹ := by
        simpa only [sourceFullImaginaryResolventCoeff,
          spectralCenter_eq_ofReal_pi_mul] using hsq
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hInv : (y ^ 2)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hy2)
  have hnorm_nonneg : 0 ≤ ‖sourceFullImaginaryResolventCoeff y m‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖sourceFullImaginaryResolventCoeff y m‖ - 1)]

lemma sourceFullImaginaryResolvent_weightedCoeff_norm_le_one
    {n : ℤ} (y : ℝ) (hy : 0 < y) (m : Sector n) :
    ‖spectralCenter m.val * sourceFullImaginaryResolventCoeff y m‖ ≤ 1 := by
  simpa only [sourceFullImaginaryResolventCoeff,
    spectralCenter_eq_ofReal_pi_mul] using
    NlsGge.Pilot.FullImaginaryScalarResolventProbeV2.weighted_imaginary_resolvent_norm_le_one
      (y := y) (a := Real.pi * (m.val : ℝ)) hy

/-- The all-mode full imaginary resolvent multiplier on the actual source
sequence Hilbert space. -/
def sourceFullImaginaryResolventSquare (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  lp.mapCLM 2
    (fun i : Bool × Sector n =>
      sourceFullImaginaryResolventCoeff y i.2 • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro i
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        sourceFullImaginaryResolventCoeff_norm_le_one y hy i.2)

@[simp] lemma sourceFullImaginaryResolventSquare_apply
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n)
    (i : Bool × Sector n) :
    sourceFullImaginaryResolventSquare n y hy x i =
      sourceFullImaginaryResolventCoeff y i.2 * x i := rfl

/-- The actual weighted coordinates of the full imaginary resolvent are
square summable, including the mode that the complementary local resolvent
removes. -/
theorem sourceFullImaginaryResolventSquare_mem_freeWeightedDomain
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) :
    sourceFullImaginaryResolventSquare n y hy x ∈ freeWeightedDomainPointwise n := by
  let W : SectorSquare n →L[ℂ] SectorSquare n :=
    lp.mapCLM 2
      (fun i : Bool × Sector n =>
        (spectralCenter i.2.val * sourceFullImaginaryResolventCoeff y i.2) •
          ContinuousLinearMap.id ℂ ℂ)
      zero_le_one
      (by
        intro i
        simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
          sourceFullImaginaryResolvent_weightedCoeff_norm_le_one y
            (by linarith) i.2)
  have hcoord :
      freeWeightedCoordinates n (sourceFullImaginaryResolventSquare n y hy x) = W x := by
    funext i
    change spectralCenter i.2.val *
        (sourceFullImaginaryResolventCoeff y i.2 * x i) =
      (spectralCenter i.2.val * sourceFullImaginaryResolventCoeff y i.2) * x i
    ring
  change Memℓp
    (freeWeightedCoordinates n (sourceFullImaginaryResolventSquare n y hy x)) 2
  rw [hcoord]
  exact lp.memℓp (W x)

/-- The actual source free shifted operator has the full right inverse at
`i y`; the zero mode is inverted just like every other mode. -/
theorem sourceFullImaginaryResolventSquare_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) :
    freeShiftedCoordinateDirac n (Complex.I * (y : ℂ))
      ⟨sourceFullImaginaryResolventSquare n y hy x,
        sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy x⟩ = x := by
  have hypos : 0 < y := by linarith
  have hscalar (m : Sector n) :=
    sourceFullImaginaryResolvent_denominator_mul_coeff y hypos m
  apply lp.ext
  funext i
  change Complex.I * (y : ℂ) *
      sourceFullImaginaryResolventSquare n y hy x i -
        freeWeightedCoordinates n (sourceFullImaginaryResolventSquare n y hy x) i = x i
  rw [sourceFullImaginaryResolventSquare_apply]
  change Complex.I * (y : ℂ) *
      (sourceFullImaginaryResolventCoeff y i.2 * x i) -
        spectralCenter i.2.val *
          (sourceFullImaginaryResolventCoeff y i.2 * x i) = x i
  calc
    _ = ((Complex.I * (y : ℂ) - spectralCenter i.2.val) *
        sourceFullImaginaryResolventCoeff y i.2) * x i := by ring
    _ = x i := by rw [hscalar i.2]; simp

/-- The left inverse holds on the exact weighted free domain. -/
theorem sourceFullImaginaryResolventSquare_left_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y)
    (x : freeWeightedDomainPointwise n) :
    sourceFullImaginaryResolventSquare n y hy
      (freeShiftedCoordinateDirac n (Complex.I * (y : ℂ)) x) = x.val := by
  have hypos : 0 < y := by linarith
  have hscalar (m : Sector n) :=
    sourceFullImaginaryResolvent_denominator_mul_coeff y hypos m
  apply lp.ext
  funext i
  change sourceFullImaginaryResolventCoeff y i.2 *
      (Complex.I * (y : ℂ) * x.val i -
        spectralCenter i.2.val * x.val i) = x.val i
  calc
    _ = (sourceFullImaginaryResolventCoeff y i.2 *
        (Complex.I * (y : ℂ) - spectralCenter i.2.val)) * x.val i := by ring
    _ = x.val i := by
      have hcomm : sourceFullImaginaryResolventCoeff y i.2 *
          (Complex.I * (y : ℂ) - spectralCenter i.2.val) = 1 := by
        rw [mul_comm, hscalar i.2]
      rw [hcomm]
      simp

end NlsGge.Schur

end
