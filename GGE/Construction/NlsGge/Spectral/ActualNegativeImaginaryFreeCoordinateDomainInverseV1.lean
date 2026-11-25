import NlsGge.Spectral.ActualNegativeImaginaryScalarConjugationV1

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate

namespace NlsGge.Schur

/-- The full negative-imaginary coefficient inverts every source denominator. -/
theorem sourceFullNegativeImaginaryResolvent_denominator_mul_coeff
    {n : ℤ} (y : ℝ) (hy : 0 < y) (m : Sector n) :
    (-Complex.I * (y : ℂ) - spectralCenter m.val) *
      sourceFullNegativeImaginaryResolventCoeff y m = 1 := by
  calc
    _ = conj ((Complex.I * (y : ℂ) - spectralCenter m.val) *
        sourceFullImaginaryResolventCoeff y m) := by
      rw [map_mul]
      simp [sourceFullNegativeImaginaryResolventCoeff_eq_conj,
        map_sub, map_mul, spectralCenter_eq_ofReal_pi_mul]
    _ = 1 := by rw [sourceFullImaginaryResolvent_denominator_mul_coeff y hy m]; simp

/-- The all-mode full imaginary resolvent multiplier on the actual source
sequence Hilbert space. -/
def sourceFullNegativeImaginaryResolventSquare (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  lp.mapCLM 2
    (fun i : Bool × Sector n =>
      sourceFullNegativeImaginaryResolventCoeff y i.2 • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro i
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        sourceFullNegativeImaginaryResolventCoeff_norm_le_one y hy i.2)

@[simp] lemma sourceFullNegativeImaginaryResolventSquare_apply
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n)
    (i : Bool × Sector n) :
    sourceFullNegativeImaginaryResolventSquare n y hy x i =
      sourceFullNegativeImaginaryResolventCoeff y i.2 * x i := rfl

/-- The actual weighted coordinates of the full imaginary resolvent are
square summable, including the mode that the complementary local resolvent
removes. -/
theorem sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) :
    sourceFullNegativeImaginaryResolventSquare n y hy x ∈ freeWeightedDomainPointwise n := by
  let W : SectorSquare n →L[ℂ] SectorSquare n :=
    lp.mapCLM 2
      (fun i : Bool × Sector n =>
        (spectralCenter i.2.val * sourceFullNegativeImaginaryResolventCoeff y i.2) •
          ContinuousLinearMap.id ℂ ℂ)
      zero_le_one
      (by
        intro i
        simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
          sourceFullNegativeImaginaryResolvent_weightedCoeff_norm_le_one y
            (by linarith) i.2)
  have hcoord :
      freeWeightedCoordinates n (sourceFullNegativeImaginaryResolventSquare n y hy x) = W x := by
    funext i
    change spectralCenter i.2.val *
        (sourceFullNegativeImaginaryResolventCoeff y i.2 * x i) =
      (spectralCenter i.2.val * sourceFullNegativeImaginaryResolventCoeff y i.2) * x i
    ring
  change Memℓp
    (freeWeightedCoordinates n (sourceFullNegativeImaginaryResolventSquare n y hy x)) 2
  rw [hcoord]
  exact lp.memℓp (W x)

/-- The actual source free shifted operator has the full right inverse at
`-i y`; the zero mode is inverted just like every other mode. -/
theorem sourceFullNegativeImaginaryResolventSquare_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) :
    freeShiftedCoordinateDirac n (-Complex.I * (y : ℂ))
      ⟨sourceFullNegativeImaginaryResolventSquare n y hy x,
        sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy x⟩ = x := by
  have hypos : 0 < y := by linarith
  have hscalar (m : Sector n) :=
    sourceFullNegativeImaginaryResolvent_denominator_mul_coeff y hypos m
  apply lp.ext
  funext i
  change -Complex.I * (y : ℂ) *
      sourceFullNegativeImaginaryResolventSquare n y hy x i -
        freeWeightedCoordinates n (sourceFullNegativeImaginaryResolventSquare n y hy x) i = x i
  rw [sourceFullNegativeImaginaryResolventSquare_apply]
  change -Complex.I * (y : ℂ) *
      (sourceFullNegativeImaginaryResolventCoeff y i.2 * x i) -
        spectralCenter i.2.val *
          (sourceFullNegativeImaginaryResolventCoeff y i.2 * x i) = x i
  calc
    _ = ((-Complex.I * (y : ℂ) - spectralCenter i.2.val) *
        sourceFullNegativeImaginaryResolventCoeff y i.2) * x i := by ring
    _ = x i := by rw [hscalar i.2]; simp

/-- The left inverse holds on the exact weighted free domain. -/
theorem sourceFullNegativeImaginaryResolventSquare_left_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y)
    (x : freeWeightedDomainPointwise n) :
    sourceFullNegativeImaginaryResolventSquare n y hy
      (freeShiftedCoordinateDirac n (-Complex.I * (y : ℂ)) x) = x.val := by
  have hypos : 0 < y := by linarith
  have hscalar (m : Sector n) :=
    sourceFullNegativeImaginaryResolvent_denominator_mul_coeff y hypos m
  apply lp.ext
  funext i
  change sourceFullNegativeImaginaryResolventCoeff y i.2 *
      (-Complex.I * (y : ℂ) * x.val i -
        spectralCenter i.2.val * x.val i) = x.val i
  calc
    _ = (sourceFullNegativeImaginaryResolventCoeff y i.2 *
        (-Complex.I * (y : ℂ) - spectralCenter i.2.val)) * x.val i := by ring
    _ = x.val i := by
      have hcomm : sourceFullNegativeImaginaryResolventCoeff y i.2 *
          (-Complex.I * (y : ℂ) - spectralCenter i.2.val) = 1 := by
        rw [mul_comm, hscalar i.2]
      rw [hcomm]
      simp

end NlsGge.Schur

end
