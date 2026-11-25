import NlsGge.Spectral.ImaginaryResolventSectorKernelBoundV2
import NlsGge.Spectral.ActualNegativeImaginaryFreeCoordinateDomainInverseV1
import NlsGge.Schur.FreeDomainContinuousL2AfterReflectedPrerequisite
import NlsGge.Schur.FreeResolventHilbertSpaceL2AfterRpowIdentity
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace NlsGge.Schur

open NlsGge.Pilot
open NlsGge.Pilot.ImaginaryResolventSectorKernelBoundV2

private def sourceSectorComponentSequence {n : ℤ}
    (x : SectorSquare n) (upper : Bool) : SquareSequence (Sector n) :=
  ⟨fun m => x (upper, m), by
    have hfull : Summable (fun i : Bool × Sector n => ‖x i‖ ^ 2) := by
      simpa using (lp.memℓp x).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hinj : Function.Injective (fun m : Sector n => (upper, m)) := by
      intro a b hab
      exact (Prod.mk.inj hab).2
    have hcomponent : Summable (fun m : Sector n => ‖x (upper, m)‖ ^ 2) :=
      hfull.comp_injective hinj
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hcomponent⟩

private def sourceResolventCoefficientSequence {n : ℤ}
    (y : ℝ) (hy : 1 ≤ y) : SquareSequence (Sector n) :=
  ⟨fun m => sourceFullNegativeImaginaryResolventCoeff y m, by
    have hfull : Summable (ImaginaryResolventSignedTsumBoundV5.signedKernel y) :=
      ImaginaryResolventSignedTsumBoundV5.signedKernel_summable (by linarith)
    have hinj : Function.Injective (fun m : Sector n => m.val) := Subtype.val_injective
    have hcomponent : Summable (fun m : Sector n =>
        ImaginaryResolventSignedTsumBoundV5.signedKernel y m.val) :=
      hfull.comp_injective hinj
    have hsum : Summable (fun m : Sector n =>
        ‖sourceFullNegativeImaginaryResolventCoeff y m‖ ^ 2) := by
      apply hcomponent.congr
      intro m
      rw [sourceFullNegativeImaginaryResolventCoeff_eq_conj, Complex.norm_conj]
      rw [← Complex.normSq_eq_norm_sq]
      rw [sourceFullImaginaryResolventCoeff]
      simp only [spectralCenter_eq_ofReal_pi_mul]
      rw [NlsGge.Pilot.FullImaginaryScalarResolventProbeV2.normSq_imaginary_sub_real_inv]
      rfl
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum⟩

private theorem sourceResolventCoefficient_norm_sq_eq_sectorKernel
    {n : ℤ} (y : ℝ) (m : Sector n) :
    ‖sourceFullNegativeImaginaryResolventCoeff y m‖ ^ 2 = sectorKernel n y m := by
  rw [sourceFullNegativeImaginaryResolventCoeff_eq_conj, Complex.norm_conj]
  rw [← Complex.normSq_eq_norm_sq]
  rw [sourceFullImaginaryResolventCoeff]
  simp only [spectralCenter_eq_ofReal_pi_mul]
  rw [NlsGge.Pilot.FullImaginaryScalarResolventProbeV2.normSq_imaginary_sub_real_inv]
  rfl

private theorem sourceSectorComponentSequence_norm_le
    {n : ℤ} (x : SectorSquare n) (upper : Bool) :
    ‖sourceSectorComponentSequence x upper‖ ≤ ‖x‖ := by
  let f := sourceSectorComponentSequence x upper
  have hfull : Summable (fun i : Bool × Sector n => ‖x i‖ ^ 2) := by
    simpa using (lp.memℓp x).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hinj : Function.Injective (fun m : Sector n => (upper, m)) := by
    intro a b hab
    exact (Prod.mk.inj hab).2
  have hcomponent : Summable (fun m : Sector n => ‖x (upper, m)‖ ^ 2) :=
    hfull.comp_injective hinj
  have hcompare : (∑' m : Sector n, ‖x (upper, m)‖ ^ 2) ≤
      ∑' i : Bool × Sector n, ‖x i‖ ^ 2 :=
    hcomponent.tsum_le_tsum_of_inj (fun m => (upper, m)) hinj
      (fun _ _ => sq_nonneg _) (fun _ => le_rfl) hfull
  have hnormF := complex_lp_two_norm_sq_eq_tsum f
  have hnormX := complex_lp_two_norm_sq_eq_tsum x
  have hsq : ‖f‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      ‖f‖ ^ 2 = ∑' m : Sector n, ‖f m‖ ^ 2 := hnormF
      _ = ∑' m : Sector n, ‖x (upper, m)‖ ^ 2 := by
        apply tsum_congr
        intro m
        rfl
      _ ≤ ∑' i : Bool × Sector n, ‖x i‖ ^ 2 := hcompare
      _ = ‖x‖ ^ 2 := hnormX.symm
  nlinarith [norm_nonneg f, norm_nonneg x,
    sq_nonneg (‖f‖ - ‖x‖)]

private theorem sourceResolventCoefficientSequence_norm_le
    {n : ℤ} (y : ℝ) (hy : 1 ≤ y) :
    ‖sourceResolventCoefficientSequence (n := n) y hy‖ ≤ Real.sqrt (2 / y) := by
  let c := sourceResolventCoefficientSequence (n := n) y hy
  have hnormC := complex_lp_two_norm_sq_eq_tsum c
  have hsector := sectorKernel_tsum_le n hy
  have hcoeffsum : (∑' m : Sector n, ‖c m‖ ^ 2) ≤ 2 / y := by
    calc
      ∑' m : Sector n, ‖c m‖ ^ 2 =
          ∑' m : Sector n, sectorKernel n y m := by
            apply tsum_congr
            intro m
            exact sourceResolventCoefficient_norm_sq_eq_sectorKernel y m
      _ ≤ 2 / y := hsector
  have hroot : 0 ≤ Real.sqrt (2 / y) := Real.sqrt_nonneg _
  have hrootsq : Real.sqrt (2 / y) ^ 2 = 2 / y :=
    Real.sq_sqrt (by positivity : 0 ≤ 2 / y)
  have hnormnonneg : 0 ≤ ‖c‖ := norm_nonneg c
  rw [← hnormC] at hcoeffsum
  nlinarith [sq_nonneg (‖c‖ - Real.sqrt (2 / y))]

/-- The actual all-mode negative-imaginary free resolvent has a continuous Fourier
representative in either source parity channel, with its L²-to-uniform bound.
The zero Fourier mode is included through the signed-kernel estimate. -/
theorem sourceFullNegativeImaginaryResolventSquare_continuous_norm_le
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) (upper : Bool) :
    ‖freeDomainContinuousComponent n
      (sourceFullNegativeImaginaryResolventSquare n y hy x) upper‖ ≤
        Real.sqrt (2 / y) * ‖x‖ := by
  let c := sourceResolventCoefficientSequence (n := n) y hy
  let f := sourceSectorComponentSequence x upper
  have hcs := complex_lp_two_tsum_mul_le c f
  have hdomain := sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy x
  have hseries := freeDomainContinuousComponent_hasSum n
    (sourceFullNegativeImaginaryResolventSquare n y hy x) hdomain upper
  have hterms : Summable (fun m : Sector n =>
      ‖sourceFullNegativeImaginaryResolventSquare n y hy x (upper, m) •
        (fourier (T := (2 : ℝ)) (if upper then m.val else -m.val) :
          C(SpectralCircle, ℂ))‖) := by
    apply hcs.1.of_norm_bounded
    intro m
    rw [sourceFullNegativeImaginaryResolventSquare_apply]
    simp only [norm_smul, fourier_norm, mul_one, norm_mul]
    simp only [norm_norm]
    change ‖sourceFullNegativeImaginaryResolventCoeff y m‖ * ‖x (upper, m)‖ ≤
      ‖c m‖ * ‖f m‖
    rfl
  calc
    _ = ‖∑' m : Sector n,
        sourceFullNegativeImaginaryResolventSquare n y hy x (upper, m) •
          (fourier (T := (2 : ℝ)) (if upper then m.val else -m.val) :
            C(SpectralCircle, ℂ))‖ := by
          rw [← hseries.tsum_eq]
    _ ≤ ∑' m : Sector n,
        ‖sourceFullNegativeImaginaryResolventSquare n y hy x (upper, m) •
          (fourier (T := (2 : ℝ)) (if upper then m.val else -m.val) :
            C(SpectralCircle, ℂ))‖ := norm_tsum_le_tsum_norm hterms
    _ = ∑' m : Sector n, ‖c m‖ * ‖f m‖ := by
          apply tsum_congr
          intro m
          rw [sourceFullNegativeImaginaryResolventSquare_apply]
          simp only [norm_smul, fourier_norm, mul_one, norm_mul]
          rfl
    _ ≤ ‖c‖ * ‖f‖ := hcs.2
    _ ≤ Real.sqrt (2 / y) * ‖x‖ := by
          exact mul_le_mul
            (sourceResolventCoefficientSequence_norm_le (n := n) y hy)
            (sourceSectorComponentSequence_norm_le x upper)
            (norm_nonneg _) (Real.sqrt_nonneg _)

end NlsGge.Schur

end
