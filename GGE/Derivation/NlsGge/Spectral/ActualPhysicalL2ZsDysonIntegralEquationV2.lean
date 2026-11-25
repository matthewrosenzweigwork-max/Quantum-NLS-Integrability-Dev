import NlsGge.Spectral.ActualPhysicalL2ZsDysonUniformEntrySummabilityV1
import NlsGge.Spectral.RestrictedIocHasSumIntegralDCTPrerequisiteV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual Dyson series for every physical L² input solves the doubled-
interval Volterra equation. The coefficient has only its proved L¹ regularity.
This is not yet AC uniqueness or spectral root identification. -/
theorem actualPhysicalL2ZsDysonTsum_integral_equationV2
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2)
    (i j : Fin 2) :
    actualComplexZsDysonTsum
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t, (zsCoefficientComplex
          (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
          z s * actualComplexZsDysonTsum
          (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
          z s) i j := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  let q : ℝ → ℝ := actualPhysicalL2ZsMajorant u z
  let Q : ℝ := actualPhysicalL2ZsCumulativeMajorant u z 2
  let b : ℕ → ℝ := fun n => (2 * Q) ^ n / (n.factorial : ℝ)
  let bound : ℕ → ℝ → ℝ := fun n s => (2 * q s) * b n
  let F : ℕ → ℝ → ℂ := fun n s =>
    (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j
  let f : ℝ → ℂ := fun s =>
    (zsCoefficientComplex U z s * actualComplexZsDysonTsum U z s) i j
  have hb : Summable b := (NormedSpace.expSeries_div_hasSum_exp (2 * Q)).summable
  have hq : Integrable q (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have hq2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 2)).mp
      (actualPhysicalL2ZsMajorant_intervalIntegrable u z)
    exact hq2.mono_set (Set.Ioc_subset_Ioc le_rfl ht.2)
  have hmeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro n
    have hA (k : Fin 2) := actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k
    have hB (k : Fin 2) : ContinuousOn
        (fun s => actualComplexZsDysonTerm U z n s k j) (Set.uIcc (0 : ℝ) 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using
        continuousOn_actualPhysicalL2ZsDysonTerm_entry u z n k j
    have hprod : IntervalIntegrable (F n) volume 0 2 := by
      simpa only [F, U, actualPhysicalL2ZsCoefficient, Matrix.mul_apply, Fin.sum_univ_two] using
        ((hA 0).mul_continuousOn (hB 0)).add ((hA 1).mul_continuousOn (hB 1))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 2)).mp hprod).mono_set
      (Set.Ioc_subset_Ioc le_rfl ht.2) |>.aestronglyMeasurable
  have hnorm : ∀ n, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖F n s‖ ≤ bound n s := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun s hs => by
      have hs2 : s ∈ Set.Icc (0 : ℝ) 2 := ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
      have hD : actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) ≤ b n := by
        unfold actualComplexMatrixEntrySup
        exact max_le
          (max_le (actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n s hs2 0 0)
            (actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n s hs2 0 1))
          (max_le (actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n s hs2 1 0)
            (actualPhysicalL2ZsDysonTerm_entry_uniform_bound u z n s hs2 1 1))
      have hDpos : 0 ≤ actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) :=
        (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
      calc
        ‖F n s‖ ≤ actualComplexMatrixEntrySup
            (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) :=
          norm_entry_le_actualComplexMatrixEntrySup _ i j
        _ ≤ 2 * actualComplexMatrixEntrySup (zsCoefficientComplex U z s) *
            actualComplexMatrixEntrySup (actualComplexZsDysonTerm U z n s) :=
          actualComplexMatrixEntrySup_mul_le _ _
        _ ≤ (2 * q s) * b n := mul_le_mul
          (mul_le_mul_of_nonneg_left
            (actualPhysicalL2ZsCoefficient_entrySup_le_majorant u z s) (by norm_num))
          hD hDpos (mul_nonneg (by norm_num) (actualPhysicalL2ZsMajorant_nonneg u z s)))
  have hbs : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      Summable (fun n => bound n s) :=
    Filter.Eventually.of_forall (fun s => hb.mul_left (2 * q s))
  have hbi : Integrable (fun s => ∑' n, bound n s)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have h := (hq.const_mul 2).mul_const (∑' n, b n)
    simpa only [bound, tsum_mul_left] using h
  have hpoint : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      HasSum (fun n => F n s) (f s) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun s hs =>
      hasSum_actualPhysicalL2ZsDysonProduct_entry u z s
        ⟨le_of_lt hs.1, hs.2.trans ht.2⟩ i j)
  have hsum := hasSum_integral_restrict_Ioc_of_dominated_convergence
    t F f bound hmeas hnorm hbs hbi hpoint
  have htail : HasSum (fun n => actualComplexZsDysonTerm U z (n + 1) t i j)
      (∫ s in (0 : ℝ)..t, f s) := by
    convert hsum using 1
    · funext n
      change (∫ s in (0 : ℝ)..t, F n s) =
        ∫ s, F n s ∂(volume.restrict (Set.Ioc (0 : ℝ) t))
      rw [intervalIntegral.integral_of_le ht.1]
    · rw [intervalIntegral.integral_of_le ht.1]
  have hsplit :=
    (summable_actualPhysicalL2ZsDysonTerm_entry u z t ht i j).sum_add_tsum_nat_add 1
  change _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j + ∫ s in (0 : ℝ)..t, f s
  calc
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∑' n, actualComplexZsDysonTerm U z (n + 1) t i j := by
      simpa [actualComplexZsDysonTsum, actualComplexZsDysonTerm] using hsplit.symm
    _ = _ := by rw [htail.tsum_eq]
end NlsGge.SpectralFoundations
end
