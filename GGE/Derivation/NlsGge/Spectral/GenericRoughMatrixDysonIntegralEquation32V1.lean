import NlsGge.Spectral.GenericRoughMatrixDysonSummability32V1
import NlsGge.Spectral.RestrictedIocHasSumIntegralDCTPrerequisiteV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

/-- The constructed series for any entrywise integrable 2-by-2 coefficient
with a realized integrable nonnegative majorant satisfies its actual Volterra
equation. The proof exchanges sums and integrals by dominated convergence on
the true restricted interval, without assuming the target equation. Concrete
interaction coefficients and uniqueness are separate realizations. -/
theorem genericRoughMatrixDysonTsum_integral_equation32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T)
    (hq : IntervalIntegrable q volume 0 T) (hqpos : ∀ s, 0 ≤ q s)
    (hmajorant : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    genericRoughMatrixDysonTsum32 B t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTsum32 B s) i j := by
  let Q : ℝ := actualCumulativeRealIntegral q T
  let b : ℕ → ℝ := fun n => (2 * Q) ^ n / (n.factorial : ℝ)
  let bound : ℕ → ℝ → ℝ := fun n s => (2 * q s) * b n
  let F : ℕ → ℝ → ℂ := fun n s =>
    (B s * genericRoughMatrixDysonTerm32 B n s) i j
  let f : ℝ → ℂ := fun s =>
    (B s * genericRoughMatrixDysonTsum32 B s) i j
  have hb : Summable b := (NormedSpace.expSeries_div_hasSum_exp (2 * Q)).summable
  have hqRestricted : Integrable q (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have hq2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      hT).mp
      hq
    exact hq2.mono_set (Set.Ioc_subset_Ioc le_rfl ht.2)
  have hmeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro n
    have hA (k : Fin 2) := hB i k
    have hB (k : Fin 2) : ContinuousOn
        (fun s => genericRoughMatrixDysonTerm32 B n s k j) (Set.uIcc (0 : ℝ) T) := by
      simpa only [Set.uIcc_of_le hT] using
        continuousOn_genericRoughMatrixDysonTerm32 B T hT hB n k j
    have hprod : IntervalIntegrable (F n) volume 0 T := by
      simpa only [F, Matrix.mul_apply, Fin.sum_univ_two] using
        ((hA 0).mul_continuousOn (hB 0)).add ((hA 1).mul_continuousOn (hB 1))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      hT).mp hprod).mono_set
      (Set.Ioc_subset_Ioc le_rfl ht.2) |>.aestronglyMeasurable
  have hnorm : ∀ n, ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ‖F n s‖ ≤ bound n s := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun s hs => by
      have hs2 : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
      have hD : actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) ≤ b n := by
        unfold actualComplexMatrixEntrySup
        exact max_le
          (max_le (genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n s hs2 0 0)
            (genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n s hs2 0 1))
          (max_le (genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n s hs2 1 0)
            (genericRoughMatrixDysonTerm_uniform_bound32 B q T hq hqpos hmajorant n s hs2 1 1))
      have hDpos : 0 ≤ actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) :=
        (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
      calc
        ‖F n s‖ ≤ actualComplexMatrixEntrySup
            (B s * genericRoughMatrixDysonTerm32 B n s) :=
          norm_entry_le_actualComplexMatrixEntrySup _ i j
        _ ≤ 2 * actualComplexMatrixEntrySup (B s) *
            actualComplexMatrixEntrySup (genericRoughMatrixDysonTerm32 B n s) :=
          actualComplexMatrixEntrySup_mul_le _ _
        _ ≤ (2 * q s) * b n := mul_le_mul
          (mul_le_mul_of_nonneg_left
            (hmajorant s hs2) (by norm_num))
          hD hDpos (mul_nonneg (by norm_num) (hqpos s)))
  have hbs : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      Summable (fun n => bound n s) :=
    Filter.Eventually.of_forall (fun s => hb.mul_left (2 * q s))
  have hbi : Integrable (fun s => ∑' n, bound n s)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    have h := (hqRestricted.const_mul 2).mul_const (∑' n, b n)
    simpa only [bound, tsum_mul_left] using h
  have hpoint : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      HasSum (fun n => F n s) (f s) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun s hs =>
      hasSum_genericRoughMatrixDysonProduct32 B q T hq hqpos hmajorant s
        ⟨le_of_lt hs.1, hs.2.trans ht.2⟩ i j)
  have hsum := hasSum_integral_restrict_Ioc_of_dominated_convergence
    t F f bound hmeas hnorm hbs hbi hpoint
  have htail : HasSum (fun n => genericRoughMatrixDysonTerm32 B (n + 1) t i j)
      (∫ s in (0 : ℝ)..t, f s) := by
    convert hsum using 1
    · funext n
      change (∫ s in (0 : ℝ)..t, F n s) =
        ∫ s, F n s ∂(volume.restrict (Set.Ioc (0 : ℝ) t))
      rw [intervalIntegral.integral_of_le ht.1]
    · rw [intervalIntegral.integral_of_le ht.1]
  have hsplit :=
    (summable_genericRoughMatrixDysonTerm32 B q T hq hqpos hmajorant t ht i j).sum_add_tsum_nat_add 1
  change _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j + ∫ s in (0 : ℝ)..t, f s
  calc
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∑' n, genericRoughMatrixDysonTerm32 B (n + 1) t i j := by
      simpa [genericRoughMatrixDysonTsum32, genericRoughMatrixDysonTerm32] using hsplit.symm
    _ = _ := by rw [htail.tsum_eq]
end NlsGge.SpectralFoundations
end
