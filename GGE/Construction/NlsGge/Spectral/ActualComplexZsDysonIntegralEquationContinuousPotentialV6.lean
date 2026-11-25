import NlsGge.Spectral.ActualComplexZsDysonSeriesUniformOnDisksV10
import NlsGge.Spectral.ActualComplexZsDysonTermFactorialEntryBoundV9
import NlsGge.Spectral.ActualComplexMatrixTwoByTwoEntrySupProductBoundV2
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Spectral.ActualComplexZsDysonProductAEStronglyMeasurableV2
import NlsGge.Spectral.RestrictedIocHasSumIntegralDCTPrerequisiteV1
import NlsGge.Spectral.RealPowerDivisionProductPrerequisiteV1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- For a continuous actual potential, the totalized actual Dyson series solves
its Volterra integral equation entrywise on the source interval.  The proof
exchanges the actual matrix-product entry series with the restricted interval
integral by the pinned dominated-convergence theorem, then shifts the actual
Dyson recurrence.  This is not yet an identification with the normalized ODE
solution. -/
theorem actualComplexZsDysonTsum_integral_equation_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2))
    (z : ℂ) (R C : ℝ) (hz : ‖z‖ ≤ R) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    actualComplexZsDysonTsum u z t i j =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t,
          (zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j := by
  let M : ℝ := R + C
  let K : ℝ := 2 * M
  let bound : ℕ → ℝ := fun n => 2 * M * ((2 * K) ^ n / (n.factorial : ℝ))
  let boundFn : ℕ → ℝ → ℝ := fun n _ => bound n
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbase : Summable (fun n : ℕ => (2 * K) ^ n / (n.factorial : ℝ)) := by
    simpa using (NormedSpace.expSeries_div_hasSum_exp (2 * K)).summable
  have hbound : Summable bound := by
    simpa [bound] using hbase.mul_left (2 * M)
  have hbound_nonneg (n : ℕ) : 0 ≤ bound n := by
    dsimp [bound]
    positivity
  have hbound_integrable : MeasureTheory.Integrable
      (fun s : ℝ => ∑' n : ℕ, boundFn n s)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    simpa [boundFn] using
      (integrable_const (∑' n : ℕ, bound n) : MeasureTheory.Integrable
        (fun _ : ℝ => ∑' n : ℕ, bound n)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)))
  have hmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => (zsCoefficientComplex u z s *
          actualComplexZsDysonTerm u z n s) i j)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro n
    exact aestronglyMeasurable_actualComplexZsDysonProductEntryOnIoc
      u hu z n t ht i j
  have hnorm_bound : ∀ n : ℕ, ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Ioc (0 : ℝ) t →
        ‖(zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j‖ ≤
          bound n := by
    intro n
    filter_upwards [] with s
    intro hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt hs.1, hs.2⟩
    have hs2 : s ∈ Set.Icc (0 : ℝ) 2 :=
      ⟨hsIcc.1, le_trans hsIcc.2 ht.2⟩
    have hAsup : actualComplexMatrixEntrySup (zsCoefficientComplex u z s) ≤ M := by
      dsimp [M]
      exact actualComplexZsCoefficient_entrySup_bound u z s R C hz (hU s hs2)
    have hDs : ∀ a b : Fin 2,
        ‖actualComplexZsDysonTerm u z n s a b‖ ≤
          ((K ^ n / (n.factorial : ℝ)) * s ^ n) := by
      intro a b
      simpa [K, M] using
        actualComplexZsDysonTerm_entry_factorial_bound
          u z R C hz hR hU hC n s hs2 a b
    have hDsup : actualComplexMatrixEntrySup
        (actualComplexZsDysonTerm u z n s) ≤
          ((K ^ n / (n.factorial : ℝ)) * s ^ n) := by
      unfold actualComplexMatrixEntrySup
      exact max_le (max_le (hDs 0 0) (hDs 0 1)) (max_le (hDs 1 0) (hDs 1 1))
    have hproduct := actualComplexMatrixEntrySup_mul_le
      (zsCoefficientComplex u z s) (actualComplexZsDysonTerm u z n s)
    have hsup : actualComplexMatrixEntrySup
        (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) ≤
          2 * M * ((K ^ n / (n.factorial : ℝ)) * s ^ n) := by
      calc
        actualComplexMatrixEntrySup
            (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) ≤
            2 * actualComplexMatrixEntrySup (zsCoefficientComplex u z s) *
              actualComplexMatrixEntrySup (actualComplexZsDysonTerm u z n s) := hproduct
        _ ≤ 2 * M * ((K ^ n / (n.factorial : ℝ)) * s ^ n) := by
          have hDnonneg : 0 ≤ actualComplexMatrixEntrySup
              (actualComplexZsDysonTerm u z n s) := by
            unfold actualComplexMatrixEntrySup
            positivity
          have hMnonneg : 0 ≤ M := hM
          calc
            2 * actualComplexMatrixEntrySup (zsCoefficientComplex u z s) *
                actualComplexMatrixEntrySup (actualComplexZsDysonTerm u z n s) ≤
                2 * M * actualComplexMatrixEntrySup (actualComplexZsDysonTerm u z n s) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hAsup (by norm_num)) hDnonneg
            _ ≤ 2 * M * ((K ^ n / (n.factorial : ℝ)) * s ^ n) := by
                  exact mul_le_mul_of_nonneg_left hDsup (by positivity)
    have hentry := norm_entry_le_actualComplexMatrixEntrySup
      (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j
    have hsPow : s ^ n ≤ (2 : ℝ) ^ n :=
      pow_le_pow_left₀ hsIcc.1 (le_trans hsIcc.2 ht.2) n
    have hcoef : 0 ≤ (K ^ n / (n.factorial : ℝ)) := by positivity
    calc
      ‖(zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j‖ ≤
          2 * M * ((K ^ n / (n.factorial : ℝ)) * s ^ n) := le_trans hentry hsup
      _ ≤ 2 * M * ((K ^ n / (n.factorial : ℝ)) * (2 : ℝ) ^ n) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hsPow hcoef
          · positivity
      _ = bound n := by
          dsimp only [bound, K]
          rw [real_pow_div_mul_pow]
          rw [mul_comm (2 * M) 2]
  have hbound_summable : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Ioc (0 : ℝ) t → Summable fun n : ℕ => boundFn n s := by
    filter_upwards [MeasureTheory.ae_of_all _ (fun _ : ℝ => hbound)] with s
    intro hs0 hst
    simpa [boundFn] using hbound
  have hlimit : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.Ioc (0 : ℝ) t →
        HasSum
          (fun n : ℕ => (zsCoefficientComplex u z s *
            actualComplexZsDysonTerm u z n s) i j)
          ((zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j) := by
    filter_upwards [] with s
    intro hs
    have hs2 : s ∈ Set.Icc (0 : ℝ) 2 :=
      ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
    exact hasSum_actualComplexZsDysonProduct_entry
      u z R C hz hR hC hU s hs2 i j
  have hnorm_bound_restrict : ∀ n : ℕ,
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
        ‖(zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j‖ ≤
          boundFn n s := by
    intro n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hnorm_bound n] with s hs
    simpa [boundFn] using hs
  have hbound_summable_restrict :
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
        Summable fun n : ℕ => boundFn n s := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hbound_summable] with s hs
    intro hsMem
    simpa [boundFn] using hs hsMem
  have hlimit_restrict :
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
        HasSum
          (fun n : ℕ => (zsCoefficientComplex u z s *
            actualComplexZsDysonTerm u z n s) i j)
          ((zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact hlimit
  have hsum_restrict := hasSum_integral_restrict_Ioc_of_dominated_convergence
    t
    (fun n s => (zsCoefficientComplex u z s *
      actualComplexZsDysonTerm u z n s) i j)
    (fun s => (zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j)
    boundFn hmeas hnorm_bound_restrict hbound_summable_restrict hbound_integrable
    hlimit_restrict
  have hintegral : HasSum
      (fun n : ℕ => ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex u z s * actualComplexZsDysonTerm u z n s) i j)
      (∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j) := by
    convert hsum_restrict using 1
    · funext n
      rw [intervalIntegral.integral_of_le ht.1]
    · rw [intervalIntegral.integral_of_le ht.1]
  have htail : HasSum
      (fun n : ℕ => actualComplexZsDysonTerm u z (n + 1) t i j)
      (∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j) := by
    convert hintegral using 1 <;> rfl
  have htail_eq := htail.tsum_eq
  let pT : ℂ × ℝ := (z, t)
  have hpT : pT ∈ {p : ℂ × ℝ | ‖p.1‖ ≤ R ∧ p.2 ∈ Set.Icc (0 : ℝ) 2} :=
    ⟨hz, ht⟩
  have hseries :=
    (hasSumUniformlyOn_actualComplexZsDysonSeries_entry
      u R C hR hC hU i j).hasSum hpT
  have hsplit :
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∑' n : ℕ, actualComplexZsDysonTerm u z (n + 1) t i j =
        actualComplexZsDysonTsum u z t i j := by
    simpa [actualComplexZsDysonTsum, actualComplexZsDysonTerm] using
      hseries.summable.sum_add_tsum_nat_add 1
  calc
    actualComplexZsDysonTsum u z t i j =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
          ∑' n : ℕ, actualComplexZsDysonTerm u z (n + 1) t i j := hsplit.symm
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
          ∫ s in (0 : ℝ)..t,
            (zsCoefficientComplex u z s * actualComplexZsDysonTsum u z s) i j := by
          rw [htail_eq]

end NlsGge.SpectralFoundations

end
