import NlsGge.Spectral.ActualComplexZsDysonPolynomialCoefficientsContinuousV6
import NlsGge.Spectral.ActualPhysicalL2ZsCoefficientAllEntriesIntegrableMinimumV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

private theorem recurrence_integrable_from_lower_coefficient_continuity
    (U : ℝ → ℂ)
    (hA : ∀ i l : Fin 2, IntervalIntegrable
      (fun s => zsCoefficientComplex U 0 s i l) volume 0 2)
    (n k : ℕ) (i j : Fin 2)
    (hC : ∀ k i j, ContinuousOn
      (fun t => actualComplexZsDysonPolynomialCoefficient U n k t i j)
      (Set.Icc (0 : ℝ) 2)) :
    IntervalIntegrable
      (fun s => ∑ l : Fin 2,
        (zsCoefficientComplex U 0 s i l *
          actualComplexZsDysonPolynomialCoefficient U n k s l j +
        if k = 0 then 0 else zsComplexSpectralSlope i l *
          actualComplexZsDysonPolynomialCoefficient U n (k - 1) s l j))
      volume 0 2 := by
  have hterm (l : Fin 2) : IntervalIntegrable
      (fun s => zsCoefficientComplex U 0 s i l *
          actualComplexZsDysonPolynomialCoefficient U n k s l j +
        if k = 0 then 0 else zsComplexSpectralSlope i l *
          actualComplexZsDysonPolynomialCoefficient U n (k - 1) s l j)
      volume 0 2 := by
    have hc : ContinuousOn
        (fun t => actualComplexZsDysonPolynomialCoefficient U n k t l j)
        (Set.uIcc (0 : ℝ) 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hC k l j
    have hprod := (hA i l).mul_continuousOn hc
    by_cases hk : k = 0
    · simpa only [if_pos hk, add_zero] using! hprod
    · have hc' : ContinuousOn
          (fun t => actualComplexZsDysonPolynomialCoefficient U n (k - 1) t l j)
          (Set.uIcc (0 : ℝ) 2) := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hC (k - 1) l j
      simpa only [if_neg hk] using!
        hprod.add ((hc'.intervalIntegrable (μ := volume)).const_mul
          (zsComplexSpectralSlope i l))
  simpa only [Fin.sum_univ_two] using! (hterm 0).add (hterm 1)

/-- Every actual recursive coefficient is continuous in time for an L¹ ZS
coefficient. The proof uses L¹ times the continuous lower recursive
coefficient, not continuity or boundedness of the rough potential. -/
theorem continuousOn_actualComplexZsDysonPolynomialCoefficient_of_L1
    (U : ℝ → ℂ)
    (hA : ∀ i l : Fin 2, IntervalIntegrable
      (fun s => zsCoefficientComplex U 0 s i l) volume 0 2)
    (n k : ℕ) (i j : Fin 2) :
    ContinuousOn
      (fun t => actualComplexZsDysonPolynomialCoefficient U n k t i j)
      (Set.Icc (0 : ℝ) 2) := by
  induction n generalizing k i j with
  | zero =>
    simp only [actualComplexZsDysonPolynomialCoefficient]
    split_ifs <;> exact continuousOn_const
  | succ n ih =>
    have hint := recurrence_integrable_from_lower_coefficient_continuity U hA n k i j ih
    have hp := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      hint (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2)
    simpa only [actualComplexZsDysonPolynomialCoefficient,
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using! hp

/-- The preceding all-order recurrence regularity applies to every actual
physical L² field on the doubled interval. -/
theorem continuousOn_actualPhysicalL2ZsDysonPolynomialCoefficient
    (u : PhysicalL2) (n k : ℕ) (i j : Fin 2) :
    ContinuousOn
      (fun t => actualComplexZsDysonPolynomialCoefficient
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        n k t i j) (Set.Icc (0 : ℝ) 2) := by
  apply continuousOn_actualComplexZsDysonPolynomialCoefficient_of_L1
  intro a b
  exact actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u 0 a b

/-- The genuine coefficient recurrence is integrable on each source
subinterval. This justifies exchanging its finite sum and integral. -/
theorem intervalIntegrable_actualComplexZsDysonCoefficientRecurrence_of_L1
    (U : ℝ → ℂ)
    (hA : ∀ i l : Fin 2, IntervalIntegrable
      (fun s => zsCoefficientComplex U 0 s i l) volume 0 2)
    (n k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) (i j : Fin 2) :
    IntervalIntegrable
      (fun s => ∑ l : Fin 2,
        (zsCoefficientComplex U 0 s i l *
          actualComplexZsDysonPolynomialCoefficient U n k s l j +
        if k = 0 then 0 else zsComplexSpectralSlope i l *
          actualComplexZsDysonPolynomialCoefficient U n (k - 1) s l j))
      volume 0 t := by
  apply (recurrence_integrable_from_lower_coefficient_continuity U hA n k i j
    (continuousOn_actualComplexZsDysonPolynomialCoefficient_of_L1 U hA n)).mono_set
  rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  exact fun s hs => ⟨hs.1, hs.2.trans ht.2⟩

end NlsGge.SpectralFoundations
end
