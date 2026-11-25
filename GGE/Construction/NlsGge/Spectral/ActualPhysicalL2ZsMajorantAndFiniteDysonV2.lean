import NlsGge.Spectral.ActualPhysicalL2ZsCoefficientAllEntriesIntegrableMinimumV1
import NlsGge.Spectral.ActualComplexZsFiniteDysonIteratesContinuousV9

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual nonnegative L¹ majorant for the rough physical coefficient. -/
def actualPhysicalL2ZsMajorant (u : PhysicalL2) (z : ℂ) (t : ℝ) : ℝ :=
  ‖z‖ + ‖(naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)‖

theorem actualPhysicalL2ZsMajorant_nonneg (u : PhysicalL2) (z : ℂ) (t : ℝ) :
    0 ≤ actualPhysicalL2ZsMajorant u z t := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem actualPhysicalL2ZsMajorant_intervalIntegrable (u : PhysicalL2) (z : ℂ) :
    IntervalIntegrable (actualPhysicalL2ZsMajorant u z) volume 0 2 := by
  exact intervalIntegrable_const.add
    (naturalPhysicalCoverL2_intervalIntegrable_doubled u).norm

theorem actualPhysicalL2ZsCoefficient_entrySup_le_majorant
    (u : PhysicalL2) (z : ℂ) (t : ℝ) :
    actualComplexMatrixEntrySup (actualPhysicalL2ZsCoefficient u z t) ≤
      actualPhysicalL2ZsMajorant u z t := by
  exact actualComplexZsCoefficient_entrySup_bound
    (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
    z t ‖z‖ ‖(naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)‖
    le_rfl le_rfl

/-- Every actual finite Dyson iterate for a physical L² input has continuous
entries on the doubled interval. Only the coefficient's proved L¹ realization
is used; this is not the infinite-series or fundamental-matrix theorem. -/
theorem continuousOn_actualPhysicalL2ZsDysonTerm_entry
    (u : PhysicalL2) (z : ℂ) (n : ℕ) (i j : Fin 2) :
    ContinuousOn (fun t => actualComplexZsDysonTerm
      (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      z n t i j) (Set.Icc (0 : ℝ) 2) := by
  let U : ℝ → ℂ := fun s =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)
  induction n generalizing i j with
  | zero =>
      simpa [actualComplexZsDysonTerm] using
        (continuousOn_const : ContinuousOn
          (fun _ : ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) (Set.Icc (0 : ℝ) 2))
  | succ n ih =>
      change ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j)
        (Set.Icc (0 : ℝ) 2)
      have hentryA (k : Fin 2) :
          IntervalIntegrable (fun s => zsCoefficientComplex U z s i k) volume 0 2 :=
        actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k
      have hB (k : Fin 2) :
          ContinuousOn (fun s => actualComplexZsDysonTerm U z n s k j)
            (Set.uIcc (0 : ℝ) 2) := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ih k j
      have hprod (k : Fin 2) := (hentryA k).mul_continuousOn (hB k)
      have hentry : IntervalIntegrable
          (fun s => (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j)
          volume 0 2 := by
        simpa only [Matrix.mul_apply, Fin.sum_univ_two] using (hprod 0).add (hprod 1)
      have hzero : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
        exact ⟨le_rfl, by norm_num⟩
      have hprimitive := intervalIntegral.continuousOn_primitive_interval'
        (μ := volume) hentry hzero
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hprimitive

end NlsGge.SpectralFoundations
end
