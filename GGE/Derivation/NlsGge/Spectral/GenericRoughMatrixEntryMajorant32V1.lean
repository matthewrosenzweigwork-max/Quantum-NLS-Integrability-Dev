import NlsGge.Spectral.GenericRoughMatrixDysonIntegralEquation32V1
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- The concrete sum of the FOUR actual coefficient entry norms. This is a
realized L¹ majorant, not an assumption about a target solution. -/
def genericRoughMatrixEntryMajorant32 (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : ℝ :=
  ‖B t 0 0‖ + ‖B t 0 1‖ + ‖B t 1 0‖ + ‖B t 1 1‖

theorem genericRoughMatrixEntryMajorant_nonneg32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    0 ≤ genericRoughMatrixEntryMajorant32 B t := by
  unfold genericRoughMatrixEntryMajorant32
  positivity

theorem genericRoughMatrixEntrySup_le_majorant32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    actualComplexMatrixEntrySup (B t) ≤ genericRoughMatrixEntryMajorant32 B t := by
  unfold actualComplexMatrixEntrySup genericRoughMatrixEntryMajorant32
  apply max_le <;> apply max_le
  all_goals linarith [norm_nonneg (B t 0 0), norm_nonneg (B t 0 1),
    norm_nonneg (B t 1 0), norm_nonneg (B t 1 1)]

theorem intervalIntegrable_genericRoughMatrixEntryMajorant32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T) :
    IntervalIntegrable (genericRoughMatrixEntryMajorant32 B) volume 0 T :=
  (((hB 0 0).norm.add (hB 0 1).norm).add (hB 1 0).norm).add (hB 1 1).norm

/-- Every entrywise L¹ coefficient has its actual constructed Dyson series
continuous on [0,T] and satisfying the true integral equation there. The
majorant is explicitly constructed above, so none is added to the input. -/
theorem genericRoughMatrixDysonTsum_wellPosed32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 T) :
    (∀ i j, ContinuousOn (fun t => genericRoughMatrixDysonTsum32 B t i j) (Set.Icc (0 : ℝ) T)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j,
      genericRoughMatrixDysonTsum32 B t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTsum32 B s) i j) := by
  let q := genericRoughMatrixEntryMajorant32 B
  have hq := intervalIntegrable_genericRoughMatrixEntryMajorant32 B T hB
  have hp := genericRoughMatrixEntryMajorant_nonneg32 B
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) T, actualComplexMatrixEntrySup (B s) ≤ q s :=
    fun s _ => genericRoughMatrixEntrySup_le_majorant32 B s
  exact ⟨fun i j => continuousOn_genericRoughMatrixDysonTsum32 B q T hT hB hq hp hm i j,
    fun t ht i j => genericRoughMatrixDysonTsum_integral_equation32 B q T hT hB hq hp hm t ht i j⟩

end NlsGge.SpectralFoundations
end
