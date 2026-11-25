import NlsGge.Spectral.ActualPhysicalZsSignFlipColumnV3
import NlsGge.Spectral.ActualReflectedUnitTraceIffSourceEigenvectorV2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open NlsGge.Schur.TransportBridgeV4

/-- The actual rough unit-period fundamental trace is unchanged by
negating the potential at the SAME original spectral parameter. This is
proved by constant conjugacy and actual AC uniqueness, not inferred from
reality of the trace. -/
theorem actualPhysicalL2ZsUnitTrace_neg_potential
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Matrix.trace (actualComplexZsDysonTsum
      (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t) =
    Matrix.trace (actualComplexZsDysonTsum
      (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t) := by
  have h0 := congrArg (fun w : Fin 2 → ℂ => w 0)
    (actualPhysicalZsSignFlipColumn_eq u z ![1, 0] t ht)
  have h1 := congrArg (fun w : Fin 2 → ℂ => w 1)
    (actualPhysicalZsSignFlipColumn_eq u z ![0, 1] t ht)
  have hd0 : actualComplexZsDysonTsum
      (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t 0 0 =
      actualComplexZsDysonTsum
        (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t 0 0 := by
    simpa [actualReflectedPhysicalL2ZsColumn, actualPhysicalZsSignFlipVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  have hd1 : actualComplexZsDysonTsum
      (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t 1 1 =
      actualComplexZsDysonTsum
        (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t 1 1 := by
    apply neg_inj.mp
    simpa [actualReflectedPhysicalL2ZsColumn, actualPhysicalZsSignFlipVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  simp only [Matrix.trace_fin_two, hd0, hd1]

/-- The original physical trace at z corresponds to an actual source
Dirac eigenvector at -z. The spectral reflection is explicit; labels,
gaps, compactness and actions are not asserted by this correspondence. -/
theorem actualOriginalPhysicalL2UnitTrace_iff_source_eigenvector
    (n : ℤ) (u : PhysicalL2) (z : ℂ) :
    Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)) z 1) =
      2 * spectralSign n ↔
    ∃ X : recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X = (-z) • X.val := by
  have h := actualReflectedPhysicalL2UnitTrace_iff_source_eigenvector n u (-z)
  simp only [neg_neg] at h
  rw [actualPhysicalL2ZsUnitTrace_neg_potential u z 1 (by norm_num)] at h
  exact h

end NlsGge.SpectralFoundations
end
