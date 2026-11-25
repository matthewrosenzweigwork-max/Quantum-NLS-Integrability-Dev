import NlsGge.Spectral.ActualPhysicalL2ZsDysonAEODEV2
import NlsGge.Schur.SourceIntervalL2FromActualContinuousOnV2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The original fundamental solution at (-u,-z), required by the reflected
Dirac convention. This definition does not change the original coefficient. -/
def actualReflectedPhysicalL2ZsColumn (u : PhysicalL2) (z : ℂ)
    (v : Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ :=
  actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 (-u) : SpectralCircle → ℂ) (x : SpectralCircle))
    (-z) t *ᵥ v

theorem continuousOn_actualReflectedPhysicalL2ZsColumn
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (i : Fin 2) :
    ContinuousOn (fun t => actualReflectedPhysicalL2ZsColumn u z v t i)
      (Set.Icc (0 : ℝ) 1) := by
  have hc (j : Fin 2) :=
    (continuousOn_actualPhysicalL2ZsDysonTsum_entry (-u) (-z) i j).mono
      (by intro t ht; exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩ :
        Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 2)
  simpa only [actualReflectedPhysicalL2ZsColumn, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.add_apply, Pi.mul_apply] using!
    ((hc 0).mul continuousOn_const).add ((hc 1).mul continuousOn_const)

theorem absolutelyContinuous_actualReflectedPhysicalL2ZsColumn
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (i : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun t => actualReflectedPhysicalL2ZsColumn u z v t i) 0 1 := by
  have hc (j : Fin 2) :=
    (absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry (-u) (-z) i j).mono
      (by simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
          intro t ht; exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩ :
        Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 2)
  simpa only [actualReflectedPhysicalL2ZsColumn, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.add_apply, smul_eq_mul, mul_comm] using!
    (hc 0 |>.const_smul (v 0)).add (hc 1 |>.const_smul (v 1))

theorem actualReflectedPhysicalL2ZsColumn_initial
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    actualReflectedPhysicalL2ZsColumn u z v 0 = v := by
  have h : actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 (-u) : SpectralCircle → ℂ) (x : SpectralCircle))
      (-z) 0 = 1 := by
    ext i j
    exact actualPhysicalL2ZsDysonTsum_initial_entry (-u) (-z) i j
  rw [actualReflectedPhysicalL2ZsColumn, h, Matrix.one_mulVec]

/-- The actual column has its actual original (-u,-z) coefficient derivative
almost everywhere. Reflection to D+V_u uses a separate AE representative bridge. -/
theorem actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (i : Fin 2) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => actualReflectedPhysicalL2ZsColumn u z v s i)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 (-u) : SpectralCircle → ℂ) (x : SpectralCircle))
          (-z) t *ᵥ actualReflectedPhysicalL2ZsColumn u z v t) i) t := by
  filter_upwards [actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry (-u) (-z) i 0,
    actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry (-u) (-z) i 1] with t h0 h1
  intro ht
  have ht2 : t ∈ Set.uIcc (0 : ℝ) 2 := by
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩
  have hd := ((h0 ht2).mul_const (v 0)).add ((h1 ht2).mul_const (v 1))
  simp only [actualReflectedPhysicalL2ZsColumn]
  rw [Matrix.mulVec_mulVec]
  simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply] using! hd

end NlsGge.SpectralFoundations
end
