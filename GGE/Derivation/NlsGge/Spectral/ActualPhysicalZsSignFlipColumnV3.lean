import NlsGge.Spectral.ActualPhysicalZsSignFlipCoefficientV4
import NlsGge.Spectral.ActualReflectedPhysicalL2ZsColumnV3
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual original monodromy at the negated potential is conjugated
by the constant component sign flip. The spectral parameter is unchanged.
The existing reflected-column notation is unfolded only after applying its
proved actual AC and AE ODE properties. -/
theorem actualPhysicalZsSignFlipColumn_eq
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      actualReflectedPhysicalL2ZsColumn u (-z)
        (actualPhysicalZsSignFlipVector v) t =
      actualPhysicalZsSignFlipVector
        (actualReflectedPhysicalL2ZsColumn (-u) (-z) v t) := by
  let F : ℝ → Fin 2 → ℂ := fun t =>
    actualReflectedPhysicalL2ZsColumn u (-z)
      (actualPhysicalZsSignFlipVector v) t
  let C : ℝ → Fin 2 → ℂ := fun t =>
    actualReflectedPhysicalL2ZsColumn (-u) (-z) v t
  let G : ℝ → Fin 2 → ℂ := fun t => actualPhysicalZsSignFlipVector (C t)
  have hinit : F 0 = G 0 := by
    dsimp [F, G, C]
    rw [actualReflectedPhysicalL2ZsColumn_initial,
      actualReflectedPhysicalL2ZsColumn_initial]
  have hF (i : Fin 2) :
      AbsolutelyContinuousOnInterval (fun t => F t i) 0 1 :=
    absolutelyContinuous_actualReflectedPhysicalL2ZsColumn u (-z)
      (actualPhysicalZsSignFlipVector v) i
  have hG (i : Fin 2) :
      AbsolutelyContinuousOnInterval (fun t => G t i) 0 1 := by
    fin_cases i
    · simpa only [G, C, actualPhysicalZsSignFlipVector, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ']
        using! absolutelyContinuous_actualReflectedPhysicalL2ZsColumn (-u) (-z) v 0
    · simpa only [G, C, actualPhysicalZsSignFlipVector, Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ'] using!
        (absolutelyContinuous_actualReflectedPhysicalL2ZsColumn (-u) (-z) v 1).neg
  have hFODE (i : Fin 2) : ∀ᵐ t ∂volume,
      t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => F s i)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t *ᵥ F t) i) t := by
    simpa only [F, neg_neg] using
      actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt u (-z)
        (actualPhysicalZsSignFlipVector v) i
  have hGODE (i : Fin 2) : ∀ᵐ t ∂volume,
      t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => G s i)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t *ᵥ G t) i) t := by
    filter_upwards [actualPhysicalL2ZsCoefficient_ae_signFlip_allStates u z,
      actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt (-u) (-z) v 0,
      actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt (-u) (-z) v 1] with t he hd0 hd1
    intro ht
    have hc := he ht (C t)
    change HasDerivAt (fun s => actualPhysicalZsSignFlipVector (C s) i)
      ((zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) z t *ᵥ
          actualPhysicalZsSignFlipVector (C t)) i) t
    rw [hc]
    fin_cases i
    · simpa only [C, neg_neg, actualPhysicalZsSignFlipVector,
        Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ'] using! hd0 ht
    · simpa only [C, neg_neg, actualPhysicalZsSignFlipVector,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ'] using! (hd1 ht).neg
  exact actualPhysicalL2Zs_vector_AC_same_initial_unique (-u) z 1
    (by norm_num) F G hinit hF hG hFODE hGODE

end NlsGge.SpectralFoundations
end
