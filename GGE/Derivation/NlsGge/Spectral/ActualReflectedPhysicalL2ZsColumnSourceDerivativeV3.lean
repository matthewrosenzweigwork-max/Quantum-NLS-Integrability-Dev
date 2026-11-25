import NlsGge.Spectral.ActualReflectedPhysicalL2ZsColumnV3
import NlsGge.Spectral.ActualContinuousReflectedDiracDerivativeClassV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual original (-u,-z) column realizes the actual reflected source
derivative representatives. The AE negative-potential and conjugate-slice
bridges are proved class identities; no pointwise rough representative is
assumed and no weighted graph-domain conclusion is a hypothesis. -/
theorem actualReflectedPhysicalL2ZsColumn_ae_actual_source_derivative
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (b : Bool) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt
        (fun s => actualReflectedPhysicalL2ZsColumn u z v s (if b then 0 else 1))
        (actualContinuousReflectedDiracDerivativeRepresentative u z
          (fun s => actualReflectedPhysicalL2ZsColumn u z v s 0)
          (fun s => actualReflectedPhysicalL2ZsColumn u z v s 1) b t) t := by
  let C := actualReflectedPhysicalL2ZsColumn u z v
  have hn : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0 : ℝ) 1 →
      naturalPhysicalCoverL2 (-u) (t : SpectralCircle) =
        -actualPhysicalL2SourcePotential u t :=
    (ae_restrict_iff' measurableSet_Ioc).mp (naturalPhysicalCoverL2_neg_source_ae u)
  have hs : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0 : ℝ) 1 →
      actualPhysicalL2SourcePotential (star u) t =
        star (actualPhysicalL2SourcePotential u t) :=
    (ae_restrict_iff' measurableSet_Ioc).mp
      (actualPhysicalL2SourcePotential_star_ae u (star u) rfl)
  have hzero : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  cases b
  · filter_upwards [actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt u z v 1,
      hn, hs, hzero] with t hd hnt hst ht0
    intro ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
    have ha : (zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ C t) 1 =
        Complex.I * (actualPhysicalL2SourcePotential (star u) t * C t 0 - z * C t 1) := by
      simp only [zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      change (-Complex.I * star (naturalPhysicalCoverL2 (-u) (t : SpectralCircle))) * C t 0 +
        (Complex.I * (-z)) * C t 1 = _
      rw [hnt hti, hst hti]
      simp only [star_neg]
      ring
    have hdt := hd ht
    change HasDerivAt (fun s => C s 1) _ t at hdt
    rw [ha] at hdt
    exact hdt
  · filter_upwards [actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt u z v 0,
      hn, hzero] with t hd hnt ht0
    intro ht
    have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
    have ha : (zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ C t) 0 =
        Complex.I * (z * C t 0 - actualPhysicalL2SourcePotential u t * C t 1) := by
      simp only [zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      change (-Complex.I * (-z)) * C t 0 +
        (Complex.I * naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) * C t 1 = _
      rw [hnt hti]
      ring
    have hdt := hd ht
    change HasDerivAt (fun s => C s 0) _ t at hdt
    rw [ha] at hdt
    exact hdt

end NlsGge.SpectralFoundations
end
