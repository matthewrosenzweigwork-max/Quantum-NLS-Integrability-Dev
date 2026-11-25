import NlsGge.Spectral.ActualPhysicalInteractionCouplingContinuity36V2
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- Recover continuity of the ACTUAL ungauged Dyson entries from the proved
interaction continuity and the actual nonzero free diagonal gauge. -/
theorem actualPhysicalDysonEntry_coupling_continuousOn36V2
    (u : PhysicalL2) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ContinuousOn (fun τ : ℝ => actualComplexZsDysonTsum
      (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z t i j)
      (Set.Icc (0 : ℝ) 1) := by
  have hG := actualPhysicalInteractionDyson_coupling_continuousOn36V2
    u z Y₀ hY₀ hY hY' t ht i j
  have hW := actualZsInverseFreeWeight_ne_zero32 z t i
  have heq (τ : ℝ) : actualComplexZsDysonTsum
      (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z t i j =
      genericRoughMatrixDysonTsum32
        (actualZsInteractionCoefficient32
          (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z) t i j /
        actualZsInverseFreeWeight32 z t i := by
    have hident := actualPhysicalInteractionState_eq_Dyson32 ((τ : ℂ) • u) z t
      ⟨ht.1, ht.2.trans (by norm_num)⟩
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hident
    apply (eq_div_iff hW).2
    simpa only [actualZsInteractionState32, mul_comm] using he
  exact (hG.div_const (actualZsInverseFreeWeight32 z t i)).congr (fun τ hτ => heq τ)
/-- The accepted unit-period half trace is continuous on the actual real
potential-coupling path, with the manuscript factor one-half preserved. -/
theorem actualPhysicalUnitHalfTrace_coupling_continuousOn36V2
    (u : PhysicalL2) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀) :
    ContinuousOn (fun τ : ℝ => actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z)
      (Set.Icc (0 : ℝ) 1) := by
  have h00 := actualPhysicalDysonEntry_coupling_continuousOn36V2
    u z Y₀ hY₀ hY hY' 1 (by norm_num) 0 0
  have h11 := actualPhysicalDysonEntry_coupling_continuousOn36V2
    u z Y₀ hY₀ hY hY' 1 (by norm_num) 1 1
  simpa only [actualPhysicalUnitHalfTrace32, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Pi.add_apply] using (h00.add h11).div_const (2 : ℂ)
end NlsGge.SpectralFoundations
end
