import NlsGge.Spectral.GenericRoughMatrixVolterraIdentification32V2
import NlsGge.Spectral.ActualPhysicalInteractionGaugeACVolterra32V3
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- For every ACTUAL rough physical L² potential and every complex spectral
parameter, the free-diagonal gauge of the original fundamental matrix equals
the constructed interaction Dyson series throughout the FULL doubled source
interval. Every regularity and coefficient hypothesis is realized below. No
termwise conjugation of the original raw A-iterates or assumed spectral
normalization is used. -/
theorem actualPhysicalInteractionState_eq_Dyson32
    (u : PhysicalL2) (z : ℂ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 2,
      actualZsInteractionState32 z
        (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t =
      genericRoughMatrixDysonTsum32
        (actualZsInteractionCoefficient32 (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t := by
  let U : ℝ → ℂ := fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)
  let B : ℝ → Matrix (Fin 2) (Fin 2) ℂ := actualZsInteractionCoefficient32 U z
  let G : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    actualZsInteractionState32 z (actualComplexZsDysonTsum U z)
  have hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 2 :=
    intervalIntegrable_actualPhysicalInteractionCoefficient32 u z
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) 2) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using
      (absolutelyContinuous_actualPhysicalInteractionState32 u z i j).continuousOn
  apply genericRoughMatrixVolterraSolution_eq_Dyson32 B 2 (by norm_num) hB G hG
  intro t ht i j
  apply actualPhysicalInteractionState_integral_equation32 u z t
  simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht

/-- The exact unit endpoint needed for the source discriminant is a
restriction of the proved FULL-interval interaction identification. This is
not a trace asymptotic, a branch sign choice or a gap-action identification. -/
theorem actualPhysicalInteractionState_unit_eq_Dyson32
    (u : PhysicalL2) (z : ℂ) :
    actualZsInteractionState32 z
      (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) 1 =
    genericRoughMatrixDysonTsum32
      (actualZsInteractionCoefficient32 (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) 1 :=
  actualPhysicalInteractionState_eq_Dyson32 u z 1 (by norm_num)

end NlsGge.SpectralFoundations
end
