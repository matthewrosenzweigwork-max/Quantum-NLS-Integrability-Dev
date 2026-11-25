import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G6.Energy031A
import NlsGge.ThirdConsultation.G6.Energy031B

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.GKDefinitionDesign

theorem embed1_ae_iota (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    ∀ᵐ x ∂spatialMeasure, (physicalSobolevEmbed 1 u : PhysicalCircle → ℂ) x = iotaCLM u x := by
  have := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure (iotaCLM u)
  rw [iotaCLM_apply, physicalSobolevContinuous38_toLp] at this
  exact this

theorem energy_quartic_eq (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    ∫ x : PhysicalCircle, ‖physicalSobolevEmbed 1 u x‖ ^ 4 ∂spatialMeasure =
      ∫ x : PhysicalCircle, ‖iotaCLM u x‖ ^ 4 ∂spatialMeasure := by
  apply integral_congr_ae
  filter_upwards [embed1_ae_iota u] with x hx
  rw [hx]

theorem energy_quartic_integrable (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    Integrable (fun x : PhysicalCircle => ‖physicalSobolevEmbed 1 u x‖ ^ 4) spatialMeasure := by
  have hc : Continuous (fun x : PhysicalCircle => ‖iotaCLM u x‖ ^ 4) := by fun_prop
  have hi : Integrable (fun x : PhysicalCircle => ‖iotaCLM u x‖ ^ 4) spatialMeasure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine hi.congr ?_
  filter_upwards [embed1_ae_iota u] with x hx
  rw [hx]

theorem energy_deriv_integrable (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    Integrable (fun x : PhysicalCircle => ‖weakDerivative (physicalSobolevEmbed 1 u) x‖ ^ 2)
      spatialMeasure := by
  have h := (Lp.memLp (weakDerivative (physicalSobolevEmbed 1 u))).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simpa using h

end NlsGge.GKDefinitionDesign
end
