import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G6.Energy031A
import NlsGge.ThirdConsultation.G6.Energy031B
import NlsGge.ThirdConsultation.G6.Energy031C
import NlsGge.ThirdConsultation.G6.Energy031D
import NlsGge.ThirdConsultation.G6.Round5

/- G6-031 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G6/G6031.lean, namespace NlsGge.GKDefinitionDesign
   (as the G6 host). Head verbatim from PRO_DEFINITION_RESPONSE_FP80_05.md section 10 with the lexical repair
   `PhysicalSobolev38 (1 : ℝ)` -> `PhysicalSobolev38 ((1 : ℕ) : ℝ)`. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.GKDefinitionDesign

theorem G6031 :
  AnalyticOnNhd ℝ nlsHamiltonian Set.univ ∧
  ∀ u : PhysicalSobolev38 ((1 : ℕ) : ℝ),
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 *
      ‖fourierSeq38 (physicalSobolevEmbed 1 u) n‖ ^ 2) ∧
    Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      reflectedFourierL2 (physicalSobolevEmbed 1 u) n) 2 ∧
    Integrable (fun x : PhysicalCircle =>
      ‖weakDerivative (physicalSobolevEmbed 1 u) x‖ ^ 2 +
      ‖physicalSobolevEmbed 1 u x‖ ^ 4) spatialMeasure ∧
    Integrable (fun x : PhysicalCircle =>
      ‖physicalSobolevEmbed 1 u x‖ ^ 4) spatialMeasure ∧
    nlsHamiltonian u = ∫ x : PhysicalCircle,
      (‖weakDerivative (physicalSobolevEmbed 1 u) x‖ ^ 2 +
       ‖physicalSobolevEmbed 1 u x‖ ^ 4) ∂spatialMeasure := by
  refine ⟨?_, fun u => ⟨energy_quad_summable u,
    weakDerivative_domain_of_H1 _ (embed1_physicalSobolev u),
    (energy_deriv_integrable u).add (energy_quartic_integrable u),
    energy_quartic_integrable u, ?_⟩⟩
  · have hfun : nlsHamiltonian = fun u : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
        ‖physicalSobolevDerivative38 1 u‖ ^ 2 +
          ∫ x : PhysicalCircle, ‖iotaCLM u x‖ ^ 4 ∂spatialMeasure := by
      funext u
      unfold nlsHamiltonian
      rw [energy_quad_eq, energy_quartic_eq]
    rw [hfun]
    exact analytic_quad.add analytic_quart
  · unfold nlsHamiltonian
    rw [integral_add (energy_deriv_integrable u) (energy_quartic_integrable u),
      integral_norm_sq_eq_norm_sq, weakDerivative_physicalSobolevEmbed, energy_quad_eq]

end NlsGge.GKDefinitionDesign
end
