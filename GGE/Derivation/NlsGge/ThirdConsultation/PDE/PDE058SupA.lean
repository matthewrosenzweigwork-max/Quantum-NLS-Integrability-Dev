import Mathlib
import NlsGge.Atomic.PDE.PDE057

/- PDE058SUPA PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/PDE058SupA.lean, namespace NlsGge.ThirdConsultation.PDE. Supporting result (a) for PDE-058
   (no packet increment): H/2 is differentiable on H1 at physicalCoreBase u. The proof replicates the derivative steps of
   landed PDE057.lean l.37-55 (nlsHamiltonian_eq_hamH1, hamiltonian_derivative through the Fourier isometry), which proves
   HasFDerivAt internally but does not export it. Opens copied from PDE057. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
namespace NlsGge.ThirdConsultation.PDE

theorem nlsHamiltonian_half_differentiableAt_core (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) :
    DifferentiableAt ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (physicalCoreBase u) := by
  set x : HamiltonianCore38 := physicalCoreFourier u with hx
  set E := physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) with hE
  have hfun : (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) =
      fun q => (1 / 2 : ℝ) * hamH1 (E q) := by
    funext q
    rw [nlsHamiltonian_eq_hamH1]; ring
  have hb : E (physicalCoreBase u) = hamiltonianBase x := by
    simp [physicalCoreBase, hE, hx]
  have h1 : HasFDerivAt hamH1 (hamiltonianDifferential x) (E (physicalCoreBase u)) := by
    rw [hb]; exact hamiltonian_derivative x
  have h3 : HasFDerivAt (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) => (1 / 2 : ℝ) * hamH1 (E q))
      (((1 / 2 : ℝ) • hamiltonianDifferential x).comp
        (E.toContinuousLinearEquiv : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] _))
      (physicalCoreBase u) :=
    (h1.const_mul (1 / 2 : ℝ)).comp (physicalCoreBase u) E.toContinuousLinearEquiv.hasFDerivAt
  rw [hfun]
  exact h3.differentiableAt

end NlsGge.ThirdConsultation.PDE
