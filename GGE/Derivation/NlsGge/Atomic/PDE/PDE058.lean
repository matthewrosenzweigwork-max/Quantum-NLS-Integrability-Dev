import Mathlib
import NlsGge.Atomic.PDE.PDE057
import NlsGge.ThirdConsultation.PDE.PDE058SupA
import NlsGge.ThirdConsultation.PDE.PDE058SupB
import NlsGge.ThirdConsultation.Common.FiniteSupport

/- PDE058 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/PDE/PDE058.lean, namespace
   NlsGge.ThirdConsultation.PDE. PDE-058: transport the physical vector field through compatible Sobolev Birkhoff maps.
   Head VERBATIM from Pro round 14 ('### PDE-058'; round 15 prints no new head).
   Opens: Pro's prelude minus NlsGge.GK38 (unused) plus  (FiniteSupportSequence is
   a COMMON name; without this open the head's unqualified name does not resolve from namespace ...PDE).
   UNLANDED IMPORTS (host/support candidates in this folder): Round14Deriv (DPhi, DPhiinv, omegaSeq; via SupB),
   PDE058SupGen/SupA/SupB, Common.FiniteSupport (FiniteSupportSequence).
   Route: with p = physicalCoreBase u, X = nlsVectorField u, w = DPhiinv 1 (Φ p) v:
     v = DPhi 1 p w                                   (SupB DPhi_DPhiinv: G6027 inverse laws + analyticity)
     omegaSeq (DPhi X) (DPhi w) = omegaPhys38 (X) (w)  (SupB DPhi_one_symplectic: level-1 canonicity)
     = D(H/2)(p) w                                     (landed PDE-057)
     = D(H̃/2)(Φ p) v                                   (SupB transformedHam_fderiv + SupA differentiability).
   hv (finite support of the test direction) is part of Pro's head and is not needed by this argument. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_nls_coordinate_pairing
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ))
    (v : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hv : FiniteSupportSequence (sequenceSobolevEmbed 1 v)) :
  omegaSeq
    (carrierCoe38 ((1 : ℕ) : ℝ)
      (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
    (carrierCoe38 ((1 : ℕ) : ℝ) v) =
  fderiv ℝ (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
    NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2)
    (birkhoffSobolev 1 (physicalCoreBase u)) v := by
  have hd := nlsHamiltonian_half_differentiableAt_core u
  have hv' := DPhi_DPhiinv (physicalCoreBase u) v
  calc omegaSeq (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
        (carrierCoe38 ((1 : ℕ) : ℝ) v)
      = omegaSeq (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u) (nlsVectorField u)))
          (carrierCoe38 ((1 : ℕ) : ℝ) (DPhi 1 (physicalCoreBase u)
            (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v))) := by rw [hv']
    _ = omegaPhys38 (physicalSobolevEmbed 1 (nlsVectorField u))
          (physicalSobolevEmbed 1 (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v)) :=
        DPhi_one_symplectic _ _ _
    _ = fderiv ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
          NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (physicalCoreBase u)
          (DPhiinv 1 (birkhoffSobolev 1 (physicalCoreBase u)) v) :=
        actual_nls_hamiltonian_normalization u _
    _ = fderiv ℝ (fun z : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
          NlsGge.GKDefinitionDesign.transformedNLSHamiltonian z / 2)
          (birkhoffSobolev 1 (physicalCoreBase u)) v :=
        (transformedHam_fderiv _ v hd).symm

end NlsGge.ThirdConsultation.PDE
