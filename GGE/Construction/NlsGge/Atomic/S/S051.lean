import Mathlib
import NlsGge.Spectral.ReservedEnergyCoercivity38V1

                                                                                                                                                    
                                                                                                                                             
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Schur
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem reservedEnergy_coercive (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ g R₀ : ℝ, 0 < g ∧ 1 ≤ R₀ ∧
      ∀ (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) (R : ℝ),
        R₀ ≤ R → R ≤ planeH1Norm38 N z →
        g * Real.exp (g * R ^ (1 / 4 : ℝ)) ≤ reservedEnergy38 c N z :=
  reservedEnergy_coercive38 lo up hl hlu

end NlsGge.ThirdConsultation.S

end
