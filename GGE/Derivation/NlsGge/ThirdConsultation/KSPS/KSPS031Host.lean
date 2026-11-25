import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host

/- KSPS-031 HOST (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). Intended target
   NlsGge/ThirdConsultation/KSPS/KSPS031Host.lean, module NlsGge.ThirdConsultation.KSPS.KSPS031Host.
   Bodies VERBATIM from Pro round 15 Q4 "Literal host bodies, unchanged from round 14"
   (PRO_DEFINITION_RESPONSE_FP80_15.md); identical to proof development KSPS031Host_HOST02.lean.txt.
   Imports the landed KSPS015Host (discriminant). No other definitions.
   REPAIR CANDIDATE (needs root/owner approval): the literal Pro text does not parse as intended in Lean 4 —
   binary `-` continues the `let w := … / 2` value across the newline, leaving the `let` without a body
   (worker lane e6047826-912e-4cea-b602-fa2b5a972fa1: "unexpected token 'def'; expected term").
   The ONLY change is a `;` terminating the `let` value; tokens, order and intended meaning
   (-i·halfNode j + log(w + sqrt(1+w²))) are unchanged. Mock lane add4e0d0-f760-446f-86a9-4233dd040c52 exit 0. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
open NlsGge.ThirdConsultation.KSPS

def halfNode (j : ℤ) : ℂ :=
  ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)

def NonresonantBranchDomain {N : ℕ} (φ : SobolevC N)
    (j : ℤ) (z : ℂ) : Prop :=
  ‖z - halfNode j‖ < Real.pi / 4 ∧
    ‖discriminant φ z / 2‖ < 1 / 2

def primitive (N : ℕ) (φ : SobolevC N)
    (p : {p : ℤ × ℂ // NonresonantBranchDomain φ p.1 p.2}) : ℂ :=
  let w := Complex.I * (-1 : ℂ) ^ p.1.1 *
    discriminant φ p.1.2 / 2;
  -Complex.I * halfNode p.1.1 +
    Complex.log (w + Complex.sqrt (1 + w ^ 2))

end
end NlsGge.ThirdConsultation.KSPSWKB
