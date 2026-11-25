import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS006Host

/- KSPS-018 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS018Host.lean.
   PROPOSED BODY, NOT FROM PRO. The head of KSPS-018 (STATEMENTS/KSPS.md, followup9, unchanged since round 1; no
   Pro round 5-11 text touches KSPS-018) mentions `NlsGge.ThirdConsultation.KSPSWKB.supMatrixDerivativeError`, but
   NO round (DEFINITIONS KSPS.lean.md, rounds 1-11) supplies a body; DEFGAP_OBJECTS01 lists it as an undefined
   draft name. The body below transcribes the packet contract
   "sup_{x in [0,1]} ||d_lam^j M - d_lam^j E||" literally: M = KSPSVolterra.fundamental (the Picard sum), E = freePropagator
   (the free propagator used by KSPS-005/006), d_lam^j = iteratedDeriv j in the complex spectral parameter, norm = the
   operator L2 norm on 2x2 matrices (the norm of KSPS-005/006), sup over the closed unit interval as a real iSup.
   Totalization: `iteratedDeriv` and the real `iSup` are totalized; the companion theorems in KSPS018 prove genuine
   differentiability (analyticity in lam) and boundedness of the family, so neither default value is ever used. -/
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section

def supMatrixDerivativeError (j : Fin 3) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1) (lam : ℂ) : ℝ :=
  ⨆ x : Set.Icc (0 : ℝ) 1,
    ‖iteratedDeriv (j : ℕ)
        (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ (x : ℝ) l) lam -
      iteratedDeriv (j : ℕ)
        (fun l : ℂ => NlsGge.ThirdConsultation.KSPS.freePropagator (x : ℝ) l) lam‖

end
end NlsGge.ThirdConsultation.KSPSWKB
