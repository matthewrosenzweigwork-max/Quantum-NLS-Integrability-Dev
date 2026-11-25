import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPS.KSPS007Host

/- KSPS-011 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Host.lean.
   Bodies copied VERBATIM from Pro round 13 section 4 (PRO_DEFINITION_RESPONSE_FP80_13.md, "KSPS-011 -- use the
   full forced-system endpoint remainders"). grep of NlsGge/ found none of: sourceFundamental, sourceForcingVector,
   sourceRemainderVector, endpointRemainderLower/Upper, KSPS.indexValue, KSPS.SquareSummable. -/
set_option autoImplicit false
open MeasureTheory Matrix
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
attribute [local instance] Classical.propDecidable

-- This is the same actual Picard fundamental matrix as the landed Round5
-- construction, with the generic-N physical pair passed to its native term.
def sourceFundamental {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (x : ℝ) (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑' k : ℕ,
    NlsGge.ThirdConsultation.KSPS.volterraTerm k x lam φ i j

def sourceForcingVector {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (t : ℝ) : Fin 2 → ℂ :=
  if b then
    ![Complex.exp (Complex.I * lam.1 * (t : ℂ)) *
        NlsGge.ThirdConsultation.KSPSRiccati.forcing φ true lam.1 t, 0]
  else
    ![0, Complex.exp (-(Complex.I * lam.1 * (t : ℂ))) *
        NlsGge.ThirdConsultation.KSPSRiccati.forcing φ false lam.1 t]

def sourceRemainderVector {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (x : ℝ) : Fin 2 → ℂ :=
  -NlsGge.ThirdConsultation.KSPSVolterra.integrateVector 0 x
    (fun t =>
      (sourceFundamental φ x lam.1 *
        NlsGge.ThirdConsultation.KSPSVolterra.adjugate2
          (sourceFundamental φ t lam.1)) *ᵥ
      (NlsGge.ThirdConsultation.KSPSVolterra.R *ᵥ
        sourceForcingVector φ b lam t))

-- Literal zero-filled sampling convention. This is not a source remainder
-- evaluation at λ=0 and does not assert a removable singularity there.
def endpointRemainderLower (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  if hz : xi n = 0 then 0 else
    sourceRemainderVector φ false ⟨xi n, hz⟩ 1 1

def endpointRemainderUpper (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (xi : ℤ → ℂ) (n : ℤ) : ℂ :=
  if hz : xi n = 0 then 0 else
    (-1 : ℂ) ^ N * sourceRemainderVector φ true ⟨xi n, hz⟩ 1 0

end
end NlsGge.ThirdConsultation.KSPSWKB

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def indexValue : ℤ → ℝ := indexWeight

def SquareSummable (e : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => ‖e n‖ ^ 2)

end
end NlsGge.ThirdConsultation.KSPS
