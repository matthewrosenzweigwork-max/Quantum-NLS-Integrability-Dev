import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

/- KSPS-007 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Host.lean.
   The nine bodies are copied from Pro round 5 "Concrete repair of KSPS-007 and all direct hosts"
   (PRO_DEFINITION_RESPONSE_FP80_05.md ~line 1630) == DEFINITIONS/KSPS.lean.md (followup9) "Forced equation and
   source correction hosts" (identical in rounds 5-11); they are absent from NlsGge/ (grep). Header opens are those of
   Round5 (names Vec, R, E, phi, term, toPair, integrateVector, integratedQuadratic, potRepFst38 ...) plus `open Matrix`
   for the notation `*ᵥ`. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open Matrix
noncomputable section

namespace NlsGge.ThirdConsultation.KSPSVolterra

def forcingValue (f : PotPair) (t : ℝ) : Vec :=
  ![potRepFst38 f t, potRepSnd38 f t]

def vectorL2Norm (f : PotPair) : ℝ := Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2)

def ForcedZS (φ : SobolevC 1) (lam : ℂ) (f : PotPair)
    (F : ℝ → Vec) : Prop :=
  ContinuousOn F (Set.Icc (0 : ℝ) 1) ∧ F 0 = 0 ∧
    ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      F x = integrateVector 0 x (fun t =>
        ((-(lam • R) + R * phi (toPair φ) t) *ᵥ F t) -
          R *ᵥ forcingValue f t)

def forcingLeading (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (x : ℝ) : Vec :=
  -integrateVector 0 x (fun t => R *ᵥ (E lam (x-t) *ᵥ forcingValue f t))

def forcingB1 (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (x : ℝ) : Vec :=
  -(2 * lam) • (term 1 x lam (toPair φ) *ᵥ
    (R *ᵥ integrateVector 0 x (fun t => E lam (-t) *ᵥ forcingValue f t)))

def forcingB2 (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (x : ℝ) : Vec :=
  integratedQuadratic φ x *ᵥ
    integrateVector 0 x (fun t => E lam (x-t) *ᵥ forcingValue f t)

def forcingB3 (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (x : ℝ) : Vec :=
  E lam x *ᵥ integrateVector 0 x (fun t =>
    (2 * lam) • (term 1 t lam (toPair φ) *ᵥ (R *ᵥ forcingValue f t)))

def forcingB4 (φ : SobolevC 1) (lam : ℂ) (f : PotPair) (x : ℝ) : Vec :=
  -integrateVector 0 x (fun t =>
    E lam (x-t) *ᵥ (integratedQuadratic φ t *ᵥ forcingValue f t))

def forcingFirstCorrection (φ : SobolevC 1) (lam : ℂ) (f : PotPair)
    (x : ℝ) : Vec :=
  (2 * lam)⁻¹ • (forcingB1 φ lam f x + forcingB2 φ lam f x +
    forcingB3 φ lam f x + forcingB4 φ lam f x)

end NlsGge.ThirdConsultation.KSPSVolterra
