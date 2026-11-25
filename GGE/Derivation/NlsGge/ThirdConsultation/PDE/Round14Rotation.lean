import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.PDE.PDE063Core

/- PDEROT HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/PDE/Round14Rotation.lean,
   namespace NlsGge.ThirdConsultation.PDE.  Hosts ONCE Pro r14 shared PDE block l.2738-2767 (PRO_DEFINITION_RESPONSE_FP80_14.md):
   rotationSequence, rotationDerivativeSequence, the two theorem obligations rotationSequence_finiteSupport /
   rotationDerivativeSequence_finiteSupport, rotationCurve, rotationDeriv.  Bodies VERBATIM.  (inverseRotationCurve /
   inverseRotationPhysical, l.2768-2776, are PDE-064's and are NOT hosted here.)  Prelude = Pro's r14 block prelude
   (l.2642-2649).  grep NlsGge/ (2026-11-02): none of these names exists; proof development's hosts (PDEACT, PDEACTRAW,
   PDEACTFREQ, COMMONFSS) do not declare them.
   ROOT LEXICAL REPAIR 22 (binder type): `Lib.L2Z` -> `NlsGge.GK38.Lib.L2Z` in the six binders (the r14 prelude does not
   open NlsGge.GK38; `NlsGge.Birkhoff.Lib.L2Z` does not exist).  No other change.
   Obligation proofs: generic PDE063Aux.rot_finite / rotDeriv_finite at ω n = actualOmega n (actions z0).
   MAIN-ONLY: imports proof development's Round14ActionFreq (actualOmega; G6041 closure; pending landing).
   Own imports: Mathlib, PDE/Round14ActionFreq (h782), Common/Actions (COMMONACT host), Common/FiniteSupport (landed),
   Birkhoff/BirkhoffAPI38 (carrierMk38, finiteSupport_mem_seqSobolev38), PDE/PDE063Core. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def rotationSequence (z0 : NlsGge.GK38.Lib.L2Z) (t : ℝ) : ℤ → ℂ :=
  fun n : ℤ =>
    Complex.exp (-Complex.I * ((t * actualOmega n (actions z0) : ℝ) : ℂ)) * z0 n

def rotationDerivativeSequence (z0 : NlsGge.GK38.Lib.L2Z) (t : ℝ) : ℤ → ℂ :=
  fun n : ℤ => -Complex.I * (actualOmega n (actions z0) : ℂ) *
    rotationSequence z0 t n

theorem rotationSequence_finiteSupport
    (z0 : NlsGge.GK38.Lib.L2Z) (hz : FiniteSupportSequence z0) (t : ℝ) :
  {n : ℤ | rotationSequence z0 t n ≠ 0}.Finite :=
  PDE063Aux.rot_finite (fun n => actualOmega n (actions z0)) z0 hz t

theorem rotationDerivativeSequence_finiteSupport
    (z0 : NlsGge.GK38.Lib.L2Z) (hz : FiniteSupportSequence z0) (t : ℝ) :
  {n : ℤ | rotationDerivativeSequence z0 t n ≠ 0}.Finite :=
  PDE063Aux.rotDeriv_finite (fun n => actualOmega n (actions z0)) z0 hz t

def rotationCurve (r : ℝ) (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : SobolevCarrier38 r :=
  carrierMk38 r (rotationSequence z0 t)
    (finiteSupport_mem_seqSobolev38 r _ (rotationSequence_finiteSupport z0 hz t))

def rotationDeriv (r : ℝ) (z0 : NlsGge.GK38.Lib.L2Z)
    (hz : FiniteSupportSequence z0) (t : ℝ) : SobolevCarrier38 r :=
  carrierMk38 r (rotationDerivativeSequence z0 t)
    (finiteSupport_mem_seqSobolev38 r _
      (rotationDerivativeSequence_finiteSupport z0 hz t))

end
end NlsGge.ThirdConsultation.PDE
