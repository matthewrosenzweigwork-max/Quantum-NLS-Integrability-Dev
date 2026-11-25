import Mathlib
import NlsGge.ThirdConsultation.M.M053Host

/- M-016 SUPPORT `hierarchyCharge_lift`, PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   SUPPORT (no packet increment). Target NlsGge/Atomic/M/M016Lift.lean, namespace NlsGge.ThirdConsultation.M.
   Head `hierarchyCharge_lift` EXACT from Pro round 16 PRO_DEFINITION_RESPONSE_FP80_16.md §1.4 (L171-182; also the
   round-15 STOP statement).  Route = Pro §1.4 "direct definitional route": the landed M053Host body depends on φ only
   through toPotPair φ (the private jet applies the global weakDerivative iterator to the two PhysicalL2 components).
   `hierarchyCharge_eq_body` restates that body with the private jet written out; it is proved by `rfl` (definitional
   unfolding; no private name is referenced and M053Host is not edited).  Rewriting `h` then closes the lift. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section

theorem hierarchyCharge_eq_body {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : NlsGge.ThirdConsultation.MRiccati.HierarchyIndex N) :
    hierarchyCharge φ k =
      if k.1 = 1 then
        ∫ x in (0 : ℝ)..1,
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 x
      else
        ∫ x in (0 : ℝ)..1,
          NlsGge.GK38.coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
          NlsGge.HierarchyRiccati.Core.polynomialEvaluation
            (fun v : NlsGge.HierarchyRiccati.Core.Jet =>
              NlsGge.GK38.coverRep38
                ((NlsGge.GKDefinitionDesign.weakDerivative^[v.2])
                  (if v.1 then (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2
                   else (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1)) x)
            (NlsGge.HierarchyRiccati.Core.p k.1) := rfl

theorem hierarchyCharge_lift
    {N N' : ℕ} (φ : KSPS.SobolevC N) (φ' : KSPS.SobolevC N')
    (h : KSPS.toPotPair φ = KSPS.toPotPair φ')
    (k : ℕ) (hk : 1 ≤ k)
    (hkN : k ≤ N + 1) (hkN' : k ≤ N' + 1) :
    hierarchyCharge φ ⟨k, hk, hkN⟩ =
      hierarchyCharge φ' ⟨k, hk, hkN'⟩ := by
  rw [hierarchyCharge_eq_body, hierarchyCharge_eq_body, h]

end
end NlsGge.ThirdConsultation.M
