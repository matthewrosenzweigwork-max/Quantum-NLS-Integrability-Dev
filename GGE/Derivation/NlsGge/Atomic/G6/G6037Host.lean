import Mathlib

/- G6037 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6037Host.lean.
   Hosts ONCE the G6-037 design names, bodies byte-identical to followup13 DEFINITIONS/G6.lean.md:306-312, namespace
   NlsGge.GKDefinitionDesign: squareInactive, finiteCoordinateEvenOn.  grep NlsGge/ (2026-11-02): neither exists. -/
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Mixed head/tail squaring: only the specified inactive coordinates are squared. -/
def squareInactive {d : ℕ} (S : Finset (Fin d)) (x : Fin d → ℂ) : Fin d → ℂ :=
  fun j => if j ∈ S then (x j)^2 else x j

def finiteCoordinateEvenOn {d : ℕ} (f : (Fin d → ℂ) → ℂ)
    (S : Finset (Fin d)) (U : Set (Fin d → ℂ)) : Prop :=
  ∀ x ∈ U, ∀ j ∈ S, f (Function.update x j (-x j)) = f x

end
end NlsGge.GKDefinitionDesign
