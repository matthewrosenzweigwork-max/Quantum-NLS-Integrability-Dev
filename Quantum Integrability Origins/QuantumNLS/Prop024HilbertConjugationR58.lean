import QuantumNLS.Prop024ContractionsR54

/-! Round 58: Hilbert-space conjugation of the actual physical interaction.

This module uses only the unitary property of `physicalWeyl`.  For a vector
whose translated state is in the exact maximal interaction domain, it proves
the full Fock-space identity after pulling the interaction back by the inverse
Weyl unitary.  It makes no claim that the pulled-back vector has the source
constant, linear, quadratic, or Wick-cell formulas; those are left to the
explicit step-one input in the assembly module. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop024HilbertConjugationR58

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The actual interaction applied to a translated vector and pulled back
to the undisplaced Fock space.  The domain witness is part of the definition. -/
def pulledInteraction (N : ℕ) (u : L2T L)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (x : Fock L)
    (hx : physicalWeyl N u x ∈ (interaction N B).domain) : Fock L :=
  (physicalWeyl N u).symm
    ((interaction N B) ⟨physicalWeyl N u x, hx⟩)

/-- Unitary pullback is an exact Hilbert-space conjugation identity on the
maximal interaction domain. -/
theorem interaction_eq_physicalWeyl_pulled (N : ℕ) (u : L2T L)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (x : Fock L)
    (hx : physicalWeyl N u x ∈ (interaction N B).domain) :
    (interaction N B) ⟨physicalWeyl N u x, hx⟩ =
      physicalWeyl N u (pulledInteraction N u B x hx) := by
  simp [pulledInteraction]

/-- The pulled-back interaction vector has exactly the same Hilbert norm
as the physical interaction output. -/
theorem norm_pulledInteraction (N : ℕ) (u : L2T L)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (x : Fock L)
    (hx : physicalWeyl N u x ∈ (interaction N B).domain) :
    ‖pulledInteraction N u B x hx‖ =
      ‖(interaction N B) ⟨physicalWeyl N u x, hx⟩‖ := by
  change ‖(physicalWeyl N u).symm
      ((interaction N B) ⟨physicalWeyl N u x, hx⟩)‖ = _
  exact (physicalWeyl N u).symm.norm_map
    ((interaction N B) ⟨physicalWeyl N u x, hx⟩)

/-- If the pulled-back interaction is identified with four specified Fock
vectors, the identity transports that equality back to the physical Fock
space.  The identity hypothesis is intentionally explicit and is not proved
from a Weyl/interaction compatibility assumption here. -/
theorem interaction_eq_physicalWeyl_of_pulled_identification
    (N : ℕ) (u : L2T L) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (x : Fock L) (hx : physicalWeyl N u x ∈ (interaction N B).domain)
    (constant : ℂ) (linearTerm quadraticTerm remainderTerm : Fock L)
    (hIdentification : pulledInteraction N u B x hx =
      constant • x + linearTerm + quadraticTerm + remainderTerm) :
    (interaction N B) ⟨physicalWeyl N u x, hx⟩ =
      physicalWeyl N u
        (constant • x + linearTerm + quadraticTerm + remainderTerm) := by
  rw [interaction_eq_physicalWeyl_pulled]
  exact congrArg (physicalWeyl N u) hIdentification

end QuantumNLS.Prop024HilbertConjugationR58

#print axioms QuantumNLS.Prop024HilbertConjugationR58.pulledInteraction
#print axioms QuantumNLS.Prop024HilbertConjugationR58.interaction_eq_physicalWeyl_pulled
#print axioms QuantumNLS.Prop024HilbertConjugationR58.norm_pulledInteraction
#print axioms QuantumNLS.Prop024HilbertConjugationR58.interaction_eq_physicalWeyl_of_pulled_identification

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024HilbertConjugationR58." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024HilbertConjugationR58." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any
          (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R58 Hilbert conjugation audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
