import QuantumNLS.Ext006StrongFieldR41a

/-! The original-row PHYSICAL unitary from R37a, now accompanied by the
strong field-power action of its inverse on an explicitly constructed dense
polynomial core. Its smearing orientation is the actual real adjoint S*.
No Weyl operator or unproved exponentiation conclusion is introduced. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PhysicalFieldR41a
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006SourceCCRR34a
open Ext006IdentityCyclicR35a Ext006CoreTransportR35a Ext006FockEmbeddingR35a
open Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a Ext006InverseSourceR36a
open Ext006SurjectivityR36a Ext006LiteralHeisR37a Ext006PhysQuasifree Ext006PhysFockCoord
open Ext006StrongFieldR41a Ext006CanonicalOrientationR38a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The same constructed physical unitary satisfies the frozen row identities,
has the frozen canonical vacuum up to phase, and has the displayed strong
inverse field action for every polynomial degree. Domains are supplied by
actual source polynomials. Exponentiation remains a separate obligation. -/
theorem source_actual_Heis_with_strong_field_powers
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
    ∃ v : D, ‖v.1‖=1 ∧ (∀ f, sourceAnn (physicalBasis L) (adjointSource S) f v=0) ∧
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      (∃ c : ℂ, ‖c‖=1 ∧ V vac=c • canonicalVacuum S hS hβ) ∧
      ∀ (f : PhysicalTensor.L2T L) (c : List (PhysicalTensor.L2T L) →₀ ℂ) (n : ℕ),
        Vtil V.symm
          (((field ((physicalBasis L).repr f))^n)
            (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1 =
          (((field ((physicalBasis L).repr (adjointSource S f)))^n)
            (evalDomain (physicalBasis L) (adjointSource S) v c)).1 := by
  have ht : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (adjointSource S)) ≠ ⊤ :=
    fun h => hβ ((beta_adjoint_hsSq (physicalBasis L) S).symm.trans h)
  let hT := adjointSource_symplectic S hS
  obtain ⟨v,hvn,hv⟩ := Ext006CreationGramR34a.source_vacuum (adjointSource S) hT ht
  obtain ⟨w,hwn,hw⟩ := inverse_source_vacuum (adjointSource S) hT ht
  let V := (physicalUnitary (adjointSource S) hT v w hvn hwn hv hw).symm
  have hA := inverse_HeisAnn (adjointSource S) hT v w hvn hwn hv hw
  have hC := inverse_HeisCre (adjointSource S) hT v w hvn hwn hv hw
  obtain ⟨ha,hb⟩ := adjoint_rows (physicalBasis L) S
  rw [ha,hb] at hA hC
  refine ⟨V,v,hvn,hv,hA,hC,
    Ext006CanonicalVacuumR38a.all_implementer_canonical_vacuum S hS hβ V hA hC,?_⟩
  intro f c n
  rw [Vtil_apply]
  change Phi (Phi.symm (embedding (physicalBasis L) (adjointSource S) hT v hvn hv
    (Phi (Phi.symm (((field ((physicalBasis L).repr f))^n)
      (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1))))=_
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]
  exact core_field_power (physicalBasis L) (adjointSource S) hT v hvn hv f c n

end QuantumNLS.Ext006PhysicalFieldR41a
#print axioms QuantumNLS.Ext006PhysicalFieldR41a.source_actual_Heis_with_strong_field_powers

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalFieldR41a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
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
  Lean.logInfo m!"Round41a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
