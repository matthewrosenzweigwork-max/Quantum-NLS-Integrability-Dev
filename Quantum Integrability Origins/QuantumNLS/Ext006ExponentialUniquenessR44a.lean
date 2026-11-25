import QuantumNLS.Ext006ExponentialIrreducibleR44a
import QuantumNLS.Ext006GlobalCovarianceR43a

/-! Phase uniqueness for every bounded exponential implementer, with no
unbounded-domain or corrected-row hypothesis on either competitor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialUniquenessR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006BoundedExponentialR43a Ext006ExponentialIrreducibleR44a
open Ext006WeakDifferentiationR44a

theorem implementers_phase (S : H → H) (U V : Fock ≃ₗᵢ[ℂ] Fock)
    (hU : ∀ h t x, U (unitary h t x)=unitary (S h) t (U x))
    (hV : ∀ h t x, V (unitary h t x)=unitary (S h) t (V x)) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ x : Fock, V x=z • U x := by
  let T : Fock ≃ₗᵢ[ℂ] Fock := V.trans U.symm
  have hT : CommutesExponential T.toLinearIsometry.toContinuousLinearMap := by
    intro h t x
    change U.symm (V (unitary h t x))=unitary h t (U.symm (V x))
    rw [hV]
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply,hU,LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨z,hz,he⟩ := unitary_commutant_phase T hT
  refine ⟨z,hz,fun x => ?_⟩
  have hx := congrArg U (he x)
  simpa only [T,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,map_smul] using hx

open Ext006PhysFockCoord Ext006PhysQuasifree Ext006GlobalCovarianceR43a
open Ext006KernelHilbertSchmidt
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

def ImplementsExponential (S : PhysicalTensor.L2T L → PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L) : Prop :=
  ∀ (f : PhysicalTensor.L2T L) (t : ℝ) (x : Ext025B3PhysicalSectors.Fock L),
    U (physicalExponential f t x)=physicalExponential (S f) t (U x)

lemma occupation_covariance (S : PhysicalTensor.L2T L → PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : ImplementsExponential S U) (h : H) (t : ℝ) (x : Fock) :
    Vtil U (unitary h t x)=
      unitary ((physicalBasis L).repr (S ((physicalBasis L).repr.symm h))) t (Vtil U x) := by
  have he := congrArg (Phi (L := L))
    (hU ((physicalBasis L).repr.symm h) t ((Phi (L := L)).symm x))
  simpa only [physicalExponential_apply,LinearIsometryEquiv.apply_symm_apply,
    Vtil_apply] using he

/-- Uniqueness for all whole-physical-Fock exponential implementers. -/
theorem physical_implementers_phase
    (S : PhysicalTensor.L2T L → PhysicalTensor.L2T L)
    (U V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : ImplementsExponential S U) (hV : ImplementsExponential S V) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ x : Ext025B3PhysicalSectors.Fock L, V x=z • U x := by
  obtain ⟨z,hz,he⟩ := implementers_phase
    (fun h => (physicalBasis L).repr (S ((physicalBasis L).repr.symm h)))
    (Vtil U) (Vtil V) (occupation_covariance S U hU) (occupation_covariance S V hV)
  refine ⟨z,hz,fun x => ?_⟩
  apply (Phi (L := L)).injective
  simpa only [Vtil_apply,LinearIsometryEquiv.symm_apply_apply,map_smul] using he (Phi x)

end QuantumNLS.Ext006ExponentialUniquenessR44a
#print axioms QuantumNLS.Ext006ExponentialUniquenessR44a.implementers_phase
#print axioms QuantumNLS.Ext006ExponentialUniquenessR44a.physical_implementers_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialUniquenessR44a." then
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
