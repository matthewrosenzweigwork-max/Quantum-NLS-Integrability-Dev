import QuantumNLS.Ext006SourceStoneR44a
import QuantumNLS.Ext006WeylScalingR44a

/-! The BD source Weyl operators on physical Fock, constructed via the
unique Stone group of the self-adjoint smeared-field closure. The source
normalization is W(f,fbar)=exp(i(a*(f)+a(f))). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SourceWeylR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006BoundedExponentialR43a Ext006SourceStoneR44a Ext006StoneGeneratorR44a
open Ext006SelfAdjointR44a Ext006PhysFockCoord Ext006GlobalCovarianceR43a
open Ext006ExponentialUniquenessR44a Ext006WeylScalingR44a
open Ext006KernelHilbertSchmidt Ext006OriginalVacuumR42a Ext006PhysQuasifree
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The source spectral exponential, characterized by Stone on the actual
self-adjoint closure of the actual smeared field. -/
def sourceWeyl (f : PhysicalTensor.L2T L) :
    Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L :=
  (Phi (L := L)).trans
    (((sourceStone ((physicalBasis L).repr f)).U 1).trans (Phi (L := L)).symm)

theorem sourceWeyl_eq (f : PhysicalTensor.L2T L)
    (x : Ext025B3PhysicalSectors.Fock L) :
    sourceWeyl f x=physicalExponential f 1 x := by
  change (Phi (L := L)).symm ((sourceStone ((physicalBasis L).repr f)).U 1 (Phi x)) = _
  rw [sourceStone_eq]
  rfl

/-- Exactly the source Weyl implementation predicate, with no field-domain,
row-interface, vacuum, or phase hypothesis imposed on the implementer. -/
def SourceWeylImplementer (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L) : Prop :=
  ∀ (f : PhysicalTensor.L2T L) (x : Ext025B3PhysicalSectors.Fock L),
    U (sourceWeyl f (U.symm x))=sourceWeyl (S f) x

lemma implementer_exponential (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : SourceWeylImplementer S U) : ImplementsExponential S U := by
  apply time_one_covariance S U
  intro f x
  have he := hU f (U x)
  simpa only [LinearIsometryEquiv.symm_apply_apply,sourceWeyl_eq] using he

/-- Phase uniqueness for ALL source Weyl implementers, derived from weak
differentiation and proved irreducibility on the whole Fock completion. -/
theorem sourceWeyl_unique_phase
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : SourceWeylImplementer S U) (hV : SourceWeylImplementer S V) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ x : Ext025B3PhysicalSectors.Fock L, V x=z • U x :=
  physical_implementers_phase S U V (implementer_exponential S U hU) (implementer_exponential S V hV)

/-- Whole-Fock Weyl covariance at the ORIGINAL S, with the original-source
vacuum. Existence and all analytic/source identifications are discharged. -/
theorem sourceWeyl_exists
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      SourceWeylImplementer S U ∧
      ∃ z : ℂ, ‖z‖=1 ∧ U vac=z • originalVacuum S hS hβ := by
  obtain ⟨U,-,-,hvac,hcov⟩ := original_source_bounded_covariance S hS hβ
  refine ⟨U,?_,hvac⟩
  intro f x
  simp only [sourceWeyl_eq]
  exact hcov f 1 x

/-- Every source-Weyl implementer has the ORIGINAL S squeezed vacuum. -/
theorem all_sourceWeyl_vacua
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hV : SourceWeylImplementer S V) :
    ∃ z : ℂ, ‖z‖=1 ∧ V vac=z • originalVacuum S hS hβ := by
  obtain ⟨U,hU,c,hc,hvac⟩ := sourceWeyl_exists S hS hβ
  obtain ⟨d,hd,hUV⟩ := sourceWeyl_unique_phase S U V hU hV
  refine ⟨d*c,by rw [norm_mul,hd,hc,mul_one],?_⟩
  rw [hUV,hvac,smul_smul]

end QuantumNLS.Ext006SourceWeylR44a
#print axioms QuantumNLS.Ext006SourceWeylR44a.sourceWeyl_eq
#print axioms QuantumNLS.Ext006SourceWeylR44a.sourceWeyl_unique_phase
#print axioms QuantumNLS.Ext006SourceWeylR44a.sourceWeyl_exists
#print axioms QuantumNLS.Ext006SourceWeylR44a.all_sourceWeyl_vacua

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceWeylR44a." then
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
