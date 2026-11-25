import QuantumNLS.Ext006OriginalVacuumR42a

/-! Forward strong field powers for the ORIGINAL S. The source domain is a
constructed dense polynomial domain, rather than an assumed invariant core.
This module does not promote that equality to bounded Weyl covariance. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ForwardFieldR42a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a Ext006SourceCCRR34a
open Ext006IdentityCyclicR35a Ext006CoreTransportR35a Ext006FockEmbeddingR35a
open Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a Ext006InverseSourceR36a
open Ext006PhysQuasifree Ext006PhysFockCoord Ext006StrongFieldR41a
open Ext006ReorientationR42a Ext006OriginalVacuumR42a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal
local instance physicalReal (L : ℝ) [Fact (0 < L)] : NormedSpace ℝ (PhysicalTensor.L2T L) :=
  (InnerProductSpace.complexToReal : InnerProductSpace ℝ (PhysicalTensor.L2T L)).toNormedSpace

lemma Vtil_symm_cancel
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L) (x : Fock) :
    Vtil U (Vtil U.symm x) = x := by
  simp only [Vtil_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.apply_symm_apply]

/-- The actual identity-source polynomial vectors form a dense physical core. -/
theorem physical_identity_polynomials_dense :
    DenseRange (fun c : List (PhysicalTensor.L2T L) →₀ ℂ =>
      (Phi (L := L)).symm (evalDomain (physicalBasis L) identitySource (ketD 0) c).1) := by
  have hd := (Phi (L := L)).symm.surjective.denseRange.comp
    (identity_eval_dense (physicalBasis L)) (Phi (L := L)).symm.continuous
  simpa only [Function.comp_def,evalDomain_val] using hd

/-- Original-source symplecticity and beta HS produce a forward physical
unitary with its original-source vacuum. Every strong power acts at S itself.
The polynomial domain on the left is proved dense below using the n=0 case. -/
theorem original_source_forward_field_powers
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
    ∃ v : D, ‖v.1‖=1 ∧ (∀ f, sourceAnn (physicalBasis L) S.symm f v=0) ∧
      HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) ∧
      HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) ∧
      (∃ c : ℂ, ‖c‖=1 ∧ U vac=c • originalVacuum S hS hβ) ∧
      DenseRange (fun c : List (PhysicalTensor.L2T L) →₀ ℂ =>
        (Phi (L := L)).symm (evalDomain (physicalBasis L) S.symm v c).1) ∧
      ∀ (f : PhysicalTensor.L2T L) (c : List (PhysicalTensor.L2T L) →₀ ℂ) (n : ℕ),
        U ((Phi (L := L)).symm
          (((field ((physicalBasis L).repr f))^n) (evalDomain (physicalBasis L) S.symm v c)).1) =
        (Phi (L := L)).symm
          (((field ((physicalBasis L).repr (S f)))^n)
            (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1 := by
  obtain ⟨U,v,hvn,hv,hA,hC,hvac,hpow⟩ :=
    Ext006PhysicalFieldR41a.source_actual_Heis_with_strong_field_powers
      (reorient S) (reorient_symplectic S hS) (reorient_hs S hS hβ)
  erw [adjointSource_reorient S] at hv hpow
  rw [canonicalVacuum_reorient S hS hβ] at hvac
  have hforward (f : PhysicalTensor.L2T L) (c : List (PhysicalTensor.L2T L) →₀ ℂ) (n : ℕ) :
      Vtil U ((((field ((physicalBasis L).repr f))^n)
        (evalDomain (physicalBasis L) S.symm v c)).1) =
      (((field ((physicalBasis L).repr (S f)))^n)
        (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1 := by
    have hh := hpow (S f) c n
    erw [ContinuousLinearEquiv.symm_apply_apply] at hh
    have he := congrArg (Vtil U) hh
    rw [Vtil_symm_cancel] at he
    exact he.symm
  have hzero (c : List (PhysicalTensor.L2T L) →₀ ℂ) :
      (Phi (L := L)).symm (evalDomain (physicalBasis L) S.symm v c).1 =
      U.symm ((Phi (L := L)).symm
        (evalDomain (physicalBasis L) identitySource (ketD 0) c).1) := by
    have hh := congrArg (Phi (L := L)).symm (hforward 0 c 0)
    simp only [pow_zero,Module.End.one_apply,Vtil_apply,LinearIsometryEquiv.symm_apply_apply] at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using congrArg U.symm hh
  refine ⟨U,v,hvn,hv,hA,hC,hvac,?_,?_⟩
  · have hd := physical_identity_polynomials_dense (L := L)
    have he := U.symm.surjective.denseRange.comp hd U.symm.continuous
    simpa only [Function.comp_def,← hzero] using he
  · intro f c n
    have hh := congrArg (Phi (L := L)).symm (hforward f c n)
    simpa only [Vtil_apply,LinearIsometryEquiv.symm_apply_apply] using hh

end QuantumNLS.Ext006ForwardFieldR42a
#print axioms QuantumNLS.Ext006ForwardFieldR42a.physical_identity_polynomials_dense
#print axioms QuantumNLS.Ext006ForwardFieldR42a.original_source_forward_field_powers

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ForwardFieldR42a." then
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
  Lean.logInfo m!"Round42a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
