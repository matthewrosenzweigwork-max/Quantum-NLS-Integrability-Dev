import QuantumNLS.Ext006RowPairingR37a

/-! Both literal frozen physical Heisenberg predicates for the inverse
of the constructed source unitary. The actual row blocks are displayed as
P-adjoint and beta-transpose; conversion to the prescribed flow is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006LiteralHeisR37a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006IdentityCyclicR35a
open Ext006CreationGramR34a Ext006FockEmbeddingR35a Ext006SurjectivityR36a
open Ext006KernelHilbertSchmidt Ext006RowPairingR37a Ext006AdjointTransportR36a
open Ext006ClosedFieldGraphsR36a Ext006PhysFockCoord Ext006PhysQuasifree

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

lemma physCore_C (a : ℤ) (m : Occ) :
    physCore (L := L) (Cre a (ket m))=
      Phi.symm (C (lp.single 2 a 1) (ketD m)).1 := by
  rw [C_mode_ket,Submodule.coe_smul,map_smul,Cre_ket,map_smul,physCore_ket]
  rfl

lemma physCore_A (a : ℤ) (m : Occ) :
    physCore (L := L) (Ann a (ket m))=
      Phi.symm (A (lp.single 2 a 1) (ketD m)).1 := by
  rw [A_mode_ket,Submodule.coe_smul,map_smul,Ann_ket,map_smul,physCore_ket]
  rfl

variable (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn (physicalBasis L) S f v=0)
    (hw : ∀ f,sourceAnn (physicalBasis L) S.symm f w=0)

lemma inverse_Phi (x : Ext025B3PhysicalSectors.Fock L) :
    Phi ((physicalUnitary S hS v w hvn hwn hv hw).symm x)=
      (unitary (physicalBasis L) S hS v w hvn hwn hv hw).symm (Phi x) := by
  change Phi (Phi.symm ((unitary (physicalBasis L) S hS v w hvn hwn hv hw).symm (Phi x)))=_
  exact LinearIsometryEquiv.apply_symm_apply _ _

lemma inverse_zvec (n : Occ) :
    zvec (physicalUnitary S hS v w hvn hwn hv hw).symm n=
      embedding (physicalBasis L) S hS v hvn hv (ketD n).1 := by
  change Phi (physicalUnitary S hS v w hvn hwn hv hw (physCore (ket n)))=_
  change Phi (Phi.symm (embedding (physicalBasis L) S hS v hvn hv
    (Phi (physCore (ket n)))))=_
  rw [LinearIsometryEquiv.apply_symm_apply,physCore_ket,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Literal HeisAnn, including its universally quantified supplied l2 rows. -/
theorem inverse_HeisAnn :
    HeisAnn (physicalUnitary S hS v w hvn hwn hv hw).symm
      (rowA (physicalBasis L) S) (rowB (physicalBasis L) S) := by
  intro d n m u q hu hq
  have hu' : u=uvec (physicalUnitary S hS v w hvn hwn hv hw).symm n m := by
    apply lp.ext
    funext c
    exact (hu c).trans (uvec_apply _ n m c).symm
  have hq' : q=wvec (physicalUnitary S hS v w hvn hwn hv hw).symm n m := by
    apply lp.ext
    funext c
    exact (hq c).trans (wvec_apply _ n m c).symm
  rw [hu',hq',uvec,wvec,inverse_zvec]
  obtain ⟨z,hz,hfields⟩ := ket_transport (physicalBasis L) S hS v hvn hv n
  rw [hz,physCore_C,inner_Phi_symm,inverse_Phi,physCore_ket,
    LinearIsometryEquiv.apply_symm_apply]
  have hi := (unitary (physicalBasis L) S hS v w hvn hwn hv hw).inner_map_map
    (C (lp.single 2 d 1) (ketD n)).1
    ((unitary (physicalBasis L) S hS v w hvn hwn hv hw).symm (ketD m).1)
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  refine hi.symm.trans ?_
  change inner ℂ (embedding (physicalBasis L) S hS v hvn hv
    (C (lp.single 2 d 1) (ketD n)).1) (ketD m).1=_
  have hf := (hfields (physicalBasis L d)).2
  rw [sourceCre_identity,HilbertBasis.repr_self] at hf
  rw [hf]
  exact (source_adjoint (physicalBasis L) S ((physicalBasis L) d) z (ketD m)).symm.trans
    (pair_sourceAnn (physicalBasis L) S d z m)

/-- Literal adjoint predicate; it is proved separately with the conjugated
row blocks required by the frozen definition. -/
theorem inverse_HeisCre :
    HeisCre (physicalUnitary S hS v w hvn hwn hv hw).symm
      (rowA (physicalBasis L) S) (rowB (physicalBasis L) S) := by
  intro d n m u q hu hq
  have hu' : u=uvec (physicalUnitary S hS v w hvn hwn hv hw).symm n m := by
    apply lp.ext
    funext c
    exact (hu c).trans (uvec_apply _ n m c).symm
  have hq' : q=wvec (physicalUnitary S hS v w hvn hwn hv hw).symm n m := by
    apply lp.ext
    funext c
    exact (hq c).trans (wvec_apply _ n m c).symm
  rw [hu',hq',uvec,wvec,inverse_zvec]
  obtain ⟨z,hz,hfields⟩ := ket_transport (physicalBasis L) S hS v hvn hv n
  rw [hz,physCore_A,inner_Phi_symm,inverse_Phi,physCore_ket,
    LinearIsometryEquiv.apply_symm_apply]
  have hi := (unitary (physicalBasis L) S hS v w hvn hwn hv hw).inner_map_map
    (A (lp.single 2 d 1) (ketD n)).1
    ((unitary (physicalBasis L) S hS v w hvn hwn hv hw).symm (ketD m).1)
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  refine hi.symm.trans ?_
  change inner ℂ (embedding (physicalBasis L) S hS v hvn hv
    (A (lp.single 2 d 1) (ketD n)).1) (ketD m).1=_
  have hf := (hfields (physicalBasis L d)).1
  rw [sourceAnn_identity,HilbertBasis.repr_self] at hf
  rw [hf]
  exact (source_adjoint_rev (physicalBasis L) S ((physicalBasis L) d) z (ketD m)).symm.trans
    (pair_sourceCre (physicalBasis L) S d z m)

include hS

/-- Both frozen predicates follow from exactly original source symplecticity
and the HS beta condition. Their exact inverse-source row blocks are explicit. -/
theorem source_inverse_Heis
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (rowA (physicalBasis L) S) (rowB (physicalBasis L) S) ∧
      HeisCre V (rowA (physicalBasis L) S) (rowB (physicalBasis L) S) := by
  obtain ⟨v,hvn,hv⟩ := source_vacuum S hS hβ
  obtain ⟨w,hwn,hw⟩ := Ext006InverseSourceR36a.inverse_source_vacuum S hS hβ
  exact ⟨(physicalUnitary S hS v w hvn hwn hv hw).symm,
    inverse_HeisAnn S hS v w hvn hwn hv hw,
    inverse_HeisCre S hS v w hvn hwn hv hw⟩

end QuantumNLS.Ext006LiteralHeisR37a

#print axioms QuantumNLS.Ext006LiteralHeisR37a.inverse_HeisAnn

#print axioms QuantumNLS.Ext006LiteralHeisR37a.inverse_HeisCre

#print axioms QuantumNLS.Ext006LiteralHeisR37a.source_inverse_Heis

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006LiteralHeisR37a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Round37a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
