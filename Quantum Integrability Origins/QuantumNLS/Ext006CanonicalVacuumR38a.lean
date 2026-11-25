import QuantumNLS.Ext006CanonicalOrientationR38a

/-! Identify EVERY original-row implementer's vacuum with the correctly
oriented canonical coefficient vector. No smoothness or word-action premise
is imposed on the competing implementer. The physical exponential and exact
Fredholm evaluation remain distinct obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006CanonicalVacuumR38a
open Occupation Ext006VacuumRecurrence Ext006PhysFockCoord Ext006PhysQuasifree
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006FockEmbeddingR35a Ext006SurjectivityR36a Ext006AdjointTransportR36a
open Ext006InverseSourceR36a Ext006InverseGraphsR36a Ext006GraphVacuumR36a
open Ext006KernelHilbertSchmidt Ext006LiteralHeisR37a Ext006SourceOrientationR37a
open Ext006CanonicalOrientationR38a Ext006RowPairingR37a
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

lemma unitary_inverse_eq_pullback (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) (x : Fock) :
    (unitary b S hS v w hvn hwn hv hw).symm x = pullback b S hS v hvn hv x := by
  have h := pullback_embedding b S hS v hvn hv
    ((unitary b S hS v w hvn hwn hv hw).symm x)
  have he : embedding b S hS v hvn hv
      ((unitary b S hS v w hvn hwn hv hw).symm x) = x :=
    (unitary b S hS v w hvn hwn hv hw).apply_symm_apply x
  rw [he] at h
  exact h.symm

variable {L : ℝ} [Fact (0 < L)]

/-- The inverse physical source unitary's vacuum has the INVERSE source
kernel. The inverse is identified with the constructed adjoint pullback. -/
theorem inverse_physical_vacuum_weak
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn (physicalBasis L) S f v=0)
    (hw : ∀ f,sourceAnn (physicalBasis L) S.symm f w=0) :
    Ext006PhysicalVacuum.PhysicalWeakVacuum
      (Ext006CompressionR32a.coordinates (physicalBasis L)
        (squeeze (physicalBasis L) S.symm (inverse_symplectic S hS)))
      ((physicalUnitary S hS v w hvn hwn hv hw).symm vac) := by
  have h := graph_vacuum_weak (physicalBasis L) S.symm (inverse_symplectic S hS)
    (pullback (physicalBasis L) S hS v hvn hv vacuum)
    (pullback_vacuum_inverse_graph (physicalBasis L) S hS v hvn hv)
  change WeakVacuum _ (Phi ((physicalUnitary S hS v w hvn hwn hv hw).symm vac))
  rw [inverse_Phi]
  have hz : Phi (vac (L := L)) = vacuum := by
    rw [Ext006PhysFockCoord.vac, physCore_ket, LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [hz]
  erw [unitary_inverse_eq_pullback]
  exact h

/-- For the literal original row blocks, the canonical coefficient vacuum
is the squeeze of (S real-adjoint)^-1, with every orientation change proved. -/
theorem all_implementer_canonical_vacuum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S))
    (hC : HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)) :
    ∃ c : ℂ, ‖c‖=1 ∧ V vac = c • canonicalVacuum S hS hβ := by
  let T := adjointSource S
  have htS := adjointSource_symplectic S hS
  have htβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) T) ≠ ⊤ :=
    fun h => hβ ((beta_adjoint_hsSq (physicalBasis L) S).symm.trans h)
  obtain ⟨v,hvn,hv⟩ := source_vacuum T htS htβ
  obtain ⟨w,hwn,hw⟩ := inverse_source_vacuum T htS htβ
  let W := (physicalUnitary T htS v w hvn hwn hv hw).symm
  have hWA := inverse_HeisAnn T htS v w hvn hwn hv hw
  have hWC := inverse_HeisCre T htS v w hvn hwn hv hw
  obtain ⟨ha,hb⟩ := adjoint_rows (physicalBasis L) S
  change HeisAnn W (rowA (physicalBasis L) (adjointSource S))
    (rowB (physicalBasis L) (adjointSource S)) at hWA
  change HeisCre W (rowA (physicalBasis L) (adjointSource S))
    (rowB (physicalBasis L) (adjointSource S)) at hWC
  rw [ha,hb] at hWA hWC
  have hWeakW := inverse_physical_vacuum_weak T htS v w hvn hwn hv hw
  change WeakVacuum (Ext006CompressionR32a.coordinates (physicalBasis L)
    (vacuumKernel S hS)) (Phi (W vac)) at hWeakW
  obtain ⟨c,-,he⟩ := Ext006ImplementerUniqueR37a.implementer_unique_phase W V
    (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)
    (actual_blocks_symplectic (physicalBasis L) S hS) hWA hWC hA hC
  have hWeakV : Ext006PhysicalVacuum.PhysicalWeakVacuum
      (Ext006CompressionR32a.coordinates (physicalBasis L) (vacuumKernel S hS)) (V vac) := by
    rw [he]
    change WeakVacuum _ (Phi (c • W vac))
    rw [map_smul]
    exact hWeakW.smul c
  have hnVac : ‖vac (L := L)‖ = 1 := by
    rw [Ext006PhysFockCoord.vac, physCore_ket, LinearIsometryEquiv.norm_map]
    exact vacuum_norm
  exact Ext006PhysicalVacuum.physical_normalized_unique_phase
    (canonicalVacuum_weak S hS hβ) hWeakV (canonicalVacuum_norm S hS hβ)
    ((V.norm_map vac).trans hnVac)

/-- Original source hypotheses produce an implementer; ALL literal-row
implementers have the displayed canonical coefficient vacuum up to phase.
This theorem does not claim the full physical-exponential BD-02 formula. -/
theorem source_implementer_canonical_vacuum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      ∀ W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        HeisAnn W (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
        HeisCre W (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
        ∃ c : ℂ, ‖c‖=1 ∧ W vac = c • canonicalVacuum S hS hβ := by
  obtain ⟨V,-,hA,hC⟩ := Ext006ActualHeisR37a.source_actual_Heis S hS hβ
  exact ⟨V,hA,hC,all_implementer_canonical_vacuum S hS hβ⟩

end QuantumNLS.Ext006CanonicalVacuumR38a

#print axioms QuantumNLS.Ext006CanonicalVacuumR38a.unitary_inverse_eq_pullback

#print axioms QuantumNLS.Ext006CanonicalVacuumR38a.inverse_physical_vacuum_weak

#print axioms QuantumNLS.Ext006CanonicalVacuumR38a.all_implementer_canonical_vacuum

#print axioms QuantumNLS.Ext006CanonicalVacuumR38a.source_implementer_canonical_vacuum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CanonicalVacuumR38a." then
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
  Lean.logInfo m!"Round38a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
