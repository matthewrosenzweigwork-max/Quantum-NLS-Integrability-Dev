import QuantumNLS.Ext006ReorientationR42a

/-! R42a: vacuum and squeeze clauses are recomputed at the ORIGINAL source S.
The row interface used below has INPUT (S^-1)*. It is not identified with a
Weyl interface. The bounded Weyl construction remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006OriginalVacuumR42a
open Ext006KernelHilbertSchmidt Ext006SymplecticKernel Ext006CompressionR32a
open Ext006HSVacuumR32a Ext006PhysicalSeriesR39a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006FredholmTracePower Ext006FredholmNormR40a
open Ext006SourceOrientationR37a Ext006ReorientationR42a Ext006CanonicalOrientationR38a
open Ext006PhysFockCoord Ext006PhysQuasifree
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Properties are proved for the original source kernel, directly from S. -/
theorem original_kernel_properties
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    (∀ i j, coordinates (physicalBasis L) (squeeze (physicalBasis L) S hS) i j =
      coordinates (physicalBasis L) (squeeze (physicalBasis L) S hS) j i) ∧
    ‖squeeze (physicalBasis L) S hS‖ < 1 ∧
    TraceClass.hsSq (physicalBasis L) (squeeze (physicalBasis L) S hS) ≠ ⊤ := by
  obtain ⟨hs,hn,hk,-,-⟩ := «FIN-CORE-BD-02-kernel» (physicalBasis L) S hS hβ
  exact ⟨hs,hn,hk⟩

/-- The literal norm-convergent exp(-a*(K(S))/2) Omega. -/
def originalExponential
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext025B3PhysicalSectors.Fock L :=
  physicalExponential (squeeze (physicalBasis L) S hS)
    (original_kernel_properties S hS hβ).1 (original_kernel_properties S hS hβ).2.1
    (original_kernel_properties S hS hβ).2.2

/-- The positive-normalized vacuum with the source's ORIGINAL kernel. -/
def originalVacuum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext025B3PhysicalSectors.Fock L :=
  physicalNormalized (squeeze (physicalBasis L) S hS)
    (original_kernel_properties S hS hβ).1 (original_kernel_properties S hS hβ).2.1
    (original_kernel_properties S hS hβ).2.2

lemma reorient_hs
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (reorient S)) ≠ ⊤ :=
  fun h => hβ ((reorient_beta_hsSq (physicalBasis L) S hS).symm.trans h)

/-- Kernel transport is proved abstractly before specializing the large source terms. -/
lemma physicalNormalized_congr
    (K K' : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hs : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hs' : ∀ i j, coordinates (physicalBasis L) K' i j = coordinates (physicalBasis L) K' j i)
    (hn : ‖K‖ < 1) (hn' : ‖K'‖ < 1)
    (hHS : TraceClass.hsSq (physicalBasis L) K ≠ ⊤)
    (hHS' : TraceClass.hsSq (physicalBasis L) K' ≠ ⊤) (he : K = K') :
    physicalNormalized K hs hn hHS = physicalNormalized K' hs' hn' hHS' := by
  subst K'
  rfl

/-- The changed row construction gives precisely the NEW original-source vacuum. -/
theorem canonicalVacuum_reorient
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    canonicalVacuum (reorient S) (reorient_symplectic S hS) (reorient_hs S hS hβ) =
      originalVacuum S hS hβ := by
  unfold canonicalVacuum originalVacuum
  apply physicalNormalized_congr
  exact vacuumKernel_reorient S hS

/-- Exact original-source (4.1), with the bar on the WHOLE product. -/
theorem original_kernel_formula
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap) :
    squeeze (physicalBasis L) S hS = operatorConjugate (physicalBasis L)
      (sourceQ (physicalBasis L) S ∘L sourcePInv S hS) :=
  sourceK_formula (physicalBasis L) S hS

theorem originalVacuum_Fredholm
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    originalVacuum S hS hβ =
      (((fredholmDet ((squeeze (physicalBasis L) S hS).adjoint ∘L
        squeeze (physicalBasis L) S hS))^(1/4:ℝ) : ℝ) : ℂ) • originalExponential S hS hβ :=
  physicalNormalized_eq_Fredholm _ _ _ _

theorem originalVacuum_norm
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ‖originalVacuum S hS hβ‖ = 1 := physicalNormalized_norm _ _ _ _

theorem originalVacuum_weak
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext006PhysicalVacuum.PhysicalWeakVacuum
      (coordinates (physicalBasis L) (squeeze (physicalBasis L) S hS))
      (originalVacuum S hS hβ) := physicalNormalized_weak _ _ _ _

theorem originalVacuum_exponential_number
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ t : ℝ, 1 < t ∧ Ext006NumberPhase.numberExpectation (fun n => ENNReal.ofReal (t^n))
      (originalVacuum S hS hβ) ≠ ⊤ :=
  Ext006NumberDomainR32a.physical_exponential_weight _ _ _ _

theorem originalExponential_hasSum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    HasSum (fockTerm (physicalPair (physicalBasis L) (squeeze (physicalBasis L) S hS)
      (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1))
      (originalExponential S hS hβ) := physical_exponential_hasSum _ _ _ _

/-- All unitaries satisfying the corrected ROW interface have the original
source vacuum. This quantifier is not yet over all Weyl implementers. -/
theorem all_reoriented_rows_vacuum
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)))
    (hC : HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S))) :
    ∃ c : ℂ, ‖c‖=1 ∧ U vac = c • originalVacuum S hS hβ := by
  obtain ⟨c,hc,he⟩ := Ext006CanonicalVacuumR38a.all_implementer_canonical_vacuum
    (reorient S) (reorient_symplectic S hS) (reorient_hs S hS hβ) U hA hC
  rw [canonicalVacuum_reorient S hS hβ] at he
  exact ⟨c,hc,he⟩

/-- Row-existence and all row-vacuum/number clauses with corrected input.
This is deliberately not called the source-Weyl BD-02 headline. -/
theorem original_source_vacuum_clauses
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    (∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) ∧
      HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S))) ∧
    (∀ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) →
      HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) →
      ∃ c : ℂ, ‖c‖=1 ∧ U vac = c • originalVacuum S hS hβ ∧
        ∀ w : ℕ → ℝ≥0∞, Ext006NumberPhase.numberExpectation w (U vac) =
          Ext006NumberPhase.numberExpectation w (originalVacuum S hS hβ)) := by
  constructor
  · obtain ⟨U,-,hA,hC⟩ := Ext006ActualHeisR37a.source_actual_Heis (reorient S)
      (reorient_symplectic S hS) (reorient_hs S hS hβ)
    exact ⟨U,hA,hC⟩
  · intro U hA hC
    obtain ⟨c,hc,he⟩ := all_reoriented_rows_vacuum S hS hβ U hA hC
    refine ⟨c,hc,he,fun w => ?_⟩
    rw [he]
    exact Ext006NumberPhase.«FIN-CORE-BD-02-phase» c hc _ w

end QuantumNLS.Ext006OriginalVacuumR42a
#print axioms QuantumNLS.Ext006OriginalVacuumR42a.canonicalVacuum_reorient
#print axioms QuantumNLS.Ext006OriginalVacuumR42a.originalVacuum_Fredholm
#print axioms QuantumNLS.Ext006OriginalVacuumR42a.originalExponential_hasSum
#print axioms QuantumNLS.Ext006OriginalVacuumR42a.original_source_vacuum_clauses

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006OriginalVacuumR42a." then
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
