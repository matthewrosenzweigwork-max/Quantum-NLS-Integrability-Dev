import QuantumNLS.Ext006NaturalWeylR44a

/-! Restated FIN-CORE-BD-02 in the ESI source's Weyl sense. Every kernel,
Fredholm, pair-series, vacuum, normalization and number clause is at the
ORIGINAL S. All competitors are source-Weyl implementers on whole Fock. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006BD02R44a
open Ext006KernelHilbertSchmidt Ext006CompressionR32a Ext006OriginalVacuumR42a
open Ext006OriginalNormalizationR42a Ext006SourceWeylR44a Ext006NaturalWeylR44a
open Ext006FredholmTracePower Ext006FredholmNormR40a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006PhysFockCoord Ext006PhysQuasifree
open Ext006SourceOrientationR37a Ext006NumberPhase
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Phase independence for every nonnegative spectral number observable,
including infinite expectations, for all source Weyl implementers. -/
lemma all_source_number_weights
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hV : SourceWeylImplementer S V) (w : ℕ → ℝ≥0∞) :
    numberExpectation w (V vac)=numberExpectation w (originalVacuum S hS hβ) := by
  obtain ⟨z,hz,hvac⟩ := all_sourceWeyl_vacua S hS hβ V hV
  rw [hvac,«FIN-CORE-BD-02-phase» z hz]

/-- FIN-CORE-BD-02: the source-normalized Weyl implementer exists at S;
all implementers differ by phase; the unique positive-normalized vacuum
has the literal determinant/pair-exponential formula and original beta
number expectation. This is an author theorem, not an acceptance decision. -/
theorem «FIN-CORE-BD-02»
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    let K := squeeze (physicalBasis L) S hS
    let c : ℝ := (fredholmDet (K.adjoint ∘L K))^(1/4 : ℝ)
    K = operatorConjugate (physicalBasis L)
      (sourceQ (physicalBasis L) S ∘L sourcePInv S hS) ∧
    (∀ i j, coordinates (physicalBasis L) K i j=coordinates (physicalBasis L) K j i) ∧
    ‖K‖<1 ∧ TraceClass.hsSq (physicalBasis L) K ≠ ⊤ ∧ 0<c ∧
    HasSum (fockTerm (physicalPair (physicalBasis L) K
      (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1))
      (originalExponential S hS hβ) ∧
    (∀ n : ℕ, term (physicalPair (physicalBasis L) K
      (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1) n =
      ((-1/2 : ℂ)^n/(n.factorial : ℂ)) • power (physicalPair (physicalBasis L) K
        (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1) n) ∧
    originalVacuum S hS hβ=(c : ℂ) • originalExponential S hS hβ ∧
    ‖originalVacuum S hS hβ‖=1 ∧
    inner ℂ vac (originalExponential S hS hβ)=1 ∧
    inner ℂ vac (originalVacuum S hS hβ)=(c : ℂ) ∧
    (∃ t : ℝ, 1<t ∧ numberExpectation (fun n => ENNReal.ofReal (t^n))
      (originalVacuum S hS hβ) ≠ ⊤) ∧
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      SourceWeylImplementer S U ∧ U vac=originalVacuum S hS hβ ∧
      (inner ℂ vac (U vac)).im=0 ∧ 0<(inner ℂ vac (U vac)).re ∧
      ∀ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        SourceWeylImplementer S V →
        (∃ z : ℂ, ‖z‖=1 ∧ ∀ x, V x=z • U x) ∧
        (∃ z : ℂ, ‖z‖=1 ∧ V vac=z • ((c : ℂ) • originalExponential S hS hβ)) ∧
        (∀ w : ℕ → ℝ≥0∞, numberExpectation w (V vac)=
          numberExpectation w ((c : ℂ) • originalExponential S hS hβ)) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac)=
          TraceClass.posTrace ((beta (physicalBasis L) S).adjoint ∘L beta (physicalBasis L) S) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac)=
          TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) ≠ ⊤ ∧
        (∃ t : ℝ, 1<t ∧ numberExpectation (fun n => ENNReal.ofReal (t^n)) (V vac) ≠ ⊤) ∧
        ((inner ℂ vac (V vac)).im=0 → 0<(inner ℂ vac (V vac)).re →
          ∀ x : Ext025B3PhysicalSectors.Fock L, V x=U x) := by
  dsimp only
  have hp := original_kernel_properties S hS hβ
  refine ⟨original_kernel_formula S hS,hp.1,hp.2.1,hp.2.2,?_,
    originalExponential_hasSum S hS hβ,term_eq_power _,originalVacuum_Fredholm S hS hβ,
    originalVacuum_norm S hS hβ,originalExponential_vacuum_expectation S hS hβ,
    originalVacuum_vacuum_expectation S hS hβ,originalVacuum_exponential_number S hS hβ,?_⟩
  · rw [← fourthRoot_eq_rpow]
    exact fourthRoot_pos _
  · obtain ⟨U,hU,hUv⟩ := natural_exists S hS hβ
    refine ⟨U,hU,hUv,?_,?_,?_⟩
    · rw [hUv,originalVacuum_vacuum_expectation,Complex.ofReal_im]
    · rw [hUv]
      exact originalVacuum_vacuum_positive S hS hβ
    · intro V hV
      have hnum := all_source_number_weights S hS hβ V hV
      refine ⟨sourceWeyl_unique_phase S U V hU hV,?_,?_,?_,?_,?_,?_,?_⟩
      · obtain ⟨z,hz,hvac⟩ := all_sourceWeyl_vacua S hS hβ V hV
        refine ⟨z,hz,?_⟩
        rw [← originalVacuum_Fredholm]
        exact hvac
      · intro w
        rw [← originalVacuum_Fredholm]
        exact hnum w
      · exact (hnum _).trans (original_number_trace S hS hβ)
      · exact (hnum _).trans (original_number_hs S hS hβ)
      · rw [hnum,original_number_hs S hS hβ]
        exact hβ
      · obtain ⟨t,ht,he⟩ := originalVacuum_exponential_number S hS hβ
        exact ⟨t,ht,by rw [hnum]; exact he⟩
      · exact natural_unique S hS hβ U V hU hV hUv

end QuantumNLS.Ext006BD02R44a
#print axioms QuantumNLS.Ext006BD02R44a.«FIN-CORE-BD-02»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006BD02R44a." then
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
