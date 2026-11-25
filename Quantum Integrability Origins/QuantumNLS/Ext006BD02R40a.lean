import QuantumNLS.Ext006FredholmNormR40a

/-! FIN-CORE-BD-02 on the actual physical Fock space: exact Fredholm
normalization of the literal completed pair exponential, including all
original-row implementing unitaries and the proved oriented source kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006BD02R40a
open Ext006KernelHilbertSchmidt Ext006CanonicalOrientationR38a Ext006CanonicalExponentialR39a
open Ext006FredholmNormR40a Ext006FredholmTracePower Ext006PhysFockCoord
open Ext006PhysicalExponentialTerms Ext006PhysicalNormBridge.PairTensor
open Ext006SourceOrientationR37a Ext006ActualHeisR37a Ext006PhysQuasifree
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

lemma canonicalVacuum_Fredholm
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    canonicalVacuum S hS hβ =
      (((fredholmDet ((vacuumKernel S hS).adjoint ∘L vacuumKernel S hS))^(1/4:ℝ) : ℝ) : ℂ) •
        sourceExponential S hS hβ :=
  physicalNormalized_eq_Fredholm _ _ _ _

/-- Every actual original-row implementer has the determinant-normalized
physical exponential vacuum; no smoothness, norm law or vacuum is a premise. -/
lemma all_implementer_Fredholm
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S))
    (hC : HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)) :
    ∃ c : ℂ, ‖c‖=1 ∧ V vac =
      c • ((((fredholmDet ((vacuumKernel S hS).adjoint ∘L vacuumKernel S hS))^(1/4:ℝ) : ℝ) : ℂ) •
        sourceExponential S hS hβ) := by
  obtain ⟨c,hc,he⟩ := Ext006CanonicalVacuumR38a.all_implementer_canonical_vacuum S hS hβ V hA hC
  exact ⟨c,hc,he.trans (congrArg (c • ·) (canonicalVacuum_Fredholm S hS hβ))⟩

/-- The determinant-normalized vacuum has a finite exponential number weight. -/
lemma Fredholm_vacuum_exponential_number
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ t : ℝ, 1 < t ∧ Ext006NumberPhase.numberExpectation (fun n => ENNReal.ofReal (t^n))
      ((((fredholmDet ((vacuumKernel S hS).adjoint ∘L vacuumKernel S hS))^(1/4:ℝ) : ℝ) : ℂ) •
        sourceExponential S hS hβ) ≠ ⊤ := by
  have ht := Ext006NumberDomainR32a.physical_exponential_weight (vacuumKernel S hS)
    (vacuumKernel_properties S hS hβ).1 (vacuumKernel_properties S hS hβ).2.1
    (vacuumKernel_properties S hS hβ).2.2
  change ∃ t : ℝ, 1 < t ∧ Ext006NumberPhase.numberExpectation (fun n => ENNReal.ofReal (t^n))
    (canonicalVacuum S hS hβ) ≠ ⊤ at ht
  rwa [canonicalVacuum_Fredholm] at ht

/-- BD Theorem 4.2 / (4.1)-(4.2): from the original symplectic map and its HS
beta block, the pure normalized vacuum is det(1-K* K)^(1/4) exp(-a*(K)/2)Omega
up to phase. The exponential is the literal norm-convergent physical series.
Its oriented K is bar(Q' P'^{-1}), for S'=(S real-adjoint)^-1, and equals the
NEGATIVE original-source squeeze under the frozen Heisenberg row convention. -/
theorem «FIN-CORE-BD-02»
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    let K := vacuumKernel S hS
    K = operatorConjugate (physicalBasis L)
      (sourceQ (physicalBasis L) (vacuumSource S) ∘L
        sourcePInv (vacuumSource S) (vacuumSource_symplectic S hS)) ∧
    K = -squeeze (physicalBasis L) S hS ∧
    (∀ i j, Ext006CompressionR32a.coordinates (physicalBasis L) K i j =
      Ext006CompressionR32a.coordinates (physicalBasis L) K j i) ∧
    ‖K‖ < 1 ∧ TraceClass.hsSq (physicalBasis L) K ≠ ⊤ ∧
    0 < (fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) ∧
    HasSum (fockTerm (physicalPair (physicalBasis L) K
      (vacuumKernel_properties S hS hβ).2.2 (vacuumKernel_properties S hS hβ).1))
      (sourceExponential S hS hβ) ∧
    (∀ n : ℕ, term (physicalPair (physicalBasis L) K
      (vacuumKernel_properties S hS hβ).2.2 (vacuumKernel_properties S hS hβ).1) n =
      ((-1/2:ℂ)^n/(n.factorial:ℂ)) • power (physicalPair (physicalBasis L) K
        (vacuumKernel_properties S hS hβ).2.2 (vacuumKernel_properties S hS hβ).1) n) ∧
    canonicalVacuum S hS hβ =
      (((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • sourceExponential S hS hβ ∧
    ‖(((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • sourceExponential S hS hβ‖ = 1 ∧
    (∃ t : ℝ, 1 < t ∧ Ext006NumberPhase.numberExpectation (fun n => ENNReal.ofReal (t^n))
      ((((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • sourceExponential S hS hβ) ≠ ⊤) ∧
    (∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)) ∧
    (∀ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
      ∃ c : ℂ, ‖c‖=1 ∧ V vac =
        c • ((((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • sourceExponential S hS hβ)) ∧
    (∀ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
      ∀ w : ℕ → ℝ≥0∞, Ext006NumberPhase.numberExpectation w (V vac) =
        Ext006NumberPhase.numberExpectation w
          ((((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • sourceExponential S hS hβ)) := by
  dsimp only
  have hp := vacuumKernel_properties S hS hβ
  refine ⟨vacuumKernel_source_formula S hS,source_kernel_sign S hS,hp.1,hp.2.1,hp.2.2,?_,
    sourceExponential_hasSum S hS hβ,term_eq_power _,canonicalVacuum_Fredholm S hS hβ,?_,
    Fredholm_vacuum_exponential_number S hS hβ,?_,all_implementer_Fredholm S hS hβ,?_⟩
  · rw [← fourthRoot_eq_rpow]
    exact fourthRoot_pos _
  · rw [← canonicalVacuum_Fredholm S hS hβ]
    exact canonicalVacuum_norm S hS hβ
  · obtain ⟨V,-,hA,hC⟩ := source_actual_Heis S hS hβ
    exact ⟨V,hA,hC⟩
  · intro V hA hC w
    obtain ⟨c,hc,he⟩ := all_implementer_Fredholm S hS hβ V hA hC
    rw [he]
    exact Ext006NumberPhase.«FIN-CORE-BD-02-phase» c hc _ w

end QuantumNLS.Ext006BD02R40a
#print axioms QuantumNLS.Ext006BD02R40a.«FIN-CORE-BD-02»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006BD02R40a." then
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
