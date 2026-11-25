import QuantumNLS.Prop024DomainEstimateR57
import QuantumNLS.Prop024HilbertConjugationR58
import QuantumNLS.Prop024WeylConventionR55
import QuantumNLS.Prop024WickSeriesR54

/-! Round 58: conditional PROP-024 assembly interface.

The exact PROP-022 `Prop022PairInput` remains named.  The undisplaced source
domain is discharged by R57.  The two inputs which still belong to the
separate Prop024W* work are explicit: translated-vector maximal-domain
membership and the step-one identification of the pulled-back interaction
with its constant, linear, quadratic, and remainder vectors.  This module
does not import or assume a Weyl affine-action theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.Prop024AssemblyR58

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Prop022FactorialCoefficientsR115 Prop022PositiveDataR126
open Prop022ClassicalFlowR126 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022OVacuum Ext006PhysFockCoord
open Prop024DomainEstimateR57 Prop024WeylConventionR55
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54
open Prop024HilbertConjugationR58 Prop024WickSeriesR54 Prop024ScalarSeriesR52

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The intermediate PROP-024 assembly scaffold.

`hTranslatedDomainInput` and `hStepOneIdentificationInput` are the exact two
unaccepted inputs.  Given them, the theorem records the already-proved
undisplaced domain statement and transports the step-one identity to the
physical Hilbert space.  It does not claim the remainder estimate until the
separate Wick-cell identity has been discharged. -/
theorem prop024_intermediate_scaffold
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1))
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) /
      Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n)
    (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hSBound :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let Phi := Prop022ClassicalFlowR126.classicalFlow B M A hA.le hB hsa
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let S := fun t s : ℝ => fderiv ℝ (Phi (t-s)) (u s)
      ∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P)
    (hN : ∀ t : ℝ, |t| ≤ T →
      256*Real.exp 1*A*(1+
        (Prop022FactorialMajorantR115.pairMajorant A*T*M*P)^2) ≤ N)
    (constantTerm : ℝ → ℂ)
    (linearTerm quadraticTerm remainderTerm : ℝ → Fock L)
    (hTranslatedDomainInput :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, |t| ≤ T →
        physicalWeyl N (u t) (V t 0 vac) ∈ (interaction N B).domain)
    (hStepOneIdentificationInput :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
        (by linarith) hA.le hB hsa u₀ s t
      ∀ t : ℝ, ∀ ht : |t| ≤ T,
        pulledInteraction N (u t) B (V t 0 vac)
          (hTranslatedDomainInput t ht) =
            constantTerm t • (V t 0 vac) + linearTerm t +
              quadraticTerm t + remainderTerm t) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le hB hsa u₀ s t
    (∀ t : ℝ, |t| ≤ T → V t 0 vac ∈ (interaction N B).domain) ∧
    (∀ t : ℝ, ∀ ht : |t| ≤ T,
      (interaction N B)
        ⟨physicalWeyl N (u t) (V t 0 vac), hTranslatedDomainInput t ht⟩ =
        physicalWeyl N (u t)
          (constantTerm t • (V t 0 vac) + linearTerm t +
            quadraticTerm t + remainderTerm t)) := by
  let B := Prop022PositiveDataR126.positiveExtension K
  let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
  let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
  let Phi := Prop022ClassicalFlowR126.classicalFlow B M A hA.le hB hsa
  let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
  let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
    (by linarith) hA.le hB hsa u₀ s t
  constructor
  · exact pairInput_untranslated_interaction_domain N K M A hM hA hK hsK
      u₀ T P hP hPair hSBound hN
  · intro t ht
    exact interaction_eq_physicalWeyl_of_pulled_identification N (u t) B
      (V t 0 vac) (hTranslatedDomainInput t ht) (constantTerm t)
      (linearTerm t) (quadraticTerm t) (remainderTerm t)
      (hStepOneIdentificationInput t ht)

/-- The already-available R54 norm-series estimate, exported at the assembly
boundary for use once the step-one vector identity is available. -/
theorem contracted_remainder_scalar_bound
    (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (hu : ‖u‖ = 1)
    (M A Q N : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) :
    N * contractedDoubleSeries B u Q N ≤
      2 * factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N :=
  contractedDoubleSeries_source_bound B u hu M A Q N hM hA hQ hN hB

end QuantumNLS.Prop024AssemblyR58

#print axioms QuantumNLS.Prop024AssemblyR58.prop024_intermediate_scaffold
#print axioms QuantumNLS.Prop024AssemblyR58.contracted_remainder_scalar_bound

set_option maxHeartbeats 10000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024AssemblyR58." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024AssemblyR58." then
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
  Lean.logInfo m!"R58 PROP-024 assembly audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
