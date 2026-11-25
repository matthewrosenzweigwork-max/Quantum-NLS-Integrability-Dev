import QuantumNLS.Prop022BetaHSR124
import QuantumNLS.Prop022BD02R122

/-! Apply the reviewed source-Weyl BD-02 theorem to the actual constructed
variational flow, with symplecticity and HS finiteness proved. The resulting
pointwise implementers are not identified with the R122 quadratic propagator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ENNReal
open ContinuousLinearMap Set
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022WeylVacuumR124
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022VariationalR123 Prop022SymplecticR123 Prop022BetaHSR124
open Prop022BD02R122 Ext006KernelHilbertSchmidt Ext006SourceWeylR44a
open Ext006GlobalCovarianceR43a Ext006SourceOrientationR37a Ext006ReorientationR42a
open Ext006PhysQuasifree Ext006PhysFockCoord Ext006NumberPhase
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))

include hM in
/-- Compact-interval bounds follow from the constructed operator-norm
continuous variational evolution. No HS or implementer premise is supplied. -/
theorem actual_beta_finite (s t : ℝ) :
    TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t s) ≠ ⊤ := by
  have hc : Continuous (fun r => (flow B M A hA hB hs u₀ r s).toContinuousLinearMap) :=
    Prop022RealEvolutionR123.evolution_continuous _ (generator_continuous B M A hA hB hs u₀) s
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := s) (b := t)).exists_bound_of_continuousOn hc.continuousOn
  exact (beta_hs_bound B M A hM hA hB hs u₀ s t (max C 1) (le_max_right _ _)
    (fun r hr => (hC r hr).trans (le_max_left _ _))).1

include hM in
/-- The printed t,0 estimate holds throughout [-T,T], including t<0. -/
theorem printed_beta_bound (T P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖(flow B M A hA hB hs u₀ r q).toContinuousLinearMap‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0) ≠ ⊤ ∧
      Real.sqrt ((TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0)).toReal) ≤
        |t| *pairMajorant A*M*P := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hb (r : ℝ) (hr : r ∈ uIcc 0 t) : |r| ≤ T := by
    apply abs_le.mpr
    rcases mem_uIcc.mp hr with hr | hr
    · exact ⟨by linarith, hr.2.trans ((le_abs_self t).trans ht)⟩
    · exact ⟨by linarith [neg_le_abs t], by linarith⟩
  simpa only [sub_zero] using beta_hs_bound B M A hM hA hB hs u₀ 0 t P hP
    (fun r hr => hS r 0 (hb r hr) (by simpa using hT))

include hM in
/-- Actual-flow source-Weyl implementability, pure quasifreeness and number
identity. All BD-02 inputs are discharged for the constructed S(t,s).
This is pointwise in (t,s); the quadratic Hamiltonian evolution identification
is a separate obligation and is deliberately absent from this statement. -/
theorem actual_flow_implementer_vacuum (s t : ℝ) :
    ∃ U : Fock L ≃ₗᵢ[ℂ] Fock L,
      SourceWeylImplementer (flow B M A hA hB hs u₀ t s) U ∧
      PhysicalQuasifreeSource (U vac) ∧ ‖U vac‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (U vac) =
        TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t s) ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (U vac) ≠ ⊤ := by
  let S := flow B M A hA hB hs u₀ t s
  have hsym := flow_symplectic B M A hA hB hs u₀ t s
  have hβ := actual_beta_finite B M A hM hA hB hs u₀ s t
  obtain ⟨_, _, _, _, hall⟩ := PROP022_BD02_forward_implementer_and_vacuum_R122 S hsym hβ
  obtain ⟨U,hAnn,hCre,_,hcov⟩ := original_source_bounded_covariance S hsym hβ
  have hU : SourceWeylImplementer S U := by
    intro f x
    simp only [sourceWeyl_eq]
    exact hcov f 1 x
  have hterminal := hall U hU
  refine ⟨U,hU,?_,?_,hterminal.2.1,hterminal.2.2⟩
  · exact ⟨U,actualA (physicalBasis L) (reorient S),actualB (physicalBasis L) (reorient S),
      actual_blocks_symplectic (physicalBasis L) (reorient S) (reorient_symplectic S hsym),
      hAnn,hCre,rfl⟩
  · rw [LinearIsometryEquiv.norm_map, Ext006VacuumNumberR30a.vac_norm]

include hM in
/-- Quantitative number bound for these actual-flow BD-02 implementers on
any report interval. This does not assert the R122 propagator's covariance. -/
theorem actual_flow_number_bound (T P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖(flow B M A hA hB hs u₀ r q).toContinuousLinearMap‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    ∃ U : Fock L ≃ₗᵢ[ℂ] Fock L,
      SourceWeylImplementer (flow B M A hA hB hs u₀ t 0) U ∧
      PhysicalQuasifreeSource (U vac) ∧ ‖U vac‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (U vac) =
        TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0) ∧
      (numberExpectation (fun n => (n : ℝ≥0∞)) (U vac)).toReal ≤
        (|t| *pairMajorant A*M*P)^2 := by
  obtain ⟨U,hU,hpure,hn,hnum,_⟩ := actual_flow_implementer_vacuum B M A hM hA hB hs u₀ 0 t
  refine ⟨U,hU,hpure,hn,hnum,?_⟩
  rw [hnum]
  have he := (printed_beta_bound B M A hM hA hB hs u₀ T P hP hS t ht).2
  have hsqrt := Real.sq_sqrt (ENNReal.toReal_nonneg :
    0 ≤ (TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0)).toReal)
  have hpa := pairMajorant_nonneg A hA
  have hP0 : 0 ≤ P := by linarith
  nlinarith [Real.sqrt_nonneg ((TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0)).toReal)]

end QuantumNLS.Prop022WeylVacuumR124
#print axioms QuantumNLS.Prop022WeylVacuumR124.actual_flow_implementer_vacuum
#print axioms QuantumNLS.Prop022WeylVacuumR124.printed_beta_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022WeylVacuumR124." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022WeylVacuumR124." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R124 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
