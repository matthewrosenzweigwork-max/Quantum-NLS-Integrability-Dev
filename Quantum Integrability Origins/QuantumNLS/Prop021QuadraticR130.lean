import QuantumNLS.Prop021QuadraticBindingR129
import QuantumNLS.Prop021DisplacementR129
import QuantumNLS.Prop021RatesR128
import QuantumNLS.Prop022WeylVacuumR124
import QuantumNLS.Prop022OVacuum

/-! Bind the reviewed torus quadratic covariance and vacuum conclusions to
one and the same R127 evolution selected in R129. The full PROP-022 named
input is retained in the review record; no general-H scope is asserted here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop021QuadraticR130
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022FactorialCoefficientsR115 Prop022FockPropagatorR122
open Prop022VariationalR123 Prop022OVacuum Prop022OClassical Prop022OCovariance
open Ext006KernelHilbertSchmidt Ext006PhysQuasifree Ext006NumberPhase Ext006PhysFockCoord
open Prop021QuadraticBindingR129 Prop021DisplacementR129 Prop021RatesR128
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "U" => singleEvolution B M A hM hA hB hs u₀
local notation "V" => propagator B M A hM hA hB hs u₀
local notation "ξ" => fluctuation B M A hM hA hB hs u₀

/-- The selected cross-j evolution has the actual unitary inverse. -/
theorem single_unitary (s t : ℝ) (x : Fock L) : U s t x = V s t x :=
  singleEvolution_eq B M A hM hA hB hs u₀ s t x

/-- Exact covariance in Q7B's displacement convention, for the actual
quadratic evolution, at the ORIGINAL real variational flow. -/
theorem quadratic_displacement (s t : ℝ) (v : L2T L) (x : Fock L) :
    U s t (displacement v (U t s x)) =
      displacement (flow B M A hA hB hs u₀ t s v) x := by
  have hi : U t s x = (V s t).symm x := by
    apply (V s t).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp only [propagator_apply, singleEvolution_eq, evolution_comp, evolution_self]
  rw [hi, single_unitary]
  exact printed_of_source (Sp B M A hA hB hs u₀ t s) (V s t)
    (propagator_implements B M A hM hA hB hs u₀ s t)
    (flow B M A hA hB hs u₀ t s) (Sp_negI B M A hA hB hs u₀ t s) v x

/-- The SAME strong vacuum curve is pure quasifree and has the ORIGINAL
beta block's exact number expectation. No unrelated implementer is chosen. -/
theorem quadratic_vacuum (t : ℝ) :
    PhysicalQuasifreeSource (ξ t) ∧ ‖ξ t‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (ξ t) =
        TraceClass.hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t 0) ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (ξ t) ≠ ⊤ := by
  have hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L)
      (Sp B M A hA hB hs u₀ t 0)) ≠ ⊤ := by
    rw [hsSq_beta_Sp]
    exact Prop022WeylVacuumR124.actual_beta_finite B M A hM hA hB hs u₀ 0 t
  have h := implementer_vacuum (Sp B M A hA hB hs u₀ t 0)
    (Sp_symplectic B M A hA hB hs u₀ t 0) hβ (V 0 t)
    (propagator_implements B M A hM hA hB hs u₀ 0 t)
  have he : ξ t = V 0 t vac := single_unitary B M A hM hA hB hs u₀ 0 t vac
  rw [he, hsSq_beta_Sp] at *
  exact h

/-- Uniform depletion on [-T,T] with precisely Q=1+C_A²T²M²P². -/
theorem quadratic_depletion (T P : ℝ) (hT : 0 ≤ T) (hP : 1 ≤ P)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖(flow B M A hA hB hs u₀ r q).toContinuousLinearMap‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    (numberExpectation (fun n => (n : ℝ≥0∞)) (ξ t)).toReal ≤
      numberParameter (Prop022FactorialMajorantR115.pairMajorant A) T M P - 1 := by
  obtain ⟨_,_,hnum,_⟩ := quadratic_vacuum B M A hM hA hB hs u₀ t
  rw [hnum]
  have hb := (Prop022WeylVacuumR124.printed_beta_bound B M A hM hA hB hs u₀ T P hP hS t ht).2
  have hc := Prop022FactorialMajorantR115.pairMajorant_nonneg A hA
  have h := beta_square_le hc hT hM (by linarith : 0 ≤ P)
    (Real.sqrt_nonneg _) ht hb
  rwa [Real.sq_sqrt ENNReal.toReal_nonneg] at h

end QuantumNLS.Prop021QuadraticR130
#print axioms QuantumNLS.Prop021QuadraticR130.quadratic_displacement
#print axioms QuantumNLS.Prop021QuadraticR130.quadratic_vacuum
#print axioms QuantumNLS.Prop021QuadraticR130.quadratic_depletion

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021QuadraticR130"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R130 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
