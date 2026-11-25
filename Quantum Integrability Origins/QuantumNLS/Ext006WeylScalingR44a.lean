import QuantumNLS.Ext006ExponentialUniquenessR44a

/-! Real smearing rescaling: time t is the source Weyl parameter t f.
This allows uniqueness to quantify over all Weyl implementers, without
adding a stronger all-times covariance hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006WeylScalingR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006AnalyticFieldR42a Ext006EntireFieldR43a Ext006SeriesIdentificationR43a

lemma field_real_smul (r : ℝ) (h : H) :
    field ((r : ℂ) • h)=(r : ℂ) • field h := by
  simp only [field,Ext006InverseGraphsR36a.A_smul,Ext006InverseGraphsR36a.C_smul,
    Complex.star_def,Complex.conj_ofReal,smul_add]

lemma term_real_smul (r : ℝ) (h : H) (v : D) (n : ℕ) :
    exponentialTerm ((r : ℂ) • h) 1 v n=exponentialTerm h r v n := by
  simp only [exponentialTerm,field_real_smul,smul_pow,LinearMap.smul_apply,
    Submodule.coe_smul,smul_smul,Complex.ofReal_one,mul_one]
  congr 1
  rw [mul_pow]
  ring

/-- Exact Weyl-parameter/time rescaling on the whole Fock space. -/
theorem unitary_real_smul (r : ℝ) (h : H) (x : Fock) :
    unitary ((r : ℂ) • h) 1 x=unitary h r x := by
  refine core_dense.induction_on
    (p := fun x => unitary ((r : ℂ) • h) 1 x=unitary h r x) x
    (isClosed_eq (unitary ((r : ℂ) • h) 1).continuous (unitary h r).continuous) ?_
  intro v
  rw [unitary_core,unitary_core]
  exact tsum_congr (term_real_smul r h v.1)

open Ext006KernelHilbertSchmidt Ext006PhysFockCoord Ext006GlobalCovarianceR43a Ext006ExponentialUniquenessR44a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

theorem physical_real_smul (r : ℝ) (f : PhysicalTensor.L2T L)
    (x : Ext025B3PhysicalSectors.Fock L) :
    physicalExponential (r • f) 1 x=physicalExponential f r x := by
  simp only [physicalExponential_apply]
  congr 1
  have hr : (physicalBasis L).repr (r • f)=(r : ℂ) • (physicalBasis L).repr f := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r f,map_smul,RCLike.ofReal_eq_complex_ofReal]
  rw [hr,unitary_real_smul]

/-- Time-one covariance over every source smearing implies covariance at
every real time; there is no extra hypothesis on the implementer. -/
theorem time_one_covariance
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hU : ∀ f x, U (physicalExponential f 1 x)=physicalExponential (S f) 1 (U x)) :
    ImplementsExponential S U := by
  intro f t x
  rw [← physical_real_smul]
  rw [hU,map_smul]
  exact physical_real_smul t (S f) (U x)

end QuantumNLS.Ext006WeylScalingR44a
#print axioms QuantumNLS.Ext006WeylScalingR44a.unitary_real_smul
#print axioms QuantumNLS.Ext006WeylScalingR44a.time_one_covariance

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006WeylScalingR44a." then
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
