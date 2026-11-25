import QuantumNLS.Ext006ExponentialContinuityR43a
import QuantumNLS.Ext006ForwardFieldR42a

/-! Whole-space covariance for the CONSTRUCTED bounded field exponential at
the original S. Identification with the spectral exponential of the
self-adjoint closure is a separate obligation, explicitly not assumed here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006GlobalCovarianceR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006AnalyticFieldR42a Ext006IdentityCyclicR35a
open Ext006CoreTransportR35a Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a
open Ext006PhysQuasifree Ext006PhysFockCoord Ext006ReorientationR42a
open Ext006OriginalVacuumR42a Ext006ForwardFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a Ext006BoundedExponentialR43a
open Ext006SeriesIdentificationR43a Ext006ExponentialContinuityR43a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Physical whole-space field exponential, transported by the frozen
occupation/physical Fock isometry. -/
def physicalExponential (f : PhysicalTensor.L2T L) (t : ℝ) :
    Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L :=
  (Phi (L := L)).trans ((unitary ((physicalBasis L).repr f) t).trans (Phi (L := L)).symm)

lemma physicalExponential_apply (f : PhysicalTensor.L2T L) (t : ℝ)
    (x : Ext025B3PhysicalSectors.Fock L) :
    physicalExponential f t x = (Phi (L := L)).symm
      (unitary ((physicalBasis L).repr f) t (Phi x)) := rfl

theorem physicalExponential_strong_continuous (f : PhysicalTensor.L2T L)
    (x : Ext025B3PhysicalSectors.Fock L) :
    Continuous (fun t : ℝ => physicalExponential f t x) :=
  (Phi (L := L)).symm.continuous.comp
    (unitary_strong_continuous ((physicalBasis L).repr f) (Phi x))

/-- A bounded global covariance theorem at the original S, with no radius,
core restriction or assumed bounded-extension premise in its conclusion. -/
theorem original_source_bounded_covariance
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) ∧
      HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)) ∧
      (∃ z : ℂ, ‖z‖=1 ∧ U vac=z • originalVacuum S hS hβ) ∧
      ∀ (f : PhysicalTensor.L2T L) (t : ℝ) (x : Ext025B3PhysicalSectors.Fock L),
        U (physicalExponential f t (U.symm x)) = physicalExponential (S f) t x := by
  obtain ⟨U,v,-,-,hA,hC,hvac,hd,hpow⟩ := original_source_forward_field_powers S hS hβ
  refine ⟨U,hA,hC,hvac,?_⟩
  have hcore (f : PhysicalTensor.L2T L) (t : ℝ) (c : List (PhysicalTensor.L2T L) →₀ ℂ) :
      U (physicalExponential f t ((Phi (L := L)).symm
        (evalDomain (physicalBasis L) S.symm v c).1)) =
      physicalExponential (S f) t (U ((Phi (L := L)).symm
        (evalDomain (physicalBasis L) S.symm v c).1)) := by
    let src := evalDomain (physicalBasis L) S.symm v c
    let tgt := evalDomain (physicalBasis L) identitySource (ketD 0) c
    obtain ⟨N,hN⟩ := identity_polynomial_particleBound c
    have htarget := entire_summable ((physicalBasis L).repr (S f)) t tgt hN
    have hterm (n : ℕ) :
        Vtil U (exponentialTerm ((physicalBasis L).repr f) t src n) =
          exponentialTerm ((physicalBasis L).repr (S f)) t tgt n := by
      have he := congrArg (Phi (L := L)) (hpow f c n)
      have ho : Vtil U ((((field ((physicalBasis L).repr f))^n) src).1) =
          (((field ((physicalBasis L).repr (S f)))^n) tgt).1 := by
        simpa only [Vtil_apply,LinearIsometryEquiv.apply_symm_apply] using he
      simp only [exponentialTerm,map_smul,ho]
    have hinv (n : ℕ) :
        (Vtil U).symm (exponentialTerm ((physicalBasis L).repr (S f)) t tgt n) =
          exponentialTerm ((physicalBasis L).repr f) t src n := by
      rw [← hterm n,LinearIsometryEquiv.symm_apply_apply]
    have hsum := (Vtil U).symm.toLinearIsometry.toContinuousLinearMap.hasSum htarget.hasSum
    change HasSum (fun n => (Vtil U).symm
      (exponentialTerm ((physicalBasis L).repr (S f)) t tgt n))
      ((Vtil U).symm (∑' n, exponentialTerm ((physicalBasis L).repr (S f)) t tgt n)) at hsum
    simp only [hinv] at hsum
    have he := congrArg (Vtil U) hsum.tsum_eq
    rw [LinearIsometryEquiv.apply_symm_apply] at he
    have hf := congrArg (Phi (L := L)).symm he
    have hzero := hpow f c 0
    simp only [pow_zero,Module.End.one_apply] at hzero
    rw [hzero]
    simp only [physicalExponential_apply,LinearIsometryEquiv.apply_symm_apply]
    rw [unitary_series _ _ src hsum.summable,unitary_series _ _ tgt htarget]
    simpa only [Vtil_apply,LinearIsometryEquiv.symm_apply_apply,exponential] using hf
  have hglobal (f : PhysicalTensor.L2T L) (t : ℝ) (y : Ext025B3PhysicalSectors.Fock L) :
      U (physicalExponential f t y) = physicalExponential (S f) t (U y) := by
    refine hd.induction_on
      (p := fun y => U (physicalExponential f t y)=physicalExponential (S f) t (U y)) y
      (isClosed_eq (U.continuous.comp (physicalExponential f t).continuous)
        ((physicalExponential (S f) t).continuous.comp U.continuous)) ?_
    exact hcore f t
  intro f t x
  rw [hglobal,LinearIsometryEquiv.apply_symm_apply]

end QuantumNLS.Ext006GlobalCovarianceR43a
#print axioms QuantumNLS.Ext006GlobalCovarianceR43a.original_source_bounded_covariance

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006GlobalCovarianceR43a." then
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
  Lean.logInfo m!"Round43a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
