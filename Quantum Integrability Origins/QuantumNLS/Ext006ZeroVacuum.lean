import QuantumNLS.Ext006PhysicalVacuum
import QuantumNLS.Ext006FredholmTracePower

/-! The zero-kernel physical instance. This does not assert the nonzero-kernel
squeezed exponential, quasifree representation, or number law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Ext006ZeroVacuum
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext006NumberPhase Ext006FredholmTracePower
variable (L : ℝ) [Fact (0 < L)]

/-- The canonical zero-particle tensor in the physical bosonic sector. -/
def sectorVacuum : HN L 0 :=
  ⟨htpow 0 (0 : L2T L), htpow_mem_symSector 0 0⟩

theorem sectorVacuum_norm : ‖sectorVacuum L‖ = 1 := by
  change ‖(htpow 0 (0 : L2T L) : HilbertTensorPower ℂ (L2T L) 0)‖ = 1
  rw [norm_htpow]
  simp

/-- Vacuum in the actual completed physical Fock direct sum. -/
def vacuum : Fock L := lp.single 2 0 (sectorVacuum L)

theorem vacuum_norm : ‖vacuum L‖ = 1 := by
  rw [vacuum, lp.norm_single (by norm_num), sectorVacuum_norm]

/-- Every nonnegative number observable has its vacuum value, even for
unbounded weights. -/
theorem vacuum_numberExpectation (w : ℕ → ℝ≥0∞) :
    numberExpectation w (vacuum L) = w 0 := by
  classical
  unfold numberExpectation
  rw [tsum_eq_single 0]
  · change w 0 * ENNReal.ofReal (‖(vacuum L) 0‖ ^ 2) = w 0
    have h : (vacuum L) 0 = sectorVacuum L := by simp [vacuum, lp.single_apply]
    rw [h, sectorVacuum_norm]
    simp
  · intro n hn
    simp [vacuum, lp.single_apply, hn]

theorem vacuum_mean : numberExpectation (fun n => n) (vacuum L) = 0 := by
  rw [vacuum_numberExpectation]
  simp

theorem vacuum_exponentialMoment (Q : ℝ) : exponentialMoment Q (vacuum L) = 1 := by
  rw [exponentialMoment, vacuum_numberExpectation]
  simp

/-- The physical vacuum satisfies the zero-kernel weak annihilation
condition on every finite occupation. -/
theorem vacuum_weak : Ext006PhysicalVacuum.PhysicalWeakVacuum (fun _ _ => 0) (vacuum L) := by
  intro a m
  have h : Occupation.total (m + Occupation.e a) ≠ 0 := by
    rw [Occupation.total_add_e]
    exact Nat.succ_ne_zero _
  simp [Ext006PhysicalVacuum.coefficient, vacuum, lp.single_apply, h]

/-- The full zero-kernel physical weak vacuum is unique up to phase. -/
theorem zero_kernel_classification (x : Fock L)
    (hx : Ext006PhysicalVacuum.PhysicalWeakVacuum (fun _ _ => 0) x) (hn : ‖x‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ x = c • vacuum L :=
  Ext006PhysicalVacuum.physical_normalized_unique_phase (vacuum_weak L) hx (vacuum_norm L) hn

/-- Exact number law for every normalized physical zero-kernel weak vacuum. -/
theorem zero_kernel_number_law (x : Fock L)
    (hx : Ext006PhysicalVacuum.PhysicalWeakVacuum (fun _ _ => 0) x) (hn : ‖x‖ = 1)
    (w : ℕ → ℝ≥0∞) : numberExpectation w x = w 0 := by
  obtain ⟨c, hc, rfl⟩ := zero_kernel_classification L x hx hn
  rw [«FIN-CORE-BD-02-phase» c hc, vacuum_numberExpectation]

/-- The trace-power Fredholm determinant and its positive fourth root at zero. -/
theorem zero_determinant : fredholmDet (0 : L2T L →L[ℂ] L2T L) = 1 ∧
    fourthRoot (0 : L2T L →L[ℂ] L2T L) = 1 := by
  have hz : TraceClass.traceNorm (0 : L2T L →L[ℂ] L2T L) = 0 :=
    (TraceClass.traceNorm_eq_zero_iff _).2 rfl
  have ht : tracePowerTerm (0 : L2T L →L[ℂ] L2T L) = 0 := by
    funext n
    simp [tracePowerTerm, hz]
  simp [fredholmDet, fourthRoot, ht]

end QuantumNLS.Ext006ZeroVacuum

#print axioms QuantumNLS.Ext006ZeroVacuum.vacuum_norm
#print axioms QuantumNLS.Ext006ZeroVacuum.vacuum_numberExpectation
#print axioms QuantumNLS.Ext006ZeroVacuum.vacuum_mean
#print axioms QuantumNLS.Ext006ZeroVacuum.vacuum_exponentialMoment
#print axioms QuantumNLS.Ext006ZeroVacuum.vacuum_weak
#print axioms QuantumNLS.Ext006ZeroVacuum.zero_kernel_classification
#print axioms QuantumNLS.Ext006ZeroVacuum.zero_kernel_number_law
#print axioms QuantumNLS.Ext006ZeroVacuum.zero_determinant

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ZeroVacuum." then
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
  Lean.logInfo m!"Ext006ZeroVacuum audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
