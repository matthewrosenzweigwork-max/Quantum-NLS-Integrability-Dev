import QuantumNLS.Ext006NumberPhase
import QuantumNLS.Ext006VacuumRecurrence

/-!
EXT-006: physical application of the weak-vacuum uniqueness theorem.
Author: sol_multi. Coordinates use the fixed free Fourier occupation basis,
not the interacting Bethe basis or a substituted complex structure.
No covariance-to-recurrence or squeezed-state existence theorem is assumed.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.Ext006PhysicalVacuum
open Occupation BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext006VacuumRecurrence

/-- The repository's actual finite-support CCR core in completed all-sector
occupation coordinates. -/
def coreEmbedding : Occupation.FS →ₗ[ℂ] Ext006VacuumRecurrence.Fock :=
  Finsupp.linearCombination ℂ (fun m => lp.single 2 m (1 : ℂ))

theorem coreEmbedding_ket (m : Occ) :
    coreEmbedding (ket m) = lp.single 2 m (1 : ℂ) := by
  simp [coreEmbedding, ket]

theorem inner_core_ket (m : Occ) (x : Ext006VacuumRecurrence.Fock) :
    inner ℂ (coreEmbedding (ket m)) x = x m := by
  rw [coreEmbedding_ket, lp.inner_single_left]
  simp

theorem inner_core_Cre (a : ℤ) (m : Occ) (x : Ext006VacuumRecurrence.Fock) :
    inner ℂ (coreEmbedding (Cre a (ket m))) x =
      (Real.sqrt ((m a : ℝ)+1) : ℂ) * x (m+e a) := by
  rw [Cre_ket, map_smul, inner_smul_left, inner_core_ket]
  simp

theorem inner_core_Ann (a : ℤ) (m : Occ) (x : Ext006VacuumRecurrence.Fock) :
    inner ℂ (coreEmbedding (Ann a (ket m))) x =
      (Real.sqrt (m a : ℝ) : ℂ) * x (m-e a) := by
  rw [Ann_ket, map_smul, inner_smul_left, inner_core_ket]
  simp

/-- The coefficient recurrence is exactly the weak CCR-core annihilation
equation, using the repository's Ann and Cre, including the source sign. -/
theorem weakVacuum_iff_core_matrix_elements (K : Kernel)
    (x : Ext006VacuumRecurrence.Fock) :
    WeakVacuum K x ↔ ∀ a m,
      inner ℂ (coreEmbedding (Cre a (ket m))) x =
        -(∑ b ∈ m.support, K a b * inner ℂ (coreEmbedding (Ann b (ket m))) x) := by
  simp only [inner_core_Cre, inner_core_Ann, WeakVacuum, mul_assoc]

variable {L : ℝ} [Fact (0 < L)]

/-- Literal physical free-occupation coefficient, in its actual total sector. -/
def coefficient (x : Ext025B3PhysicalSectors.Fock L) (m : Occ) : ℂ :=
  occupationCoefficient (freeBasis L (total m)) (x (total m)) ⟨m, rfl⟩

theorem coefficient_sub (x y : Ext025B3PhysicalSectors.Fock L) (m : Occ) :
    coefficient (x-y) m = coefficient x m-coefficient y m := by
  simp [coefficient]

theorem coefficient_smul (c : ℂ) (x : Ext025B3PhysicalSectors.Fock L) (m : Occ) :
    coefficient (c • x) m = c * coefficient x m := by
  simp [coefficient, lp.coeFn_smul]

theorem coefficient_separates (x : Ext025B3PhysicalSectors.Fock L)
    (hx : ∀ m, coefficient x m = 0) : x = 0 := by
  apply lp.ext
  funext n
  change x n = 0
  apply (occupationCoefficient (freeBasis L n)).injective
  rw [map_zero]
  apply lp.ext
  funext m
  rcases m with ⟨m, hm⟩
  change total m = n at hm
  subst n
  exact hx m

/-- The weak annihilation equation on the actual physical Fock space. -/
def PhysicalWeakVacuum (K : Kernel) (x : Ext025B3PhysicalSectors.Fock L) : Prop :=
  WeakVacuum K (coefficient x)

theorem physical_eq_zero {K : Kernel} {x : Ext025B3PhysicalSectors.Fock L}
    (hx : PhysicalWeakVacuum K x) (h0 : coefficient x 0 = 0) : x = 0 :=
  coefficient_separates x (coefficients_zero_of_vacuum_zero hx h0)

theorem physical_vacuum_coefficient_ne_zero {K : Kernel}
    {x : Ext025B3PhysicalSectors.Fock L} (hx : PhysicalWeakVacuum K x) (hn : ‖x‖ = 1) :
    coefficient x 0 ≠ 0 := by
  intro h0
  have hz := physical_eq_zero hx h0
  simp [hz] at hn

/-- Physical counterpart of the recurrence uniqueness theorem.  No truncation
and no equivalence between two independently postulated carriers is assumed. -/
theorem physical_normalized_unique_phase {K : Kernel}
    {x y : Ext025B3PhysicalSectors.Fock L}
    (hx : PhysicalWeakVacuum K x) (hy : PhysicalWeakVacuum K y)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ y = c • x := by
  let c : ℂ := coefficient y 0 / coefficient x 0
  have hd : PhysicalWeakVacuum K (y-c • x) := by
    intro a m
    have hh := WeakVacuum.sub hy (WeakVacuum.smul hx c)
    simpa only [coefficient_sub, coefficient_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] using hh a m
  have h0 : coefficient (y-c • x) 0 = 0 := by
    rw [coefficient_sub, coefficient_smul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (physical_vacuum_coefficient_ne_zero hx hnx)).symm
  have he : y = c • x := sub_eq_zero.mp (physical_eq_zero hd h0)
  refine ⟨c, ?_, he⟩
  have h := congrArg norm he
  rw [norm_smul, hny, hnx, mul_one] at h
  exact h.symm

/-- The PROP-023 number law is identical for any two normalized physical
weak vacua with the same kernel.  This is a proved uniqueness/phase wrapper;
the determinant-normalized representative has not been constructed. -/
theorem «PROP-023-weak-vacuum-number-wrapper» {K : Kernel}
    {x y : Ext025B3PhysicalSectors.Fock L}
    (hx : PhysicalWeakVacuum K x) (hy : PhysicalWeakVacuum K y)
    (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) (w : ℕ → ℝ≥0∞) :
    Ext006NumberPhase.numberExpectation w y = Ext006NumberPhase.numberExpectation w x := by
  obtain ⟨c, hc, he⟩ := physical_normalized_unique_phase hx hy hnx hny
  rw [he]
  exact Ext006NumberPhase.«FIN-CORE-BD-02-phase» c hc x w

end QuantumNLS.Ext006PhysicalVacuum

#print axioms QuantumNLS.Ext006PhysicalVacuum.coefficient_separates
#print axioms QuantumNLS.Ext006PhysicalVacuum.physical_normalized_unique_phase
#print axioms QuantumNLS.Ext006PhysicalVacuum.«PROP-023-weak-vacuum-number-wrapper»

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalVacuum." then
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
  Lean.logInfo m!"Ext006PhysicalVacuum audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
