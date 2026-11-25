import QuantumNLS.OccupationHilbert

/-!
EXT-006 / FIN-CORE-BD-02: uniqueness part of the squeezed-vacuum problem.
Author: sol_multi.  This is the full completed occupation coefficient space,
with the same occupation arrays and sqrt coefficients as Occupation.Ann/Cre.
No existence or determinant formula is assumed or asserted.  The weak
coefficient equation is meaningful without an unbounded-operator domain:
the creation contribution at a fixed finite occupation is a finite sum.
-/
noncomputable section
set_option autoImplicit false
namespace QuantumNLS.Ext006VacuumRecurrence
open Occupation OccupationHilbert

abbrev Fock := L2 Occ
abbrev Kernel := ℤ → ℤ → ℂ

/-- Weak coefficients of (a_a + sum_b K_ab a_b^*) x = 0.
The plus sign corresponds to exp(-a^*(K)/2) Omega.
This equation is a definition of the weak annihilation condition, not a
definition of quasifree state or an implementability assumption. -/
def WeakVacuum (K : Kernel) (x : Occ → ℂ) : Prop :=
  ∀ (a : ℤ) (m : Occ),
    (Real.sqrt ((m a : ℝ) + 1) : ℂ) * x (m + e a) =
      -(∑ b ∈ m.support, K a b * (Real.sqrt (m b : ℝ) : ℂ) * x (m - e b))

theorem WeakVacuum.sub {K : Kernel} {x y : Occ → ℂ}
    (hx : WeakVacuum K x) (hy : WeakVacuum K y) : WeakVacuum K (x-y) := by
  intro a m
  change _ * (x (m+e a)-y (m+e a)) =
    -(∑ b ∈ m.support, K a b * _ * (x (m-e b)-y (m-e b)))
  simp only [mul_sub, Finset.sum_sub_distrib, hx a m, hy a m]
  ring

theorem WeakVacuum.smul {K : Kernel} {x : Occ → ℂ}
    (hx : WeakVacuum K x) (c : ℂ) : WeakVacuum K (c • x) := by
  intro a m
  change _ * (c * x (m+e a)) =
    -(∑ b ∈ m.support, K a b * _ * (c * x (m-e b)))
  calc
    _ = c * ((Real.sqrt ((m a : ℝ)+1) : ℂ) * x (m+e a)) := by ring
    _ = c * (-(∑ b ∈ m.support, K a b * (Real.sqrt (m b : ℝ) : ℂ) * x (m-e b))) :=
      congrArg (c * ·) (hx a m)
    _ = _ := by rw [mul_neg, Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring

/-- The recurrence has no nonzero solution with zero vacuum coefficient.
No symmetry, HS or strict-contraction premise is needed for this uniqueness
statement; those premises are needed for the still-open construction. -/
theorem coefficients_zero_of_vacuum_zero {K : Kernel} {x : Occ → ℂ}
    (hx : WeakVacuum K x) (h0 : x 0 = 0) : ∀ n, x n = 0 := by
  have hz : ∀ k : ℕ, ∀ n : Occ, total n = k → x n = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hnk
      by_cases hn : n = 0
      · simpa only [hn] using h0
      obtain ⟨a, ha⟩ : ∃ a, n a ≠ 0 := by
        by_contra! h
        exact hn (Finsupp.ext h)
      have ha' : 1 ≤ n a := Nat.one_le_iff_ne_zero.mpr ha
      have htotal := total_sub_e ha'
      have hs : (∑ b ∈ (n-e a).support,
          K a b * (Real.sqrt ((n-e a) b : ℝ) : ℂ) * x ((n-e a)-e b)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb' : 1 ≤ (n-e a) b :=
          Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
        have ht := total_sub_e hb'
        have hlt : total ((n-e a)-e b) < k := by omega
        rw [ih _ hlt _ rfl, mul_zero]
      have he := hx a (n-e a)
      rw [shift_sub_add ha', hs, neg_zero] at he
      have hp : 0 < Real.sqrt (((n-e a) a : ℝ)+1) :=
        Real.sqrt_pos.mpr (by positivity)
      have hnz : (Real.sqrt (((n-e a) a : ℝ)+1) : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne'
      exact (mul_eq_zero.mp he).resolve_left hnz
  exact fun n => hz (total n) n rfl

theorem eq_zero_of_vacuum_zero {K : Kernel} {x : Fock}
    (hx : WeakVacuum K x) (h0 : x 0 = 0) : x = 0 := by
  apply lp.ext
  funext n
  exact coefficients_zero_of_vacuum_zero hx h0 n

/-- All coefficients of a weak squeezed vacuum are determined by its
vacuum coefficient, on the actual completed occupation Hilbert space. -/
theorem vacuum_coefficient_injective {K : Kernel} {x y : Fock}
    (hx : WeakVacuum K x) (hy : WeakVacuum K y) (h0 : x 0 = y 0) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_vacuum_zero (hx.sub hy)
  change x 0-y 0 = 0
  exact sub_eq_zero.mpr h0

theorem vacuum_coefficient_ne_zero {K : Kernel} {x : Fock}
    (hx : WeakVacuum K x) (hn : ‖x‖ = 1) : x 0 ≠ 0 := by
  intro h0
  have hz := eq_zero_of_vacuum_zero hx h0
  simp [hz] at hn

/-- A normalized weak squeezed vacuum is unique up to scalar phase.
The scalar is constructed as the ratio of vacuum coefficients. -/
theorem normalized_unique_phase {K : Kernel} {x y : Fock}
    (hx : WeakVacuum K x) (hy : WeakVacuum K y) (hnx : ‖x‖ = 1) (hny : ‖y‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ y = c • x := by
  let c : ℂ := y 0 / x 0
  have he : y = c • x := by
    apply vacuum_coefficient_injective hy (hx.smul c)
    change y 0 = c * x 0
    exact (div_mul_cancel₀ _ (vacuum_coefficient_ne_zero hx hnx)).symm
  refine ⟨c, ?_, he⟩
  have hn := congrArg norm he
  rw [norm_smul, hnx, hny, mul_one] at hn
  exact hn.symm

/-- A concrete normalized zero-squeeze vacuum. -/
def vacuum : Fock := lp.single 2 (0 : Occ) (1 : ℂ)

theorem vacuum_norm : ‖vacuum‖ = 1 := by
  rw [vacuum, lp.norm_single (by norm_num)]
  exact norm_one

theorem vacuum_weak : WeakVacuum (fun _ _ => 0) vacuum := by
  intro a m
  simp [vacuum, lp.single_apply]

/-- The zero-kernel case is actually classified, without assuming a vacuum
formula.  The nonzero-kernel determinant/exponential case remains open. -/
theorem zero_kernel_classification (x : Fock) (hx : WeakVacuum (fun _ _ => 0) x)
    (hn : ‖x‖ = 1) : ∃ c : ℂ, ‖c‖ = 1 ∧ x = c • vacuum :=
  normalized_unique_phase vacuum_weak hx vacuum_norm hn

end QuantumNLS.Ext006VacuumRecurrence

#print axioms QuantumNLS.Ext006VacuumRecurrence.eq_zero_of_vacuum_zero
#print axioms QuantumNLS.Ext006VacuumRecurrence.vacuum_coefficient_injective
#print axioms QuantumNLS.Ext006VacuumRecurrence.normalized_unique_phase
#print axioms QuantumNLS.Ext006VacuumRecurrence.zero_kernel_classification

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006VacuumRecurrence." then
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
  Lean.logInfo m!"Ext006VacuumRecurrence audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
