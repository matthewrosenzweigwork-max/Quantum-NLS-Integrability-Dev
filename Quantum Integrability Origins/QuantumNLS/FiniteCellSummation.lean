import QuantumNLS.FiniteCellIncidence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! R-D8BB052C E2 countable incidence summation, with summability explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical
namespace QuantumNLS.FiniteCellSummation
open Occupation OccupationHilbert FiniteCellPartition FiniteCellPaths FiniteCellIncidence

/-- Finite row sums and uniformly bounded finite columns preserve summability.
The index types need not have a finite list of exterior configurations. -/
theorem bounded_incidence {α β : Type*} (p : α → Finset β) (B : ℕ)
    (hfiber : ∀ x, Finite {m : α // x ∈ p m})
    (hcard : ∀ x, Nat.card {m : α // x ∈ p m} ≤ B)
    (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) (hs : Summable f) :
    Summable (fun m => ∑ x ∈ p m, f x) ∧
      (∑' m, ∑ x ∈ p m, f x) ≤ (B : ℝ) * ∑' x, f x := by
  have hpartial : ∀ M : Finset α,
      ∑ m ∈ M, ∑ x ∈ p m, f x ≤ (B : ℝ) * ∑' x, f x := by
    intro M
    let V := M.biUnion p
    have hsubset : ∀ m ∈ M, p m ⊆ V := by
      intro m hm x hx
      exact Finset.mem_biUnion.mpr ⟨m, hm, hx⟩
    have heq : (∑ m ∈ M, ∑ x ∈ p m, f x) =
        ∑ x ∈ V, ((M.filter (fun m => x ∈ p m)).card : ℝ) * f x := by
      calc
        _ = ∑ m ∈ M, ∑ x ∈ V, if x ∈ p m then f x else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [← Finset.sum_filter]
          congr 1
          ext x
          simp only [Finset.mem_filter]
          exact ⟨fun hx => ⟨hsubset m hm hx, hx⟩, fun hx => hx.2⟩
        _ = ∑ x ∈ V, ∑ m ∈ M, if x ∈ p m then f x else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.sum_filter]
          simp
    have hc : ∀ x, (M.filter (fun m => x ∈ p m)).card ≤ B := by
      intro x
      let := hfiber x
      let j : {m // m ∈ M.filter (fun m => x ∈ p m)} → {m : α // x ∈ p m} :=
        fun m => ⟨m.1, (Finset.mem_filter.mp m.2).2⟩
      have hj : Function.Injective j := by
        intro m n he
        exact Subtype.ext (congrArg (fun v : {m : α // x ∈ p m} => v.1) he)
      have hh := Nat.card_le_card_of_injective j hj
      exact (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hh : (M.filter (fun m => x ∈ p m)).card ≤
        Nat.card {m : α // x ∈ p m}).trans (hcard x)
    rw [heq]
    calc
      _ ≤ ∑ x ∈ V, (B : ℝ) * f x := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc x) (hf x)
      _ = (B : ℝ) * ∑ x ∈ V, f x := (Finset.mul_sum _ _ _).symm
      _ ≤ (B : ℝ) * ∑' x, f x :=
        mul_le_mul_of_nonneg_left (hs.sum_le_tsum V (fun x _ => hf x)) (Nat.cast_nonneg B)
  have hn : ∀ m, 0 ≤ ∑ x ∈ p m, f x := fun m => Finset.sum_nonneg (fun x _ => hf x)
  exact ⟨summable_of_sum_le hn hpartial, Real.tsum_le_of_sum_le hn hpartial⟩

variable {N : ℕ}

/-- The empty-active cell is a singleton, so it causes no exception to E1. -/
theorem users_card_le_all (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (x : Arr N) :
    Nat.card (Users I K ell x) ≤ ell ^ (I.card - 1) := by
  by_cases ha : (active I K x).Nonempty
  · exact users_card_le I K ell hell x ha
  · have he : active I K x = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hcell := inactive_cell_singleton I K ell x he
    have hu : ∀ m : Users I K ell x, m.1 = x := by
      intro m
      have hm : m.1 ∈ cell I K ell x := users_sameCell I K ell hell x m
      rw [hcell] at hm
      exact Set.mem_singleton_iff.mp hm
    let j : Users I K ell x → Unit := fun _ => ()
    have hj : Function.Injective j := by
      intro m n _
      exact Subtype.ext ((hu m).trans (hu n).symm)
    calc
      Nat.card (Users I K ell x) ≤ Nat.card Unit := Nat.card_le_card_of_injective j hj
      _ = 1 := by simp
      _ ≤ ell ^ (I.card - 1) := Nat.one_le_pow _ _ hell

/-- Apply finite-column incidence to the full canonical paths, over all arrays. -/
theorem path_energy_summable (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell)
    (f : Arr N → ℝ) (hf : ∀ x, 0 ≤ f x) (hs : Summable f) :
    Summable (fun m => ∑ x ∈ (path I K ell m).toFinset, f x) ∧
      (∑' m, ∑ x ∈ (path I K ell m).toFinset, f x) ≤
        (ell ^ (I.card - 1) : ℕ) * ∑' x, f x := by
  apply bounded_incidence (fun m => (path I K ell m).toFinset) (ell ^ (I.card - 1))
  · intro x
    simpa only [Users, List.mem_toFinset] using users_finite I K ell hell x
  · intro x
    simpa only [Users, List.mem_toFinset] using users_card_le_all I K ell hell x
  · exact hf
  · exact hs

end QuantumNLS.FiniteCellSummation

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellSummation.bounded_incidence
#print axioms QuantumNLS.FiniteCellSummation.users_card_le_all
#print axioms QuantumNLS.FiniteCellSummation.path_energy_summable

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellSummation.bounded_incidence,
    ``QuantumNLS.FiniteCellSummation.users_card_le_all,
    ``QuantumNLS.FiniteCellSummation.path_energy_summable]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellSummation aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
