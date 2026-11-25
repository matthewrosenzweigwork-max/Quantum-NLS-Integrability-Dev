import QuantumNLS.FiniteCellGauge

/-! R-D8BB052C group E, incidence prerequisites. The deterministic path has no
repeated source vertex. Its users form a derived finite subset of one full-array
cell, independently of how many exterior arrays exist. -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace QuantumNLS.FiniteCellIncidence
open Occupation OccupationHilbert FiniteCellPartition FiniteCellPaths
variable {N : ℕ}

theorem walk_distance_le (I : Finset ℤ) (K ell fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) :
    ∀ x ∈ walk I K ell fuel m n hc, distance I n x ≤ distance I n m := by
  induction fuel generalizing m with
  | zero =>
    intro x hx
    have he : x = m := by simpa only [walk, List.mem_singleton] using hx
    subst x
    exact le_rfl
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · intro x hx
      have hh : x = m := List.mem_singleton.mp hx
      subst x
      exact le_rfl
    · intro x hx
      rcases List.mem_cons.mp hx with hh | hh
      · subst x
        exact le_rfl
      · have hl := ih _ (next_sameCell I K ell m n hc he) x hh
        have hd := distance_next I K ell m n hc he
        omega

theorem walk_nodup (I : Finset ℤ) (K ell fuel : ℕ) (m n : Arr N)
    (hc : SameCell I K ell m n) : (walk I K ell fuel m n hc).Nodup := by
  induction fuel generalizing m with
  | zero => simp [walk]
  | succ fuel ih =>
    rw [walk]
    split_ifs with he
    · simp
    · apply List.nodup_cons.mpr
      constructor
      · intro hm
        have hl := walk_distance_le I K ell fuel _ n (next_sameCell I K ell m n hc he) m hm
        have hd := distance_next I K ell m n hc he
        omega
      · exact ih _ (next_sameCell I K ell m n hc he)

theorem path_nodup (I : Finset ℤ) (K ell : ℕ) (m : Arr N) : (path I K ell m).Nodup :=
  walk_nodup I K ell _ _ _ _

/-- All starting complete arrays whose prescribed path visits x. -/
def Users (I : Finset ℤ) (K ell : ℕ) (x : Arr N) :=
  {m : Arr N // x ∈ path I K ell m}

theorem users_sameCell (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (x : Arr N)
    (m : Users I K ell x) : SameCell I K ell x m.1 :=
  sameCell_symm I K ell ((path_spec I K ell hell m.1).2.2.2.1 x m.2)

theorem users_finite (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (x : Arr N) :
    Finite (Users I K ell x) := by
  let f : Users I K ell x → Vertices I K ell x :=
    fun m => ⟨m.1, users_sameCell I K ell hell x m⟩
  apply Finite.of_injective f
  intro m n he
  exact Subtype.ext (congrArg (fun v : Vertices I K ell x => v.1) he)

/-- No finite collection of exteriors is supplied or multiplied into the bound. -/
theorem users_card_le_cell (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (x : Arr N) :
    Nat.card (Users I K ell x) ≤ Nat.card (Vertices I K ell x) := by
  let f : Users I K ell x → Vertices I K ell x :=
    fun m => ⟨m.1, users_sameCell I K ell hell x m⟩
  apply Nat.card_le_card_of_injective f
  intro m n he
  exact Subtype.ext (congrArg (fun v : Vertices I K ell x => v.1) he)

theorem users_card_le (I : Finset ℤ) (K ell : ℕ) (hell : 0 < ell) (x : Arr N)
    (hactive : (active I K x).Nonempty) :
    Nat.card (Users I K ell x) ≤ ell ^ (I.card - 1) := by
  calc
    Nat.card (Users I K ell x) ≤ Nat.card (Vertices I K ell x) := users_card_le_cell I K ell hell x
    _ ≤ ell ^ ((active I K x).card - 1) := active_cell_card I K ell hell x hactive
    _ ≤ ell ^ (I.card - 1) := Nat.pow_le_pow_right hell
      (Nat.sub_le_sub_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)

end QuantumNLS.FiniteCellIncidence

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellIncidence.walk_distance_le
#print axioms QuantumNLS.FiniteCellIncidence.walk_nodup
#print axioms QuantumNLS.FiniteCellIncidence.path_nodup
#print axioms QuantumNLS.FiniteCellIncidence.Users
#print axioms QuantumNLS.FiniteCellIncidence.users_sameCell
#print axioms QuantumNLS.FiniteCellIncidence.users_finite
#print axioms QuantumNLS.FiniteCellIncidence.users_card_le_cell
#print axioms QuantumNLS.FiniteCellIncidence.users_card_le

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellIncidence.walk_distance_le,
    ``QuantumNLS.FiniteCellIncidence.walk_nodup,
    ``QuantumNLS.FiniteCellIncidence.path_nodup,
    ``QuantumNLS.FiniteCellIncidence.Users,
    ``QuantumNLS.FiniteCellIncidence.users_sameCell,
    ``QuantumNLS.FiniteCellIncidence.users_finite,
    ``QuantumNLS.FiniteCellIncidence.users_card_le_cell,
    ``QuantumNLS.FiniteCellIncidence.users_card_le]
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
  Lean.logInfo m!"FiniteCellIncidence aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
