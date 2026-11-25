import QuantumNLS.Local005FlattenD

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

/-- The full path includes its two endpoints. -/
def flatNode {ι : Type*} {k : ℕ} (q : Fin k → ι) (i j : ι) : Fin (k + 2) → ι :=
  Fin.cons (α := fun _ => ι) j (Fin.snoc (α := fun _ => ι) q i)

theorem flatTerm_node {ι : Type*} (K : ℕ → ι → ι → ℂ) (k : ℕ)
    (i j : ι) (q : Fin k → ι) :
    flatTerm K k i j q = ∏ t : Fin (k + 1),
      K t.val (flatNode q i j t.succ) (flatNode q i j t.castSucc) := by
  apply Finset.prod_congr rfl
  intro t _
  simp only [flatNode, Fin.cons_succ, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc]

theorem componentAfter_one_comp (t : ℕ) (j : Fin 2) :
    componentAfter 1 (componentAfter t j) = componentAfter (t + 1) j := by
  apply Fin.ext
  simp only [componentAfter]
  omega

/-- Nonzero physical words force every component, including the output component. -/
theorem flatTerm_forced_components {L κ : ℝ} [Fact (0 < L)] (n : ℤ) (z : ℂ)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2 × ℤ) (q : Fin k → Fin 2 × ℤ)
    (hnz : flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j q ≠ 0) :
    i.1 = componentAfter (k + 1) j.1 ∧
      ∀ t, (q t).1 = componentAfter (t.val + 1) j.1 := by
  rw [flatTerm_node] at hnz
  have hs (t : Fin (k + 1)) :
      (flatNode q i j t.succ).1 = componentAfter 1 (flatNode q i j t.castSucc).1 := by
    have hf := Finset.prod_ne_zero_iff.mp hnz t (Finset.mem_univ t)
    by_contra h
    exact hf (by simp only [sourceFactorEntry, if_neg h])
  have hall : ∀ t : Fin (k + 2), (flatNode q i j t).1 = componentAfter t.val j.1 := by
    intro t
    induction t using Fin.induction with
    | zero => simp [flatNode, componentAfter_zero]
    | succ t ih => rw [hs t, ih, componentAfter_one_comp]; rfl
  constructor
  · simpa only [flatNode, Fin.cons_last, Fin.snoc_last, Fin.val_last] using hall (Fin.last (k + 1))
  · intro t
    simpa only [flatNode, Fin.cons_succ, Fin.snoc_castSucc, Fin.val_succ,
      Fin.val_castSucc] using hall t.castSucc.succ

/-- Physical Fourier modes are represented by their shifts in the forced component. -/
def shiftPath {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) (t : Fin k) : Fin 2 × ℤ :=
  (componentAfter (t.val + 1) j, sourceModeIndex (componentAfter (t.val + 1) j) (q t))

def unshiftPath {k : ℕ} (q : Fin k → Fin 2 × ℤ) (t : Fin k) : ℤ :=
  sourceModeIndex (q t).1 (q t).2

theorem unshift_shift {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) :
    unshiftPath (shiftPath j q) = q := by
  funext t
  exact sourceModeIndex_twice _ _

theorem shift_unshift {k : ℕ} (j : Fin 2) (q : Fin k → Fin 2 × ℤ)
    (hc : ∀ t, (q t).1 = componentAfter (t.val + 1) j) :
    shiftPath j (unshiftPath q) = q := by
  funext t
  apply Prod.ext
  · exact (hc t).symm
  · change sourceModeIndex _ (sourceModeIndex (q t).1 (q t).2) = (q t).2
    rw [← hc t, sourceModeIndex_twice]

theorem shiftPath_injective {k : ℕ} (j : Fin 2) :
    Function.Injective (shiftPath (k := k) j) :=
  Function.LeftInverse.injective (unshift_shift j)

/-- Every nonzero physical path belongs to this explicit shift parametrization. -/
theorem nonzero_path_in_shift_range {L κ : ℝ} [Fact (0 < L)] (n : ℤ) (z : ℂ)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2 × ℤ) (q : Fin k → Fin 2 × ℤ)
    (hnz : flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j q ≠ 0) :
    q ∈ Set.range (shiftPath j.1) := by
  exact ⟨unshiftPath q, shift_unshift j.1 q
    (flatTerm_forced_components n z u k i j q hnz).2⟩

/-- Removing the impossible component paths is an exact reindexing of the tsum. -/
theorem flatTerm_shift_tsum {L κ : ℝ} [Fact (0 < L)] (n : ℤ) (z : ℂ)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2 × ℤ) :
    (∑' q, flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j q) =
      ∑' q : Fin k → ℤ,
        flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j (shiftPath j.1 q) := by
  symm
  apply (shiftPath_injective j.1).tsum_eq
  intro q hq
  exact nonzero_path_in_shift_range n z u k i j q hq

/-- Absolute convergence of the shift series supplies absolute convergence of the full path. -/
theorem flatTerm_shift_summable_iff {L κ : ℝ} [Fact (0 < L)] (n : ℤ) (z : ℂ)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2 × ℤ) :
    Summable (fun q : Fin k → ℤ =>
      flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j (shiftPath j.1 q)) ↔
      Summable (flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j) := by
  have hz : ∀ q ∉ Set.range (shiftPath (k := k) j.1),
      flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j q = 0 := by
    intro q hq
    by_contra hnz
    exact hq (nonzero_path_in_shift_range n z u k i j q hnz)
  simpa only [Function.comp_def] using (shiftPath_injective j.1).summable_iff hz

#print axioms flatTerm_shift_tsum
#print axioms flatTerm_shift_summable_iff

#print axioms flatTerm_forced_components
#print axioms unshift_shift
#print axioms shift_unshift
#print axioms nonzero_path_in_shift_range
end QuantumNLS.Local005.SourceD

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005.SourceD." ||
        n.toString.startsWith "_private.QuantumNLS.Local005" then
      pending := pending.push n
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
  Lean.logInfo m!"Local005PathModesD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
