import QuantumNLS.Local005SourceWordsC

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC

/-- A degree k+1 word has k intermediate indices, in input-to-output order. -/
def flatTerm {ι : Type*} (K : ℕ → ι → ι → ℂ) (k : ℕ) (i j : ι)
    (q : Fin k → ι) : ℂ :=
  ∏ t : Fin (k + 1), K t.val (Fin.snoc (α := fun _ => ι) q i t) (Fin.cons (α := fun _ => ι) j q t)

theorem flatTerm_zero {ι : Type*} (K : ℕ → ι → ι → ℂ) (i j : ι)
    (q : Fin 0 → ι) : flatTerm K 0 i j q = K 0 i j := by
  simp [flatTerm, Fin.snoc]

theorem flatTerm_snoc {ι : Type*} (K : ℕ → ι → ι → ℂ) (k : ℕ)
    (i j m : ι) (q : Fin k → ι) :
    flatTerm K (k + 1) i j (Fin.snoc (α := fun _ => ι) q m) = K (k + 1) i m * flatTerm K k m j q := by
  unfold flatTerm
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_last, Fin.cons_last]
  have he : (∏ t : Fin (k + 1),
      K t.castSucc.val (Fin.snoc (α := fun _ => ι) (Fin.snoc (α := fun _ => ι) q m) i t.castSucc)
        (Fin.cons (α := fun _ => ι) j (Fin.snoc (α := fun _ => ι) q m) t.castSucc)) =
      ∏ t : Fin (k + 1), K t.val (Fin.snoc (α := fun _ => ι) q m t) (Fin.cons (α := fun _ => ι) j q t) := by
    apply Finset.prod_congr rfl
    intro t _
    rw [Fin.snoc_castSucc, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc]
    rfl
  rw [he, mul_comm]
  rfl

/-- Fubini for a word is justified by the full path's summability. This auxiliary
lemma adds no assumption to a source theorem: the source path majorant must supply it. -/
theorem matrixPrefix_flat_of_summable
    (K : ℕ → (Fin 2 × ℤ) → (Fin 2 × ℤ) → ℂ) (k : ℕ) (i j : Fin 2 × ℤ)
    (hs : Summable (flatTerm K k i j)) :
    matrixPrefix K (k + 1) i j = ∑' q : Fin k → Fin 2 × ℤ, flatTerm K k i j q := by
  let ι := Fin 2 × ℤ
  induction k generalizing i j with
  | zero =>
    simp only [matrixPrefix]
    simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]
    simp [flatTerm_zero]
  | succ k ih =>
    let e := Fin.snocEquiv (fun _ : Fin (k + 1) => ι)
    have hp : Summable (fun p : ι × (Fin k → ι) =>
        K (k + 1) i p.1 * flatTerm K k p.1 j p.2) := by
      have hp0 := e.summable_iff.mpr hs
      exact hp0.congr (fun p => flatTerm_snoc K k i j p.1 p.2)
    rw [show (∑' q, flatTerm K (k + 1) i j q) =
        ∑' p : ι × (Fin k → ι), K (k + 1) i p.1 * flatTerm K k p.1 j p.2 from
      (e.tsum_eq _).symm.trans (tsum_congr fun p => flatTerm_snoc K k i j p.1 p.2)]
    rw [hp.tsum_prod]
    change (∑' m, K (k + 1) i m * matrixPrefix K (k + 1) m j) = _
    apply tsum_congr
    intro m
    by_cases hm : K (k + 1) i m = 0
    · simp [hm]
    · have hf : Summable (flatTerm K k m j) :=
        (summable_mul_left_iff hm).mp (hp.prod_factor m)
      rw [ih m j hf]
      exact (tsum_mul_left).symm

#print axioms flatTerm_snoc
#print axioms matrixPrefix_flat_of_summable
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
  Lean.logInfo m!"Local005FlattenD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
