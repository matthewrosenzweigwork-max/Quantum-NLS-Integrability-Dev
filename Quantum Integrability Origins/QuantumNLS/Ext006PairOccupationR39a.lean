import QuantumNLS.Ext006SymmetricConcatR39a

/-! Two literal mode creators in the actual normalized tensor occupation basis.
Diagonal multiplicities and both bosonic square roots are derived. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PairOccupationR39a
open TensorCarrier OccupationUnitary Occupation Ext006PairPowerWick
open Ext006OccupationConcatR39a Ext006SymmetricConcatR39a

def modePair (i j : ℤ) : Word 2 := ![i,j]

def pairMode {N : ℕ} (m : Arr N) (i j : ℤ) : Arr (2+N) :=
  ⟨m.1 + e j + e i, by
    change total (m.1 + e j + e i) = 2+N
    rw [total_add_e, total_add_e, m.2]
    omega⟩

lemma occupation_modePair (i j : ℤ) : occupation (modePair i j) = e i + e j := by
  classical
  ext a
  simp only [occupation_apply, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_two]
  change (if i = a then 1 else 0) + (if j = a then 1 else 0) = (e i + e j) a
  simp only [Finsupp.add_apply, Finsupp.single_apply]

lemma occupation_pair_rep {N : ℕ} (m : Arr N) (i j : ℤ) :
    occupationArr (Fin.append (modePair i j) (representative m)) = pairMode m i j := by
  apply Subtype.ext
  simp only [occupationArr, occupation_append, occupation_modePair,
    occupation_representative, pairMode]
  abel

/-- Exact two-mode normalization, including i=j. -/
lemma normalization_pairMode {N : ℕ} (m : Arr N) (i j : ℤ) :
    Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) * normalization m =
      (Real.sqrt ((m.1 j : ℝ)+1) * Real.sqrt (((m.1+e j) i : ℝ)+1)) *
        normalization (pairMode m i j) := by
  have h1 := normalization_addMode m j
  have h2 := normalization_addMode (addMode m j) i
  have he : normalization (addMode (addMode m j) i) = normalization (pairMode m i j) := by
    simp only [normalization, addMode, pairMode, show N+1+1=2+N by omega]
  rw [he] at h2
  have h2' : Real.sqrt ((N : ℝ)+2) * normalization (addMode m j) =
      Real.sqrt (((m.1+e j) i : ℝ)+1) * normalization (pairMode m i j) := by
    simpa only [addMode, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h2
  rw [Real.sqrt_mul (by positivity)]
  calc
    _ = Real.sqrt ((N : ℝ)+2) * (Real.sqrt ((N : ℝ)+1) * normalization m) := by ring
    _ = Real.sqrt ((N : ℝ)+2) * (Real.sqrt ((m.1 j : ℝ)+1) * normalization (addMode m j)) := by rw [h1]
    _ = Real.sqrt ((m.1 j : ℝ)+1) * (Real.sqrt ((N : ℝ)+2) * normalization (addMode m j)) := by ring
    _ = _ := by rw [h2']; ring

/-- The projected tensor formula is exactly two normalized core creations.
The tensor on the left is the Fourier form of the physical creation block. -/
theorem two_mode_creation {N : ℕ} (m : Arr N) (i j : ℤ) :
    (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
      symProj ℂ OneParticle (2+N) (concat (symProduct (modePair i j)) (occupationVector m)) =
    ((Real.sqrt ((m.1 j : ℝ)+1) : ℂ) * (Real.sqrt (((m.1+e j) i : ℝ)+1) : ℂ)) •
      occupationVector (pairMode m i j) := by
  rw [symProduct, symProj_concat_symProj_left, symProj_product_occupation,
    symProduct_eq_occupationVector, occupation_pair_rep, smul_smul, smul_smul]
  congr 1
  have hn : (normalization (pairMode m i j) : ℂ) ≠ 0 := by
    exact_mod_cast (normalization_pos (pairMode m i j)).ne'
  have h := congrArg Complex.ofReal (normalization_pairMode m i j)
  push_cast at h
  apply mul_right_cancel₀ hn
  calc
    _ = (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) * (normalization m : ℂ) := by
      field_simp
    _ = _ := h

end QuantumNLS.Ext006PairOccupationR39a

#print axioms QuantumNLS.Ext006PairOccupationR39a.two_mode_creation

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PairOccupationR39a." then
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
  Lean.logInfo m!"Round39a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
