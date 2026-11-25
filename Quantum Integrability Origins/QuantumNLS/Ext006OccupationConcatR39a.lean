import QuantumNLS.Ext006PairPowerWick
import QuantumNLS.OccupationUnitary

/-! Literal occupation normalization for completed tensor concatenation.
No physical/core action or exponential identity is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006OccupationConcatR39a
open TensorCarrier OccupationUnitary Occupation Ext006PairPowerWick

/-- Adding one particle multiplies the multiplicity factorial by m(a)+1. -/
lemma multiplicityFactorial_add_e (m : Occ) (a : ℤ) :
    multiplicityFactorial (m + e a) = (m a + 1) * multiplicityFactorial m := by
  classical
  let T := insert a m.support
  have h0 : m.support ⊆ T := Finset.subset_insert _ _
  have h1 : (m + e a).support ⊆ T := by
    intro i hi
    by_cases hia : i = a
    · subst i; exact Finset.mem_insert_self _ _
    · have hm : m i ≠ 0 := by simpa [e, Ne.symm hia] using Finsupp.mem_support_iff.mp hi
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hm)
  have expand (v : Occ) (hv : v.support ⊆ T) :
      multiplicityFactorial v = (v a).factorial * ∏ i ∈ T.erase a, (v i).factorial := by
    rw [multiplicityFactorial, Finsupp.prod_of_support_subset v hv _ (by simp)]
    exact (Finset.mul_prod_erase T (fun i => (v i).factorial) (Finset.mem_insert_self _ _)).symm
  rw [expand _ h1, expand _ h0]
  have hp : (∏ i ∈ T.erase a, ((m + e a) i).factorial) =
      ∏ i ∈ T.erase a, (m i).factorial := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [e, Ne.symm (Finset.ne_of_mem_erase hi)]
  rw [hp]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [Nat.factorial_succ]
  ring

/-- A representative of the occupation after adding a mode. -/
def addMode {N : ℕ} (m : Arr N) (a : ℤ) : Arr (N+1) :=
  ⟨m.1 + e a, by change total (m.1 + e a) = N+1; rw [total_add_e, m.2]⟩

/-- The exact adjacent-sector normalization identity; it also covers occupied modes. -/
lemma normalization_addMode {N : ℕ} (m : Arr N) (a : ℤ) :
    Real.sqrt ((N : ℝ)+1) * normalization m =
      Real.sqrt ((m.1 a : ℝ)+1) * normalization (addMode m a) := by
  have hm : (multiplicityFactorial m.1 : ℝ) > 0 := by
    exact_mod_cast multiplicityFactorial_pos m.1
  have hN : (N.factorial : ℝ) > 0 := by exact_mod_cast Nat.factorial_pos N
  have ha : (m.1 a : ℝ)+1 > 0 := by positivity
  have hs : ∀ {k : ℕ} (v : Arr k), (normalization v)^2 =
      (k.factorial : ℝ) / (multiplicityFactorial v.1 : ℝ) :=
    fun v => Real.sq_sqrt (by positivity)
  have hsq : (Real.sqrt ((N : ℝ)+1) * normalization m)^2 =
      (Real.sqrt ((m.1 a : ℝ)+1) * normalization (addMode m a))^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      hs, hs]
    simp only [addMode, multiplicityFactorial_add_e, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  exact (sq_eq_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (normalization_pos m).le)
    (mul_nonneg (Real.sqrt_nonneg _) (normalization_pos (addMode m a)).le)).mp hsq

/-- Histogram addition for an ordered concatenation, with all integer labels retained. -/
lemma occupation_append {k n : ℕ} (v : Word k) (w : Word n) :
    occupation (Fin.append v w) = occupation v + occupation w := by
  classical
  apply Finsupp.ext
  intro a
  simp only [occupation_apply, Finsupp.add_apply, Fintype.card_subtype]
  simp only [Finset.card_filter]
  simpa only [Fin.append_left, Fin.append_right] using
    Fin.sum_univ_add (fun i => if Fin.append v w i = a then 1 else 0)

/-- Tensor concatenation of two actual normalized occupation vectors before the
outer bosonic projection; the inner projection on the right can be removed. -/
lemma symProj_product_occupation {k n : ℕ} (v : Word k) (m : Arr n) :
    symProj ℂ OneParticle (k+n) (concat (productVector v) (occupationVector m)) =
      (normalization m : ℂ) • symProduct (Fin.append v (representative m)) := by
  rw [occupationVector, symProduct, concat_smul_right, map_smul,
    symProj_concat_symProj_right]
  congr 1
  rw [productVector, productVector, tensorMultilinear_apply, tensorMultilinear_apply,
    concat_ptprod]
  unfold symProduct productVector
  simp only [tensorMultilinear_apply]
  congr 3
  funext i
  exact Fin.addCases (fun j => by simp) (fun j => by simp) i

end QuantumNLS.Ext006OccupationConcatR39a

#print axioms QuantumNLS.Ext006OccupationConcatR39a.multiplicityFactorial_add_e

#print axioms QuantumNLS.Ext006OccupationConcatR39a.normalization_addMode

#print axioms QuantumNLS.Ext006OccupationConcatR39a.occupation_append

#print axioms QuantumNLS.Ext006OccupationConcatR39a.symProj_product_occupation

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006OccupationConcatR39a." then
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
