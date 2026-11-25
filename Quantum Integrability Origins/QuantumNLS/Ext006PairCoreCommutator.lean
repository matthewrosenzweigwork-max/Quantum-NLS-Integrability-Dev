import QuantumNLS.Occupation

/-! Finite-kernel pair-creation commutators on the repository's literal CCR core.
The identities are proved from the frozen Ann/Cre operators, not postulated.
Transport to the completed physical pair blocks remains a separate step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
namespace QuantumNLS.Ext006PairCoreCommutator
open Occupation

/-- Pair creation with a finite matrix of modes, with no factor 1/2. -/
def pairCreator (S : Finset ℤ) (K : ℤ → ℤ → ℂ) : Module.End ℂ FS :=
  ∑ i ∈ S, ∑ j ∈ S, K i j • (Cre i * Cre j)

/-- Creation in one row of the same finite matrix. -/
def rowCreator (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) : Module.End ℂ FS :=
  ∑ j ∈ S, K a j • Cre j

lemma ann_cre (a i : ℤ) :
    Ann a * Cre i = Cre i * Ann a + (if a = i then 1 else 0) := by
  by_cases h : a = i
  · subst i
    simpa using Ann_Cre_same a
  · simpa [h] using Ann_Cre_ne a i h

/-- The elementary Leibniz commutator for two creation operators. -/
lemma ann_cre_cre (a i j : ℤ) :
    Ann a * (Cre i * Cre j) = (Cre i * Cre j) * Ann a +
      (if a = i then Cre j else 0) + (if a = j then Cre i else 0) := by
  rw [← mul_assoc, ann_cre, add_mul, mul_assoc, ann_cre, mul_add]
  split_ifs <;> simp only [one_mul, zero_mul, mul_one, mul_zero, mul_assoc] <;> abel

/-- Exact finite-matrix commutator, before using symmetry. -/
theorem ann_pairCreator (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) (ha : a ∈ S) :
    Ann a * pairCreator S K = pairCreator S K * Ann a +
      rowCreator S K a + ∑ i ∈ S, K i a • Cre i := by
  classical
  simp only [pairCreator, rowCreator, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, ann_cre_cre, smul_add, Finset.sum_add_distrib]
  have hleft : (∑ i ∈ S, ∑ j ∈ S, K i j • (if a = i then Cre j else 0)) =
      ∑ j ∈ S, K a j • Cre j := by
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro i _ hi
      have hn : a ≠ i := Ne.symm hi
      simp [hn]
    · exact fun h => (h ha).elim
  have hright : (∑ i ∈ S, ∑ j ∈ S, K i j • (if a = j then Cre i else 0)) =
      ∑ i ∈ S, K i a • Cre i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · exact fun h => (h ha).elim
  rw [hleft, hright]

/-- Symmetry gives the factor two, including diagonal modes. -/
theorem ann_symmetric_pairCreator (S : Finset ℤ) (K : ℤ → ℤ → ℂ)
    (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (a : ℤ) (ha : a ∈ S) :
    Ann a * pairCreator S K = pairCreator S K * Ann a +
      (2 : ℂ) • rowCreator S K a := by
  rw [ann_pairCreator S K a ha]
  have he : (∑ i ∈ S, K i a • Cre i) = rowCreator S K a := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hK i hi a ha]
  rw [he, two_smul]
  abel

set_option maxHeartbeats 2000000 in
lemma cre_pairCreator_comm (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) :
    Cre a * pairCreator S K = pairCreator S K * Cre a := by
  classical
  simp only [pairCreator, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun T : Module.End ℂ FS => K i j • T)
  rw [← mul_assoc, Cre_Cre_comm a i, mul_assoc, Cre_Cre_comm a j, ← mul_assoc]

/-- The commutator itself commutes with the pair creator. -/
lemma row_pairCreator_comm (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) :
    rowCreator S K a * pairCreator S K = pairCreator S K * rowCreator S K a := by
  classical
  simp only [rowCreator, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    cre_pairCreator_comm]

/-- The n-th power identity is proved once by induction in an arbitrary algebra. -/
lemma commutator_power {A : Type*} [Ring A] (D B C : A)
    (hDB : D*B = B*D+C) (hCB : C*B = B*C) (n : ℕ) :
    D*B^(n+1) = B^(n+1)*D + (n+1) • (B^n*C) := by
  induction n with
  | zero => simpa using hDB
  | succ n ih =>
    have hm : ((n+1) • (B^n*C))*B = (n+1) • ((B^n*C)*B) :=
      (AddMonoidHom.mulRight B).map_nsmul _ _
    rw [pow_succ B (n+1), ← mul_assoc, ih, add_mul, mul_assoc, hDB, mul_add,
      hm, mul_assoc, hCB]
    simp only [← mul_assoc, ← pow_succ, add_nsmul, one_nsmul]
    abel

/-- All-degree pair-creation commutator on the actual finite-support CCR core.
The factor 2n is derived from the symmetric matrix, for every n. -/
theorem ann_pairCreator_power (S : Finset ℤ) (K : ℤ → ℤ → ℂ)
    (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (a : ℤ) (ha : a ∈ S) (n : ℕ) :
    Ann a * (pairCreator S K)^(n+1) = (pairCreator S K)^(n+1)*Ann a +
      (2*((n+1 : ℕ) : ℂ)) • ((pairCreator S K)^n * rowCreator S K a) := by
  have hc : ((2 : ℂ) • rowCreator S K a) * pairCreator S K =
      pairCreator S K * ((2 : ℂ) • rowCreator S K a) := by
    rw [smul_mul_assoc, mul_smul_comm, row_pairCreator_comm]
  have h := commutator_power (Ann a) (pairCreator S K) ((2 : ℂ) • rowCreator S K a)
    (ann_symmetric_pairCreator S K hK a ha) hc n
  simpa only [mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_comm ((n+1 : ℕ) : ℂ) 2] using h


/-- Literal homogeneous pair-exponential terms on the finite CCR core. -/
def coreTerm (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (n : ℕ) : FS :=
  ((-1/2 : ℂ)^n / (n.factorial : ℂ)) • (((pairCreator S K)^n) (ket 0))

lemma row_pairCreator_pow_comm (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) (n : ℕ) :
    rowCreator S K a * (pairCreator S K)^n =
      (pairCreator S K)^n * rowCreator S K a :=
  (Commute.pow_right (show Commute (rowCreator S K a) (pairCreator S K) from
    row_pairCreator_comm S K a) n).eq

/-- The one-annihilator recurrence in every exponential degree, with the
source sign, derived from the all-power commutator and the actual core vacuum. -/
theorem ann_coreTerm (S : Finset ℤ) (K : ℤ → ℤ → ℂ)
    (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (a : ℤ) (ha : a ∈ S) (n : ℕ) :
    Ann a (coreTerm S K (n+1)) = -(rowCreator S K a (coreTerm S K n)) := by
  have hv : Ann a (ket 0) = 0 := by simp [Ann_ket]
  have hp := LinearMap.congr_fun (ann_pairCreator_power S K hK a ha n) (ket 0)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hv, map_zero, zero_add] at hp
  have hr := LinearMap.congr_fun (row_pairCreator_pow_comm S K a n) (ket 0)
  simp only [Module.End.mul_apply] at hr
  simp only [coreTerm, map_smul, hp, ← hr, smul_smul]
  rw [← neg_smul]
  congr 1
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

end QuantumNLS.Ext006PairCoreCommutator
end

#print axioms QuantumNLS.Ext006PairCoreCommutator.pairCreator
#print axioms QuantumNLS.Ext006PairCoreCommutator.rowCreator
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_cre
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_cre_cre
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_pairCreator
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_symmetric_pairCreator
#print axioms QuantumNLS.Ext006PairCoreCommutator.cre_pairCreator_comm
#print axioms QuantumNLS.Ext006PairCoreCommutator.row_pairCreator_comm
#print axioms QuantumNLS.Ext006PairCoreCommutator.commutator_power
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_pairCreator_power
#print axioms QuantumNLS.Ext006PairCoreCommutator.coreTerm
#print axioms QuantumNLS.Ext006PairCoreCommutator.row_pairCreator_pow_comm
#print axioms QuantumNLS.Ext006PairCoreCommutator.ann_coreTerm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PairCoreCommutator." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
