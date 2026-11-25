import QuantumNLS.Local005SourceBridgeC

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

variable {L r κ : ℝ} [Fact (0 < L)]

theorem sourceModeIndex_twice (j : Fin 2) (m : ℤ) :
    sourceModeIndex j (sourceModeIndex j m) = m := by
  fin_cases j <;> simp [sourceModeIndex]

theorem basis_eq_source (n : ℤ) (i : Fin 2 × ℤ) :
    vectorModeBasis L n i = chi L (n + 2 * sourceModeIndex i.1 i.2) i.1 := by
  have he := vectorModeBasis_eq_chi L n i.1 (sourceModeIndex i.1 i.2)
  simpa only [sourceModeIndex_twice, Prod.eta] using he

/-- Each entry is computed from the physical Fourier transform, not from an operator entry definition. -/
def sourceFactorEntry (n : ℤ) (z : ℂ) (u : ScalarInterval L) (i j : Fin 2 × ℤ) : ℂ :=
  if i.1 = componentAfter 1 j.1 then
    slotPhase L κ j.1 *
      physicalSlot j.1 u (n + sourceModeIndex i.1 i.2 + sourceModeIndex j.1 j.2) *
        (z - (pm L (n + 2 * sourceModeIndex j.1 j.2) : ℂ))⁻¹
  else 0

theorem sourceFactorEntry_eq (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (i j : Fin 2 × ℤ) :
    ⟪vectorModeBasis L n i, Mop κ (free L κ n z) u (vectorModeBasis L n j)⟫_ℂ =
      sourceFactorEntry (κ := κ) n z u i j := by
  rw [basis_eq_source, basis_eq_source]
  exact mop_matrix_entry hL hκ hr hsmall n
    (sourceModeIndex i.1 i.2) (sourceModeIndex j.1 j.2) hz u i.1 j.1

/-- Multiplying two actual bounded operators gives the convergent Fourier convolution. -/
theorem matrix_mul_hasSum (n : ℤ) (A B : Op L) (i j : Fin 2 × ℤ) :
    HasSum (fun m : Fin 2 × ℤ =>
      ⟪vectorModeBasis L n i, A (vectorModeBasis L n m)⟫_ℂ *
        ⟪vectorModeBasis L n m, B (vectorModeBasis L n j)⟫_ℂ)
      ⟪vectorModeBasis L n i, (A * B) (vectorModeBasis L n j)⟫_ℂ := by
  simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.mul_apply] using
    (vectorModeBasis L n).hasSum_inner_mul_inner
      (A.adjoint (vectorModeBasis L n i)) (B (vectorModeBasis L n j))

/-- Operators act on input 0 first; factor k is multiplied on the left at step k+1. -/
def operatorPrefix (T : ℕ → Op L) : ℕ → Op L
  | 0 => 1
  | k + 1 => T k * operatorPrefix T k

/-- The corresponding iterated Fourier convolution, retaining every intermediate mode. -/
def matrixPrefix (K : ℕ → (Fin 2 × ℤ) → (Fin 2 × ℤ) → ℂ) :
    ℕ → (Fin 2 × ℤ) → (Fin 2 × ℤ) → ℂ
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑' m, K k i m * matrixPrefix K k m j

theorem operatorPrefix_matrix (n : ℤ) (T : ℕ → Op L) (k : ℕ) (i j : Fin 2 × ℤ) :
    ⟪vectorModeBasis L n i, operatorPrefix T k (vectorModeBasis L n j)⟫_ℂ =
      matrixPrefix (fun t i j =>
        ⟪vectorModeBasis L n i, T t (vectorModeBasis L n j)⟫_ℂ) k i j := by
  induction k generalizing i j with
  | zero =>
    simp only [operatorPrefix, ContinuousLinearMap.one_apply, matrixPrefix]
    exact orthonormal_iff_ite.mp (vectorModeBasis L n).orthonormal i j
  | succ k ih =>
    simp only [operatorPrefix, matrixPrefix]
    rw [(matrix_mul_hasSum n (T k) (operatorPrefix T k) i j).tsum_eq.symm]
    apply tsum_congr
    intro m
    rw [ih m j]

/-- All degrees and all independent physical inputs: exact source operator Fourier words. -/
theorem source_operator_word_matrix (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2 × ℤ) :
    ⟪vectorModeBasis L n i,
      operatorPrefix (fun t => Mop κ (free L κ n z) (u t)) k (vectorModeBasis L n j)⟫_ℂ =
        matrixPrefix (fun t => sourceFactorEntry (κ := κ) n z (u t)) k i j := by
  rw [operatorPrefix_matrix]
  congr 1
  funext t a b
  exact sourceFactorEntry_eq hL hκ hr hsmall n hz (u t) a b

/-- In the repeated-input case these words are precisely the Neumann powers already integrated. -/
theorem operatorPrefix_const (T : Op L) (k : ℕ) :
    operatorPrefix (fun _ => T) k = T ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [operatorPrefix, ih, pow_succ']

#print axioms basis_eq_source
#print axioms sourceFactorEntry_eq
#print axioms matrix_mul_hasSum
#print axioms operatorPrefix_matrix
#print axioms source_operator_word_matrix
#print axioms operatorPrefix_const
end QuantumNLS.Local005.SourceC

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local005.SourceC." ||
        n.toString.startsWith "_private.QuantumNLS.Local005Source" then
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
  Lean.logInfo m!"Local005SourceWordsC audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
