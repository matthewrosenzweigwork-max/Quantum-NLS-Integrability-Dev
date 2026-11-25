import QuantumNLS.Prop022FormContinuityR119
import QuantumNLS.Prop022PhysicalCommutatorR115

/-! The bounded-cutoff moment commutator is the literal physical sector
commutator on the cutoff vector. All cutoff factors are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022CutoffCommutatorR119
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005FormScaleR109
open Ext005PhysicalNumberFormR114 Ext005PhysicalPairFormR114 Ext005PhysicalHalfPairR114
open Ext005QuadraticEnergyR108 Ext005PairSector Ext005PairCommutatorR108
open Prop022CutoffHamiltonianR115 Prop022PhysicalCommutatorR115
variable {L : ℝ} [Fact (0 < L)]

lemma cutoff_idempotent (N : ℕ) (x : Fock L) : cutoff N (cutoff N x) = cutoff N x := by
  apply Subtype.ext
  funext n
  simp only [cutoff_apply]
  split_ifs <;> rfl

lemma rootCutoff_apply (j N : ℕ) (x : Fock L) (n : ℕ) :
    rootCutoff j N x n = (Real.sqrt (momentWeight j n) : ℂ) • cutoff N x n := by
  classical
  simp only [rootCutoff, sum_apply, smul_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single n]
    · rw [projection_same, cutoff_apply, ite_eq_left hn]
    · intro i _ hin
      rw [projection_other L i n (Ne.symm hin), smul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr hn)).elim
  · rw [cutoff_apply, ite_eq_right hn, smul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [projection_other L i n (by have := Finset.mem_range.mp hi; omega), smul_zero]

lemma embedding_rootCutoff (N : ℕ) (x : Fock L) :
    embedding 1 (rootCutoff 1 N x) = cutoff N x := by
  apply Subtype.ext
  funext n
  change (((Real.sqrt (momentWeight 1 n))⁻¹ : ℝ) : ℂ) • (rootCutoff 1 N x n) = _
  rw [rootCutoff_apply, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀
    (ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (momentWeight_one_le 1 n)))), Complex.ofReal_one, one_smul]

/-- Bounded truncation of the actual (Num+1)^j observable. -/
def momentCutoff (j N : ℕ) : Fock L →L[ℂ] Fock L :=
  ∑ n ∈ Finset.range N, (momentWeight j n : ℂ) • projection L n

lemma momentCutoff_apply (j N : ℕ) (x : Fock L) (n : ℕ) :
    momentCutoff j N x n = (momentWeight j n : ℂ) • cutoff N x n := by
  classical
  simp only [momentCutoff, sum_apply, smul_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single n]
    · rw [projection_same, cutoff_apply, ite_eq_left hn]
    · intro i _ hin
      rw [projection_other L i n (Ne.symm hin), smul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr hn)).elim
  · rw [cutoff_apply, ite_eq_right hn, smul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [projection_other L i n (by have := Finset.mem_range.mp hi; omega), smul_zero]

lemma momentCutoff_symmetric (j N : ℕ) (x y : Fock L) :
    ⟪momentCutoff j N x, y⟫_ℂ = ⟪x, momentCutoff j N y⟫_ℂ := by
  simp only [momentCutoff, sum_apply, smul_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_left, projection_selfadjoint]

lemma cutoff_momentCutoff (j N : ℕ) (x : Fock L) :
    cutoff N (momentCutoff j N x) = momentCutoff j N x := by
  apply Subtype.ext
  funext n
  simp only [cutoff_apply, momentCutoff_apply]
  split_ifs <;> simp

lemma rootCutoff_commutes_moment (j N : ℕ) (x : Fock L) :
    rootCutoff 1 N (momentCutoff j N x) = momentCutoff j N (rootCutoff 1 N x) := by
  apply Subtype.ext
  funext n
  simp only [rootCutoff_apply, momentCutoff_apply, cutoff_apply]
  split_ifs <;> simp [smul_smul, mul_comm]

lemma embedded_weight (j N : ℕ) (x : Fock L) (n : ℕ) :
    embedding 1 (rootCutoff 1 N (momentCutoff j N x)) n =
      (momentWeight j n : ℂ) • cutoff N x n := by
  rw [embedding_rootCutoff, cutoff_momentCutoff, momentCutoff_apply]

lemma number_pairing_commutes (a : HN L 1 →L[ℂ] HN L 1) (j N : ℕ) (x : Fock L) :
    numberContinuous a (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x) =
      numberContinuous a (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x)) := by
  rw [numberContinuous_offDiagonal, numberContinuous_offDiagonal]
  apply tsum_congr
  intro n
  rw [embedding_rootCutoff, embedded_weight,
    map_smul, inner_smul_right, inner_smul_left, Complex.conj_ofReal]

lemma annihilation_pairing_difference (b : HN L 2) (j N : ℕ) (x : Fock L) :
    annihilationForm b (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x)) -
      annihilationForm b (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x) =
        ∑' n, differenceTerm j b (cutoff N x) n := by
  change (∑' n, sectorTerm b (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x)) n) -
    (∑' n, sectorTerm b (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x) n) = _
  rw [← (sectorTerm_summable b (rootCutoff 1 N x)
    (rootCutoff 1 N (momentCutoff j N x))).tsum_sub
    (sectorTerm_summable b (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x))]
  apply tsum_congr
  intro n
  simp only [sectorTerm, embedding_rootCutoff, cutoff_momentCutoff, momentCutoff_apply, inner_smul_left,
    Complex.conj_ofReal, map_smul, inner_smul_right, differenceTerm,
    Complex.ofReal_sub, Nat.add_comm 2 n]
  ring

/-- Exact physical commutator on the cutoff vector, proved from the form
pairing, without assuming a moment differentiation identity. -/
theorem cutoff_commutator_identity (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (j N : ℕ) (x : Fock L) :
    Complex.I * ⟪x, (cutoffHamiltonian a b N * momentCutoff (L := L) j N -
      momentCutoff (L := L) j N * cutoffHamiltonian a b N) x⟫_ℂ =
        physicalCommutator j b (cutoff N x) := by
  simp only [sub_apply, mul_apply_eq_comp, inner_sub_right]
  rw [← momentCutoff_symmetric, cutoff_pair, cutoff_pair]
  rw [physicalCommutator_identity]
  have hn := number_pairing_commutes a j N x
  have hp := annihilation_pairing_difference b j N x
  change Complex.I * ((numberContinuous a (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x) +
    (1/2 : ℂ) * (annihilationForm b (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x) +
      starRingEnd ℂ (annihilationForm b (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x))))) -
    (numberContinuous a (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x)) +
    (1/2 : ℂ) * (annihilationForm b (rootCutoff 1 N x) (rootCutoff 1 N (momentCutoff j N x)) +
      starRingEnd ℂ (annihilationForm b (rootCutoff 1 N (momentCutoff j N x)) (rootCutoff 1 N x))))) = _
  rw [hn]
  unfold diagonalCommutator
  rw [← hp]
  simp only [star_sub, starRingEnd_apply]
  ring

lemma momentCutoff_pair (j N : ℕ) (x : Fock L) :
    ⟪x, momentCutoff j N x⟫_ℂ = (energy j (cutoff N x) : ℂ) := by
  rw [lp.inner_eq_tsum, energy, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [momentCutoff_apply, cutoff_apply]
  split_ifs
  · simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_mul,
      Complex.ofReal_pow]
    rfl
  · simp only [smul_zero, inner_zero_right, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, Complex.ofReal_zero]

lemma cutoffHamiltonian_range (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (N : ℕ) (x : Fock L) : cutoff N (cutoffHamiltonian a b N x) = cutoffHamiltonian a b N x := by
  have hr (y : Fock L) : rootCutoff 1 N (cutoff N y) = rootCutoff 1 N y := by
    apply Subtype.ext
    funext n
    rw [rootCutoff_apply, rootCutoff_apply, cutoff_idempotent]
  apply ext_inner_left ℂ
  intro y
  rw [← Ext005FormCutoffR109.cutoff_symmetric, cutoff_pair, cutoff_pair, hr]

lemma cutoffHamiltonian_cutoff (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (N : ℕ) (x : Fock L) : cutoffHamiltonian a b N (cutoff N x) = cutoffHamiltonian a b N x := by
  have hr : rootCutoff 1 N (cutoff N x) = rootCutoff 1 N x := by
    apply Subtype.ext
    funext n
    rw [rootCutoff_apply, rootCutoff_apply, cutoff_idempotent]
  apply ext_inner_left ℂ
  intro y
  rw [cutoff_pair, cutoff_pair, hr]

end QuantumNLS.Prop022CutoffCommutatorR119

#print axioms QuantumNLS.Prop022CutoffCommutatorR119.cutoff_commutator_identity

#print axioms QuantumNLS.Prop022CutoffCommutatorR119.momentCutoff_pair

#print axioms QuantumNLS.Prop022CutoffCommutatorR119.cutoffHamiltonian_range

#print axioms QuantumNLS.Prop022CutoffCommutatorR119.cutoffHamiltonian_cutoff

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CutoffCommutatorR119." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CutoffCommutatorR119." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R119 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
