import QuantumNLS.Local005PathFactorsD

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

theorem pathIntegrand_summable (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (kind : WordKind) {k : ℕ} (j : Fin 2) (u : Fin k → ℤ → ℂ)
    (hu : ∀ t, Summable fun m => ‖u t m‖ ^ 2) (n : ℤ) {z : ℂ}
    (hz : OnGamma L r n z) : Summable (fun q => pathIntegrand L r κ kind j u n q z) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => pathIntegrand_bound hL hr hsmall κ kind j u n q hz)
    (pathUniformBound_summable hL hr hsmall κ kind u hu n)

/-- The frozen majorant supplies the summability needed by the Fubini lemma. -/
theorem physical_flatTerm_summable (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2) :
    Summable (flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k (i, 0) (j, 0)) := by
  by_cases hi : i = componentAfter (k + 1) j
  · subst i
    apply (flatTerm_shift_summable_iff n z u k _ _).mp
    have hd : (z - (pm L n : ℂ))⁻¹ ≠ 0 := by
      apply inv_ne_zero
      apply norm_pos_iff.mp
      rw [hz]
      exact hr
    apply (summable_mul_left_iff hd).mp
    have hs := pathIntegrand_summable (κ := κ) hL hr hsmall .projection j
      (physicalInputs j (fun t : Fin (k + 1) => u t))
      (physicalInputs_summable j _) n hz
    exact hs.congr (fun q => (flatTerm_projection_integrand n z j q u).symm)
  · have he : flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k (i, 0) (j, 0) = 0 := by
      funext q
      by_contra h
      exact hi (flatTerm_forced_components n z u k (i, 0) (j, 0) q h).1
    rw [he]
    exact summable_zero

theorem basis_zero (n : ℤ) (j : Fin 2) : vectorModeBasis L n (j, 0) = chi L n j := by
  rw [basis_eq_source]
  simp [sourceModeIndex_zero]

theorem free_inner_zero (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (n : ℤ) {z : ℂ} (hz : OnGamma L r n z) (i : Fin 2) (f : H2 L) :
    ⟪chi L n i, free L κ n z f⟫_ℂ =
      (z - (pm L n : ℂ))⁻¹ * ⟪chi L n i, f⟫_ℂ := by
  rw [sourceResolvent_eq_freeDiagonal L hL κ n hr hsmall hz
    (free_isResolvent hL hr hsmall n hz)]
  rw [← basis_zero n i, freeDiagonalResolvent_inner]
  simp only [CompletionB.freeResolventMultiplier, CompletionB.sourceMode,
    sourceModeIndex_zero, mul_zero, add_zero]

/-- The actual source word is the one absolutely convergent shift sum, with no supplied
coefficient identity or summability hypothesis. -/
theorem source_word_path_sum (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ℕ → ScalarInterval L) (k : ℕ) (i j : Fin 2) :
    ⟪chi L n i, (free L κ n z *
      operatorPrefix (fun t => QuantumNLS.Local002.Mop κ (free L κ n z) (u t)) (k + 1))
        (chi L n j)⟫_ℂ =
      if i = componentAfter (k + 1) j then
        ∑' q : Fin k → ℤ, pathIntegrand L r κ .projection j
          (physicalInputs j (fun t : Fin (k + 1) => u t)) n q z else 0 := by
  rw [ContinuousLinearMap.mul_apply, free_inner_zero hL hr hsmall n hz]
  rw [← basis_zero n i, ← basis_zero n j,
    source_operator_word_matrix hL hκ hr hsmall n hz u (k + 1),
    matrixPrefix_flat_of_summable _ k _ _ (physical_flatTerm_summable hL hr hsmall n hz u k i j),
    flatTerm_shift_tsum n z u k (i, 0) (j, 0)]
  split_ifs with hi
  · subst i
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    exact flatTerm_projection_integrand n z j q u
  · have he : ∀ q : Fin k → ℤ,
        flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k
          (i, 0) (j, 0) (shiftPath j q) = 0 := by
      intro q
      by_contra h
      exact hi (flatTerm_forced_components n z u k (i, 0) (j, 0) (shiftPath j q) h).1
    simp only [he, tsum_zero, mul_zero]

#print axioms pathIntegrand_summable
#print axioms physical_flatTerm_summable
#print axioms free_inner_zero
#print axioms source_word_path_sum
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
  Lean.logInfo m!"Local005SourcePathD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
