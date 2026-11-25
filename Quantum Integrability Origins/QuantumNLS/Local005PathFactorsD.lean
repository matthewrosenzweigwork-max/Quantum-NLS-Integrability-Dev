import QuantumNLS.Local005PathModesD

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.ResolventWordCoefficientLOCAL005

variable {L κ : ℝ} [Fact (0 < L)]

theorem sourceModeIndex_zero (j : Fin 2) : sourceModeIndex j 0 = 0 := by
  simp [sourceModeIndex]

theorem shift_input_component {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) (t : Fin (k + 1)) :
    (Fin.cons (α := fun _ => Fin 2 × ℤ) (j, 0) (shiftPath j q) t).1 =
      componentAfter t.val j := by
  refine Fin.cases ?_ (fun s => ?_) t
  · simp [componentAfter_zero]
  · simp [shiftPath]

theorem shift_output_component {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) (t : Fin (k + 1)) :
    (Fin.snoc (α := fun _ => Fin 2 × ℤ) (shiftPath j q) (componentAfter (k + 1) j, 0) t).1 =
      componentAfter (t.val + 1) j := by
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simp
  · simp [shiftPath]

theorem shift_input_mode {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) (t : Fin (k + 1)) :
    sourceModeIndex
      (Fin.cons (α := fun _ => Fin 2 × ℤ) (j, 0) (shiftPath j q) t).1
      (Fin.cons (α := fun _ => Fin 2 × ℤ) (j, 0) (shiftPath j q) t).2 =
        previousShift q t := by
  refine Fin.cases ?_ (fun s => ?_) t
  · simp [previousShift, sourceModeIndex_zero]
  · simp [previousShift, shiftPath, sourceModeIndex_twice]

theorem shift_output_mode {k : ℕ} (j : Fin 2) (q : Fin k → ℤ) (t : Fin (k + 1)) :
    sourceModeIndex
      (Fin.snoc (α := fun _ => Fin 2 × ℤ) (shiftPath j q) (componentAfter (k + 1) j, 0) t).1
      (Fin.snoc (α := fun _ => Fin 2 × ℤ) (shiftPath j q) (componentAfter (k + 1) j, 0) t).2 =
        nextShift q t := by
  refine Fin.lastCases ?_ (fun s => ?_) t
  · simp [nextShift, sourceModeIndex_zero]
  · have hn : s.val ≠ k := Nat.ne_of_lt s.isLt
    simp [nextShift, hn, shiftPath, sourceModeIndex_twice]

/-- Each ordered physical factor has exactly the frozen label and phase. -/
theorem shifted_factor {k : ℕ} (n : ℤ) (z : ℂ) (j : Fin 2) (q : Fin k → ℤ)
    (u : Fin (k + 1) → ScalarInterval L) (t : Fin (k + 1)) :
    sourceFactorEntry (κ := κ) n z (u t)
      (Fin.snoc (α := fun _ => Fin 2 × ℤ) (shiftPath j q) (componentAfter (k + 1) j, 0) t)
      (Fin.cons (α := fun _ => Fin 2 × ℤ) (j, 0) (shiftPath j q) t) =
        slotPhase L κ (componentAfter t.val j) *
          physicalInputs j u t (wordLabel n q t) *
            (z - (pm L (n + 2 * previousShift q t) : ℂ))⁻¹ := by
  unfold sourceFactorEntry
  rw [shift_input_mode, shift_output_mode, shift_input_component, shift_output_component,
    componentAfter_one_comp, if_pos rfl]
  rw [show n + nextShift q t + previousShift q t = wordLabel n q t by
    unfold wordLabel; ring]
  rfl

/-- The input-end free pole and all internal poles occur once, in their original order. -/
theorem previous_poles {k : ℕ} (n : ℤ) (z : ℂ) (q : Fin k → ℤ) :
    (∏ t : Fin (k + 1), (z - (pm L (n + 2 * previousShift q t) : ℂ))⁻¹) =
      (z - (pm L n : ℂ))⁻¹ *
        ∏ t : Fin k, (z - (pm L (QuantumNLS.ResetFreeResolventLOCAL001.sourceMode n (q t)) : ℂ))⁻¹ := by
  rw [Fin.prod_univ_succ]
  simp [previousShift, QuantumNLS.ResetFreeResolventLOCAL001.sourceMode]

/-- Multiplying the left free pole gives the exact S path integrand. -/
theorem flatTerm_projection_integrand {k : ℕ} (n : ℤ) (z : ℂ) (j : Fin 2)
    (q : Fin k → ℤ) (u : ℕ → ScalarInterval L) :
    (z - (pm L n : ℂ))⁻¹ *
      flatTerm (fun t => sourceFactorEntry (κ := κ) n z (u t)) k
        (componentAfter (k + 1) j, 0) (j, 0) (shiftPath j q) =
      pathIntegrand L 0 κ .projection j (physicalInputs j (fun t : Fin (k + 1) => u t)) n q z := by
  unfold flatTerm
  have hf := fun t : Fin (k + 1) => shifted_factor (κ := κ) n z j q (fun t => u t) t
  simp_rw [hf, Finset.prod_mul_distrib]
  rw [previous_poles]
  unfold pathIntegrand endpointOrder
  ring_nf
  rfl

#print axioms shifted_factor
#print axioms previous_poles
#print axioms flatTerm_projection_integrand
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
  Lean.logInfo m!"Local005PathFactorsD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
