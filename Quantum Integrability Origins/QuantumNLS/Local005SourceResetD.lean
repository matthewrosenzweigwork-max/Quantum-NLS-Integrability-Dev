import QuantumNLS.Local005SourceEntriesD

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace QuantumNLS.Local005.SourceD
open QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

variable {L r κ : ℝ} [Fact (0 < L)]

/-- A common absolute Fourier majorant for both input components of the actual source word. -/
def physicalMajorant (L r κ : ℝ) [Fact (0 < L)] (kind : WordKind) (k : ℕ)
    (u : ℕ → ScalarInterval L) (n : ℤ) : ℝ :=
  contourMajorant L r κ kind k (physicalInputs 0 (fun t : Fin k => u t)) n

set_option backward.isDefEq.respectTransparency false in
theorem physicalMajorant_component (kind : WordKind) (k : ℕ)
    (u : ℕ → ScalarInterval L) (n : ℤ) (j : Fin 2) :
    contourMajorant L r κ kind k (physicalInputs j (fun t : Fin k => u t)) n =
      physicalMajorant L r κ kind k u n := by
  unfold physicalMajorant contourMajorant contourAbsTerm amplitude
  simp only [physicalInputs, physicalSlot_norm]

set_option backward.isDefEq.respectTransparency false in
theorem physicalMajorant_finite (kind : WordKind) (k : ℕ)
    (u : Fin k → ScalarInterval L) (n : ℤ) (j : Fin 2) :
    contourMajorant L r κ kind k (physicalInputs j u) n =
      physicalMajorant L r κ kind k (extendInputs u) n := by
  simpa only [extendInputs_apply_fin] using
    (physicalMajorant_component (L := L) (r := r) (κ := κ) kind k (extendInputs u) n j)

set_option backward.isDefEq.respectTransparency false in
theorem orderedSourceWord_entry_posdegree (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ℕ → ScalarInterval L)
    {k : ℕ} (hk : 1 ≤ k) (kind : WordKind) (i j : Fin 2) :
    entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind u n k) =
      coefficientEntry L r κ kind k (physicalInputs j (fun t : Fin k => u t)) n i j := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  exact orderedSourceWord_entry hL hκ hr hsmall n u a kind i j

/-- Independent complex Fourier slots allow every conjugated occurrence to be replaced
by an independent input. This is a conclusion of the frozen estimates, not a premise. -/
def independentSlotBounds (L r κ C : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (u : Fin k → ℤ → ℂ),
    (∀ t, Summable fun m => ‖u t m‖ ^ 2) → ∀ kind : WordKind,
      (∀ (n : ℤ) (j : Fin 2),
        Summable (fun q : Fin (k - 1) → ℤ => ‖pathCoefficient L r κ kind j u n q‖)) ∧
      if Odd k then
        Summable (fun n : ℤ => contourMajorant L r κ kind k u n ^ 2) ∧
          ∑' n : ℤ, contourMajorant L r κ kind k u n ^ 2 ≤
            (C ^ k * ∏ t, inputL2Norm u t) ^ 2
      else ∀ n : ℤ, contourMajorant L r κ kind k u n ≤ C ^ k * ∏ t, inputL2Norm u t

set_option backward.isDefEq.respectTransparency false in
/-- LOCAL-005 for the source S and K. The ordered coefficients are defined by actual
operator products, the source contour functional, and both free source projections.
They equal the frozen absolutely convergent Fourier series. Repeated inputs give the
locally convergent degree series of the actual S/K operators. Odd coefficients are
off-diagonal with a collective l2 majorant; even coefficients are diagonal with a uniform
majorant. Every physical input is independent and the constants are uniform in n and k. -/
theorem reset_resolvent_word (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    ∃ C : ℝ, 0 < C ∧ independentSlotBounds L r κ C ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ (n : ℤ) (u : ScalarInterval L), ‖u‖ < ρ →
        ∀ kind : WordKind, HasSum (sourceWord hL hκ hr hsmall kind u n)
          (sourceCompressed (κ := κ) (r := r) kind u n)) ∧
      (∀ (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ),
        orderedSourceWord hL hκ hr hsmall kind (extendInputs (fun _ : Fin k => u)) n k =
          sourceWord hL hκ hr hsmall kind u n k) ∧
      (∀ (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (k : ℕ) (a : ℝ),
        sourceWord hL hκ hr hsmall kind (a • u) n k =
          (a : ℂ) ^ k • sourceWord hL hκ hr hsmall kind u n k) ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (u : Fin k → ScalarInterval L) (kind : WordKind),
        (∀ (n : ℤ) (i j : Fin 2),
          entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) =
            coefficientEntry L r κ kind k (physicalInputs j u) n i j ∧
          Summable (fun q : Fin (k - 1) → ℤ =>
            ‖pathCoefficient L r κ kind j (physicalInputs j u) n q‖) ∧
          ‖entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k)‖ ≤
            physicalMajorant L r κ kind k (extendInputs u) n) ∧
        if Odd k then
          (∀ (n : ℤ) (j : Fin 2),
            entryFunctional n j j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) = 0) ∧
          Summable (fun n : ℤ => physicalMajorant L r κ kind k (extendInputs u) n ^ 2) ∧
          ∑' n : ℤ, physicalMajorant L r κ kind k (extendInputs u) n ^ 2 ≤
            (C ^ k * ∏ t : Fin k, ‖u t‖) ^ 2
        else
          (∀ (n : ℤ) (i j : Fin 2), i ≠ j →
            entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) = 0) ∧
          ∀ n : ℤ, physicalMajorant L r κ kind k (extendInputs u) n ≤ C ^ k * ∏ t : Fin k, ‖u t‖ := by
  obtain ⟨C, hC, hbound⟩ := QuantumNLS.ResetResolventWordLOCAL005.reset_resolvent_word
    L r κ hL hκ hr hsmall
  have hind : independentSlotBounds L r κ C := by
    intro k hk u hu kind
    have hb := hbound k hk u hu kind
    refine ⟨fun n j => (hb.1 n j j).1, ?_⟩
    split_ifs with ho
    · rw [if_pos ho] at hb
      exact hb.2.2
    · rw [if_neg ho] at hb
      exact hb.2.2
  refine ⟨C, hC, hind, source_series_on_ball hL hκ hr hsmall,
    fun kind u n k => orderedSourceWord_repeat hL hκ hr hsmall kind u n k,
    fun kind u n k a => sourceWord_real_smul hL hκ hr hsmall kind u n k a, ?_⟩
  intro k hk u kind
  have hentry (n : ℤ) (i j : Fin 2) :
      entryFunctional n i j (orderedSourceWord hL hκ hr hsmall kind (extendInputs u) n k) =
        coefficientEntry L r κ kind k (physicalInputs j u) n i j := by
    simpa only [extendInputs_apply_fin] using
      orderedSourceWord_entry_posdegree hL hκ hr hsmall n (extendInputs u) hk kind i j
  have hzero := hbound k hk (physicalInputs 0 u)
    (physicalInputs_summable 0 _) kind
  simp only [physicalInputs_norm, physicalMajorant_finite] at hzero
  refine ⟨?_, ?_⟩
  · intro n i j
    have hc := coefficient_converges hL hr hsmall κ kind
      (physicalInputs j u) (physicalInputs_summable j _) n i j
    rw [physicalMajorant_finite] at hc
    refine ⟨hentry n i j, hc.1, ?_⟩
    rw [hentry n i j]
    exact hc.2
  · split_ifs with ho
    · rw [if_pos ho] at hzero
      refine ⟨?_, hzero.2.2.1, hzero.2.2.2⟩
      intro n j
      rw [hentry]
      exact coefficient_odd ho L r κ kind _ n j
    · rw [if_neg ho] at hzero
      refine ⟨?_, hzero.2.2⟩
      intro n i j hij
      rw [hentry]
      exact coefficient_even (Nat.not_odd_iff_even.mp ho) L r κ kind _ n i j hij

#print axioms physicalMajorant_component
#print axioms reset_resolvent_word
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
  Lean.logInfo m!"Local005SourceResetD audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
