import QuantumNLS.Reg013OHomeo

/-! REG-013 `lem:regularity-induction` (`source-text/chapters/regularity/fractional_moments.tex:610`),
opus_tensor stage O6: the printed lemma.

Fix an integer `k ≥ 2`. If the moment characterization, weighted-action continuity and the
conditional homeomorphism statement hold through order `k` (every real `0 ≤ s ≤ k`), and the two
printed assertions hold — `IntegerAssertion k R` (for all `u ∈ L²`, `u ∈ H^{k+1} ⟺ 𝓜_{2k+2}(u) < ∞`;
on `H^k` the extended identity `𝓜_{2k+2} = Q_{k+1} + R` with `R : H^k → ℝ` continuous) and
`FiniteYAssertion k` (fixed-`Y` continuity of `D_{k+1,u}(Y)` on `H^k` and a bound uniform for large
`Y` on every `H^k` bounded set) — then the same conclusions hold for every `k < s ≤ k+1`; and if
the lower moments and the correction are bounded on bounded Sobolev sets (`LowerBounded k R`), the
new weighted-action maps send bounded sets to bounded sets.

The vocabulary is that of `Reg015Setting` (opus_tensor REG-015 stage S1), where the same statement
is the named input `Reg013InductionInput`; `REG013Statement` is written out in full and is
definitionally `Reg013InductionInput` (`statement_eq : … := rfl`). The proof does not use REG-011:
the homeomorphism clause at order `s` is derived from the assumed order-`k` homeomorphism
statement, exactly as printed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.Reg015Setting QuantumNLS.Reg013OCorrection QuantumNLS.Reg013OOrder
open QuantumNLS.Reg013OHomeo
namespace QuantumNLS.Reg013OMain
variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed REG-013 statement, written out. -/
def REG013Statement (hκ : 0 < κ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (∀ s : ℝ, 0 ≤ s → s ≤ k → OrderStatement (L := L) hκ s) →
    ∀ R : Hk L k → ℝ, IntegerAssertion hκ k R → FiniteYAssertion (L := L) hκ k →
      (∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → OrderStatement (L := L) hκ s) ∧
      (LowerBounded hκ k R →
        ∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → BoundedActions (L := L) hκ s)

/-- The written-out statement is definitionally the REG-015 named input. -/
theorem statement_eq (hκ : 0 < κ) :
    REG013Statement (L := L) hκ = Reg013InductionInput (L := L) hκ := rfl

/-- **REG-013, `lem:regularity-induction`.** -/
theorem regularity_induction (hκ : 0 < κ) :
    ∀ k : ℕ, 2 ≤ k →
      (∀ s : ℝ, 0 ≤ s → s ≤ k → OrderStatement (L := L) hκ s) →
      ∀ R : Hk L k → ℝ, IntegerAssertion hκ k R → FiniteYAssertion (L := L) hκ k →
        (∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → OrderStatement (L := L) hκ s) ∧
        (LowerBounded hκ k R →
          ∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → BoundedActions (L := L) hκ s) := by
  intro k _hk hOS R hIA hfy
  obtain ⟨hmc, hwc, hch⟩ := hOS k (Nat.cast_nonneg k) le_rfl
  refine ⟨fun s h1 h2 => ?_, fun hlb s h1 h2 => ?_⟩
  · obtain ⟨Jc, hJc, hId, -⟩ := identity_exists hκ hmc hwc R hIA hfy h1 h2
    have hmcs := momentChar_of hκ hmc h1 hId
    exact ⟨hmcs, weightedCont_of hκ h1.le hmcs hJc hId,
      fun hs0 => condHomeo_of hκ h1.le hmcs (hch (Nat.cast_nonneg k)) hJc hId hs0⟩
  · obtain ⟨Jc, -, hId, hJb⟩ := identity_exists hκ hmc hwc R hIA hfy h1 h2
    exact boundedActions_of hκ h1 (momentChar_of hκ hmc h1 hId) hId (hJb hlb)

theorem regularity_induction_statement (hκ : 0 < κ) : REG013Statement (L := L) hκ :=
  regularity_induction hκ

/-- REG-013 gives the REG-015 named input `Reg013InductionInput` (definitionally). -/
theorem reg013InductionInput (hκ : 0 < κ) : Reg013InductionInput (L := L) hκ :=
  regularity_induction hκ

/-- The requested bridge: the REG-013 statement, given the REG-011 input, implies
`Reg013InductionInput`. The REG-011 input is not used (the order-`s` homeomorphism clause is
derived from the order-`k` hypothesis inside the statement). -/
theorem reg013_to_input (hκ : 0 < κ) (h : REG013Statement (L := L) hκ)
    (_h11 : Reg011HomeomorphismInput (L := L) hκ) : Reg013InductionInput (L := L) hκ := h

#print axioms regularity_induction
#print axioms reg013InductionInput
#print axioms reg013_to_input
#print axioms statement_eq
end QuantumNLS.Reg013OMain

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013O" ||
        n.toString.startsWith "_private.QuantumNLS.Reg013O" then
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
        if n.toString.endsWith "HeldGP14Tonelli" || n.toString.endsWith "RegularCut" then
          throwError "Held name in closure: {n}"
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Reg013O* aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
