import QuantumNLS.Reg015Assembly
import QuantumNLS.Reg015HBridges
import QuantumNLS.Reg013OMain

/-! REG-015 conditional final (haiku_inventory, module Reg015HFinal).

`REG015_final` is the conclusion of `Reg015Assembly.REG015Input`, with its three named inputs
discharged by:
* REG-010 input: `Reg015HBridges.reg010_input`, from `TerraMultiRound80Weighted.REG010`
  (REG-010 pending review);
* REG-011 input: `Reg015HBridges.reg011_input`, from `Reg011HFinal.reg011_final`
  (REG-011 pending review);
* REG-013 input: `Reg013OMain.reg013InductionInput` (REG-013 pending review).

The accepted REG-004 and REG-014 enter through `Reg015Assembly`, as in the frozen assembly.
No acceptance of REG-010, REG-011, REG-013 or REG-015 is claimed. No sorry, admit,
native_decide, or axiom. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.Reg015Setting
namespace QuantumNLS.Reg015HFinal
variable {L κ : ℝ} [Fact (0 < L)]

/-- **REG-015, conditional final.** For every real `s ≥ 0`: the printed three-way
characterization on all of `L²`; the indexed action map is continuous from `H^s` into the
weighted `ℓ¹` space and sends bounded sets to bounded sets; and the homeomorphism clause for
every homeomorphism `Φ : L² → V ⊂ ℓ²` onto its image with exact moduli. CONDITIONAL on REG-010,
REG-011 and REG-013 pending review; no acceptance of these predecessors or of REG-015 is claimed. -/
theorem REG015_final (hκ : 0 < κ) :
    ∀ s : ℝ, ∀ hs0 : 0 ≤ s,
      (∀ u : L2T L,
        ((∃ v : H02 L s, v.val = u) ↔
          Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
        (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
          Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
            (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
      (∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
        (∀ u n, A u n = (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
        Continuous A ∧
        ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)) ∧
      (∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
        ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n) :=
  QuantumNLS.Reg015Assembly.REG015Input (L := L) hκ
    (QuantumNLS.Reg015HBridges.reg010_input (L := L) hκ)
    (QuantumNLS.Reg015HBridges.reg011_input (L := L) hκ)
    (QuantumNLS.Reg013OMain.reg013InductionInput (L := L) hκ)

#print axioms REG015_final
end QuantumNLS.Reg015HFinal

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg015HFinal." ||
        n.toString.startsWith "_private.QuantumNLS.Reg015HFinal." ||
        n.toString.startsWith "QuantumNLS.Reg015HBridges." ||
        n.toString.startsWith "_private.QuantumNLS.Reg015HBridges." then
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
  Lean.logInfo m!"Reg015HFinal aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
