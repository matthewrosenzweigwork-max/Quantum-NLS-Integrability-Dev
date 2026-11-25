import QuantumNLS.Reg015Setting
import QuantumNLS.TerraMultiRound80Weighted
import QuantumNLS.Reg011HFinal

/-! REG-015 bridge lemmas (haiku_inventory, conditional).

Both bridges are CONDITIONAL on predecessors pending review: REG-010 (`TerraMultiRound80Weighted.REG010`)
and REG-011 (`Reg011HFinal.reg011_final`). No acceptance of either is claimed here.

* `reg010_input`: `TerraMultiRound80Weighted.REG010` gives the three-way characterization and the
  continuity and bounded-set clauses of `Reg010LowOrdersInput` on the carrier
  `TerraMultiRound80Weighted.actions`, whose coordinates are definitionally the weighted action
  values `(1+|momentum n|)^(2s) * masses n` (`TerraMultiRound80Carrier.weightedActions_apply`, rfl).
  The coordinate clause `coordinate (actions u) n = masses n` of REG010 is not needed.
* `reg011_input`: `Reg011HFinal.reg011_final` gives `F` with `toBase (F u) = e u` in `ℓ²`. The
  coordinatewise clause of `Reg011HomeomorphismInput` follows from `toBase_apply`
  (`toBase z n = z.val n`). The target `TargetA` (R48a) is the subtype `{z // toBase z ∈ V}` with
  the same `toBase` body as `Target` (Reg015Setting), so the two targets are definitionally equal.

Notation: the R48a names are written with their full prefix, since `Reg015Setting` is opened. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.Reg015Setting
namespace QuantumNLS.Reg015HBridges
variable {L κ : ℝ} [Fact (0 < L)]

/-- Bridge for REG-010 (CONDITIONAL on REG-010 pending review). -/
theorem reg010_input (hκ : 0 < κ) : Reg010LowOrdersInput (L := L) hκ := by
  intro s hs0 hs2
  obtain ⟨h1, -, -, hc, hb⟩ :=
    QuantumNLS.TerraMultiRound80Weighted.REG010 (L := L) κ hκ s hs0 hs2
  exact ⟨h1, QuantumNLS.TerraMultiRound80Weighted.actions (L := L) κ hκ s hs0 hs2,
    fun u n => rfl, hc, hb⟩

/-- Bridge for REG-011 (CONDITIONAL on REG-011 pending review). -/
theorem reg011_input (hκ : 0 < κ) : Reg011HomeomorphismInput (L := L) hκ := by
  intro V e he s hs0 hs2
  obtain ⟨F, hF⟩ := QuantumNLS.Reg011HFinal.reg011_final (L := L) κ hκ V e he s hs0 hs2
  refine ⟨F, fun u n => ?_⟩
  have h := congrArg (fun q : QuantumNLS.Reg011SettingR48a.Seq => q n) (hF u)
  simp only [QuantumNLS.Reg011SettingR48a.toBase_apply] at h
  exact h

#print axioms reg010_input
#print axioms reg011_input
end QuantumNLS.Reg015HBridges
