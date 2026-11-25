import Mathlib
import QuantumNLS.Reg015Assembly
import QuantumNLS.RB7Moment
import QuantumNLS.RB7Chart
import QuantumNLS.RB7Scale

/-!
# R-7B122087 `thm:hierarchy`: bridge to the REG-015 interface of the review (`Reg015Setting` fe860b62, `Reg015Assembly` b3679f96)

* `reg015Moments_of_REG015Input`: the first clause of `REG015Input` (three-way equivalence, composed) is exactly `RB7Moment.Reg015Moments`;
* `cmp_def002`: `Cmp (def002 L S) (def002 L (2S))` (`1 ≤ W`, `W² = U`), the weight pair used with `RB7Unif`/`RB7Chart`;
* `curve_continuous`, `curve_coord`: the conditional homeomorphism clause of `REG015Input` makes `ε ↦ Φ(u + ε h)` a continuous curve in `h^s` for `u, h ∈ H^s`, with the
  coordinates of the chart `e` (this is the continuity hypothesis `ζ` of `RB7Chart.chart_dI`).
The only unaccepted inputs are those of `REG015Input` (`Reg010LowOrdersInput`, `Reg011HomeomorphismInput`, `Reg013InductionInput`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor
open QuantumNLS.Reg015Setting

variable {L κ : ℝ} [Fact (0 < L)]

theorem reg015Moments_of_REG015Input (hκ : 0 < κ) (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (reg013 : Reg013InductionInput (L := L) hκ) :
    Reg015Moments (L := L) hκ := by
  intro s hs u
  have h := (QuantumNLS.Reg015Assembly.REG015Input hκ reg010 reg011 reg013 s hs).1 u
  exact h.1.trans h.2

theorem cmp_def002 {S : ℝ} (hS : 0 ≤ S) : Cmp (def002 L S) (def002 L (2 * S)) where
  one_le := fun j => by
    have := QuantumNLS.Fourier.one_le_sobolevWeight L S hS j
    simpa [def002] using this
  sq_le := fun j => by
    have h := sobolevWeight_add L S S j
    simp only [def002]
    rw [sq, h, two_mul]

theorem curve_continuous {s : ℝ} (hs0 : 0 ≤ s) (V : Set Seq) (_e : L2T L ≃ₜ V)
    (F : H02 L s ≃ₜ Target (L := L) V s hs0) (u h : H02 L s) :
    Continuous (fun ε : ℝ => (F (u + (ε : ℂ) • h)).val) :=
  continuous_subtype_val.comp (F.continuous.comp
    (continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)))

theorem curve_coord {s : ℝ} (hs0 : 0 ≤ s) (V : Set Seq) (e : L2T L ≃ₜ V)
    (F : H02 L s ≃ₜ Target (L := L) V s hs0) (hF : ∀ u n, (F u).val.val n = (e u.val).val n)
    (u h : H02 L s) (ε : ℝ) (n : ℤ) :
    (F (u + (ε : ℂ) • h)).val.val n = (e (u.val + (ε : ℂ) • h.val)).val n := by
  rw [hF]
  rfl

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.reg015Moments_of_REG015Input
#print axioms QuantumNLS.RB7.cmp_def002
#print axioms QuantumNLS.RB7.curve_continuous
#print axioms QuantumNLS.RB7.curve_coord
