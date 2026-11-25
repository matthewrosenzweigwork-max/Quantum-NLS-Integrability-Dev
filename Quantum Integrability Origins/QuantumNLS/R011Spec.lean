import QuantumNLS.Reg011HFinal
/-! integrator-authored trusted spec for REG-011 (terra_review r229 ACCEPT): headline statement(s) copied verbatim from Reg011HFinal (QuantumNLS.Reg011HFinal). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.R011Spec
open QuantumNLS.Reg011HFinal
variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

set_option maxHeartbeats 8000000 in
theorem reg011_final_spec : ∀ (κ : ℝ) (hκ : 0 < κ) (V : Set Seq) (e : L2T L ≃ₜ V),
    ExactModuli e hκ → ∀ (s : ℝ) (hs0 : 0 ≤ s), s ≤ 2 →
      ∃ F : H02 L s ≃ₜ QuantumNLS.Reg011HForward.TargetA L V s hs0,
        ∀ u : H02 L s, toBase (L := L) s hs0 (F u).1 = (e u.val).val := by
  exact QuantumNLS.Reg011HFinal.reg011_final

theorem ExactModuli_literal (e : L2T L ≃ₜ V) (hκ : 0 < κ) :
    QuantumNLS.Reg011SettingR48a.ExactModuli (L := L) e hκ ↔ (∀ u n, ‖(e u).val n‖^2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := Iff.rfl
theorem TargetA_literal (s : ℝ) (hs : 0 ≤ s) :
    QuantumNLS.Reg011HForward.TargetA L V s hs = {z : h02 L s // toBase (L := L) s hs z ∈ V} := rfl

end QuantumNLS.R011Spec
#print axioms QuantumNLS.R011Spec.reg011_final_spec
