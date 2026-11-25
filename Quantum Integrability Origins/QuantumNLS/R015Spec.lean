import QuantumNLS.Reg015HFinal
/-! integrator-authored trusted spec for REG-015 (terra_review r229 PASS): headline statement(s) copied verbatim from Reg015HFinal (QuantumNLS.Reg015HFinal). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.Reg015Setting
namespace QuantumNLS.R015Spec
open QuantumNLS.Reg015HFinal
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem REG015_final_spec (hκ : 0 < κ) :
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
        ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n) := by
  exact QuantumNLS.Reg015HFinal.REG015_final hκ

theorem ExactModuli_literal {V : Set Seq} (e : L2T L ≃ₜ V) (hκ : 0 < κ) :
    QuantumNLS.Reg015Setting.ExactModuli (L := L) e hκ ↔ (∀ u n, ‖(e u).val n‖^2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := Iff.rfl
theorem Target_literal (V : Set Seq) (s : ℝ) (hs : 0 ≤ s) :
    QuantumNLS.Reg015Setting.Target (L := L) V s hs = ({z : h02 L s // toBase s hs z ∈ V}) := rfl

end QuantumNLS.R015Spec
#print axioms QuantumNLS.R015Spec.REG015_final_spec
