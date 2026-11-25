import QuantumNLS.Reg013OMain
/-! integrator-authored trusted spec for REG-013 (review record r66 PASS): headline statement(s) copied verbatim from Reg013OMain (QuantumNLS.Reg013OMain). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.Reg015Setting QuantumNLS.Reg013OCorrection QuantumNLS.Reg013OOrder
open QuantumNLS.Reg013OHomeo
open QuantumNLS.TerraMultiRound64ExtendedMeasure
namespace QuantumNLS.R013Spec
open QuantumNLS.Reg013OMain
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem regularity_induction_spec (hκ : 0 < κ) :
    ∀ k : ℕ, 2 ≤ k →
      (∀ s : ℝ, 0 ≤ s → s ≤ k → OrderStatement (L := L) hκ s) →
      ∀ R : Hk L k → ℝ, IntegerAssertion hκ k R → FiniteYAssertion (L := L) hκ k →
        (∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → OrderStatement (L := L) hκ s) ∧
        (LowerBounded hκ k R →
          ∀ s : ℝ, (k:ℝ) < s → s ≤ (k:ℝ)+1 → BoundedActions (L := L) hκ s) := by
  exact QuantumNLS.Reg013OMain.regularity_induction hκ

theorem MomentChar_literal (hκ : 0 < κ) (s : ℝ) :
    QuantumNLS.Reg015Setting.MomentChar (L := L) hκ s ↔ (∀ u : L2T L,
    ((∃ v : H02 L s, v.val = u) ↔
      Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
    (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) := Iff.rfl
theorem WeightedCont_literal (hκ : 0 < κ) (s : ℝ) :
    QuantumNLS.Reg015Setting.WeightedCont (L := L) hκ s ↔ (∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
    (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    Continuous A) := Iff.rfl
theorem CondHomeo_literal (hκ : 0 < κ) (s : ℝ) (hs0 : 0 ≤ s) :
    QuantumNLS.Reg015Setting.CondHomeo (L := L) hκ s hs0 ↔ (∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
    ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n) := Iff.rfl
theorem OrderStatement_literal (hκ : 0 < κ) (s : ℝ) :
    QuantumNLS.Reg015Setting.OrderStatement (L := L) hκ s ↔ (MomentChar (L := L) hκ s ∧ WeightedCont (L := L) hκ s ∧ ∀ hs0 : 0 ≤ s, CondHomeo (L := L) hκ s hs0) := Iff.rfl
theorem BoundedActions_literal (hκ : 0 < κ) (s : ℝ) :
    QuantumNLS.Reg015Setting.BoundedActions (L := L) hκ s ↔ (∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
    (∀ u n, A u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
    ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)) := Iff.rfl
theorem IntegerAssertion_literal (hκ : 0 < κ) (k : ℕ) (R : Hk L k → ℝ) :
    QuantumNLS.Reg015Setting.IntegerAssertion (L := L) hκ k R ↔ ((∀ u : L2T L, (∃ v : Hk L (k+1), v.val = u) ↔
      (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(k+1))) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ≠ ⊤) ∧
  Continuous R ∧
  ∀ v : Hk L k,
    ennrealToWithTop (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(k+1)))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      ennrealToWithTop (∑' n : ℤ, ENNReal.ofReal ((momentum L n)^(2*(k+1)) *
        ‖QuantumNLS.Fourier.coeff L v.val n‖^2)) + ↑(R v)) := Iff.rfl
theorem FiniteYAssertion_literal (hκ : 0 < κ) (k : ℕ) :
    QuantumNLS.Reg015Setting.FiniteYAssertion (L := L) hκ k ↔ ((∀ Y : ℝ, 0 < Y → Continuous (fun u : Hk L k =>
      (∫ t : ℝ, Y ^ 2 * t ^ (2 * (k+1)) / (Y ^ 2 + t ^ 2)
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
        ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * (k+1)) /
          (Y ^ 2 + (momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
  (∀ B : Set (Hk L k), Bornology.IsBounded B →
      ∃ C Y₀ : ℝ, 0 < C ∧ 0 < Y₀ ∧ ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y →
        |(∫ t : ℝ, Y ^ 2 * t ^ (2 * (k+1)) / (Y ^ 2 + t ^ 2)
            ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
          ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * (k+1)) /
            (Y ^ 2 + (momentum L n) ^ 2) *
            ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2| ≤ C)) := Iff.rfl
theorem LowerBounded_literal (hκ : 0 < κ) (k : ℕ) (R : Hk L k → ℝ) :
    QuantumNLS.Reg015Setting.LowerBounded (L := L) hκ k R ↔ ((∀ s : ℝ, 0 ≤ s → s ≤ k → ∀ B : Set (H02 L s), Bornology.IsBounded B →
      ∃ C : ℝ, ∀ u ∈ B,
        (∫ t : ℝ, |t|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≤ C) ∧
  (∀ B : Set (Hk L k), Bornology.IsBounded B → ∃ C : ℝ, ∀ u ∈ B, |R u| ≤ C)) := Iff.rfl

end QuantumNLS.R013Spec
#print axioms QuantumNLS.R013Spec.regularity_induction_spec
