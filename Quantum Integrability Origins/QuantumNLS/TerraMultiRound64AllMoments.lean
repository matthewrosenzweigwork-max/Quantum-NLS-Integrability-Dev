import QuantumNLS.TerraMultiRound64InductiveStep
import QuantumNLS.TerraMultiRound64BaseCriterion

/-! Strong induction for every integer even moment. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevS QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound64InductiveStep QuantumNLS.TerraMultiRound64BaseCriterion
namespace QuantumNLS.TerraMultiRound64AllMoments

theorem integer_moment_induction (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) :
    ∀ s : ℕ, ∀ hs : 2 ≤ s,
      (∀ w : L2T L, Integrable (fun t : ℝ => t^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) ↔
        hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤) ∧
      (∀ w : L2T L, hsq L (s-1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
        ∃ x : Ell2, ∃ ha : 0 ≤ ((s-1 : ℕ) : ℝ), fieldMap L (s-1 : ℕ) ha x = w ∧
          (hsq L (s : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
            (∫ t : ℝ, t^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
            (∫ t : ℝ, t^(2*s) ∂(freeMeasure L w)) =
              retainedR (L := L) s hs κ (physicalToHk (L := L) (s-1) x) s)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    cases s with
    | zero => intro hs; omega
    | succ n =>
      intro hs
      have hprev : ∀ w : L2T L, Integrable (fun t : ℝ => t^(2*n)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) ↔
          hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ := by
        intro w
        by_cases h1 : n = 1
        · simpa only [h1, mul_one] using physical_second_iff_hsq L κ hκ w
        · exact (ih n (by omega) (by omega)).1 w
      have hIH : ∀ j (hj : 2 ≤ j), j < n+1 → ∀ w : L2T L,
          hsq L (j : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
          ∃ y : Ell2, ∃ hb : 0 ≤ ((j-1 : ℕ) : ℝ), fieldMap L (j-1 : ℕ) hb y = w ∧
            (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
            (∫ t : ℝ, t^(2*j) ∂(freeMeasure L w)) =
              retainedR (L := L) j hj κ (physicalToHk (L := L) (j-1) y) j := by
        intro j hj hjlt w hu
        have hlower : hsq L (j-1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ :=
          ne_top_of_le_ne_top hu (hsq_mono (by exact_mod_cast (show j-1 ≤ j by omega)) _)
        obtain ⟨y, hb, hy, hid⟩ := (ih j (by omega) hj).2 w hlower
        exact ⟨y, hb, hy, hid hu⟩
      exact moment_inductive_step L n hs κ hκ hprev hIH

#print axioms integer_moment_induction
end QuantumNLS.TerraMultiRound64AllMoments
