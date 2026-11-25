import QuantumNLS.TerraMultiRound64InductiveCoefficients
import QuantumNLS.TerraMultiRound62MomentTransfer
import QuantumNLS.TerraMultiRound64LowerMoment

/-! Induction step for physical even moments and their finite corrections. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevS QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound64InductiveCoefficients QuantumNLS.TerraMultiRound62MomentTransfer
open QuantumNLS.TerraMultiRound64LowerMoment
namespace QuantumNLS.TerraMultiRound64InductiveStep

theorem moment_inductive_step (L : ℝ) [Fact (0 < L)] (n : ℕ) (hs : 2 ≤ n+1)
    (κ : ℝ) (hκ : 0 < κ)
    (hprev : ∀ w : L2T L, Integrable (fun t : ℝ => t^(2*n)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) ↔
      hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤)
    (hIH : ∀ j (hj : 2 ≤ j), j < n+1 → ∀ w : L2T L,
      hsq L (j : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
      ∃ y : Ell2, ∃ hb : 0 ≤ ((j-1 : ℕ) : ℝ), fieldMap L (j-1 : ℕ) hb y = w ∧
        (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
        (∫ t : ℝ, t^(2*j) ∂(freeMeasure L w)) =
          retainedR (L := L) j hj κ (physicalToHk (L := L) (j-1) y) j) :
    (∀ w : L2T L, Integrable (fun t : ℝ => t^(2*(n+1))) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) ↔
      hsq L ((n+1) : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤) ∧
    (∀ w : L2T L, hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
      ∃ x : Ell2, ∃ ha : 0 ≤ ((n : ℕ) : ℝ), fieldMap L n ha x = w ∧
        (hsq L ((n+1) : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
          (∫ t : ℝ, t^(2*(n+1)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
          (∫ t : ℝ, t^(2*(n+1)) ∂(freeMeasure L w)) =
            retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1))) := by
  have hlocal : ∀ w : L2T L, hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
      ∃ x : Ell2, ∃ ha : 0 ≤ ((n : ℕ) : ℝ), fieldMap L n ha x = w ∧
      ((Integrable (fun t : ℝ => t^(2*(n+1))) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) ↔
        hsq L ((n+1) : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤) ∧
       (hsq L ((n+1) : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ →
        (∫ t : ℝ, t^(2*(n+1)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w)) -
        (∫ t : ℝ, t^(2*(n+1)) ∂(freeMeasure L w)) =
          retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1))) := by
    intro w hw
    have hμn := (hprev w).mpr hw
    have hνn := (free_even_integrable_iff_hsq w n).mpr hw
    obtain ⟨x, ha, hx, hlim⟩ := physical_limit_from_induction L n hs κ hκ w hw hμn hIH
    let R := retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1)
    have ht := moment_transfer (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) (freeMeasure L w) n R hμn hνn
      (hlim.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
    have hf := free_even_integrable_iff_hsq w (n+1)
    refine ⟨x, ha, hx, ht.1.trans hf, ?_⟩
    intro hh
    have he := ht.2 (hf.mpr hh)
    dsimp only [R] at he
    linarith
  constructor
  · intro w
    constructor
    · intro hp
      have hlower := even_integrable_of_higher (QuantumNLS.PhysicalQuantumMeasure.measure hκ w) n (n+1) (by omega) hp
      obtain ⟨_, _, _, heq, _⟩ := hlocal w ((hprev w).mp hlower)
      exact heq.mp hp
    · intro hh
      have hlower : hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤ :=
        ne_top_of_le_ne_top hh (hsq_mono (by exact_mod_cast (show n ≤ n+1 by omega)) _)
      obtain ⟨_, _, _, heq, _⟩ := hlocal w hlower
      exact heq.mpr hh
  · intro w hw
    obtain ⟨x, ha, hx, _, hid⟩ := hlocal w hw
    exact ⟨x, ha, hx, hid⟩

#print axioms moment_inductive_step
end QuantumNLS.TerraMultiRound64InductiveStep
