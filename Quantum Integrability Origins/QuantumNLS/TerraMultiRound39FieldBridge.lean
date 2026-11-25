import QuantumNLS.TerraMultiRound39SignedGain
import QuantumNLS.TerraMultiRound39AlgebraBall

/-! Physical L² fields with finite weighted Fourier mass are represented by
points of the signed Picard model, with exact Fourier and norm identities. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound39FieldBridge
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.PhysicalTensor

/-- Every physical Sobolev field is represented by a point in the weighted
Fourier model, and the original field and Fourier coefficients are recovered. -/
theorem physical_field_bridge (L : ℝ) [Fact (0 < L)] (a : ℝ) (ha : 0 ≤ a)
    (u : L2T L) (hu : hsq L a (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, fieldMap L a ha x = u ∧
      toField L a x = (fun k => QuantumNLS.Fourier.coeff L u k) ∧
      hsq L a (fun k => QuantumNLS.Fourier.coeff L u k) = ENNReal.ofReal (‖x‖ ^ 2) := by
  let c : ℤ → ℂ := fun k => QuantumNLS.Fourier.coeff L u k
  let x : Ell2 := ⟨fun k => ((pw L a k : ℝ) : ℂ) * c k,
    memℓp_of_summable (hsq_summable_eq hu).1⟩
  have hcoeff : toField L a x = c := by
    funext k
    change ((pw L a k : ℝ) : ℂ) * c k / ((pw L a k : ℝ) : ℂ) = c k
    exact mul_div_cancel_left₀ _ (pw_ne_zero L a k)
  have hf : fieldMap L a ha x = u := by
    apply (QuantumNLS.Fourier.fourierL2 L).injective
    apply lp.ext
    funext k
    rw [QuantumNLS.Fourier.fourierL2_apply, QuantumNLS.Fourier.fourierL2_apply,
      coeff_fieldMap L a ha, hcoeff]
  refine ⟨x, hf, hcoeff, ?_⟩
  change hsq L a c = _
  rw [← hcoeff]
  exact hsq_toField L a x


/-- Signed fixed points for a physical Sobolev field, with the exact algebra
ball and one extra Fourier order. This does not include the scalar clauses. -/
theorem physical_field_signed_ball (L : ℝ) [hL : Fact (0 < L)] (a : ℝ)
    (ha : 1 / 2 < a) (κ : ℝ) (u : L2T L)
    (hu : hsq L a (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ a, fieldMap L a ha0 x = u ∧
      ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
        ∃ (hY : 0 < |Y|) (r : Ell2),
          QuantumNLS.TerraMultiRound39AlgebraBall.algebraNorm L a r ≤
            2 * QuantumNLS.TerraMultiRound39AlgebraBall.algebraNorm L a x / |Y| ∧
          QuantumNLS.TerraMultiRound39PhysicalBall.physicalT hL.out ha hY κ x r = r ∧
          hsq L (a + 1) (toField L a r) ≠ ⊤ ∧
          ∀ r' : Ell2,
            QuantumNLS.TerraMultiRound39AlgebraBall.algebraNorm L a r' ≤
              2 * QuantumNLS.TerraMultiRound39AlgebraBall.algebraNorm L a x / |Y| →
            QuantumNLS.TerraMultiRound39PhysicalBall.physicalT hL.out ha hY κ x r' = r' → r' = r := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨x, hx, _, _⟩ := physical_field_bridge L a ha0 u hu
  obtain ⟨B, hB, hfixed⟩ := QuantumNLS.TerraMultiRound39AlgebraBall.algebra_fixed_eventually hL.out ha κ x
  refine ⟨x, ha0, hx, max 1 B, ?_, ?_⟩
  · exact lt_of_lt_of_le hB (le_max_right _ _)
  · intro Y hYB
    have hY1 : 1 ≤ |Y| := (le_max_left _ _).trans hYB
    obtain ⟨hY, r, hr, hf, huniq⟩ := hfixed Y ((le_max_right _ _).trans hYB)
    exact ⟨hY, r, hr, hf,
      QuantumNLS.TerraMultiRound39SignedGain.physical_fixed_gain hL.out ha hY hY1 κ x r hf,
      huniq⟩

end QuantumNLS.TerraMultiRound39FieldBridge
#print axioms QuantumNLS.TerraMultiRound39FieldBridge.physical_field_bridge
#print axioms QuantumNLS.TerraMultiRound39FieldBridge.physical_field_signed_ball
