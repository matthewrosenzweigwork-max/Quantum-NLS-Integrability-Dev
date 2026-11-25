import QuantumNLS.TerraMultiRound40ParityEventually
import QuantumNLS.TerraMultiRound39FieldBridge

/-! Signed scalar parity on the physical Sobolev field and exact algebra ball.
This does not assert agreement with the scalar construction or smooth expansion. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound40PhysicalParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.PhysicalTensor QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound39AlgebraBall QuantumNLS.TerraMultiRound39FieldBridge
open QuantumNLS.TerraMultiRound39SignedGain QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound40ParityEventually

/-- Physical Sobolev fields have signed small fixed points, unique in the exact
algebra ball, with one extra Fourier order and conjugate-odd scalar integrals. -/
theorem physical_field_scalar_parity (L : ℝ) [hLf : Fact (0 < L)] (a : ℝ)
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : κ ≠ 0) (u : L2T L)
    (hu : hsq L a (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ a, fieldMap L a ha0 x = u ∧
      ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
        ∃ (hY : 0 < |Y|) (r s : Ell2),
          algebraNorm L a r ≤ 2 * algebraNorm L a x / |Y| ∧
          algebraNorm L a s ≤ 2 * algebraNorm L a x / |Y| ∧
          physicalT hLf.out ha hY κ x r = r ∧
          physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ x s = s ∧
          hsq L (a + 1) (toField L a r) ≠ ⊤ ∧
          hsq L (a + 1) (toField L a s) ≠ ⊤ ∧
          (∀ t : Ell2, algebraNorm L a t ≤ 2 * algebraNorm L a x / |Y| →
            physicalT hLf.out ha hY κ x t = t → t = r) ∧
          (∀ t : Ell2, algebraNorm L a t ≤ 2 * algebraNorm L a x / |Y| →
            physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ x t = t → t = s) ∧
          scalar L a x r = -conj (scalar L a x s) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨x, hx, _, _⟩ := physical_field_bridge L a ha0 u hu
  obtain ⟨B₁, hB₁, hpar⟩ := scalar_parity_eventually L ha κ hκ x
  obtain ⟨B₂, hB₂, huniq⟩ := algebra_fixed_eventually hLf.out ha κ x
  refine ⟨x, ha0, hx, max 1 (max B₁ B₂), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro Y hB
  have h1 : 1 ≤ |Y| := (le_max_left _ _).trans hB
  have hB₁' : B₁ ≤ |Y| := (le_max_left _ _).trans ((le_max_right _ _).trans hB)
  have hB₂' : B₂ ≤ |Y| := (le_max_right _ _).trans ((le_max_right _ _).trans hB)
  obtain ⟨hY, r, s, hr, hs, hfr, hfs, hp⟩ := hpar Y hB₁'
  have hnorm (t : Ell2) (ht : ‖t‖ ≤ 2 * ‖x‖ / |Y|) :
      algebraNorm L a t ≤ 2 * algebraNorm L a x / |Y| := by
    unfold algebraNorm
    have h := mul_le_mul_of_nonneg_left ht (algebraScale_pos L a).le
    convert h using 1
    ring
  have hr' := hnorm r hr
  have hs' := hnorm s hs
  obtain ⟨_, r₀, _, hfr₀, hur⟩ := huniq Y hB₂'
  obtain ⟨_, s₀, _, hfs₀, hus⟩ := huniq (-Y) (by simpa using hB₂')
  have er : r = r₀ := hur r hr' hfr
  have es : s = s₀ := hus s (by simpa using hs') hfs
  refine ⟨hY, r, s, hr', hs', hfr, hfs, ?_, ?_, ?_, ?_, hp⟩
  · exact physical_fixed_gain hLf.out ha hY h1 κ x r hfr
  · exact physical_fixed_gain hLf.out ha (by simpa using hY) (by simpa using h1) κ x s hfs
  · intro t ht hf
    exact (hur t ht hf).trans er.symm
  · intro t ht hf
    exact (hus t (by simpa using ht) hf).trans es.symm

end QuantumNLS.TerraMultiRound40PhysicalParity
#print axioms QuantumNLS.TerraMultiRound40PhysicalParity.physical_field_scalar_parity
