import QuantumNLS.TerraMultiRound42PositivePhysical
import QuantumNLS.RiccatiFourierBase
import QuantumNLS.RiccatiODEConverse

/-! Positive-height smooth expansion for one fixed Fourier representative.
The signed negative-height branch and L∞-solution identification remain open. -/
set_option autoImplicit false
noncomputable section
open Complex Finset
namespace QuantumNLS.TerraMultiRound42SmoothPositive
open QuantumNLS.ClassicalCharges QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiFourierBase QuantumNLS.RiccatiODEConverse
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound42PositivePhysical

/-- Every smooth periodic field has one Fourier representative for which the
positive signed fixed points admit the printed polynomial with an all-order
weighted Fourier-norm remainder. -/
theorem smooth_positive_expansion (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (f : ℝ → ℂ) (hf : SmoothPeriodic L f) :
    ∃ x : Ell2, physRep L a x = f ∧
      ∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
        ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
          physicalT hLf.out ha (abs_pos.mpr hY.ne') κ x r = r ∧
          (∀ t : ℝ, physRep L a p t =
            ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) ∧
          ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹ := by
  obtain ⟨x₀, hx₀⟩ := riccati_fourier_base hLf.out ha (le_refl a) hf
  let x := lowT L a a x₀
  refine ⟨x, hx₀, ?_⟩
  intro M hM
  let S : ℝ := a + (M : ℝ) + 1
  have haS : a + (M : ℝ) + 1 ≤ S := le_refl _
  have haS' : a ≤ S := by dsimp [S]; have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith
  obtain ⟨u, hu⟩ := riccati_fourier_base hLf.out ha haS' hf
  have he : lowT L a S u = x := (physRep_injective hLf.out ha) (hu.trans hx₀.symm)
  have h := positive_physical_expansion L ha haS hM κ u f hu
  rw [he] at h
  exact h

#print axioms smooth_positive_expansion
end QuantumNLS.TerraMultiRound42SmoothPositive
