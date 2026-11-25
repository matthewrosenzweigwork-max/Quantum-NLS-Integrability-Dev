import QuantumNLS.GlobalCompatFinalR47a
import QuantumNLS.ActionTorus

/-! Common phase and spatial translation leave the entire actual action
sequence unchanged. Consequently every function of actions, including the
physical frequency supplied by the dynamics theorem, is unchanged. This
makes no claim about the still-open physical-flow covariance. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound85InvariantFrequency
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.GlobalCompatR47a
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}

/-- Equality of the full indexed action vector under common phase. -/
theorem phase_mass_vector (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) (u : L2T L) (γ : ℝ) :
    QuantumNLS.RootIndexedMasses.masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u) =
      QuantumNLS.RootIndexedMasses.masses hκ u := by
  apply Subtype.ext
  apply lp.ext
  funext n
  rw [← h.moduli, ← h.moduli, ((hc.1 κ hκ).1 u n).1 γ]
  simp [norm_mul, Complex.norm_exp_ofReal_mul_I]

/-- Equality of the full indexed action vector under spatial translation. -/
theorem translation_mass_vector (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) (u : L2T L) (y : ℝ) :
    QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.BornTranslation.trans y u) =
      QuantumNLS.RootIndexedMasses.masses hκ u := by
  apply Subtype.ext
  apply lp.ext
  funext n
  rw [← h.moduli, ← h.moduli, ((hc.1 κ hκ).1 u n).2.1 y]
  have hexp : ‖Complex.exp (Complex.I * ((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) * (y : ℂ))‖ = 1 := by
    have heq : Complex.I * ((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) * (y : ℂ) =
        (((QuantumNLS.LocalSpectral.pm L n * y : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [heq, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, hexp, one_mul]

/-- Any action-dependent function is unchanged; no boundary frequency is asserted. -/
theorem phase_translation_frequency
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) (ν : ℤ → QuantumNLS.ActionTorus.PosL1 → ℝ)
    (u : L2T L) (γ y : ℝ) (n : ℤ) :
    ν n (QuantumNLS.RootIndexedMasses.masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u)) =
      ν n (QuantumNLS.RootIndexedMasses.masses hκ u) ∧
    ν n (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.BornTranslation.trans y u)) =
      ν n (QuantumNLS.RootIndexedMasses.masses hκ u) := by
  rw [phase_mass_vector hκ h hc u γ, translation_mass_vector hκ h hc u y]
  exact ⟨rfl, rfl⟩

#print axioms phase_mass_vector
#print axioms translation_mass_vector
#print axioms phase_translation_frequency
end QuantumNLS.TerraMultiRound85InvariantFrequency
