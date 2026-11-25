import QuantumNLS.TerraMultiRound38SignedPicard
import QuantumNLS.RiccatiPointwiseDisc

/-! A physical conjugate-field specialization of the signed Fourier-model
fixed point. This is a supporting result, not the full REG-005 lemma. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.ComplexifiedSobolevField

/-- The normalization `κ / L` compensates for the Fourier convolution convention. -/
def physicalT {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2) : Ell2 :=
  signedT hL ha hY (κ / L) u (jEll u) r

/-- Signed existence and uniqueness in the exact Fourier Sobolev ball, including zero.
The uniqueness ball is in fact twice the requested radius. -/
theorem physical_fixed_eventually {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (κ : ℝ) (u : Ell2) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
      ∃ (hY : 0 < |Y|) (r : Ell2), ‖r‖ ≤ 2 * ‖u‖ / |Y| ∧
        physicalT hL ha hY κ u r = r ∧
        ∀ r' : Ell2, ‖r'‖ ≤ 2 * ‖u‖ / |Y| →
          physicalT hL ha hY κ u r' = r' → r' = r := by
  by_cases hu : u = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro Y hB
    have hY : 0 < |Y| := by linarith
    refine ⟨hY, 0, ?_, ?_, ?_⟩
    · simp [hu]
    · simp [physicalT, signedT, hu]
    · intro r' hr' _
      have : ‖r'‖ = 0 := by simpa [hu] using hr'
      exact norm_eq_zero.mp this
  · have hβ : 0 < ‖u‖ := norm_pos_iff.mpr hu
    obtain ⟨B, hB, he⟩ := signed_fixed_eventually hL ha (κ / L) ‖u‖ hβ u (jEll u)
      (le_refl _) (by rw [norm_jEll])
    refine ⟨B, hB, ?_⟩
    intro Y hYB
    obtain ⟨hY, r, hr, hf, huniq⟩ := he Y hYB
    refine ⟨hY, r, hr, hf, ?_⟩
    intro r' hr' hfix
    apply huniq r' _ hfix
    have hn : 0 ≤ ‖u‖ / |Y| := div_nonneg (norm_nonneg _) (abs_nonneg _)
    have e₂ : 2 * ‖u‖ / |Y| = 2 * (‖u‖ / |Y|) := by ring
    have e₄ : 4 * ‖u‖ / |Y| = 4 * (‖u‖ / |Y|) := by ring
    rw [e₂] at hr'
    rw [e₄]
    linarith

/-- At positive spectral parameter the physical signed map is the existing
upper-half-plane map, with exactly the same normalization. -/
theorem physicalT_positive {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < Y) (κ : ℝ) (u r : Ell2) :
    physicalT hL ha (abs_pos.mpr hY.ne') κ u r =
      QuantumNLS.RiccatiPicardBall.riccatiT hL ha (z := (Y : ℂ) * Complex.I)
        (by simpa using hY) (κ / L) u (jEll u) r :=
  signedT_positive hL ha hY (κ / L) u (jEll u) r


/-- Positive-parameter fixed points satisfy the physical Riccati differential
 equation with the printed coupling, and have a periodic representative. -/
theorem physical_positive_ode (L : ℝ) [hLf : Fact (0 < L)] {a Y : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < Y) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r) :
    (∀ x : ℝ, HasDerivAt (QuantumNLS.RiccatiPointwiseDisc.physRep L a r)
      (-(Y : ℂ) * QuantumNLS.RiccatiPointwiseDisc.physRep L a r x +
        QuantumNLS.RiccatiPointwiseDisc.physRep L a u x -
        (κ : ℂ) * conj (QuantumNLS.RiccatiPointwiseDisc.physRep L a u x) *
          QuantumNLS.RiccatiPointwiseDisc.physRep L a r x ^ 2) x) ∧
      QuantumNLS.RiccatiPointwiseDisc.physRep L a r L =
        QuantumNLS.RiccatiPointwiseDisc.physRep L a r 0 := by
  have hr' := hr
  rw [physicalT_positive hLf.out ha hY] at hr'
  constructor
  · intro x
    have h := QuantumNLS.RiccatiPointwiseDisc.physRep_ode L ha
      (z := (Y : ℂ) * Complex.I) (by simpa using hY) hr' x
    have he : Complex.I * ((Y : ℂ) * Complex.I) = -(Y : ℂ) := by
      calc
        Complex.I * ((Y : ℂ) * Complex.I) = (Y : ℂ) * (Complex.I * Complex.I) := by ring
        _ = -(Y : ℂ) := by simp [← pow_two, Complex.I_sq]
    rw [he] at h
    exact h
  · exact QuantumNLS.RiccatiPointwiseDisc.physRep_periodic hLf.out r

end QuantumNLS.TerraMultiRound39PhysicalBall
#print axioms QuantumNLS.TerraMultiRound39PhysicalBall.physical_fixed_eventually
#print axioms QuantumNLS.TerraMultiRound39PhysicalBall.physicalT_positive
#print axioms QuantumNLS.TerraMultiRound39PhysicalBall.physical_positive_ode
