import QuantumNLS.TerraMultiRound88Markov
import QuantumNLS.HilbertDiagOp
import QuantumNLS.TerraMultiRound89Orthogonal
import QuantumNLS.TerraMultiRound87Quantum

/-! The Markov bound for an actual Hilbert-space orthogonal spectral mask.
This is a generic projection bridge; a concrete first-moment/form identity
is still required to apply it to the product state. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.OccupationHilbert QuantumNLS.Ext025B3DiagonalForms
namespace QuantumNLS.TerraMultiRound89SpectralProjection

/-- Any bounded operator with the 0/1 mask on a complete basis is exactly
an orthogonal projection. -/
theorem spectral_mask_orthogonal {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (ev : ι → ℝ) (E : ℝ) (P : H →L[ℂ] H)
    (hP : ∀ i, P (b i) = ((if ev i ≤ E then (1 : ℝ) else 0 : ℝ) : ℂ) • b i) :
    P * P = P ∧ ContinuousLinearMap.adjoint P = P := by
  classical
  let μ : ι → ℝ := fun i => if ev i ≤ E then 1 else 0
  have hμ : ∀ i, μ i = 0 ∨ μ i = 1 := by
    intro i
    by_cases h : ev i ≤ E <;> simp [μ, h]
  obtain ⟨Q, hQ, hQQ, hQsa⟩ := EnergyProjection.diag_projection b μ hμ
  have heq : P = Q := by
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    rw [hP i, hQ i]
  rw [heq]
  exact ⟨hQQ, hQsa⟩

/-- A 0/1 diagonal energy mask discards at most its first spectral moment
divided by the positive cutoff. -/
theorem spectral_projection_defect {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H)
    (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i) (E : ℝ) (hE : 0 < E)
    (P : H →L[ℂ] H)
    (hP : ∀ i, P (b i) = ((if ev i ≤ E then (1 : ℝ) else 0 : ℝ) : ℂ) • b i)
    (v : H) (hv : InFormDomain ev (b.repr v)) :
    ‖v - P v‖ ^ 2 ≤ ‖formRoot ev (b.repr v) hv‖ ^ 2 / E := by
  classical
  have heq : ‖v - P v‖ ^ 2 = ∑' i, if E < ev i then ‖b.repr v i‖ ^ 2 else 0 := by
    rw [← b.repr.norm_map, norm_sq_tsum]
    apply tsum_congr
    intro i
    rw [map_sub]
    change ‖b.repr v i - b.repr (P v) i‖ ^ 2 = _
    simp only [HilbertBasis.repr_apply_apply]
    rw [HilbertDiagOp.eig_coeff b P (fun i => ((if ev i ≤ E then (1 : ℝ) else 0 : ℝ) : ℂ)) hP]
    by_cases hi : ev i ≤ E
    · simp [hi, not_lt_of_ge hi]
    · simp [hi, lt_of_not_ge hi]
  rw [heq]
  exact TerraMultiRound88Markov.spectral_markov ev hev (b.repr v) hv E hE

/-- The projector supplied by the accepted high-angle theorem is an
orthogonal projection on the actual Bethe basis. -/
theorem actual_mask_orthogonal {L κ E : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    {N : ℕ} (hN : 0 < N)
    (P : QuantumNLS.BetheCoefficientTransform.HN L N →L[ℂ] QuantumNLS.BetheCoefficientTransform.HN L N)
    (hP : ∀ m, P (HaarSpectralTail.bas L hκ hN m) =
      HaarSpectralTail.mask L κ N E m • HaarSpectralTail.bas L hκ hN m) :
    P * P = P ∧ ContinuousLinearMap.adjoint P = P := by
  classical
  apply spectral_mask_orthogonal (HaarSpectralTail.bas L hκ hN)
    (fun m => EnergyProjection.energyEig L κ N (NormalityBridge.label m)) ((N : ℝ) * E) P
  intro m
  by_cases h : EnergyProjection.energyEig L κ N (NormalityBridge.label m) ≤ (N : ℝ) * E
  · simpa [HaarSpectralTail.mask, HaarSpectralTail.adm, h] using hP m
  · simpa [HaarSpectralTail.mask, HaarSpectralTail.adm, h] using hP m

#print axioms actual_mask_orthogonal
#print axioms spectral_mask_orthogonal
#print axioms spectral_projection_defect
end QuantumNLS.TerraMultiRound89SpectralProjection
