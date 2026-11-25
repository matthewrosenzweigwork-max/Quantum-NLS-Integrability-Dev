import QuantumNLS.TerraMultiRound25Parity
import QuantumNLS.TerraMultiRound24Embed

/-! Intertwining of the actual inverse-square-root compression series. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.LocalSpectral.Round26

/-- An intertwiner of two small compressions also intertwines the convergent
inverse-square-root series. The two norm assumptions are exactly those used by
`SmallCompression`; the intertwining relation is a separate intermediate goal. -/
theorem invSqrtM_intertwine (J A B : E2 →L[ℂ] E2)
    (hA : ‖A - 1‖ < 1) (hB : ‖B - 1‖ < 1)
    (h : SemiconjBy J A B) : SemiconjBy J (invSqrtM A) (invSqrtM B) := by
  unfold invSqrtM
  apply SemiconjBy.tsum_right J (summable_invSqrtM hA) (summable_invSqrtM hB)
  intro k
  have hs : SemiconjBy J (A - 1) (B - 1) := h.sub_right (SemiconjBy.one_right J)
  exact (hs.pow_right k).smul_right ((invSqrtCoeff k : ℂ))

/-- The preceding series law instantiated on the source's compression matrices. -/
theorem invSqrtCompression_intertwine {L κ : ℝ} {u v : ℝ → ℂ} {n : ℤ} {r : ℝ}
    (hu : SmallCompression L κ u n r) (hv : SmallCompression L κ v n r)
    (J : E2 →L[ℂ] E2)
    (h : SemiconjBy J (compressionMatrix L κ u n r) (compressionMatrix L κ v n r)) :
    SemiconjBy J (invSqrtCompression L κ u n r hu) (invSqrtCompression L κ v n r hv) :=
  invSqrtM_intertwine J _ _ hu hv h

end QuantumNLS.LocalSpectral.Round26
#print axioms QuantumNLS.LocalSpectral.Round26.invSqrtM_intertwine
#print axioms QuantumNLS.LocalSpectral.Round26.invSqrtCompression_intertwine
