import QuantumNLS.TerraMultiRound26Compression

/-! Sign-flip covariance of the actual normalized and reduced maps. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace QuantumNLS.LocalSpectral.Round26
open Round23 Round24 Round25 QuantumNLS.Local002

variable {L κ r : ℝ} (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1)
    (hu : SmallCompression L κ (u : ℝ → ℂ) n r)
    (hv : SmallCompression L κ (fun t => -(u : ℝ → ℂ) t) n r)

include hyp hr hr2 hq

/-- Covariance passes through the actual convergent inverse-square-root series. -/
theorem invSqrtCompression_parity :
    SemiconjBy fiberParity (invSqrtCompression L κ (u : ℝ → ℂ) n r hu)
      (invSqrtCompression L κ (fun t => -(u : ℝ → ℂ) t) n r hv) :=
  invSqrtCompression_intertwine hu hv fiberParity (compression_parity hyp hr hr2 n u hq)

/-- The normalized map intertwines the source sign flips. -/
theorem normalized_parity (v : E2) :
    normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv (fiberParity v) =
      parityOp L (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v) := by
  have hs := invSqrtCompression_parity hyp hr hr2 n u hq hu hv
  have hs' := congrArg (fun T : E2 →L[ℂ] E2 => T v) hs
  change fiberParity (invSqrtCompression L κ (u : ℝ → ℂ) n r hu v) =
    invSqrtCompression L κ (fun t => -(u : ℝ → ℂ) t) n r hv (fiberParity v) at hs'
  change perturbedProj L κ (fun t => -(u : ℝ → ℂ) t) n r
      (embed L n (invSqrtCompression L κ (fun t => -(u : ℝ → ℂ) t) n r hv (fiberParity v))) =
    parityOp L (perturbedProj L κ (u : ℝ → ℂ) n r
      (embed L n (invSqrtCompression L κ (u : ℝ → ℂ) n r hu v)))
  rw [← hs', ← embed_parityOp]
  exact (contour_parity hyp hr hr2 n u hq _).1

/-- The adjoint normalized maps obey the corresponding covariance. -/
theorem adjoint_normalized_parity (x : H2 L) :
    (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv))
        (parityOp L x) =
      fiberParity ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x) := by
  apply ext_inner_left ℂ
  intro v
  have hn := normalized_parity hyp hr hr2 n u hq hu hv (fiberParity v)
  rw [fiberParity_involution] at hn
  have hn' : parityOp L (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv v) =
      normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (fiberParity v) := by
    rw [hn, parityOp_involution]
  calc
    ⟪v, (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv))
      (parityOp L x)⟫_ℂ =
        ⟪normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv v, parityOp L x⟫_ℂ :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪parityOp L (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv v), x⟫_ℂ := by
      rw [← parityOp_inner L _ (parityOp L x), parityOp_involution]
    _ = ⟪normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (fiberParity v), x⟫_ℂ := by rw [hn']
    _ = ⟪fiberParity v, (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪v, fiberParity ((ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu)) x)⟫_ℂ := by
      rw [← fiberParity_inner (fiberParity v) _, fiberParity_involution]

/-- The actual reduced maps at `u` and `-u` are intertwined by the fiber sign flip. -/
theorem reducedMatrix_parity :
    SemiconjBy fiberParity (reducedMatrix2 L κ (u : ℝ → ℂ) n r hu)
      (reducedMatrix2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv) := by
  apply ContinuousLinearMap.ext
  intro v
  change fiberParity ((pm L n : ℂ) • v +
      (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu))
        (dressedIntegral L κ (u : ℝ → ℂ) n r (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v))) =
    (pm L n : ℂ) • fiberParity v +
      (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv))
        (dressedIntegral L κ (fun t => -(u : ℝ → ℂ) t) n r
          (normalizedIsometry2 L κ (fun t => -(u : ℝ → ℂ) t) n r hv (fiberParity v)))
  rw [map_add, map_smul, normalized_parity hyp hr hr2 n u hq hu hv,
    (contour_parity hyp hr hr2 n u hq _).2,
    adjoint_normalized_parity hyp hr hr2 n u hq hu hv]

end QuantumNLS.LocalSpectral.Round26
#print axioms QuantumNLS.LocalSpectral.Round26.invSqrtCompression_parity
#print axioms QuantumNLS.LocalSpectral.Round26.normalized_parity
#print axioms QuantumNLS.LocalSpectral.Round26.adjoint_normalized_parity
#print axioms QuantumNLS.LocalSpectral.Round26.reducedMatrix_parity
