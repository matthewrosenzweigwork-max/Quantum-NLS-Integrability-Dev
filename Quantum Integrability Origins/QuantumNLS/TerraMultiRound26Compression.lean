import QuantumNLS.TerraMultiRound26Parity

/-! Sign-flip covariance of the actual compression matrix. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace QuantumNLS.LocalSpectral.Round26
open Round23 Round24 Round25 QuantumNLS.Local002

/-- The fiber sign flip as a complex-linear bounded map. -/
def fiberParity : E2 →L[ℂ] E2 where
  toLinearMap := {
    toFun := parityFlip
    map_add' := parityFlipIsometry.map_add
    map_smul' := fun c v => by
      ext i
      fin_cases i <;> simp [parityFlip, Jm, vec2] }
  cont := parityFlipIsometry.toContinuousLinearMap.continuous

/-- The fiber sign flip is an involutive complex isometry. -/
def fiberParityIsometry : E2 →ₗᵢ[ℂ] E2 where
  toLinearMap := fiberParity.toLinearMap
  norm_map' v := parityFlipIsometry.norm_map v

theorem fiberParity_involution (v : E2) : fiberParity (fiberParity v) = v :=
  parityFlip_involutive v

theorem fiberParity_inner (v w : E2) :
    ⟪fiberParity v, fiberParity w⟫_ℂ = ⟪v, w⟫_ℂ :=
  fiberParityIsometry.inner_map_map v w

theorem embed_parityOp (L : ℝ) (n : ℤ) (v : E2) :
    parityOp L (embed L n v) = embed L n (fiberParity v) :=
  embed_parity L n v

/-- The adjoint of the actual free embedding also intertwines the sign flip. -/
theorem adjoint_embed_parity (L : ℝ) (n : ℤ) (x : H2 L) :
    (ContinuousLinearMap.adjoint (embed L n)) (parityOp L x) =
      fiberParity ((ContinuousLinearMap.adjoint (embed L n)) x) := by
  apply ext_inner_left ℂ
  intro v
  calc
    ⟪v, (ContinuousLinearMap.adjoint (embed L n)) (parityOp L x)⟫_ℂ =
        ⟪embed L n v, parityOp L x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪parityOp L (embed L n v), x⟫_ℂ := by
      rw [← parityOp_inner L (embed L n v) (parityOp L x), parityOp_involution]
    _ = ⟪embed L n (fiberParity v), x⟫_ℂ := by rw [embed_parityOp]
    _ = ⟪fiberParity v, (ContinuousLinearMap.adjoint (embed L n)) x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪v, fiberParity ((ContinuousLinearMap.adjoint (embed L n)) x)⟫_ℂ := by
      rw [← fiberParity_inner (fiberParity v) ((ContinuousLinearMap.adjoint (embed L n)) x),
        fiberParity_involution]

/-- On the explicit Neumann ball the source compression at `-u` is intertwined
with the compression at `u` by the fiber sign flip. -/
theorem compression_parity {L κ r : ℝ} (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) :
    SemiconjBy fiberParity (compressionMatrix L κ (u : ℝ → ℂ) n r)
      (compressionMatrix L κ (fun t => -(u : ℝ → ℂ) t) n r) := by
  apply ContinuousLinearMap.ext
  intro v
  change fiberParity ((ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n v))) =
    (ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (fun t => -(u : ℝ → ℂ) t) n r (embed L n (fiberParity v)))
  rw [← adjoint_embed_parity, ← embed_parityOp]
  exact congrArg (ContinuousLinearMap.adjoint (embed L n))
    ((contour_parity hyp hr hr2 n u hq (embed L n v)).1).symm

end QuantumNLS.LocalSpectral.Round26
#print axioms QuantumNLS.LocalSpectral.Round26.fiberParity
#print axioms QuantumNLS.LocalSpectral.Round26.fiberParityIsometry
#print axioms QuantumNLS.LocalSpectral.Round26.fiberParity_involution
#print axioms QuantumNLS.LocalSpectral.Round26.fiberParity_inner
#print axioms QuantumNLS.LocalSpectral.Round26.embed_parityOp
#print axioms QuantumNLS.LocalSpectral.Round26.adjoint_embed_parity
#print axioms QuantumNLS.LocalSpectral.Round26.compression_parity
