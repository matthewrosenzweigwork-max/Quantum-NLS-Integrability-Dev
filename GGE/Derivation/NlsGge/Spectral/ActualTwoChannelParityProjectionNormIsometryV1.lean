import NlsGge.Spectral.ActualScalarParityProjectionNormIsometryV3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Two actual complex L² channels on the doubled period-two spectral circle. -/
abbrev ActualTwoChannelSpectralL2 :=
  PiLp 2 (fun _ : Bool => SpectralScalarL2)

/-- Each physical channel, split into its actual even and odd half-translation
subspaces on the doubled circle. -/
abbrev ActualTwoChannelParityPair :=
  PiLp 2 (fun _ : Bool => ActualScalarParityPair)

/-- Apply the actual scalar even/odd projection to both Boolean channels. -/
def actualTwoChannelParityProjectionPair
    (x : ActualTwoChannelSpectralL2) : ActualTwoChannelParityPair :=
  WithLp.toLp 2 (fun b : Bool =>
    actualScalarParityProjectionLinearEquiv (x b))

/-- Reconstruct each doubled-circle scalar channel from its two parity pieces. -/
def actualTwoChannelParityReconstruction
    (x : ActualTwoChannelParityPair) : ActualTwoChannelSpectralL2 :=
  WithLp.toLp 2 (fun b : Bool =>
    actualScalarParityProjectionLinearEquiv.symm (x b))

/-- The two-channel parity decomposition is a genuine complex-linear
equivalence. Its input is a Bool-indexed pair of full doubled-circle L²
classes; its output stores, for each channel, the even and odd eigenspaces of
translation by one on the period-two circle. -/
def actualTwoChannelParityProjectionLinearEquiv :
    ActualTwoChannelSpectralL2 ≃ₗ[ℂ] ActualTwoChannelParityPair where
  toFun := actualTwoChannelParityProjectionPair
  invFun := actualTwoChannelParityReconstruction
  left_inv x := by
    apply PiLp.ext
    intro b
    change actualScalarParityProjectionLinearEquiv.symm
      (actualScalarParityProjectionLinearEquiv (x b)) = x b
    exact actualScalarParityProjectionLinearEquiv.left_inv (x b)
  right_inv x := by
    apply PiLp.ext
    intro b
    change actualScalarParityProjectionLinearEquiv
      (actualScalarParityProjectionLinearEquiv.symm (x b)) = x b
    exact actualScalarParityProjectionLinearEquiv.right_inv (x b)
  map_add' x y := by
    apply PiLp.ext
    intro b
    change actualScalarParityProjectionLinearEquiv (x b + y b) =
      actualScalarParityProjectionLinearEquiv (x b) +
        actualScalarParityProjectionLinearEquiv (y b)
    exact map_add actualScalarParityProjectionLinearEquiv (x b) (y b)
  map_smul' c x := by
    apply PiLp.ext
    intro b
    change actualScalarParityProjectionLinearEquiv (c • x b) =
      c • actualScalarParityProjectionLinearEquiv (x b)
    exact map_smul actualScalarParityProjectionLinearEquiv c (x b)

/-- The Boolean two-channel parity decomposition preserves the actual
sum-of-squares L² norm. -/
theorem actualTwoChannelParityProjection_norm_preserving
    (x : ActualTwoChannelSpectralL2) :
    ‖actualTwoChannelParityProjectionLinearEquiv x‖ = ‖x‖ := by
  have hchannel (b : Bool) :
      ‖actualTwoChannelParityProjectionPair x b‖ ^ 2 = ‖x b‖ ^ 2 := by
    change ‖actualScalarParityProjectionLinearEquiv (x b)‖ ^ 2 = ‖x b‖ ^ 2
    rw [actualScalarParityProjectionLinearEquiv_norm_preserving]
  have hsq :
      ‖actualTwoChannelParityProjectionLinearEquiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖actualTwoChannelParityProjectionLinearEquiv x‖ ^ 2 =
          ∑ b : Bool, ‖actualTwoChannelParityProjectionLinearEquiv x b‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ b : Bool, ‖x b‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hchannel b
      _ = ‖x‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ x).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Isometric version of the actual two-channel, period-two parity
decomposition. The theorem concerns only the carrier norm and does not assert
invariance of an unbounded Dirac domain or identify its operator action. -/
noncomputable def actualTwoChannelParityProjectionLinearIsometryEquiv :
    ActualTwoChannelSpectralL2 ≃ₗᵢ[ℂ] ActualTwoChannelParityPair :=
  LinearIsometryEquiv.ofBounds actualTwoChannelParityProjectionLinearEquiv
    (fun x => (actualTwoChannelParityProjection_norm_preserving x).le)
    (fun y => by
      have h := actualTwoChannelParityProjection_norm_preserving
        (actualTwoChannelParityProjectionLinearEquiv.symm y)
      simpa using h.symm.le)

end NlsGge.Schur

end
