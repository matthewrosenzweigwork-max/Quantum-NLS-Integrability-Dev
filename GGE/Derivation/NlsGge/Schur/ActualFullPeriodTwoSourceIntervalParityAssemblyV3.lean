import NlsGge.Spectral.ActualTwoChannelParityProjectionNormIsometryV1
import NlsGge.Schur.PhysicalSector
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The source-interval Hilbert space for the two actual period-two parity
blocks, indexed by the periodic and antiperiodic signs. -/
abbrev ActualFullPeriodTwoSourcePair :=
  PiLp 2 (fun p : Fin 2 => SourcePairL2)

/-- The parity-first Fourier carrier: for each sign sector, retain both
physical Bool channels. -/
abbrev ActualFullPeriodTwoParitySectorPair :=
  PiLp 2 (fun p : Fin 2 => ParityPair (p.val : ℤ))

/-- Reindex channel-first parity pieces as parity-first two-channel blocks. -/
def actualTwoChannelParityReindexPair
    (x : ActualTwoChannelParityPair) : ActualFullPeriodTwoParitySectorPair :=
  WithLp.toLp 2 (fun p : Fin 2 =>
    WithLp.toLp 2 (fun b : Bool => x b p))

/-- Undo the finite channel/parity reindexing. -/
def actualFullPeriodTwoParitySectorPairUnreindex
    (x : ActualFullPeriodTwoParitySectorPair) : ActualTwoChannelParityPair :=
  WithLp.toLp 2 (fun b : Bool =>
    WithLp.toLp 2 (fun p : Fin 2 => x p b))

/-- The reindexing between the two Boolean channels and the two parity blocks
is a complex-linear equivalence. -/
def actualTwoChannelParityReindexLinearEquiv :
    ActualTwoChannelParityPair ≃ₗ[ℂ] ActualFullPeriodTwoParitySectorPair where
  toFun := actualTwoChannelParityReindexPair
  invFun := actualFullPeriodTwoParitySectorPairUnreindex
  left_inv x := by
    apply PiLp.ext
    intro b
    apply PiLp.ext
    intro p
    rfl
  right_inv x := by
    apply PiLp.ext
    intro p
    apply PiLp.ext
    intro b
    rfl
  map_add' x y := by
    apply PiLp.ext
    intro p
    apply PiLp.ext
    intro b
    rfl
  map_smul' c x := by
    apply PiLp.ext
    intro p
    apply PiLp.ext
    intro b
    rfl

/-- Reindexing the finite sums preserves the actual nested L² norm. -/
theorem actualTwoChannelParityReindex_norm_preserving
    (x : ActualTwoChannelParityPair) :
    ‖actualTwoChannelParityReindexLinearEquiv x‖ = ‖x‖ := by
  have hsq :
      ‖actualTwoChannelParityReindexLinearEquiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖actualTwoChannelParityReindexLinearEquiv x‖ ^ 2 =
          ∑ p : Fin 2, ‖actualTwoChannelParityReindexLinearEquiv x p‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ p : Fin 2, ∑ b : Bool, ‖x b p‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [PiLp.norm_sq_eq_of_L2 _
          (actualTwoChannelParityReindexLinearEquiv x p)]
        apply Finset.sum_congr rfl
        intro b hb
        rfl
      _ = ∑ b : Bool, ∑ p : Fin 2, ‖x b p‖ ^ 2 := Finset.sum_comm
      _ = ‖x‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2 _ x]
        apply Finset.sum_congr rfl
        intro b hb
        rw [PiLp.norm_sq_eq_of_L2 _ (x b)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Isometric finite reindexing of the two channel and two parity coordinates. -/
noncomputable def actualTwoChannelParityReindexLinearIsometryEquiv :
    ActualTwoChannelParityPair ≃ₗᵢ[ℂ] ActualFullPeriodTwoParitySectorPair :=
  LinearIsometryEquiv.ofBounds actualTwoChannelParityReindexLinearEquiv
    (fun x => (actualTwoChannelParityReindex_norm_preserving x).le)
    (fun y => by
      have h := actualTwoChannelParityReindex_norm_preserving
        (actualTwoChannelParityReindexLinearEquiv.symm y)
      simpa using h.symm.le)

/-- Apply the existing actual parity-to-source-interval isometry in each
periodic/antiperiodic block. The source pair retains the true/false physical
channels with the project’s existing reflected Fourier convention. -/
noncomputable def actualFullPeriodTwoSourceIntervalBlockIsometry :
    ActualFullPeriodTwoParitySectorPair ≃ₗᵢ[ℂ] ActualFullPeriodTwoSourcePair :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun p : Fin 2 => parityPairIntervalEquiv (p.val : ℤ))

/-- Actual two-channel L² on the doubled circle is isometric to the direct sum
of the two actual source-interval blocks (periodic and antiperiodic). This is
the carrier assembly used by later graph-domain and operator-action proofs. -/
noncomputable def actualFullPeriodTwoSourceIntervalAssembly :
    ActualTwoChannelSpectralL2 ≃ₗᵢ[ℂ] ActualFullPeriodTwoSourcePair :=
  actualTwoChannelParityProjectionLinearIsometryEquiv.trans
    (actualTwoChannelParityReindexLinearIsometryEquiv.trans
      actualFullPeriodTwoSourceIntervalBlockIsometry)

/-- The assembly’s true/false coordinates are the source pair in the same
order as the actual source free and potential operators. -/
theorem actualFullPeriodTwoSourceIntervalAssembly_apply
    (x : ActualTwoChannelSpectralL2) (p : Fin 2) (b : Bool) :
    actualFullPeriodTwoSourceIntervalAssembly x p b =
      scalarParityIntervalEquiv (p.val : ℤ)
        ((actualScalarParityProjectionLinearEquiv (x b)) p) := rfl

end NlsGge.Schur

end
