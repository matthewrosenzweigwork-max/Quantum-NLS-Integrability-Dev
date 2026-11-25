import NlsGge.Spectral.ActualScalarParityProjectionLinearEquivV4
import NlsGge.Spectral.ActualEvenOddParitySubspacesOrthogonalV3
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual parity-coordinate linear equivalence preserves the L2 norm. -/
theorem actualScalarParityProjectionLinearEquiv_norm_preserving
    (f : SpectralScalarL2) :
    ‖actualScalarParityProjectionLinearEquiv f‖ = ‖f‖ := by
  let e : scalarParity (0 : ℤ) := actualEvenParityProjection f
  let o : scalarParity (1 : ℤ) := actualOddParityProjection f
  have he : actualScalarParityProjectionLinearEquiv f ⟨0, by norm_num⟩ = e := rfl
  have ho : actualScalarParityProjectionLinearEquiv f ⟨1, by norm_num⟩ = o := rfl
  have hpair :
      ‖actualScalarParityProjectionLinearEquiv f‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 _ (actualScalarParityProjectionLinearEquiv f)]
    rw [Fin.sum_univ_two]
    change ‖(actualScalarParityProjectionLinearEquiv f).ofLp 0‖ ^ 2 +
        ‖(actualScalarParityProjectionLinearEquiv f).ofLp 1‖ ^ 2 = _
    rw [show (actualScalarParityProjectionLinearEquiv f).ofLp 0 = e by
          simpa using he,
        show (actualScalarParityProjectionLinearEquiv f).ofLp 1 = o by
          simpa using ho]
  have horth : inner ℂ (e : SpectralScalarL2) (o : SpectralScalarL2) = 0 :=
    actualEvenOddParitySubspaces_orthogonal_v3 e o
  have hpyth :
      ‖(e : SpectralScalarL2) + (o : SpectralScalarL2)‖ ^ 2 =
        ‖e‖ ^ 2 + ‖o‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (e : SpectralScalarL2) (o : SpectralScalarL2) horth
    rw [← Submodule.norm_coe e, ← Submodule.norm_coe o]
    simpa only [pow_two] using h
  have hrec : (e : SpectralScalarL2) + (o : SpectralScalarL2) = f :=
    actualEvenOddHalfTranslationProjection_add f
  have hfnorm : ‖f‖ ^ 2 = ‖e‖ ^ 2 + ‖o‖ ^ 2 := by
    calc
      ‖f‖ ^ 2 = ‖(e : SpectralScalarL2) + (o : SpectralScalarL2)‖ ^ 2 := by rw [hrec]
      _ = ‖e‖ ^ 2 + ‖o‖ ^ 2 := hpyth
  have hsq : ‖actualScalarParityProjectionLinearEquiv f‖ ^ 2 = ‖f‖ ^ 2 :=
    hpair.trans hfnorm.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The actual parity-coordinate equivalence is an isometry for the L2 norm. -/
noncomputable def actualScalarParityProjectionLinearIsometryEquiv :
    SpectralScalarL2 ≃ₗᵢ[ℂ] ActualScalarParityPair :=
  LinearIsometryEquiv.ofBounds actualScalarParityProjectionLinearEquiv
    (fun f => (actualScalarParityProjectionLinearEquiv_norm_preserving f).le)
    (fun x => by
      have h := actualScalarParityProjectionLinearEquiv_norm_preserving
        (actualScalarParityProjectionLinearEquiv.symm x)
      simpa using h.symm.le)

end NlsGge.Schur

end
