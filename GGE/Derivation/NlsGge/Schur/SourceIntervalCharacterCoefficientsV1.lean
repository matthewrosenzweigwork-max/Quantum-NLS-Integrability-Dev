import NlsGge.Schur.SourceFiniteFourierIntervalRepresentative
import NlsGge.Schur.PhysicalSector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.Schur

/-- Actual scalar coordinates of an arbitrary interval L² class, using the
already constructed onto signed-parity restriction isometry. -/
def sourceScalarCoefficient (n : ℤ) (F : SourceIntervalL2) :
    lp (fun _ : Sector n => ℂ) 2 :=
  scalarParityRepr n ((scalarParityIntervalEquiv n).symm F)

lemma sourceRestrictedScalar_character_coefficient
    (n : ℤ) (f : scalarParity n) (m : Sector n) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      scalarParityRestrict n f x * fourier (-m.val) (x : SpectralCircle)) =
      scalarParityRepr n f m := by
  rw [scalarParityRepr_inner,
    ← (scalarParityRestrict n).inner_map_map (scalarParityVector n m) f, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarParityRestrictVector_ae_character n m] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, starRingEnd_apply, fourier_neg]

lemma sourceScalarCoefficient_character_integral
    (n : ℤ) (F : SourceIntervalL2) (m : Sector n) :
    (∫ x in Set.Ioc (0 : ℝ) 1, F x * fourier (-m.val) (x : SpectralCircle)) =
      sourceScalarCoefficient n F m := by
  let f : scalarParity n := (scalarParityIntervalEquiv n).symm F
  have hf : scalarParityRestrict n f = F :=
    (scalarParityIntervalEquiv n).apply_symm_apply F
  calc
    _ = ∫ x in Set.Ioc (0 : ℝ) 1,
        scalarParityRestrict n f x * fourier (-m.val) (x : SpectralCircle) := by rw [hf]
    _ = _ := sourceRestrictedScalar_character_coefficient n f m

end NlsGge.Schur
