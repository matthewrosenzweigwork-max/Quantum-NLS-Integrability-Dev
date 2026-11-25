import NlsGge.Schur.PhysicalSector
import NlsGge.Schur.SourceIntervalWeakPairingLimit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace NlsGge.Schur
/-- Actual interval restriction of the complete scalar Fourier basis sum. -/
lemma sourceInterval_scalarParity_fourier_hasSum (n : ℤ) (f : scalarParity n) :
    HasSum (fun m : Sector n => scalarParityRepr n f m •
      scalarParityRestrict n (scalarParityVector n m)) (scalarParityRestrict n f) := by
  have h := ((scalarParityFourierBasis n).hasSum_repr f).mapL
    (scalarParityRestrict n).toContinuousLinearMap
  simpa only [map_smul, scalarParityRepr, scalarParityFourierBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot] using! h
/-- Weak integration-by-parts passes along arbitrary nontrivial nets in the
actual unit-interval L² space. Fourier finite subsets use this exact net. -/
lemma sourceIntervalWeakPairingLimit_net {ι : Type*} {l : Filter ι} [NeBot l]
    (f g : ι → SourceIntervalL2) (F G test testDerivative : SourceIntervalL2)
    (hf : Tendsto f l (nhds F)) (hg : Tendsto g l (nhds G))
    (hweak : ∀ k,
      (∫ x in Set.Ioc (0 : ℝ) 1, f k x * testDerivative x) =
        -(∫ x in Set.Ioc (0 : ℝ) 1, g k x * test x)) :
    (∫ x in Set.Ioc (0 : ℝ) 1, F x * testDerivative x) =
      -(∫ x in Set.Ioc (0 : ℝ) 1, G x * test x) := by
  have hleft := ((sourceIntervalTestPairing testDerivative).continuous.tendsto F).comp hf
  have hright := (((sourceIntervalTestPairing test).continuous.tendsto G).comp hg).neg
  simp only [Function.comp_def, sourceIntervalTestPairing_integral] at hleft hright
  exact tendsto_nhds_unique hleft (hright.congr (fun k => (hweak k).symm))
end NlsGge.Schur
