import NlsGge.Schur.SourceIntervalFourierNet
import NlsGge.Schur.FreeCoordinateDomainInverse
import NlsGge.Schur.SourceFiniteFourierIntervalRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace NlsGge.Schur

/-- The actual source interval field represented by the paired coordinates. -/
def sourceCoordinateComponent (n : ℤ) (x : SectorSquare n) (upper : Bool) :
    SourceIntervalL2 := scalarParityRestrict n ((parityPairRepr n).symm x upper)

/-- Both channels, including the genuinely reflected lower channel, have
this complete source-interval Fourier sum. No regularity is assumed here. -/
lemma sourceCoordinateComponent_hasSum (n : ℤ) (x : SectorSquare n) (upper : Bool) :
    HasSum (fun m : Sector n => x (upper,m) •
      scalarParityRestrict n (scalarParityVector n (if upper then m else negateIndex n m)))
      (sourceCoordinateComponent n x upper) := by
  let f : ParityPair n := (parityPairRepr n).symm x
  have hcoord (m : Sector n) :
      scalarParityRepr n (f upper) (mixedIndex n (upper,m)) = x (upper,m) := by
    calc
      _ = parityPairRepr n f (upper,m) := (parityPairRepr_apply n f (upper,m)).symm
      _ = _ := congrArg (fun y : SectorSquare n => y (upper,m))
        ((parityPairRepr n).apply_symm_apply x)
  have hb := sourceInterval_scalarParity_fourier_hasSum n (f upper)
  cases upper
  · have hr := (negateEquiv n).hasSum_iff.mpr hb
    simpa only [← hcoord, mixedIndex, Bool.false_eq_true, if_false,
      sourceCoordinateComponent, f] using! hr
  · simpa only [← hcoord, mixedIndex, if_true, sourceCoordinateComponent, f] using! hb

/-- The actual finite coordinate vectors converge in interval L², in both
channels, along all finite subsets; no arbitrary representative is substituted. -/
lemma sourceCoordinateComponent_finite_tendsto (n : ℤ) (x : SectorSquare n) (upper : Bool) :
    Tendsto (fun S : Finset (Sector n) =>
      scalarParityRestrict n (sourceFiniteParityFourier n upper S (fun m => x (upper,m))))
      atTop (nhds (sourceCoordinateComponent n x upper)) := by
  have h := sourceCoordinateComponent_hasSum n x upper
  simpa only [HasSum, sourceFiniteParityFourier, map_sum, map_smul] using! h

/-- The free coordinate operator supplies an actual L² derivative class;
its upper/lower signs are fixed by the source Dirac convention. The assertion
that this is the weak derivative is proved separately. -/
def sourceFreeCoordinateDerivative (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) : SourceIntervalL2 :=
  (if upper then Complex.I else -Complex.I) •
    sourceCoordinateComponent n (freeCoordinateDirac n ⟨x,hx⟩) upper

end NlsGge.Schur
