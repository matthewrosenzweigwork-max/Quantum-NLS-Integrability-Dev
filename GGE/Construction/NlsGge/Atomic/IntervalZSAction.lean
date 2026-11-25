import NlsGge.Atomic.IntervalZS
import NlsGge.Atomic.LIB.LIB026
/-! The genuine unit-interval Zakharov--Shabat action on H1 pairs.
The L2 construction is justified by the proved boundedness of H1 representatives.
Real type is a relation between L2 classes; endpoint values come from the canonical
representatives constructed in LIB026. No endpoint condition is imposed here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace NlsGge.Atomic.Interval
open NlsGge.Schur NlsGge.Atomic.LIB026

def IsRealType (φ : SourcePairL2) : Prop := φ false = star (φ true)

lemma h1Value_memLp_top (f : H1) :
    MemLp (fun x => f.value x) ∞ (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply memLp_top_of_bound (Lp.aestronglyMeasurable f.value) (‖f.value‖ + ‖f.derivative‖)
  filter_upwards [representative_ae f, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  rw [← hx, IccExtend_of_mem zero_le_one (representative f) ⟨hmem.1.le, hmem.2⟩]
  exact representative_norm_le f ⟨x, ⟨hmem.1.le, hmem.2⟩⟩

lemma zsExpression_memLp (φ : SourcePairL2) (f : H1Pair) (b : Bool) :
    MemLp (zsExpression φ (fun c x => (f c).value x)
      (fun c x => (f c).derivative x) b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  ((Lp.memLp (f b).derivative).const_mul _).add
    ((Lp.memLp (φ b)).mul (h1Value_memLp_top (f (!b))))

def zsApply (φ : SourcePairL2) (f : H1Pair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => (zsExpression_memLp φ f b).toLp
    (zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) b))

lemma zsApply_ae (φ : SourcePairL2) (f : H1Pair) (b : Bool) :
    (fun x => zsApply φ f b x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) b :=
  (zsExpression_memLp φ f b).coeFn_toLp

def zsBoundaryForm (f g : H1Pair) : ℂ :=
  -Complex.I *
    ((star (traceRight (f true)) * traceRight (g true) -
        star (traceRight (f false)) * traceRight (g false)) -
      (star (traceLeft (f true)) * traceLeft (g true) -
        star (traceLeft (f false)) * traceLeft (g false)))

end NlsGge.Atomic.Interval
