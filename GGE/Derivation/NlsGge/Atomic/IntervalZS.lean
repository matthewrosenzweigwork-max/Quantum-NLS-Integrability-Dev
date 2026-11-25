import NlsGge.Atomic.IntervalH1
import NlsGge.Schur.PhysicalSector

/-! Literal unit-interval Zakharov--Shabat expressions and adjoint test pairing.
The existing paired L2 carrier uses the sum-of-squares norm. Boolean `true`
labels the upper component. These definitions impose no endpoint relation,
real-type condition, or regularity conclusion on an adjoint witness. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NlsGge.Atomic.Interval

open NlsGge.Schur

/-- Two independent interval H1 components, before any boundary condition. -/
abbrev H1Pair := Bool → H1

/-- The actual paired L2 values, with the repository's Hilbert pair norm. -/
def h1PairValue (f : H1Pair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b => (f b).value)

/-- `i diag(1,-1) f' + [[0,phi1],[phi2,0]] f`, with upper component `true`. -/
def zsExpression (φ : SourcePairL2) (f df : Bool → ℝ → ℂ)
    (b : Bool) (x : ℝ) : ℂ :=
  (if b then Complex.I else -Complex.I) * df b x + φ b x * f (!b) x

/-- The literal adjoint equality against all smooth compactly supported pairs.
The inner-product convention is conjugate-linear in the first slot. -/
def IsAdjointDomainWitness (φ g h : SourcePairL2) : Prop :=
  ∀ f : Bool → ℝ → ℂ,
    (∀ b, ContDiff ℝ ∞ (f b)) →
    (∀ b, HasCompactSupport (f b)) →
    (∀ b, tsupport (f b) ⊆ Ioo (0 : ℝ) 1) →
    (∫ x in (0 : ℝ)..1,
      star (zsExpression φ f (fun b => deriv (f b)) true x) * g true x +
      star (zsExpression φ f (fun b => deriv (f b)) false x) * g false x) =
    (∫ x in (0 : ℝ)..1,
      star (f true x) * h true x + star (f false x) * h false x)

end NlsGge.Atomic.Interval
