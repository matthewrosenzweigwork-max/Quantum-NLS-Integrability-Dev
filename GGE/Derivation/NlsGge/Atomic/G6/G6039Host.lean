import Mathlib
import NlsGge.Atomic.G6.G6038Host

/- G6039 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6039Host.lean.
   Hosts ONCE, namespace NlsGge.GKDefinitionDesign, bodies byte-identical to followup13:
   * DEFINITIONS/G6.lean.md:271-276: flipComplexCoordinate, CoordinatewiseEvenOn (G6-039 head vocabulary);
   * STATEMENTS/G6.md:1294-1305 (Pro round 14 "Local complexification and parametrized infinite-tail descent"):
     parametricActionDescent, complexHeadLift, complexTailProjection.
   ComplexDiagonalSpace / ComplexActionSpace / complexActionRoot: landed-pending G6038Host (proof development).
   grep NlsGge/ (2026-11-02): none of these names exists. -/
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

def flipComplexCoordinate (n : ℤ) (x : ComplexDiagonalSpace) : ComplexDiagonalSpace :=
  x - lp.single 2 n (2 * x n)

def CoordinatewiseEvenOn (f : ComplexDiagonalSpace → ℂ)
    (S : Set ℤ) (U : Set ComplexDiagonalSpace) : Prop :=
  ∀ x ∈ U, ∀ n ∈ S, f (flipComplexCoordinate n x) = f x

def parametricActionDescent
    {P : Type*} (f : P × ComplexDiagonalSpace → ℂ)
    (q : P × ComplexActionSpace) : ℂ :=
  f (q.1, complexActionRoot q.2)

def complexHeadLift (F : Finset ℤ) (p : F → ℂ) : ComplexDiagonalSpace :=
  ∑ n : F, lp.single 2 (n : ℤ) (p n)

def complexTailProjection (F : Finset ℤ) (x : ComplexDiagonalSpace) :
    ComplexDiagonalSpace :=
  x - ∑ n ∈ F, lp.single 2 n (x n)

end
end NlsGge.GKDefinitionDesign
