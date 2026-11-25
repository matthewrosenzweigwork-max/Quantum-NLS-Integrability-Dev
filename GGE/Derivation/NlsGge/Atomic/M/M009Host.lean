import Mathlib
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.Atomic.M.M008Host

/- M-009 HOST01 (proof development, AUTHOR; not reviewed).  Stage 1 of Pro round 13 section 11
   (PRO_DEFINITION_RESPONSE_FP80_13.md, "Literal geometry/integral definitions"), bodies VERBATIM.
   Nothing in NlsGge/ defines any name of namespace NlsGge.ThirdConsultation.MPrimitive (grep, 2026-11-01).
   Lexical changes: import header; `local attribute [instance]` (invalid Lean 4 syntax) -> `attribute [local instance]`. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

def complexGapCut (φ : PotPair) (n : ℤ) : Set ℂ :=
  segment ℝ (lamMinus φ n) (lamPlus φ n)

-- Product-domain ABI required by M.primitiveDomain.
def cutFreeDomain : Set (PotPair × ℂ) := rootDomain38

def cutFreeFiber (φ : PotPair) : Set ℂ :=
  {z | z ∉ gapSegments38 φ}

def endpointClosureFiber (φ : PotPair) : Set ℂ :=
  cutFreeFiber φ ∪
    {z | ∃ n : ℤ, z = lamMinus φ n ∨ z = lamPlus φ n}

def baseEndpoint (φ : PotPair) (upper : Bool) : ℂ :=
  if upper then lamPlus φ 0 else lamMinus φ 0

def AdmissiblePrimitiveChain (φ : PotPair) (a b : ℂ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) : Prop :=
  MContour.ChainCompatible m p ∧
  (∀ i : Fin (m + 1),
    ContinuousOn (p i) (Icc (0 : ℝ) 1) ∧
    ContDiffOn ℝ 1 (p i) (Ioo (0 : ℝ) 1)) ∧
  p 0 0 = a ∧ p (Fin.last m) 1 = b ∧
  (((∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
        p i t ∈ cutFreeFiber φ) ∧
      (∀ i : Fin m, p i.castSucc 1 ∈ cutFreeFiber φ)) ∨
    (a = b ∧
      ∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        p i t = a))

def HasBaseEndpointIntegral (φ : PotPair) (upper : Bool)
    (z A : ℂ) : Prop :=
  ∃ (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ),
    AdmissiblePrimitiveChain φ (baseEndpoint φ upper) z m p ∧
    MContour.HasFiniteChainIntegral φ m p A

def HasSymmetricPrimitiveValue (φ : PotPair) (z A : ℂ) : Prop :=
  φ ∈ gkW ∧ z ∈ endpointClosureFiber φ ∧
    ∃ Aminus Aplus : ℂ,
      HasBaseEndpointIntegral φ false z Aminus ∧
      HasBaseEndpointIntegral φ true z Aplus ∧
      A = (1 / 2 : ℂ) * (Aminus + Aplus)

abbrev PrimitivePoint :=
  {p : PotPair × ℂ // p.1 ∈ gkW ∧ p.2 ∈ endpointClosureFiber p.1}

end
end NlsGge.ThirdConsultation.MPrimitive
