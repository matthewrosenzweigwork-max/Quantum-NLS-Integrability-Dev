import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.PeriodicLabellingCriticalFree

/- M-008 HOST01 (proof development, AUTHOR; not reviewed).  Local host of Pro round 6 section 10E (PRO_DEFINITION_RESPONSE_FP80_06.md
   lines ~3430-3540), definition bodies verbatim; round 7/8 README: "M-008 reuses round 6 section 10E"; rounds 9-12 add no M-008 text.
   Nothing in NlsGge/ defines any name of namespace NlsGge.ThirdConsultation.MContour (grep, 2026-11-01).
   Lexical changes: only `set_option autoImplicit false` and the import header. -/
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

def omega (φ : PotPair) (z : ℂ) : ℂ :=
  deriv (discrim φ) z / canonRoot38 φ z

def gapContour (φ : PotPair) (n : ℤ) (t : ℝ) : ℂ :=
  discC φ n + (discR φ n : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

def contourIntegral (p : ℝ → ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (p t) * deriv p t

def AdmissibleGapLoop (φ : PotPair) (n : ℤ) (p : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 1 p (Set.Icc (0 : ℝ) 1) ∧ p 0 = p 1 ∧
  ∀ t ∈ Set.Icc (0 : ℝ) 1,
    p t ∈ discU φ n ∧ p t ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)

def AdmissibleEndpointCurve (φ : PotPair) (n : ℤ) (p : ℝ → ℂ) : Prop :=
  ContinuousOn p (Set.Icc (0 : ℝ) 1) ∧
  ContDiffOn ℝ 1 p (Set.Ioo (0 : ℝ) 1) ∧
  p 0 = lamMinus φ n ∧ p 1 = lamPlus φ n ∧
  ((∀ t ∈ Set.Ioo (0 : ℝ) 1,
      p t ∈ discU φ n ∧ p t ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) ∨
    (lamMinus φ n = lamPlus φ n ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, p t = lamMinus φ n))

def HasEndpointIntegral (φ : PotPair) (p : ℝ → ℂ) (a : ℂ) : Prop :=
  (∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
    IntervalIntegrable (fun t : ℝ => omega φ (p t) * deriv p t)
      volume ε (1 - η)) ∧
  Tendsto
    (fun q : ℝ × ℝ =>
      ∫ t in q.1..(1 - q.2), omega φ (p t) * deriv p t)
    (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] (0, 0))
    (𝓝 a)

-- A nonempty finite chain, with each piece parametrized on [0,1].
-- Fin.castSucc and Fin.succ name the two pieces adjacent to a junction.
def ChainCompatible (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) : Prop :=
  ∀ i : Fin m, p i.castSucc 1 = p i.succ 0

def AdmissibleGapLoopChain (φ : PotPair) (n : ℤ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) : Prop :=
  ChainCompatible m p ∧ p (Fin.last m) 1 = p 0 0 ∧
  ∀ i : Fin (m + 1),
    ContDiffOn ℝ 1 (p i) (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      p i t ∈ discU φ n ∧
      p i t ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)

def AdmissibleEndpointChain (φ : PotPair) (n : ℤ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) : Prop :=
  ChainCompatible m p ∧
  (∀ i : Fin (m + 1),
    ContinuousOn (p i) (Set.Icc (0 : ℝ) 1) ∧
    ContDiffOn ℝ 1 (p i) (Set.Ioo (0 : ℝ) 1)) ∧
  p 0 0 = lamMinus φ n ∧ p (Fin.last m) 1 = lamPlus φ n ∧
  (((∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 →
        p i t ∈ discU φ n ∧
        p i t ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) ∧
      (∀ i : Fin m,
        p i.castSucc 1 ∈ discU φ n ∧
        p i.castSucc 1 ∉ segment ℝ (lamMinus φ n) (lamPlus φ n))) ∨
    (lamMinus φ n = lamPlus φ n ∧
      ∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        p i t = lamMinus φ n))

-- Each piece has its own joint two-endpoint improper integral.
-- Their finite sum is the integral of the concatenated chain.
def HasFiniteChainIntegral (φ : PotPair) (m : ℕ)
    (p : Fin (m + 1) → ℝ → ℂ) (a : ℂ) : Prop :=
  ∃ I : Fin (m + 1) → ℂ,
    (∀ i : Fin (m + 1), HasEndpointIntegral φ (p i) (I i)) ∧
    (∑ i : Fin (m + 1), I i) = a

end
end NlsGge.ThirdConsultation.MContour
