import NlsGge.GK38.PeriodicLabellingCriticalCounting
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort

/-! # S2: certified-cutoff candidates; defaults require proved index bounds -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def complexLexLE38 (z w : ℂ) : Prop :=
  toLex (Complex.equivRealProd z) ≤ toLex (Complex.equivRealProd w)

def sortComplexRoots38 (s : Multiset ℂ) : List ℂ :=
  ((s.map (fun z => toLex (Complex.equivRealProd z))).sort).map
    (fun p : Lex (ℝ × ℝ) => Complex.equivRealProd.symm (ofLex p))

def centralRoots (f : ℂ → ℂ) (N : ℕ) : List ℂ :=
  sortComplexRoots38 (Lib.zeroMultiset f (ball 0 (countingRadius38 N)))

def smallRoots (f : ℂ → ℂ) (n : ℤ) : List ℂ :=
  sortComplexRoots38 (Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)))

/-- Candidate only. Future certified-cutoff proofs must exclude every getD default. -/
def periodicCandidate38 (f : ℂ → ℂ) (N : ℕ) (k : ℤ) : ℂ :=
  if -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1 then
    (centralRoots f N).getD (k + 2 * (N : ℤ)).toNat 0
  else
    (smallRoots f (k / 2)).getD (k % 2).toNat 0

def criticalCandidate38 (f : ℂ → ℂ) (N : ℕ) (n : ℤ) : ℂ :=
  if -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) then
    (centralRoots f N).getD (n + (N : ℤ)).toNat 0
  else
    (smallRoots f n).getD 0 0

def minusFromSeq38 (L : PotPair → ℤ → ℂ) (φ : PotPair) (n : ℤ) : ℂ := L φ (2 * n)
def plusFromSeq38 (L : PotPair → ℤ → ℂ) (φ : PotPair) (n : ℤ) : ℂ := L φ (2 * n + 1)

/-- The hypotheses that will be realized by S1 or the derivative counting proof. -/
def RootCountingAt38 (f : ℂ → ℂ) (q N : ℕ) : Prop :=
  0 < N ∧ AnalyticOnNhd ℂ f univ ∧ (∃ w : ℂ, f w ≠ 0) ∧
  (∀ c : ℂ, ∀ r : ℝ, (Function.support (Lib.zeroMult f (ball c r))).Finite) ∧
  (∀ n : ℤ, (N : ℤ) < |n| →
    Multiset.card (Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4))) = q) ∧
  Multiset.card (Lib.zeroMultiset f (ball 0 (countingRadius38 N))) = q * (2 * N + 1) ∧
  ∀ z : ℂ, f z = 0 → z ∈ ball 0 (countingRadius38 N) ∨
    ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4)

end
end NlsGge.GK38
