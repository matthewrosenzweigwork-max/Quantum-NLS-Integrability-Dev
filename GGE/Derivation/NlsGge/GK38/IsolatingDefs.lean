import NlsGge.GK38.NeumannLabels
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Exact approved GK I.12 isolating geometry and four-spectrum certificates.
The neighbourhood uses certified balls centered on the actual real slice. -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def ballDistance38 (c d : ℂ) (r s : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ z ∈ ball c r, ∃ w ∈ ball d s, v = dist z w}

def IsolatingGeometry38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ) : Prop :=
  (∀ n : ℤ, 0 < R n ∧ (C n).im = 0) ∧ StrictMono (fun n => (C n).re) ∧
  1 ≤ c ∧ (∀ m n : ℤ, m ≠ n →
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ballDistance38 (C m) (C n) (R m) (R n) ∧
    ballDistance38 (C m) (C n) (R m) (R n) ≤ c * |((m - n : ℤ) : ℝ)|) ∧
  (∀ n : ℤ, (N : ℤ) < |n| → C n = countingCenter38 n ∧ R n = Real.pi / 4 ∧
    ball (C n) (R n) = ball (countingCenter38 n) (Real.pi / 4))

def IsolatingSpectral38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) : Prop :=
  (∀ n : ℤ, segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) (R n) ∧
    muSeq φ n ∈ ball (C n) (R n) ∧ nuSeq38 φ n ∈ ball (C n) (R n) ∧
    lamDot φ n ∈ ball (C n) (R n) ∧
    (lamMinus φ n ::ₘ lamPlus φ n ::ₘ 0) = Lib.zeroMultiset (perChar φ) (ball (C n) (R n)) ∧
    ({muSeq φ n} : Multiset ℂ) = Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n)) ∧
    ({nuSeq38 φ n} : Multiset ℂ) = Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n)) ∧
    ({lamDot φ n} : Multiset ℂ) = Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n)) ∧
    (Lib.zeroMultiset (perChar φ) (ball (C n) (R n))).card = 2 ∧
    (Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n))).card = 1 ∧
    (Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n))).card = 1 ∧
    (Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n))).card = 1 ∧
    (∀ z : ℂ, z ∈ sphere (C n) (R n) → perChar φ z ≠ 0 ∧
      dirichletChar φ z ≠ 0 ∧ neumannChar38 φ z ≠ 0 ∧ deriv (discrim φ) z ≠ 0)) ∧
  (∀ z : ℂ, perChar φ z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n)) ∧
  (∀ z : ℂ, dirichletChar φ z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n)) ∧
  (∀ z : ℂ, neumannChar38 φ z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n)) ∧
  (∀ z : ℂ, deriv (discrim φ) z = 0 → ∃ n : ℤ, z ∈ ball (C n) (R n))

def IsolatingFamily38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) : Prop :=
  ∃ c : ℝ, ∃ N : ℕ, IsolatingGeometry38 C R c N ∧ IsolatingSpectral38 φ C R

def CertifiedRealBall38 (u : PhysicalL2) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ,
    IsolatingGeometry38 C R c N ∧ ∀ φ : PotPair, φ ∈ ball (realSlice u) ρ → IsolatingSpectral38 φ C R

def gkW : Set PotPair := {φ | ∃ u : PhysicalL2, ∃ ρ : ℝ,
  CertifiedRealBall38 u ρ ∧ φ ∈ ball (realSlice u) ρ}

end
end NlsGge.GK38
