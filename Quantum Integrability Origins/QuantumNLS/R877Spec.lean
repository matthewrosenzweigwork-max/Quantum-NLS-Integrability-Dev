import QuantumNLS.TerraMultiRound86Final
/-! integrator-authored trusted spec for R-877E839C (terra_review r240 ACCEPT): the headline type is
`RC05FreqCov.FreqCovCorollary`; it is pinned to its literal body, and `FreqCovClauses` likewise. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric
open QuantumNLS.StrongSymplectic QuantumNLS.RC05Statement
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.RF535Final (Local023Body)
open QuantumNLS.GlobalCompatR47a (Family)
open QuantumNLS.RootIndexedMasses (masses)
namespace QuantumNLS.R877Spec

theorem global_frequency_covariance_spec :
  ∀ (L : ℝ) [Fact (0 < L)], ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
    ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
      Local023Body L d CL Φl Ψl ∧ (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
      ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ →
        ∃ ν : ℝ → ℤ → PosL1 → ℝ,
          (∀ (κ : ℝ) (hκ : 0 < κ), PhysicalFrequency hκ (Φ := Φ κ) (ν κ)) ∧ FreqCovClauses L ν :=
  QuantumNLS.TerraMultiRound86Final.global_frequency_covariance

theorem FreqCovCorollary_literal : QuantumNLS.RC05FreqCov.FreqCovCorollary ↔ (
  ∀ (L : ℝ) [Fact (0 < L)], ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
    ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
      Local023Body L d CL Φl Ψl ∧ (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
      ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ →
        ∃ ν : ℝ → ℤ → PosL1 → ℝ,
          (∀ (κ : ℝ) (hκ : 0 < κ), PhysicalFrequency hκ (Φ := Φ κ) (ν κ)) ∧ FreqCovClauses L ν) := Iff.rfl

theorem FreqCovClauses_literal (L : ℝ) [Fact (0 < L)] (ν : ℝ → ℤ → PosL1 → ℝ) :
    QuantumNLS.RC05Statement.FreqCovClauses L ν ↔ (
  (∀ κ : ℝ, 0 < κ → ∀ (k : ℤ) (a b : PosL1), (∀ n, b.1 n = a.1 (n - k)) → ∀ n, 0 < b.1 n →
    ν κ n b = ν κ (n - k) a + QuantumNLS.LocalSpectral.pm L n ^ 2 - QuantumNLS.LocalSpectral.pm L (n - k) ^ 2) ∧
  (∀ κ : ℝ, 0 < κ → ∀ (a b : PosL1), (∀ n, b.1 n = a.1 (-n)) → ∀ n, 0 < b.1 n →
    ν κ n b = ν κ (-n) a) ∧
  (∀ κ : ℝ, 0 < κ → ∀ s : ℝ, 0 < s → ∀ (a b : PosL1), (∀ n, b.1 n = s ^ 2 * a.1 n) → ∀ n, 0 < a.1 n →
    ν κ n b = ν (κ * s ^ 2) n a) ∧
  (∀ (κ : ℝ) (hκ : 0 < κ) (u : L2T L),
    (∀ n, (masses hκ (star u)).1 n = (masses hκ u).1 (-n)) ∧
    ∀ n, 0 < (masses hκ (star u)).1 n → ν κ n (masses hκ (star u)) = ν κ (-n) (masses hκ u)) ∧
  (∀ (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (γ y : ℝ),
    masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u) = masses hκ u ∧
    masses hκ (QuantumNLS.BornTranslation.trans y u) = masses hκ u ∧
    (∀ n, ν κ n (masses hκ (Complex.exp ((γ : ℂ) * Complex.I) • u)) = ν κ n (masses hκ u)) ∧
    (∀ n, ν κ n (masses hκ (QuantumNLS.BornTranslation.trans y u)) = ν κ n (masses hκ u)))) := Iff.rfl

end QuantumNLS.R877Spec
#print axioms QuantumNLS.R877Spec.global_frequency_covariance_spec
#print axioms QuantumNLS.R877Spec.FreqCovCorollary_literal
