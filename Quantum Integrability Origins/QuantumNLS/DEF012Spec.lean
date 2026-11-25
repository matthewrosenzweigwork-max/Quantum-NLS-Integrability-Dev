import QuantumNLS.RapidityTransport
/-! integrator-authored trusted spec for DEF-012 (DEFINITIONS_LEDGER.md def:report-12), parametric in A.
W_p(μ,ν) = inf over couplings π of probability measures of (∫|x−y|^p dπ)^{1/p}; for p ≥ 1 and finite p-th
moments it is finite (a coupling exists). Weighted occupation error Σ_n (1+|n|)^a |m_n/N − A_n| ∈ [0,∞],
finite for nonnegative A with Σ(1+|n|)^a A_n < ∞. Convergence in probability: P_N{ε < error} → 0
(no moment convergence asserted). -/
namespace DEF012Spec
open QuantumNLS.RapidityTransport QuantumNLS.BetheLabels MeasureTheory Filter Topology
open scoped ENNReal

theorem spec :
    (∀ (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ), IsCoupling π μ ν ↔
      (IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν)) ∧
    (∀ (p : ℝ) (μ ν : Measure ℝ), wasserstein p μ ν =
      ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π μ ν), (∫⁻ z, ‖z.1 - z.2‖ₑ ^ p ∂π) ^ (1 / p)) ∧
    (∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (p : ℝ), 1 ≤ p →
      (∫⁻ x, ‖x‖ₑ ^ p ∂μ) < ∞ → (∫⁻ x, ‖x‖ₑ ^ p ∂ν) < ∞ → wasserstein p μ ν < ∞) ∧
    (∀ (p : ℝ) (μ ν : Measure ℝ), wasserstein p μ ν = wasserstein p ν μ) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ), 0 < p → wasserstein p μ μ = 0) ∧
    (∀ (a : ℝ) (A : ℤ → ℝ) (N : ℕ) (m : MArr N), weightedError a A N m =
      ∑' n : ℤ, ENNReal.ofReal ((1 + |(n : ℝ)|) ^ a * |(m.1 n : ℝ) / N - A n|)) ∧
    (∀ (a : ℝ) (A : ℤ → ℝ), (∀ n, 0 ≤ A n) → Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ a * A n) →
      ∀ (N : ℕ) (m : MArr N), weightedError a A N m < ∞) ∧
    (∀ (P : ∀ N, Measure (MArr N)) (a : ℝ) (A : ℤ → ℝ), WeightedErrorInProbability P a A ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P N {m | ENNReal.ofReal ε < weightedError a A N m}) atTop (𝓝 0)) := by
  refine ⟨fun π μ ν => ⟨fun h => ⟨h.prob, h.fst, h.snd⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩,
    fun p μ ν => rfl, fun μ ν _ _ p hp hμ hν => wasserstein_lt_top hp hμ hν,
    wasserstein_comm, fun μ _ p hp => wasserstein_self hp, fun a A N m => rfl,
    fun a A h0 hs N m => weightedError_lt_top a h0 hs N m, fun P a A => Iff.rfl⟩

end DEF012Spec
#print axioms DEF012Spec.spec
