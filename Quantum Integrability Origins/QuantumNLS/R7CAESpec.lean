import QuantumNLS.QuantileTransport

/-! integrator-authored trusted spec for R-7CAE5993 `F05:transport` (foundations/F05.tex).
Definitions pinned literally: couplings (probability measures with marginals σ, τ), W₂ = inf over couplings
of (∫|x−y|² dπ)^{1/2}, Q_σ(s) = inf {x : s ≤ σ(−∞,x]}, finite second moment, uniform empirical measures,
weak convergence (all bounded continuous tests), weak convergence in probability (convergence in
measure of each test integral), and the expected-tail assumption. Four clauses as printed. -/

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction
open QuantumNLS.QuantileTransport

namespace QuantumNLS.R7CAESpec

def Spec : Prop :=
  -- definitions pinned
  (∀ σ τ π, IsCoupling σ τ π ↔ IsProbabilityMeasure π ∧ π.map Prod.fst = σ ∧ π.map Prod.snd = τ) ∧
  (∀ σ τ, W2 σ τ = ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling σ τ π),
      (∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ 2) ∂π) ^ (1 / 2 : ℝ)) ∧
  (∀ σ s, quantile σ s = sInf {x : ℝ | s ≤ (σ (Iic x)).toReal}) ∧
  (∀ σ, HasFiniteSecondMoment σ ↔ Integrable (fun x : ℝ => x ^ 2) σ) ∧
  (∀ N (x : Fin N → ℝ), empirical N x = ∑ j, (N : ℝ≥0∞)⁻¹ • Measure.dirac (x j)) ∧
  (∀ σs σ, WeakConv σs σ ↔ ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂σs j) atTop (𝓝 (∫ x, f x ∂σ))) ∧
  -- (1) quantile formula
  (∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ],
    HasFiniteSecondMoment σ → HasFiniteSecondMoment τ →
    W2 σ τ = eLpNorm (fun s => quantile σ s - quantile τ s) 2 (volume.restrict (Ioo 0 1))) ∧
  -- (2) empirical measures
  (∀ (N : ℕ) (x y : Fin N → ℝ), 0 < N → Monotone x → Monotone y →
    W2 (empirical N x) (empirical N y) ^ 2 = ENNReal.ofReal ((1 / N : ℝ) * ∑ j, (x j - y j) ^ 2)) ∧
  -- (3) weak convergence + second moments
  (∀ (σs : ℕ → Measure ℝ) (σ : Measure ℝ) [∀ j, IsProbabilityMeasure (σs j)] [IsProbabilityMeasure σ],
    (∀ j, HasFiniteSecondMoment (σs j)) → HasFiniteSecondMoment σ → WeakConv σs σ →
    Tendsto (fun j => ∫ x, x ^ 2 ∂σs j) atTop (𝓝 (∫ x, x ^ 2 ∂σ)) →
    Tendsto (fun j => W2 (σs j) σ) atTop (𝓝 0)) ∧
  -- (4) random measures with the expected-tail assumption
  (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σN : ℕ → Ω → Measure ℝ) [∀ N ω, IsProbabilityMeasure (σN N ω)],
    (∀ N, ∀ᵐ ω ∂P, HasFiniteSecondMoment (σN N ω)) →
    ∀ (σ : Measure ℝ) [IsProbabilityMeasure σ], HasFiniteSecondMoment σ →
    (∀ f : ℝ →ᵇ ℝ, TendstoInMeasure P (fun N ω => ∫ x, f x ∂σN N ω) atTop (fun _ => ∫ x, f x ∂σ)) →
    Tendsto (fun R : ℝ => ⨆ N, ∫⁻ ω, (∫⁻ x in {x : ℝ | R < |x|}, ENNReal.ofReal (x ^ 2) ∂σN N ω) ∂P)
      atTop (𝓝 0) →
    Tendsto (fun N => ∫⁻ ω, W2 (σN N ω) σ ^ 2 ∂P) atTop (𝓝 0))

theorem spec : Spec := by
  refine ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ _ => rfl,
    fun _ _ => Iff.rfl, ?_, ?_, ?_, ?_⟩
  · intro σ τ _ _ h1 h2; exact W2_eq_eLpNorm_quantile σ τ h1 h2
  · intro N x y hN hx hy; exact W2_empirical_sq hN hx hy
  · intro σs σ _ _ h1 h2 h3 h4; exact tendsto_W2_of_weak_of_moment h1 h2 h3 h4
  · intro Ω _ P _ σN _ h1 σ _ h2 h3 h4; exact tendsto_expected_W2_sq P σN h1 σ h2 h3 h4

end QuantumNLS.R7CAESpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R7CAESpec.spec
  IO.println s!"R7CAESpec.spec axioms: {ax}"
