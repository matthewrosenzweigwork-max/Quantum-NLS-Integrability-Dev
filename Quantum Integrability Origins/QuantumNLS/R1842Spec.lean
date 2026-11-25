import QuantumNLS.LocalHeight

/-! integrator-authored trusted spec for R-1842678C `CC:F04:local-height` (root_response/F04.tex:137-143,
standing setup F04.tex:3-18 and 96-103). Fix L, κ > 0 and a probability measure μ on ℝ. For each particle
number n = N+1 ≥ 1 let q_{·,n} be strictly increasing and ν_{·,n} nondecreasing reals solving the
real-label equations L q_i − 2 Σ_{j≠i} arctan(c_n/(q_i − q_j)) = 2πν_i with c_n = κ/n (CC:F04:real-bethe),
and suppose the empirical measures n⁻¹ Σ_i δ_{q_{i,n}} converge weakly to μ (against bounded continuous f).
If q_{i_n,n} → x and x ∉ supp μ, then ν_{i_n,n} → θ(x)/π with θ(x) = Lx/2 − κ ∫ dμ(y)/(x − y)
(CC:F04:phase). (The source's μ is a specific quantum-derived measure; the statement is proved for every
probability measure.) -/

open Filter Topology MeasureTheory
open scoped BoundedContinuousFunction

namespace QuantumNLS.R1842Spec

noncomputable def sTheta (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ := L * x / 2 - κ * ∫ y, 1 / (x - y) ∂μ

def Spec : Prop :=
  ∀ (L κ : ℝ), 0 < L → 0 < κ → ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
    ∀ (q ν : (N : ℕ) → Fin (N + 1) → ℝ),
    (∀ N, StrictMono (q N) ∧ Monotone (ν N) ∧
      ∀ i, L * q N i - 2 * ∑ j ∈ Finset.univ.erase i,
          Real.arctan ((κ / ((N : ℝ) + 1)) / (q N i - q N j)) = 2 * Real.pi * ν N i) →
    (∀ f : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ j, f (q N j)) atTop
      (𝓝 (∫ y, f y ∂μ))) →
    ∀ (i : (N : ℕ) → Fin (N + 1)) (x : ℝ), Tendsto (fun N => q N (i N)) atTop (𝓝 x) →
      x ∉ μ.support →
      Tendsto (fun N => ν N (i N)) atTop (𝓝 (sTheta L κ μ x / Real.pi))

theorem spec : Spec := by
  intro L κ hL hκ μ hμ q ν hB hw i x hx hs
  exact LocalHeight.local_height hL hκ (μ := μ) (q := q) (ν := ν)
    (fun N => ⟨(hB N).1, (hB N).2.1, (hB N).2.2⟩)
    (fun f => by simpa [one_div] using hw f) i hx hs

end QuantumNLS.R1842Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R1842Spec.spec
  IO.println s!"R1842Spec.spec axioms: {ax}"
