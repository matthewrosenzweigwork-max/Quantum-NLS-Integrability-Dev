import QuantumNLS.D1Prop005
/-! integrator-authored trusted spec for PROP-005 D1 restatement (terra_review r208 PASS): headline statement(s) copied verbatim from D1Prop005 (QuantumNLS.D1Prop005). -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace QuantumNLS.D1P005Spec
open QuantumNLS.D1Prop005
open MeasureTheory Filter Topology Set Complex intervalIntegral
open scoped BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelExactPeriod

set_option maxHeartbeats 8000000 in
theorem exact_period_d1_spec :
    (∀ {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
      (hqb : 2 * c < |q - b|) (hab : a < b),
      rectIntegral (fun z => log (1 + I * c / (z - q))) a b h =
        if a < q ∧ q < b then 2 * Real.pi * I * (I * c) else 0) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp h : ℝ}
      (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp) (hh : 0 < h)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
          (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) =
            -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ B.q) xm xp h) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, OnShellBethe L κ (N k)}
      (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
      {n : ℤ} {xm xp h : ℝ} (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp)
      (hh : 0 < h)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∀ᶠ k in atTop, (((Finset.univ.filter fun j => (B k).n j = n).card : ℝ) / N k : ℂ) =
        -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ (B k).q) xm xp h) ∧
    (∀ (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
      {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ),
      BetheSpectralContinuity.spectralValue L hc hn z *
          ∏ j, (z - BetheSmooth.sourceRoots L n c j) =
        ∏ j, (z - BetheSmooth.sourceRoots L n c j + I * c) +
          exp (I * L * z) * ∏ j, (z - BetheSmooth.sourceRoots L n c j - I * c)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
      {n : Fin N → ℤ} (hn : Antitone n) {z : ℂ}
      (hz : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j)
      (hz' : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j + I * c),
      BetheSpectralContinuity.spectralValue L hc hn z =
        AN c (BetheSmooth.sourceRoots L n c) z +
          exp (I * L * z) / AN c (BetheSmooth.sourceRoots L n c) (z - I * c)) := by
  exact QuantumNLS.D1Prop005.exact_period_d1 

end QuantumNLS.D1P005Spec
#print axioms QuantumNLS.D1P005Spec.exact_period_d1_spec
