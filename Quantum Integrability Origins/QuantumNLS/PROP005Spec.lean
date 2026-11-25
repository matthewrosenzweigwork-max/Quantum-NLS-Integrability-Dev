import QuantumNLS.LabelExactPeriod
/-! integrator-authored trusted spec for PROP-005 prop:B3-exact-period (Terra r138 ACCEPT; regular-cut interface; explicit-primitive route): frozen statements restated verbatim. -/
namespace PROP005Spec
open MeasureTheory Filter Topology Set Complex intervalIntegral
open scoped BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelExactPeriod

set_option maxHeartbeats 4000000 in
theorem root_period_spec  {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
    (hqb : 2 * c < |q - b|) (hab : a < b) :
    rectIntegral (fun z => log (1 + I * c / (z - q))) a b h =
      if a < q ∧ q < b then 2 * Real.pi * I * (I * c) else 0 := by
  apply QuantumNLS.LabelExactPeriod.root_period <;> assumption

set_option maxHeartbeats 4000000 in
theorem exact_period_uniform_spec  {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) =
          -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ B.q) xm xp h := by
  apply QuantumNLS.LabelExactPeriod.exact_period_uniform <;> assumption

set_option maxHeartbeats 4000000 in
theorem exact_period_seq_spec  {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∀ᶠ k in atTop, (((Finset.univ.filter fun j => (B k).n j = n).card : ℝ) / N k : ℂ) =
      -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ (B k).q) xm xp h := by
  apply QuantumNLS.LabelExactPeriod.exact_period_seq <;> assumption

set_option maxHeartbeats 4000000 in
theorem spectralValue_polynomial_identity_spec  (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) :
    BetheSpectralContinuity.spectralValue L hc hn z *
        ∏ j, (z - BetheSmooth.sourceRoots L n c j) =
      ∏ j, (z - BetheSmooth.sourceRoots L n c j + I * c) +
        exp (I * L * z) * ∏ j, (z - BetheSmooth.sourceRoots L n c j - I * c) := by
  apply QuantumNLS.LabelExactPeriod.spectralValue_polynomial_identity <;> assumption

set_option maxHeartbeats 4000000 in
theorem spectralValue_difference_riccati_spec  (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j)
    (hz' : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j + I * c) :
    BetheSpectralContinuity.spectralValue L hc hn z =
      AN c (BetheSmooth.sourceRoots L n c) z +
        exp (I * L * z) / AN c (BetheSmooth.sourceRoots L n c) (z - I * c) := by
  apply QuantumNLS.LabelExactPeriod.spectralValue_difference_riccati <;> assumption

end PROP005Spec
#print axioms PROP005Spec.root_period_spec
#print axioms PROP005Spec.exact_period_uniform_spec
#print axioms PROP005Spec.exact_period_seq_spec
#print axioms PROP005Spec.spectralValue_polynomial_identity_spec
#print axioms PROP005Spec.spectralValue_difference_riccati_spec
