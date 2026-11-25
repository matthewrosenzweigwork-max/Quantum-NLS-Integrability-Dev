import QuantumNLS.PeriodTwoTerm
/-! integrator-authored trusted spec for PROP-006 thm:B3-period-reconstruction (Terra r140 ACCEPT):
the complete theorem (log reconstruction on Γ, integrated two-term period formula, and both
uniformity-on-families clauses), copied verbatim from PT1 `PeriodTwoTerm` 815d5ded, together with
the defining equations of every bounded quantity (rfl). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Filter Topology Asymptotics Set
namespace PROP006Spec
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
  QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts QuantumNLS.EmpiricalRapidity
  QuantumNLS.PeriodTwoTerm

set_option maxHeartbeats 4000000 in
theorem period_reconstruction_spec {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp h : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    (∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h,
      ‖remf κ L N (fun k => (B k).q) (cauchyTransform S.μ) (k, z)‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∀ᶠ k in atTop,
      ‖twoTermErr L κ (cauchyTransform S.μ) (B k) n xm xp h‖ ≤ C * ((N k : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → ∀ z ∈ Gam xm xp h,
        ‖remOne κ L (cauchyTransform S.μ) B.q z‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) ∧
    (∃ C : ℝ, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ‖twoTermErr L κ (cauchyTransform S.μ) B n xm xp h‖ ≤ C * ((N : ℝ)⁻¹) ^ 2) :=
  QuantumNLS.PeriodTwoTerm.period_reconstruction S hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4

/-! Defining equations (rfl) of the quantities bounded above. -/
theorem remf_def (κ L : ℝ) (N : ℕ → ℕ) (q : ∀ k, Fin (N k) → ℝ) (G : ℂ → ℂ) (p : ℕ × ℂ) :
    remf κ L N q G p =
  ellf (κ / N p.1) (q p.1) p.2 - logaNf L κ (κ / N p.1) G (q p.1) p.2 +
    I * κ / (N p.1 : ℂ) * (ef L p.2 * deriv (aNf L κ (κ / N p.1) G (q p.1)) p.2 /
      (aNf L κ (κ / N p.1) G (q p.1) p.2 *
        (aNf L κ (κ / N p.1) G (q p.1) p.2 ^ 2 - ef L p.2))) := rfl
theorem remOne_def (κ L : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    remOne κ L G q z = remf κ L (fun _ => N) (fun _ => q) G (0, z) := rfl
theorem twoTermErr_def (L κ : ℝ) (G : ℂ → ℂ) {N : ℕ} (B : OnShellBethe L κ N) (n : ℤ) (xm xp h : ℝ) :
    twoTermErr L κ G B n xm xp h =
  (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) -
    (-(1 / (2 * Real.pi * κ)) * QuantumNLS.LabelExactPeriod.rectIntegral (logaNf L κ (κ / N) G B.q) xm xp h +
      I / (2 * Real.pi * N) * QuantumNLS.LabelExactPeriod.rectIntegral (corrf L κ (κ / N) G B.q) xm xp h) := rfl
theorem corrf_def (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    corrf L κ c G q z =
  ef L z * deriv (aNf L κ c G q) z / (aNf L κ c G q z * (aNf L κ c G q z ^ 2 - ef L z)) := rfl
theorem ellf_def (c : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    ellf c q z = ∑ j, log (1 + I * c / (z - q j)) := rfl
theorem ef_def (L : ℝ) (z : ℂ) : ef L z = exp (I * L * z) := rfl
theorem Af_def (κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : Af κ G z = exp (I * κ * G z) := rfl
theorem aNf_def (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    aNf L κ c G q z = (sNf L c q z + DNf L κ c G q z) / 2 := rfl
theorem logaNf_def (L κ c : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    logaNf L κ c G q z = I * κ * G z + log (aNf L κ c G q z / Af κ G z) := rfl
theorem Gam_def (a b h : ℝ) : Gam a b h =
  {z | z.re ∈ Icc a b ∧ (z.im = -h ∨ z.im = h)} ∪ {z | z.im ∈ Icc (-h) h ∧ (z.re = a ∨ z.re = b)} := rfl
end PROP006Spec
#print axioms PROP006Spec.period_reconstruction_spec
