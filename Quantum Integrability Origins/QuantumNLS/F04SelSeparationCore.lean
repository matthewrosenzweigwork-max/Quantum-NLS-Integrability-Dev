import Mathlib
import QuantumNLS.LocalHeightUniform

/-!
# CC:F04:separation (R-F4C3E5BE), generic core

Source: `F04.tex`, Proposition `CC:F04:selection`, conclusion (CC:F04:separation) and the last paragraph of its proof: "If (CC:F04:separation) failed, a subsequence would have another root `q_{j_N,N}(s_N(λ)) → x(λ)`.
Lemma `CC:F04:local-height`, applied to these interpolated arrays, would force its real label to tend to `λ`. This contradicts (CC:F04:other-labels), since `dist(λ, ℤ) > 0`."

`separation_core`: real-Bethe arrays `q N`, `ν N` (`CC:F04:real-bethe`, `LocalHeight.RealBethe`) with weakly convergent empirical measures, a selected index `i N` with `q_{i_N,N} → x`, `x ∉ supp μ`, `θ(x) = πλ`,
and every other label uniformly away from `λ` (`κ₀ ≤ |ν_{j,N} − λ|` for `j ≠ i_N`, the content of `CC:F04:other-labels` for `λ ∈ (k, k+1)`):
there is `c₀ > 0` with `|q_{j,N} − q_{i_N,N}| ≥ c₀` for all large `N` and all `j ≠ i_N` (this is `liminf_N min_{j ≠ i_N} |q_{j,N} − q_{i_N,N}| > 0`).
The proof applies `LocalHeightUniform.local_height_uniform` (the subsequence argument of the printed proof, made uniform in the index).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open scoped Topology
open Filter MeasureTheory

namespace QuantumNLS.F04SelSeparationCore

open QuantumNLS.LocalHeight

theorem separation_core {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {q ν : (N : ℕ) → Fin (N + 1) → ℝ} (hB : ∀ N, RealBethe L κ N (q N) (ν N))
    (hw : EmpiricalWeakConv q μ) (i : (N : ℕ) → Fin (N + 1)) {x : ℝ}
    (hx : Tendsto (fun N => q N (i N)) atTop (𝓝 x)) (hsupp : x ∉ μ.support) {lam : ℝ}
    (hθ : theta L κ μ x = Real.pi * lam) {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hlab : ∀ N : ℕ, ∀ j : Fin (N + 1), j ≠ i N → κ₀ ≤ |ν N j - lam|) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ N : ℕ in atTop, ∀ j : Fin (N + 1), j ≠ i N →
      c₀ ≤ |q N j - q N (i N)| := by
  obtain ⟨ε₀, hε₀, hev⟩ := QuantumNLS.LocalHeightUniform.local_height_uniform hL hκ hB hw hsupp
    (η := κ₀ / 2) (by positivity)
  refine ⟨ε₀ / 2, by positivity, ?_⟩
  have hxe : ∀ᶠ N : ℕ in atTop, |q N (i N) - x| < ε₀ / 2 := by
    have := (Metric.tendsto_nhds.mp hx) (ε₀ / 2) (by positivity)
    simpa [Real.dist_eq] using this
  filter_upwards [hev, hxe] with N hN hNx j hj
  by_contra hlt
  push Not at hlt
  have hqj : |q N j - x| ≤ ε₀ := by
    calc |q N j - x| = |(q N j - q N (i N)) + (q N (i N) - x)| := by ring_nf
      _ ≤ |q N j - q N (i N)| + |q N (i N) - x| := abs_add_le _ _
      _ ≤ ε₀ := by linarith
  have h1 := hN j hqj
  have hth : theta L κ μ x / Real.pi = lam := by
    rw [hθ]; field_simp
  rw [hth] at h1
  have h2 := hlab N j hj
  linarith

end QuantumNLS.F04SelSeparationCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.F04SelSeparationCore.separation_core
