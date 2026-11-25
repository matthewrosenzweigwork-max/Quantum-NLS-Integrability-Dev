import QuantumNLS.ConvolutionComparison
/-!
Trusted statement for REG-001 `CC:convolution-comparison`, written by the integrator (not the prover) from
`source/chapters/regularity/root_confinement.tex:12–20`. The source's `M : [0,∞) → (0,∞)` continuously differentiable is
modelled by `M : ℝ → ℝ` with a one-sided derivative `M'` on `[0,∞)` (within `Ici 0`) and `M'` continuous on `[0,∞)`;
`M(0) = 1`; the inequality holds for all `t ≥ 0`. Values of `M` on `t < 0` are irrelevant.
-/
open Set

def Reg001 : Prop :=
  ∀ (a : ℝ), 0 ≤ a → ∀ (M M' : ℝ → ℝ),
    (∀ t, 0 ≤ t → HasDerivWithinAt M (M' t) (Ici 0) t) →
    ContinuousOn M' (Ici 0) →
    (∀ t, 0 ≤ t → 0 < M t) →
    M 0 = 1 →
    (∀ t, 0 ≤ t → M' t ≤ a * ∫ s in (0 : ℝ)..t, M s * M (t - s)) →
    ∀ t, 0 ≤ t → M t ≤ Real.exp (2 * Real.sqrt a * t)

theorem reg001 : Reg001 := by
  intro a ha M M' hd _hcont hpos h0 hineq
  refine QuantumNLS.ConvolutionComparison.convolution_comparison_bound a ha M M' ?_ h0 hpos ?_ ?_
  · intro t ht
    exact (hd t ht).continuousWithinAt
  · intro t ht
    exact (hd t ht.le).hasDerivAt (Ici_mem_nhds ht)
  · intro t ht
    exact hineq t ht.le

#print axioms reg001
