import Mathlib
import QuantumNLS.LabelJointLimit
import QuantumNLS.UniformLabelDistance

/-!
# PROP-002 item (1): tightness of the integer label marginal

Source: `source/chapters/propagation/label_periods.tex:43-55` (the tightness step of the proof of
`lem:B3-weak-joint-limit`), using the uniform label distance `QG:eq:B3-uniform-label-distance`
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:99-106`).

Imports (read-only, frozen):
* `QuantumNLS.LabelJointLimit` (4120590e): `OnShellBethe` (strictly ordered roots, nondecreasing labels,
  `QG:eq:our-bethe` at `c = κ/N`), and the finite Bethe pairing identity.
* `QuantumNLS.UniformLabelDistance` (R-274B2C0D, proved; no `sorry`): `uniform_label_distance`,
  `|q_j − 2πn_j/L| ≤ 3√(κ/L)` for an actual configuration `RootContraction.IsActualConfig L (κ/N) n q`.

Proved here:
* `toActualConfig`: the finite on-shell data is an actual configuration at `c = κ/N`
  (the Bethe relations coincide term by term, `BoseBethe`).
* `label_uniform_distance`: the printed bound for every root and label.
* `label_abs_le_bound`: `|n_j| ≤ (L/2π)(|q_j| + 3√(κ/L))`, the explicit tightness input.
* `label_bounded_of_roots`: roots in `[−M, M]` force labels in a fixed finite set (the
  compact-tightness step used for the integer marginal).

NOT in this module (items (2)–(5) of PROP-002): the weak limit on `ℝ × ℤ`, the monotonicity passing to the
limit, the identification `γ = μ ⊗ δ_{n(t)}`, the kernel limit, the classical data `μ` / `IndexedScalarMeasureCuts`,
and the binding to `DEF-010` empirical measures.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.LabelTightness

open QuantumNLS.LabelJointLimit QuantumNLS.RootContraction

variable {L κ : ℝ} {N : ℕ}

/-- The finite on-shell data is an actual Bethe configuration at `c = κ/N` (`BoseBethe` coincides with
`OnShellBethe.bethe` term by term). -/
theorem toActualConfig (hκ : 0 < κ) (hN : 0 < N) (B : OnShellBethe L κ N) :
    IsActualConfig L (κ / (N : ℝ)) B.n B.q where
  c_pos := div_pos hκ (by exact_mod_cast hN)
  sorted := B.q_strict
  labels_sorted := B.n_mono
  bethe := B.bethe

/-- **Uniform label distance** (`QG:eq:B3-uniform-label-distance`) for on-shell finite data. -/
theorem label_uniform_distance (hL : 0 < L) (hκ : 0 < κ) (hN : 1 ≤ N)
    (B : OnShellBethe L κ N) (j : Fin N) :
    |B.q j - 2 * Real.pi * B.n j / L| ≤ 3 * Real.sqrt (κ / L) :=
  QuantumNLS.UniformLabelDistance.uniform_label_distance hN hL hκ (toActualConfig hκ (by omega) B) j

/-- **Tightness of the integer labels.** `|n_j| ≤ (L/2π)(|q_j| + 3√(κ/L))`. -/
theorem label_abs_le_bound (hL : 0 < L) (hκ : 0 < κ) (hN : 1 ≤ N)
    (B : OnShellBethe L κ N) (j : Fin N) :
    |(B.n j : ℝ)| ≤ (L / (2 * Real.pi)) * (|B.q j| + 3 * Real.sqrt (κ / L)) := by
  have hd := label_uniform_distance hL hκ hN B j
  have hpi : 0 < 2 * Real.pi := by positivity
  -- |2π n_j / L| ≤ |q_j| + 3√(κ/L)
  have h1 : |2 * Real.pi * (B.n j : ℝ) / L| ≤ |B.q j| + 3 * Real.sqrt (κ / L) := by
    have htri : |2 * Real.pi * (B.n j : ℝ) / L| ≤ |B.q j| + |B.q j - 2 * Real.pi * (B.n j : ℝ) / L| := by
      have h0 := abs_sub (B.q j) (B.q j - 2 * Real.pi * (B.n j : ℝ) / L)
      rw [sub_sub_cancel] at h0
      exact h0
    linarith [hd]
  -- multiply by L/(2π)
  have hn : (B.n j : ℝ) = (L / (2 * Real.pi)) * (2 * Real.pi * (B.n j : ℝ) / L) := by
    field_simp
  rw [hn, abs_mul, abs_of_pos (div_pos hL hpi)]
  exact mul_le_mul_of_nonneg_left h1 (div_nonneg hL.le hpi.le)

/-- **Compact tightness.** Roots in `[−M, M]` force the labels into the finite set
`Finset.Icc (−K) K` with `K = ⌈(L/2π)(M + 3√(κ/L))⌉`. -/
theorem label_bounded_of_roots (hL : 0 < L) (hκ : 0 < κ) (hN : 1 ≤ N)
    (B : OnShellBethe L κ N) {M : ℝ} (hM : ∀ j, |B.q j| ≤ M) (j : Fin N) :
    |B.n j| ≤ ⌈(L / (2 * Real.pi)) * (M + 3 * Real.sqrt (κ / L))⌉ := by
  have h := label_abs_le_bound hL hκ hN B j
  have h2 : (L / (2 * Real.pi)) * (|B.q j| + 3 * Real.sqrt (κ / L)) ≤
      (L / (2 * Real.pi)) * (M + 3 * Real.sqrt (κ / L)) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hL.le (by positivity))
    linarith [hM j]
  have h3 : |(B.n j : ℝ)| ≤ (L / (2 * Real.pi)) * (M + 3 * Real.sqrt (κ / L)) := h.trans h2
  have h4 : ((|B.n j| : ℤ) : ℝ) ≤ ((⌈(L / (2 * Real.pi)) * (M + 3 * Real.sqrt (κ / L))⌉ : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact h3.trans (Int.le_ceil _)
  exact_mod_cast h4

end QuantumNLS.LabelTightness

/-! Axiom audit (PROP-002 item 1). -/
#print axioms QuantumNLS.LabelTightness.toActualConfig
#print axioms QuantumNLS.LabelTightness.label_uniform_distance
#print axioms QuantumNLS.LabelTightness.label_abs_le_bound
#print axioms QuantumNLS.LabelTightness.label_bounded_of_roots
