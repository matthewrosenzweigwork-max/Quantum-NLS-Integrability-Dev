import QuantumNLS.Reg014Continuity
import QuantumNLS.Reg014Finite

/-! REG-014 (`CC:all-fractional:uniform`, `all_orders.tex:23`): uniform finite-parameter
correction.  For every integer `r ≥ 2`, the regularized difference
`D_{r,u}(Y) = ∫ Y² t^{2r}/(Y²+t²) dM_u(t) - Σ_n Y² p_n^{2r}/(Y²+p_n²) |û(n)|²`
(finite for `u ∈ H^{r-1}`, `Y > 0`) is continuous in `u ∈ H^{r-1}` for each fixed `Y > 0`, and is
bounded, uniformly on every bounded subset of `H^{r-1}`, for all sufficiently large `Y`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg014Main
open QuantumNLS.TranslatedCorrelation QuantumNLS.Reg014Moments QuantumNLS.Reg014Continuity
open QuantumNLS.Reg014Finite

/-- **REG-014.**  Fixed `L > 0`, physical coupling `κ > 0`, integer `r ≥ 2`; `Hk L (r-1)` is
`H^{r-1}(𝕋_L)`, `PhysicalQuantumMeasure.measure hκ u` is the limiting physical measure `M_u`,
`momentum L n = p_n = 2πn/L`, and `Fourier.coeff L u n = û(n)`.  The first conjunct is the
printed finiteness of both terms of `D_{r,u}(Y)`; the second is continuity for each fixed
`Y > 0`; the third is the uniform bound on bounded sets. -/
theorem REG014 (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) :
    (∀ (u : Hk L (r - 1)) (Y : ℝ), 0 < Y →
      Integrable (fun t : ℝ => Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2))
          (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) ∧
        Summable (fun n : ℤ => Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
          (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
    (∀ Y : ℝ, 0 < Y → Continuous (fun u : Hk L (r - 1) =>
      (∫ t : ℝ, Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2)
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
        ∑' n : ℤ, Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
          (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
          ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2)) ∧
    (∀ B : Set (Hk L (r - 1)), Bornology.IsBounded B →
      ∃ C Y₀ : ℝ, 0 < C ∧ 0 < Y₀ ∧ ∀ u ∈ B, ∀ Y : ℝ, Y₀ ≤ Y →
        |(∫ t : ℝ, Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2)
            ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
          ∑' n : ℤ, Y ^ 2 * (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ (2 * r) /
            (Y ^ 2 + (QuantumNLS.RootWeightedCellsR26.momentum L n) ^ 2) *
            ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2| ≤ C) := by
  refine ⟨fun u Y hY => terms_finite κ hκ r hr u hY,
    fun Y hY => Dfun_continuous κ hκ r hr hY, ?_⟩
  intro B hB
  obtain ⟨U₀, hU₀⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨C, Y₀, hY₀, hC⟩ := D_uniform (L := L) κ hκ r hr (max U₀ 0) (le_max_right _ _)
  refine ⟨max C 1, Y₀, lt_of_lt_of_le one_pos (le_max_right _ _), lt_of_lt_of_le one_pos hY₀,
    fun u hu Y hY => ?_⟩
  exact (hC u ((hU₀ u hu).trans (le_max_left _ _)) Y hY).trans (le_max_left _ _)

#print axioms REG014
end QuantumNLS.Reg014Main
