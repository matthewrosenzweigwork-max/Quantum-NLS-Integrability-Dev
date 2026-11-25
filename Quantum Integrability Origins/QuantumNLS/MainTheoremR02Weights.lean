import QuantumNLS.MainTheoremR01Values

/-!
# MainTheoremR02Weights: part (i) of R-AF8F7562 `thm:main`, "its weighted conclusion is equivalent to
eq:actions-main" (both directions, smooth-profile setting)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 16-21:
"The original theorem uses the weight `(1+|n|)^p`; for every fixed `p ≥ 0`,
`(1+n²)^{p/2} ≤ (1+|n|)^p ≤ 2^{p/2}(1+n²)^{p/2}`, so its weighted conclusion is equivalent to eq:actions-main."
review record r107: the real `tsum` convention needs care; `AuditWeightedProbabilityR49a.summable_error` proves
summability of the printed series for each smooth profile and sample, and `weightAbs_le` gives summability of the
original-weight series by nonnegative comparison.

Proved here, for every smooth profile `u` and every `p ≥ 0`:
* `summable_errorAbs`: the original-weight series is summable for every sample (so both errors are actual sums);
* `error_le_errorAbs`, `errorAbs_le` (MainTheoremR01Values): the two-sided pointwise comparison of the actual sums,
  `error ≤ errorAbs ≤ 2^{p/2} error`;
* `weighted_equivalent`: for each fixed `p ≥ 0`, convergence in probability of the printed error is EQUIVALENT to
  convergence in probability of the original error, each direction proved from the corresponding pointwise bound.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology MeasureTheory

namespace QuantumNLS.MainTheoremR02Weights

open Def033HierarchyR24m (Smooth physical)
open BetheLabels (MArr)
open BulkResponseActual (physBasis)
open EmpiricalRapidity (bornMeasure)
open MainTheoremR01Values (weightAbs errorAbs)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed series is summable for every smooth profile and sample (R-115CAA16 audit, R49a). -/
theorem summable_error (hκ : 0 < κ) (u : Smooth L) (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (m : MArr N) :
    Summable (fun n : ℤ => AuditWeightedSeriesR49a.weight p n *
      |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n|) :=
  AuditWeightedProbabilityR49a.summable_error hκ u.property p hp N m

/-- The original-weight series is summable (nonnegative comparison with `2^{p/2}` times the printed series). -/
theorem summable_errorAbs (hκ : 0 < κ) (u : Smooth L) (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (m : MArr N) :
    Summable (fun n : ℤ => weightAbs p n *
      |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n|) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by unfold weightAbs; positivity) (abs_nonneg _))
    (fun n => ?_) ((summable_error hκ u p hp N m).mul_left ((2 : ℝ) ^ (p / 2)))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (MainTheoremR01Values.weightAbs_le p hp n) (abs_nonneg _)

/-- The printed error is at most the original error (both actual sums). -/
theorem error_le_errorAbs (hκ : 0 < κ) (u : Smooth L) (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (m : MArr N) :
    AuditWeightedProbabilityR49a.error hκ (physical u) p N m ≤ errorAbs hκ (physical u) p N m := by
  unfold AuditWeightedProbabilityR49a.error errorAbs
  exact (summable_error hκ u p hp N m).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (MainTheoremR01Values.weight_le_weightAbs p hp n) (abs_nonneg _))
    (summable_errorAbs hκ u p hp N m)

/-- **The weight equivalence of part (i)**, for each fixed `p ≥ 0` and smooth unit profile `u`: the printed
conclusion eq:actions-main in probability holds iff the original `(1+|n|)^p` conclusion does. -/
theorem weighted_equivalent (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (p : ℝ) (hp : 0 ≤ p) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
        {m | ε < AuditWeightedProbabilityR49a.error hκ (physical u) p N m}) atTop (𝓝 0)) ↔
      (∀ ε : ℝ, 0 < ε → Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
        {m | ε < errorAbs hκ (physical u) p N m}) atTop (𝓝 0)) := by
  constructor
  · intro h1 ε hε
    have hc : 0 < (2 : ℝ) ^ (p / 2) := by positivity
    have h := h1 (ε / (2 : ℝ) ^ (p / 2)) (div_pos hε hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) (fun N => ?_)
    refine measure_mono (fun m hm => ?_)
    simp only [Set.mem_ofPred_eq] at hm ⊢
    have he := MainTheoremR01Values.errorAbs_le hκ (physical u) p hp N m
    rw [div_lt_iff₀ hc]
    linarith [mul_comm ((2 : ℝ) ^ (p / 2)) (AuditWeightedProbabilityR49a.error hκ (physical u) p N m)]
  · intro h2 ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h2 ε hε) (fun _ => bot_le)
      (fun N => ?_)
    refine measure_mono (fun m hm => ?_)
    simp only [Set.mem_ofPred_eq] at hm ⊢
    exact hm.trans_le (error_le_errorAbs hκ u p hp N m)

/-- **Part (i) weight clause**: summability of both actual series, the two-sided pointwise comparison of the actual
sums, and the equivalence of the two weighted conclusions, for every fixed `p ≥ 0`. -/
def WeightEquivalence (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : Prop :=
  ∀ p : ℝ, 0 ≤ p →
    (∀ (N : ℕ) (m : MArr N),
      Summable (fun n : ℤ => AuditWeightedSeriesR49a.weight p n *
        |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n|) ∧
      Summable (fun n : ℤ => weightAbs p n *
        |(m.1 n : ℝ) / N - (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n|) ∧
      AuditWeightedProbabilityR49a.error hκ (physical u) p N m ≤ errorAbs hκ (physical u) p N m ∧
      errorAbs hκ (physical u) p N m ≤ (2 : ℝ) ^ (p / 2) * AuditWeightedProbabilityR49a.error hκ (physical u) p N m) ∧
    ((∀ ε : ℝ, 0 < ε → Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
        {m | ε < AuditWeightedProbabilityR49a.error hκ (physical u) p N m}) atTop (𝓝 0)) ↔
      (∀ ε : ℝ, 0 < ε → Tendsto (fun N => bornMeasure (physBasis L hκ N) (physical u) hu
        {m | ε < errorAbs hκ (physical u) p N m}) atTop (𝓝 0)))

theorem weight_equivalence (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    WeightEquivalence (L := L) hκ u hu := fun p hp =>
  ⟨fun N m => ⟨summable_error hκ u p hp N m, summable_errorAbs hκ u p hp N m,
      error_le_errorAbs hκ u p hp N m, MainTheoremR01Values.errorAbs_le hκ (physical u) p hp N m⟩,
    weighted_equivalent hκ u hu p hp⟩

end QuantumNLS.MainTheoremR02Weights

#print axioms QuantumNLS.MainTheoremR02Weights.weight_equivalence
