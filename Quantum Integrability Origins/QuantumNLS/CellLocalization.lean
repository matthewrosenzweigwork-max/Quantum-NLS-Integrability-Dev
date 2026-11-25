import Mathlib
import QuantumNLS.LabelWeakJointLimit
import QuantumNLS.IndividualRootBound

/-!
# REG-003 `CC:limiting-cell-localization`: localization of the limiting indexed cells (conditional on the printed joint-limit identification)

Source: `source-text/chapters/regularity/root_confinement.tex`, Corollary `CC:limiting-cell-localization` (line 142) and its proof (lines 167-197).
Printed proof: (1) the mean-field root bound applies to every configuration, so every joint empirical root-label measure is supported on the closed set `{(x,n) : |x − 2πn/L| ≤ 2√(κ/L)}`;
(2) the joint root-label convergence (`thm:root-occupation-limit`) identifies the limit with `M_u` on the graph of the indexed cells; (3) a weak limit of probabilities supported on a closed set is supported there;
(4) comparison of moments, `1+|x| ≤ (1+C)(1+|p|)` and `1+|p| ≤ (1+C)(1+|x|)`, integrated over the joint measure whose label marginal has mass `I_n`.

Formalized here (all with explicit hypotheses, none of which is an unproved printed claim except the identification (2), carried as `hlab`):
* `onshell_in_cellSet`: every on-shell Bethe point lies in the closed set `cellSet L (2√(κ/L))` (REG-002 `individual_root_bound`, `c = κ/N`);
* `graph_localization` (steps 1 and 3): if the joint empirical measures converge weakly to `graphP μ n` (`LabelWeakJointLimit`), then `|t − 2π n(t)/L| ≤ 2√(κ/L)` for `μ`-a.e. `t`;
* `moment_comparison` (step 4, in `[0,∞]`): for disjoint measurable cells covering `μ`-almost everything, and `μ`-a.e. localization `|t − p_k| ≤ C` on the `k`th cell, both inequalities of `CC:all-moment-comparison`;
* `cell_localization`: the combination: with `hlab` (the label function equals the cell index `μ`-a.e. on the `k`th cell, the printed identification of the joint limit with the indexed cells) the localization `CC:cell-localization` and both moment inequalities hold.
For total mass `m`: apply to the normalized measure at the effective coupling `κ' = κ m` and multiply by `m` (the printed normalization, `prop:root-full-mass`): the constant is `2√(κ'/L) = 2√(κ m/L)`; the factor `m` is immaterial to a.e. statements
and multiplies both sides of the moment inequalities.
Not formalized here: the closure clause (endpoints of a positive-density interval; it needs the continuous density of `thm:root-spectral-density`), and the identification `hlab` itself (R-E6DFC650, R-950BFB30).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace QuantumNLS.CellLocalization

open QuantumNLS.LabelJointLimit (OnShellBethe)
open QuantumNLS.LabelJointWeak (jointP pts emp_eq_zero)
open QuantumNLS.LabelWeakJointLimit (graphP graphP_toMeasure)

/-- The closed set `{(x,n) : |x − 2πn/L| ≤ C}` of `ℝ × ℤ`. -/
def cellSet (L C : ℝ) : Set (ℝ × ℤ) := {p | |p.1 - 2 * Real.pi * (p.2 : ℝ) / L| ≤ C}

theorem isClosed_cellSet (L C : ℝ) : IsClosed (cellSet L C) := by
  have hc : Continuous fun p : ℝ × ℤ => |p.1 - 2 * Real.pi * (p.2 : ℝ) / L| := by
    have h2 : Continuous fun p : ℝ × ℤ => (p.2 : ℝ) :=
      (continuous_of_discreteTopology (f := fun n : ℤ => (n : ℝ))).comp continuous_snd
    exact (continuous_fst.sub ((continuous_const.mul h2).div_const L)).abs
  exact isClosed_le hc continuous_const

/-- Every on-shell Bethe point `(q_j, n_j)` lies in the closed set (REG-002 at `c = κ/N`). -/
theorem onshell_in_cellSet {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (B : OnShellBethe L κ N) (j : Fin N) :
    pts B j ∈ cellSet L (2 * Real.sqrt (κ / L)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < κ / (N : ℝ) := by positivity
  have hE : ∀ i : Fin N, L * (B.q i - 2 * Real.pi * (B.n i : ℝ) / L) =
      2 * ∑ k ∈ Finset.univ.erase i, Real.arctan ((κ / N) / (B.q i - B.q k)) := by
    intro i
    have h := B.bethe i
    have : L * (B.q i - 2 * Real.pi * (B.n i : ℝ) / L) = L * B.q i - 2 * Real.pi * (B.n i : ℝ) := by
      field_simp
    rw [this]
    linarith
  have hp : Monotone (fun i => 2 * Real.pi * (B.n i : ℝ) / L) := by
    intro i k hik
    have : (B.n i : ℝ) ≤ B.n k := by exact_mod_cast B.n_mono hik
    have hpi := Real.pi_pos
    simp only
    gcongr
  have hb := QuantumNLS.IndividualRootBound.individual_root_bound hN hL hc B.q
    (fun i => 2 * Real.pi * (B.n i : ℝ) / L) B.q_strict hp hE j
  have hD : 2 * Real.sqrt (κ / N * ((N : ℝ) - 1) / L) ≤ 2 * Real.sqrt (κ / L) := by
    have : κ / N * ((N : ℝ) - 1) / L ≤ κ / L := by
      rw [div_le_div_iff_of_pos_right hL, div_mul_eq_mul_div, div_le_iff₀ hN']
      nlinarith
    linarith [Real.sqrt_le_sqrt this]
  show |B.q j - 2 * Real.pi * (B.n j : ℝ) / L| ≤ 2 * Real.sqrt (κ / L)
  have hb' : |B.q j - 2 * Real.pi * (B.n j : ℝ) / L| ≤ 2 * Real.sqrt (κ / N * ((N : ℝ) - 1) / L) := hb
  exact hb'.trans hD

/-- **Steps 1 and 3 of the printed proof**: a weak limit `graphP μ n` of joint empirical measures of on-shell
configurations is supported on `{|x − 2πn/L| ≤ 2√(κ/L)}`, i.e. `|t − 2π n(t)/L| ≤ 2√(κ/L)` `μ`-a.e. -/
theorem graph_localization {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : ProbabilityMeasure ℝ}
    {n : ℝ → ℤ} (hn : Measurable n) {N : ℕ → ℕ} (hN : ∀ k, 0 < N k)
    (B : ∀ k, OnShellBethe L κ (N k))
    (hjoint : Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n))) :
    ∀ᵐ t ∂(μ : Measure ℝ), |t - 2 * Real.pi * (n t : ℝ) / L| ≤ 2 * Real.sqrt (κ / L) := by
  set S := cellSet L (2 * Real.sqrt (κ / L)) with hS
  have hSc : IsClosed S := isClosed_cellSet _ _
  have hone : ∀ k, (jointP (B k) (hN k) : Measure (ℝ × ℤ)) S = 1 := by
    intro k
    have hz : (jointP (B k) (hN k) : Measure (ℝ × ℤ)) Sᶜ = 0 :=
      emp_eq_zero hSc.measurableSet.compl (fun j hj => hj (onshell_in_cellSet hL hκ (hN k) (B k) j))
    exact (prob_compl_eq_zero_iff hSc.measurableSet).1 hz
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hjoint hSc
  simp only [hone, limsup_const] at hlim
  have h1 : (graphP μ n : Measure (ℝ × ℤ)) S = 1 :=
    le_antisymm prob_le_one hlim
  have h0 : (graphP μ n : Measure (ℝ × ℤ)) Sᶜ = 0 := (prob_compl_eq_zero_iff hSc.measurableSet).2 h1
  have hmg : Measurable (fun t : ℝ => (t, n t)) := measurable_id.prodMk hn
  rw [graphP_toMeasure, Measure.map_apply hmg hSc.measurableSet.compl] at h0
  rw [ae_iff]
  exact h0

/-- **Step 4** (`CC:all-moment-comparison`), in `[0,∞]`: for disjoint measurable cells covering `μ`-almost everything and `μ`-a.e. localization `|t − p_k| ≤ C` on the `k`th cell. -/
theorem moment_comparison {μ : Measure ℝ} {cell : ℤ → Set ℝ} (hmeas : ∀ k, MeasurableSet (cell k))
    (hdisj : Pairwise (Function.onFun Disjoint cell)) (hcover : ∀ᵐ t ∂μ, ∃ k, t ∈ cell k)
    {p : ℤ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hloc : ∀ k, ∀ᵐ t ∂μ, t ∈ cell k → |t - p k| ≤ C) {s : ℝ} (hs : 0 ≤ s) :
    (ENNReal.ofReal ((1 + C) ^ (-s)) *
        ∑' k, ENNReal.ofReal ((1 + |p k|) ^ s) * μ (cell k) ≤
      ∫⁻ t, ENNReal.ofReal ((1 + |t|) ^ s) ∂μ) ∧
    (∫⁻ t, ENNReal.ofReal ((1 + |t|) ^ s) ∂μ ≤
      ENNReal.ofReal ((1 + C) ^ s) * ∑' k, ENNReal.ofReal ((1 + |p k|) ^ s) * μ (cell k)) := by
  have hU : ∀ᵐ t ∂μ, t ∈ ⋃ k, cell k := by
    filter_upwards [hcover] with t ⟨k, hk⟩ using mem_iUnion.2 ⟨k, hk⟩
  have hres : μ.restrict (⋃ k, cell k) = μ := Measure.restrict_eq_self_of_ae_mem hU
  have hsplit : ∫⁻ t, ENNReal.ofReal ((1 + |t|) ^ s) ∂μ =
      ∑' k, ∫⁻ t in cell k, ENNReal.ofReal ((1 + |t|) ^ s) ∂μ := by
    conv_lhs => rw [← hres]
    exact lintegral_iUnion hmeas hdisj _
  have h1C : 0 < 1 + C := by linarith
  -- pointwise comparisons
  have up : ∀ t q : ℝ, |t - q| ≤ C → (1 + |t|) ^ s ≤ (1 + C) ^ s * (1 + |q|) ^ s := by
    intro t q h
    rw [← Real.mul_rpow h1C.le (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hs
    have := abs_le.1 h
    have h2 : |t| ≤ |q| + C := by
      calc |t| = |(t - q) + q| := by ring_nf
        _ ≤ |t - q| + |q| := abs_add_le _ _
        _ ≤ C + |q| := by linarith
        _ = |q| + C := by ring
    nlinarith [abs_nonneg q]
  have low : ∀ t q : ℝ, |t - q| ≤ C → (1 + C) ^ (-s) * (1 + |q|) ^ s ≤ (1 + |t|) ^ s := by
    intro t q h
    have h2 : 1 + |q| ≤ (1 + C) * (1 + |t|) := by
      have h3 : |q| ≤ |t| + C := by
        calc |q| = |(q - t) + t| := by ring_nf
          _ ≤ |q - t| + |t| := abs_add_le _ _
          _ ≤ C + |t| := by rw [abs_sub_comm]; linarith
          _ = |t| + C := by ring
      nlinarith [abs_nonneg t]
    have h4 : (1 + |q|) ^ s ≤ (1 + C) ^ s * (1 + |t|) ^ s := by
      rw [← Real.mul_rpow h1C.le (by positivity)]
      exact Real.rpow_le_rpow (by positivity) h2 hs
    rw [Real.rpow_neg h1C.le]
    have h5 : 0 < (1 + C) ^ s := Real.rpow_pos_of_pos h1C s
    rw [inv_mul_le_iff₀ h5]
    exact h4
  constructor
  · rw [hsplit, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have e : ENNReal.ofReal ((1 + C) ^ (-s)) * (ENNReal.ofReal ((1 + |p k|) ^ s) * μ (cell k)) =
        ∫⁻ t in cell k, ENNReal.ofReal ((1 + C) ^ (-s) * (1 + |p k|) ^ s) ∂μ := by
      rw [setLIntegral_const, ENNReal.ofReal_mul (Real.rpow_nonneg h1C.le _), mul_assoc]
    rw [e]
    refine lintegral_mono_ae ((ae_restrict_iff' (hmeas k)).2 ?_)
    filter_upwards [hloc k] with t ht hmem
    exact ENNReal.ofReal_le_ofReal (low t (p k) (ht hmem))
  · rw [hsplit, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    have e : ENNReal.ofReal ((1 + C) ^ s) * (ENNReal.ofReal ((1 + |p k|) ^ s) * μ (cell k)) =
        ∫⁻ t in cell k, ENNReal.ofReal ((1 + C) ^ s * (1 + |p k|) ^ s) ∂μ := by
      rw [setLIntegral_const, ENNReal.ofReal_mul (Real.rpow_nonneg h1C.le _), mul_assoc]
    rw [e]
    refine lintegral_mono_ae ((ae_restrict_iff' (hmeas k)).2 ?_)
    filter_upwards [hloc k] with t ht hmem
    exact ENNReal.ofReal_le_ofReal (up t (p k) (ht hmem))

/-- **`CC:limiting-cell-localization`** (conditional on the printed identification `hlab` of the joint limit with the indexed cells):
on the `k`th cell the measure lives in `[2πk/L − C, 2πk/L + C]`, `C = 2√(κ/L)`, and the moment comparison holds. -/
theorem cell_localization {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : ProbabilityMeasure ℝ}
    {n : ℝ → ℤ} (hn : Measurable n) {N : ℕ → ℕ} (hN : ∀ k, 0 < N k)
    (B : ∀ k, OnShellBethe L κ (N k))
    (hjoint : Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)))
    {cell : ℤ → Set ℝ} (hmeas : ∀ k, MeasurableSet (cell k))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcover : ∀ᵐ t ∂(μ : Measure ℝ), ∃ k, t ∈ cell k)
    (hlab : ∀ k : ℤ, ∀ᵐ t ∂(μ : Measure ℝ), t ∈ cell k → n t = k) :
    (∀ k : ℤ, ∀ᵐ t ∂(μ : Measure ℝ), t ∈ cell k →
      t ∈ Icc (2 * Real.pi * k / L - 2 * Real.sqrt (κ / L)) (2 * Real.pi * k / L + 2 * Real.sqrt (κ / L))) ∧
    ∀ s : ℝ, 0 ≤ s →
      (ENNReal.ofReal ((1 + 2 * Real.sqrt (κ / L)) ^ (-s)) *
          ∑' k : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * k / L|) ^ s) * (μ : Measure ℝ) (cell k) ≤
        ∫⁻ t, ENNReal.ofReal ((1 + |t|) ^ s) ∂(μ : Measure ℝ)) ∧
      (∫⁻ t, ENNReal.ofReal ((1 + |t|) ^ s) ∂(μ : Measure ℝ) ≤
        ENNReal.ofReal ((1 + 2 * Real.sqrt (κ / L)) ^ s) *
          ∑' k : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * k / L|) ^ s) * (μ : Measure ℝ) (cell k)) := by
  have hg := graph_localization hL hκ hn hN B hjoint
  have hloc : ∀ k : ℤ, ∀ᵐ t ∂(μ : Measure ℝ), t ∈ cell k →
      |t - 2 * Real.pi * (k : ℝ) / L| ≤ 2 * Real.sqrt (κ / L) := by
    intro k
    filter_upwards [hg, hlab k] with t h1 h2 hmem
    rw [h2 hmem] at h1
    exact h1
  refine ⟨fun k => ?_, fun s hs => moment_comparison hmeas hdisj hcover (p := fun k : ℤ => 2 * Real.pi * k / L)
    (by positivity) hloc hs⟩
  filter_upwards [hloc k] with t ht hmem
  have := abs_le.1 (ht hmem)
  constructor <;> linarith [this.1, this.2]

end QuantumNLS.CellLocalization

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.CellLocalization.onshell_in_cellSet
#print axioms QuantumNLS.CellLocalization.graph_localization
#print axioms QuantumNLS.CellLocalization.moment_comparison
#print axioms QuantumNLS.CellLocalization.cell_localization
