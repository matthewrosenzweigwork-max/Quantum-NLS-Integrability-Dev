import Mathlib
import QuantumNLS.F03ActualProb
import QuantumNLS.F03ActualQuantile
import QuantumNLS.F03ActualData
import QuantumNLS.RootEnergyMoment

/-!
# R-BB7EDFF3 (`CC:F03:actual`): mean squared convergence under the original product law

Source: `source-text/chapters/root_response/F03.tex`, `\begin{theorem}[Mean squared convergence under the
original law]` (`CC:F03:actual`, lines 322-373 of the source text), statement and proof.

**Printed statement.**  Let `u ∈ H¹(𝕋_L)` be a unit vector.  Sample the ordered Bethe roots at coupling `κ/N`
under the original product coefficient law `ℙ_{N,u}`.  Let `μ = μ_{κ,u}`, and define `Q, F, Q_N, F_N` as above
(`Q` the increasing quantile of `μ`; `F` the unique solution of the response equation
`CC:F03:limit-equation`; `Q_N` the step quantile of the ordered root array on the `N` equal subintervals of
`(0,1)`; `F_N` the step function with values `B_N⁻¹ q`).  Then
`𝔼_{N,u} ‖Q_N − Q‖₂² → 0` and `𝔼_{N,u} ‖F_N − F‖₂² → 0`.  No fourth moment is assumed.

**Lean formulation (`actual_mean_square_convergence`).**
* `law hκ u hu N = bornMeasure (physBasis L hκ N) u hu`: the Born law `|⟨Ψ_{N,m}, u^{⊗N}⟩|²` of the complete
  physical Bethe basis at coupling `κ/N` (the original product coefficient law `ℙ_{N,u}`); the sampled array is
  `m : 𝓜_N`, whose ordered Bethe roots at coupling `κ/N` are `arrRoots L (κ/N) m` (strictly increasing).
* `μ` is the field `D.μ` of an `ActualBulkData L κ hκ u hu`: by `IsLimitingRapidityMeasure` it IS the unique
  quantum-derived limiting rapidity measure `μ_{κ,u}` (R-09E1EAE9), and its field `bulk` is the standing
  assumptions of the section (probability, no atoms, finite second moment, the density assumptions of
  `CC:F03:core`), which are PROVED for the actual measure in `F03ActualData.bulkMeasure_actual`.  The statement is
  existential in `D`, so nothing is assumed: the existence of the data is part of the conclusion.
* `Q = Q2 D.toBulkResponseData ∈ L²(0,1)` is the quantile of `μ`; `F` is a response (the solution of
  `CC:F03:limit-equation` in the form domain), and it is the only one.
* `Q_N = stepL2 (arrRoots L (κ/N) m)` (step quantile of the ordered array), and
  `F_N = stepL2 (responseVec L (κ/N) (arrRoots L (κ/N) m))` with `responseVec = B⁻¹ q` (DEF-051, the Gaudin
  matrix, equal to the printed operator by `F03ActualQuantile.bop_eq_gaudin`).
* `𝔼 ‖·‖²` is the extended expectation `∫⁻ ofReal(‖·‖²) d law`, so no integrability is hidden in a Bochner
  integral.
* Hypotheses: `0 < κ`, `Fact (0 < L)`, `‖u‖ = 1` and `OneH1 u` (finite `Σ (1+p_n²)|û(n)|²`, DEF-002 `s=1`), i.e.
  exactly "`L, κ > 0`, `u ∈ H¹` unit".  No fourth moment appears.

**Argument (as printed).**  (1) weak convergence in probability of `ν_N` to `μ` (`D.limit`, thm:root-measure);
(2) `E_N = ‖Q_N‖² = N⁻¹ Σ q_i² → E_* = ∫x²dμ` in `L¹` (`RootEnergyMoment.root_energy_moment`, thm:root-energy-moment),
hence in probability (`F03ActualProb.inProb_of_L1`); (3) the quantile criterion in neighbourhood form
(`F03ActualQuantile.w2_nbhd`, `quantile_inProb`) with `‖Q_N−Q‖ = W₂(ν_N, μ)`
(`DetGapW2.norm_step_sub_Q2`, ordered coupling) gives `‖Q_N − Q‖ → 0` in probability; (4) `‖Q_N−Q‖² ≤ 2E_N + 2‖Q‖²`
with `E_N → E_*` in `L¹` gives the first limit (`F03ActualProb.tendsto_lintegral_of_dom`); (5) sequential local
uniformity of the deterministic response theorem (`F03ActualQuantile.response_local_uniform`, from
`StrongLimitBulk.strong_limit_bulk`) gives `‖F_N − F‖ → 0` in probability; (6) `‖F_N − F‖² ≤ 2E_N/L² + 2‖F‖²`
(`F03ActualQuantile.response_norm_sq_le`) and (2) give the second limit.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.F03Actual

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.BornConvergence (TendstoInProbability)
open QuantumNLS.BulkResponseActual (ActualBulkData empiricalProb)
open QuantumNLS.BulkResponseForm (L2Unit)
open QuantumNLS.StepIntegrals (stepL2 norm_sq_step)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.GaudinResponse (responseVec)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.ChargeEnergy (energyH1)
open QuantumNLS.RootEnergyMomentLaws (law sample_second_moment)
open QuantumNLS.RootEnergyMomentExpectation (sampleEnergy)
open QuantumNLS.QuantileTransport (W2 HasFiniteSecondMoment empirical)
open QuantumNLS.EmpiricalRapidity (empiricalMeasure)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The ordered Bethe roots of the sampled label `m ∈ 𝓜_{n+1}` at coupling `κ/(n+1)`. -/
def rts (L κ : ℝ) (n : ℕ) (m : MArr (n + 1)) : Fin (n + 1) → ℝ :=
  arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m

/-- The energy `E_N = ‖Q_N‖²₂`. -/
def En (L κ : ℝ) (n : ℕ) (m : MArr (n + 1)) : ℝ := ‖stepL2 (rts L κ n m)‖ ^ 2

/-- The two mean-square limits, for given actual data `D` and response `F`, along `N = n + 1`. -/
theorem mean_square_of_data (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u)
    (D : ActualBulkData L κ hκ u hu) {F : L2Unit} (hF : D.toBulkResponseData.IsResponse F) :
    Tendsto (fun n : ℕ => ∫⁻ m, ENNReal.ofReal
        (‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ ^ 2) ∂(law hκ u hu (n + 1)))
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ m, ENNReal.ofReal
        (‖stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) - F‖ ^ 2)
        ∂(law hκ u hu (n + 1))) atTop (𝓝 0) := by
  have hL : 0 < L := Fact.out
  have hmu : D.μ = QuantumNLS.FreeLimit.muKappa u hu κ :=
    D.limit.unique (QuantumNLS.FreeLimit.muKappa_spec u hu hκ)
  -- the energy theorem
  obtain ⟨-, -, hmain⟩ := QuantumNLS.RootEnergyMoment.root_energy_moment hκ u hH
  obtain ⟨-, -, hint, hL1⟩ := hmain hu
  have he : ∀ (n : ℕ) (m : MArr (n + 1)),
      (∫ t : ℝ, t ^ 2 ∂empiricalMeasure L (κ / ((n + 1 : ℕ) : ℝ)) m) = sampleEnergy L κ (n + 1) m :=
    fun n m => (sample_second_moment (Nat.succ_pos n) m).2
  have hEn : ∀ (n : ℕ) (m : MArr (n + 1)), En L κ n m = sampleEnergy L κ (n + 1) m := by
    intro n m
    unfold En rts sampleEnergy
    rw [norm_sq_step (Nat.succ_pos n)]
    unfold QuantumNLS.FiniteResponse.L2N
    rw [one_div]
  set Es : ℝ := energyH1 κ (u : AddCircle L → ℂ) with hEsdef
  have hEint : ∀ n : ℕ, Integrable (En L κ n) (law hκ u hu (n + 1)) := by
    intro n
    refine (hint n).congr (Eventually.of_forall fun m => ?_)
    simp only [he, hEn]
  have hL1' : Tendsto (fun n : ℕ => ∫ m, |En L κ n m - Es| ∂(law hκ u hu (n + 1))) atTop (𝓝 0) := by
    refine hL1.congr (fun n => integral_congr_ae (Eventually.of_forall fun m => ?_))
    simp only [he, hEn]
  have hEprob : TendstoInProbability (fun n => law hκ u hu (n + 1)) (En L κ) Es :=
    QuantumNLS.F03ActualProb.inProb_of_L1 (fun n => law hκ u hu (n + 1)) (En L κ) Es
      (fun n => (hEint n).sub (integrable_const Es)) hL1'
  -- the empirical measures
  let ν : ∀ n : ℕ, MArr (n + 1) → ProbabilityMeasure ℝ := fun n m => empiricalProb L κ (n + 1) m
  have hνm : ∀ (n : ℕ) (m : MArr (n + 1)), ((ν n m : ProbabilityMeasure ℝ) : Measure ℝ) =
      empiricalMeasure L (κ / ((n + 1 : ℕ) : ℝ)) m :=
    fun n m => QuantumNLS.RootEnergyMomentAverage.empiricalProb_succ n m
  have hEs : ∫ x, x ^ 2 ∂(D.μ : Measure ℝ) = Es := by
    rw [hmu]; exact (QuantumNLS.RootEnergyMoment.unit_scalar hκ u hu hH).2
  have hμ2 : HasFiniteSecondMoment (D.μ : Measure ℝ) :=
    QuantumNLS.BulkResponseRiesz.hasFiniteSecondMoment_of_moment D.bulk.finiteSecondMoment
  have hfin : ∀ (n : ℕ) (m : MArr (n + 1)), HasFiniteSecondMoment (ν n m : Measure ℝ) := by
    intro n m
    rw [hνm]
    exact (sample_second_moment (Nat.succ_pos n) m).1
  have hmom : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => ∫ x, x ^ 2 ∂(ν n m : Measure ℝ)) (∫ x, x ^ 2 ∂(D.μ : Measure ℝ)) := by
    rw [hEs]
    have : (fun (n : ℕ) (m : MArr (n + 1)) => ∫ x, x ^ 2 ∂(ν n m : Measure ℝ)) = En L κ := by
      funext n m
      rw [hνm, he, hEn]
    rw [this]
    exact hEprob
  have hw : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => LevyProkhorov.ofMeasure (ν n m)) (LevyProkhorov.ofMeasure D.μ) :=
    fun ε hε => (D.limit ε hε).comp (tendsto_add_atTop_nat 1)
  have hW := QuantumNLS.F03ActualQuantile.quantile_inProb (fun n => law hκ u hu (n + 1)) ν D.μ
    hfin hμ2 hw hmom
  -- `‖Q_N − Q‖ = W₂(ν_N, μ)`
  have hemp : ∀ (n : ℕ) (m : MArr (n + 1)),
      empirical (n + 1) (rts L κ n m) = empiricalMeasure L (κ / ((n + 1 : ℕ) : ℝ)) m := by
    intro n m
    unfold empirical empiricalMeasure rts
    rw [Finset.smul_sum]
  have hX1 : ∀ (n : ℕ) (m : MArr (n + 1)),
      ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ =
        (W2 (ν n m : Measure ℝ) (D.μ : Measure ℝ)).toReal := by
    intro n m
    have hc : 0 < κ / ((n + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      positivity
    have hmono : Monotone (rts L κ n m) := by
      unfold rts QuantumNLS.BetheLabels.arrRoots
      exact (QuantumNLS.BetheLabels.roots_strictMono_labels hL hc _).monotone
    rw [QuantumNLS.DetGapW2.norm_step_sub_Q2 D.toBulkResponseData (Nat.succ_pos n) hmono,
      hemp, ← hνm]
    rfl
  have hX1prob : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖) 0 := by
    have : (fun (n : ℕ) (m : MArr (n + 1)) => ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖) =
        fun n m => (W2 (ν n m : Measure ℝ) (D.μ : Measure ℝ)).toReal :=
      funext fun n => funext fun m => hX1 n m
    rw [this]
    exact hW
  have hX1sq : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ ^ 2) 0 := by
    have := hX1prob.comp_continuousAt (g := fun x : ℝ => x ^ 2) (continuous_pow 2).continuousAt
    simpa using this
  -- first limit
  have h1 : Tendsto (fun n : ℕ => ∫⁻ m, ENNReal.ofReal
      (‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ ^ 2) ∂(law hκ u hu (n + 1)))
      atTop (𝓝 0) := by
    refine QuantumNLS.F03ActualProb.tendsto_lintegral_of_dom (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ ^ 2) (En L κ)
      (fun n => measurable_of_countable _) (fun n => measurable_of_countable _)
      2 (2 * ‖Q2 D.toBulkResponseData‖ ^ 2) Es (by norm_num) ?_ hEint hL1' hX1sq
    intro n m
    have h2 := norm_sub_le (stepL2 (rts L κ n m)) (Q2 D.toBulkResponseData)
    have h3 : ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ ^ 2 ≤
        (‖stepL2 (rts L κ n m)‖ + ‖Q2 D.toBulkResponseData‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    unfold En
    nlinarith [sq_nonneg (‖stepL2 (rts L κ n m)‖ - ‖Q2 D.toBulkResponseData‖)]
  -- response in probability
  have hX2prob : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) - F‖) 0 := by
    intro ε hε
    obtain ⟨δ, hδ, N₀, hN₀, hloc⟩ :=
      QuantumNLS.F03ActualQuantile.response_local_uniform D.toBulkResponseData hF hε
    have hs := hX1prob (δ / 2) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [eventually_ge_atTop N₀] with n hn
    refine measure_mono ?_
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    by_contra hcon
    have hlt : ‖stepL2 (rts L κ n m) - Q2 D.toBulkResponseData‖ < δ := by
      simp only [not_lt, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hcon
      linarith
    have hres := hloc (n + 1) (by omega) (rts L κ n m) hlt
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hm
    exact absurd hm (not_lt.2 hres.le)
  have hX2sq : TendstoInProbability (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) - F‖ ^ 2) 0 := by
    have := hX2prob.comp_continuousAt (g := fun x : ℝ => x ^ 2) (continuous_pow 2).continuousAt
    simpa using this
  -- second limit
  have h2 : Tendsto (fun n : ℕ => ∫⁻ m, ENNReal.ofReal
      (‖stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) - F‖ ^ 2)
      ∂(law hκ u hu (n + 1))) atTop (𝓝 0) := by
    refine QuantumNLS.F03ActualProb.tendsto_lintegral_of_dom (fun n => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) - F‖ ^ 2)
      (En L κ) (fun n => measurable_of_countable _) (fun n => measurable_of_countable _)
      (2 / L ^ 2) (2 * ‖F‖ ^ 2) Es (by positivity) ?_ hEint hL1' hX2sq
    intro n m
    have hb := QuantumNLS.F03ActualQuantile.response_norm_sq_le hL hκ (Nat.succ_pos n) (rts L κ n m)
    set Fn := stepL2 (responseVec L (κ / ((n + 1 : ℕ) : ℝ)) (rts L κ n m)) with hFn
    have hL2 : 0 < L ^ 2 := by positivity
    have hF1 : ‖Fn‖ ^ 2 ≤ En L κ n m / L ^ 2 := by
      rw [le_div_iff₀ hL2]
      unfold En
      nlinarith [hb]
    have h2' := norm_sub_le Fn F
    have h3 : ‖Fn - F‖ ^ 2 ≤ (‖Fn‖ + ‖F‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2' 2
    have h4 : 2 / L ^ 2 * En L κ n m = 2 * (En L κ n m / L ^ 2) := by ring
    rw [h4]
    nlinarith [sq_nonneg (‖Fn‖ - ‖F‖)]
  exact ⟨h1, h2⟩

/-- **R-BB7EDFF3 (`CC:F03:actual`), Mean squared convergence under the original law.**  For `L, κ > 0` and a
unit `u ∈ H¹(𝕋_L)`, with `μ = μ_{κ,u}` (the field `D.μ`, the unique quantum-derived limiting measure, whose
standing assumptions are part of the proved conclusion), `Q` its quantile, `F` the unique solution of the response
equation, `Q_N` the step quantile of the sampled ordered Bethe roots at coupling `κ/N` and `F_N` the step function
of `B_N⁻¹ q`, both expected squared `L²(0,1)` errors tend to `0` under the original product law.  No fourth moment is
assumed. -/
theorem actual_mean_square_convergence (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    ∃ D : ActualBulkData L κ hκ u hu, ∃ F : L2Unit,
      D.toBulkResponseData.IsResponse F ∧
      (∀ F' : L2Unit, D.toBulkResponseData.IsResponse F' → F' = F) ∧
      Tendsto (fun N : ℕ => ∫⁻ m, ENNReal.ofReal
          (‖stepL2 (arrRoots L (κ / N) m) - Q2 D.toBulkResponseData‖ ^ 2) ∂(law hκ u hu N))
        atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => ∫⁻ m, ENNReal.ofReal
          (‖stepL2 (responseVec L (κ / N) (arrRoots L (κ / N) m)) - F‖ ^ 2) ∂(law hκ u hu N))
        atTop (𝓝 0) := by
  obtain ⟨D⟩ := QuantumNLS.F03ActualData.actualBulkData_nonempty hκ hu hH
  obtain ⟨F, hF, hFu⟩ := D.toBulkResponseData.existsUnique_response
  obtain ⟨h1, h2⟩ := mean_square_of_data hκ u hu hH D hF
  exact ⟨D, F, hF, hFu, (tendsto_add_atTop_iff_nat 1).1 h1, (tendsto_add_atTop_iff_nat 1).1 h2⟩

end QuantumNLS.F03Actual

#print axioms QuantumNLS.F03Actual.mean_square_of_data
#print axioms QuantumNLS.F03Actual.actual_mean_square_convergence
