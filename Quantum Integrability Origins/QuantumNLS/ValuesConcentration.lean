import Mathlib
import QuantumNLS.Prop017Bias
import QuantumNLS.RootMeasureConcentrationSharp
import QuantumNLS.RootMeasureExistence
import QuantumNLS.BulkResponseActual

/-!
# values:prop:concentration (R-0270D1F7): Cauchy-transform mean square and bias

Source: `source-text/chapters/foundations/concentration_and_tails.tex`, Proposition `values:prop:concentration` (line 12) with its proof.
Statement: there are `η₀, C > 0` depending only on `L, κ` such that for every `N ≥ 1`, every unit profile and every `z` with `Im z = η ≥ η₀`,
`E|G_N(z) − G_μ(z)|² ≤ C/(Nη²)` and `|E G_N(z) − G_μ(z)| ≤ C/(Nη²)`; the constants are independent of `Re z`, of the Bethe configuration and of the unit profile,
and uniform for `κ` in a compact subset of `(0, ∞)`.

Realization (DEF-048, DEF-010, R-09E1EAE9; all accepted/realized):
* `E` is the expectation under the actual Born law `bornMeasure (physBasis L hκ N) u hu` of the physical Bethe basis at coupling `κ/N`
  (the product law `p_{N,u}` of eq. `eq:law`), `G_N(z) = cauchyTransform (empiricalProb L κ N m) z` the Cauchy transform of the empirical rapidity measure,
  `μ` the quantum-derived limiting measure (`IsLimitingRapidityMeasure`, any witness; by uniqueness it is `muOf`), `G_μ = cauchyTransform μ`.
* mean square: `RootMeasureConcentrationSharp.concentration_sharp` (the sharp `η⁻²` estimate of R-09E1EAE9), with `G_μ = g` by
  `RootMeasureExistence.cauchy_limiting_measure`;
* bias: `Prop017Bias.born_mean_G` (second-order expansion of `f_z` at `g`, `eq:root-product-error` and the mean-square bound), written as an integral over the Born law.
* `η₀ = max{4K, L⁻¹ log 16}` and `C = max{Csharp, |Cg| K}` depend only on `L` and an upper bound `K ≥ κ`; taking `K = κ` gives the constants for fixed `κ`, and a compact subset of `(0,∞)` is covered by its maximum.
  The estimates are proved for every unit `u ∈ L²(𝕋_L)` (in particular every unit smooth profile).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.ValuesConcentration

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (GN HighHalf)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.RootMeasureConcentration (norm_GN_le)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp Kc_nonneg concentration_sharp)
open QuantumNLS.RootMeasureExistence (cauchy_empirical physBasis_eq cauchy_limiting_measure)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.Prop017Bias (Cg born_mean_G)

variable {L : ℝ} [Fact (0 < L)]

/-- **The Born mean of `G_N`** as an integral over the Born law: `E G_N(z)`, with bias `≤ Cg κ/(Nη²)` from `g`. -/
theorem born_mean_integral {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1)
    {z : ℂ} (hz : HighHalf L κ z) :
    ‖(∫ m : MArr N, cauchyTransform (empiricalProb L κ N m : Measure ℝ) z
        ∂(bornMeasure (physBasis L hκ N) u hu)) -
      QuantumNLS.RootMeasureConcentration.gStar L κ hκ u hu z‖ ≤ Cg * κ / (N * z.im ^ 2) := by
  have hη : 0 < z.im := by linarith [hz.1]
  rw [physBasis_eq hκ (by omega : 1 ≤ N)]
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  have hf : ∀ m : MArr N, cauchyTransform (empiricalProb L κ N m : Measure ℝ) z =
      GN N (arrRoots L (κ / N) m) z := fun m => cauchy_empirical hN m hη
  simp_rw [hf]
  have hint : Integrable (fun m : MArr N => GN N (arrRoots L (κ / N) m) z) (bornMeasure Ψ u hu) :=
    Integrable.of_bound (C := (z.im)⁻¹) Measurable.of_discrete.aestronglyMeasurable
      (Eventually.of_forall fun m => norm_GN_le _ hη)
  rw [integral_countable hint]
  have hmu : ∀ m : MArr N, (bornMeasure Ψ u hu).real {m} = bornLaw Ψ u m := by
    intro m
    rw [measureReal_def, QuantumNLS.EmpiricalRapidity.bornMeasure_singleton,
      ENNReal.toReal_ofReal (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)]
  simp_rw [hmu, Complex.real_smul]
  obtain ⟨EG, hEG, hb⟩ := born_mean_G hκ hN u hu hz
  rw [hEG.tsum_eq]
  exact hb

/-- **`values:prop:concentration`** (R-0270D1F7), with constants `η₀ = max{4K, L⁻¹ log 16}`,
`C = max{Csharp, |Cg| K}` for any upper bound `K ≥ κ`. -/
theorem values_concentration {κ K : ℝ} (hκ : 0 < κ) (hκK : κ ≤ K) :
    0 < max (4 * K) (Real.log 16 / L) ∧ 0 < max Csharp (|Cg| * K) ∧
    ∀ (N : ℕ) (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) (μ : ProbabilityMeasure ℝ),
      IsLimitingRapidityMeasure L κ hκ u hu μ →
      ∀ z : ℂ, max (4 * K) (Real.log 16 / L) ≤ z.im →
        (∫ m : MArr N, ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z -
            cauchyTransform (μ : Measure ℝ) z‖ ^ 2 ∂(bornMeasure (physBasis L hκ N) u hu) ≤
          max Csharp (|Cg| * K) / (N * z.im ^ 2)) ∧
        ‖(∫ m : MArr N, cauchyTransform (empiricalProb L κ N m : Measure ℝ) z
            ∂(bornMeasure (physBasis L hκ N) u hu)) - cauchyTransform (μ : Measure ℝ) z‖ ≤
          max Csharp (|Cg| * K) / (N * z.im ^ 2) := by
  have hL : 0 < L := Fact.out
  have hCs : 0 < Csharp := by
    unfold Csharp
    have := Kc_nonneg
    linarith
  refine ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), lt_of_lt_of_le hCs (le_max_left _ _), ?_⟩
  intro N hN u hu μ hμ z hz
  have hzH : HighHalf L κ z := by
    refine ⟨?_, ?_⟩
    · exact (le_trans (by linarith) (le_max_left _ _)).trans hz
    · have h1 : Real.log 16 / L ≤ z.im := (le_max_right _ _).trans hz
      rw [div_le_iff₀ hL] at h1
      linarith
  have hη : 0 < z.im := by linarith [hzH.1]
  have hg := cauchy_limiting_measure hκ u hu hμ hzH
  rw [hg]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 ≤ 1 / (N * z.im ^ 2) := by positivity
  refine ⟨?_, ?_⟩
  · refine (concentration_sharp hκ hN u hu hzH).trans ?_
    rw [div_eq_mul_one_div, div_eq_mul_one_div (max _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hden
  · refine (born_mean_integral hκ hN u hu hzH).trans ?_
    rw [div_eq_mul_one_div, div_eq_mul_one_div (max _ _)]
    refine mul_le_mul_of_nonneg_right ?_ hden
    refine le_trans ?_ (le_max_right _ _)
    calc Cg * κ ≤ |Cg| * κ := mul_le_mul_of_nonneg_right (le_abs_self _) hκ.le
      _ ≤ |Cg| * K := mul_le_mul_of_nonneg_left hκK (abs_nonneg _)

end QuantumNLS.ValuesConcentration

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ValuesConcentration.born_mean_integral
#print axioms QuantumNLS.ValuesConcentration.values_concentration
