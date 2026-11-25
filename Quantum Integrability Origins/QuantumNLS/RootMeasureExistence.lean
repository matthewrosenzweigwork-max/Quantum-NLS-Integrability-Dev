import Mathlib
import QuantumNLS.RootMeasureConcentration
import QuantumNLS.RootMeasureNoLoss
import QuantumNLS.CauchyInProbability
import QuantumNLS.BulkResponseActual

/-!
# R-09E1EAE9 `thm:root-measure`: existence of `μ_{κ,u}` and its Cauchy transform

Source: `ROOT_spectral_measure.tex`, `thm:root-measure`, Steps 1-5 (Step 6, continuity in `u`, is not formalized here).

Chain of the proof as realized (no EXT-025 contract used; in particular the vague-compactness contract `FIN-EXT025-GP-10` is NOT needed:
compactness is mathlib's Prokhorov theorem for the TIGHT sequences produced by Step 4's no-loss-of-mass estimate, see
`CauchyLimitCriterion`):

1. `RootMeasureComplex` (Steps 1-2): injectivity of `f_z` and the deterministic product error.
2. `RootMeasureTransfer`: the on-shell eigenvalue equals `s_N`; Born-law variance bound from the accepted PROP-008 `p = 1` estimate.
3. `RootMeasureConcentration` (Step 3, pointwise): the limiting Cauchy value `gStar` on the high half-plane.
4. `RootMeasureNoLoss` (Step 4): `iY g(iY) → 1`.
5. `CauchyUniqueness`, `CauchyLimitCriterion`, `CauchyInProbability`: Cauchy-transform uniqueness (one horizontal line), tail inequality, tightness,
   Prokhorov, selection of outcomes, weak convergence in probability.
6. This module: `G_{ν_N}(z) → gStar(z)` in probability under the Born law (Chebyshev with PROP-008, product error, injectivity), and the assembly:
   `exists_limiting_measure : ∃ μ, IsLimitingRapidityMeasure L κ hκ u hu μ` and the identification `G_μ = gStar` on the high half-plane.

Deviation from the printed statement: the concentration constant in `eq:root-G-concentration` is not tracked (see `RootMeasureConcentration`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.RootMeasureExistence

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (sProd GN fz HighHalf fz_lower product_error)
open QuantumNLS.NormalizedTransfer (productSymbol)
open QuantumNLS.BetheCoefficientTransform (bornLaw BetheBasis)
open QuantumNLS.HighMomentsTransfer (Cunif)
open QuantumNLS.RootMeasureTransfer (hasSum_born_variance born_variance_le)
open QuantumNLS.RootMeasureConcentration (norm_GN_le gStar gStar_spec)
open QuantumNLS.EmpiricalRapidity (bornMeasure empiricalMeasure empiricalMeasureκ)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.BornConvergence (TendstoInProbabilityWeak TendstoInProbability)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### Chebyshev under the Born measure -/

theorem born_chebyshev {N : ℕ} (Ψ : BetheBasis L N) (u : L2T L) (hu : ‖u‖ = 1) (f : MArr N → ℝ)
    {c W : ℝ} (hc : 0 < c) (hsum : Summable (fun m => bornLaw Ψ u m * f m ^ 2))
    (hW : ∑' m, bornLaw Ψ u m * f m ^ 2 ≤ W) :
    bornMeasure Ψ u hu {m | c ≤ f m} ≤ ENNReal.ofReal (W / c ^ 2) := by
  unfold bornMeasure
  rw [PMF.toMeasure_apply _ (MeasurableSet.of_discrete (s := {m : MArr N | c ≤ f m}))]
  have hnn : ∀ m, 0 ≤ bornLaw Ψ u m * f m ^ 2 / c ^ 2 := fun m => by
    have := QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg Ψ u m
    positivity
  have hs2 : Summable (fun m => bornLaw Ψ u m * f m ^ 2 / c ^ 2) := hsum.div_const _
  calc ∑' m, {m | c ≤ f m}.indicator (QuantumNLS.BetheCoefficientTransform.bornPMF Ψ u hu) m
      ≤ ∑' m, ENNReal.ofReal (bornLaw Ψ u m * f m ^ 2 / c ^ 2) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        by_cases hm : c ≤ f m
        · rw [Set.indicator_of_mem (by exact hm), QuantumNLS.BetheCoefficientTransform.bornPMF_apply]
          apply ENNReal.ofReal_le_ofReal
          rw [le_div_iff₀ (by positivity)]
          have : c ^ 2 ≤ f m ^ 2 := pow_le_pow_left₀ hc.le hm 2
          nlinarith [QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg Ψ u m]
        · rw [Set.indicator_of_notMem (by exact hm)]; exact zero_le
    _ = ENNReal.ofReal (∑' m, bornLaw Ψ u m * f m ^ 2 / c ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hs2).symm
    _ ≤ ENNReal.ofReal (W / c ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_div_const]
        exact div_le_div_of_nonneg_right hW (by positivity)

/-! ### The random Cauchy transform and the deterministic estimate -/

theorem physBasis_eq (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    physBasis L hκ N = QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ := by
  unfold physBasis; rw [dif_pos hN]

theorem cauchy_empirical {N : ℕ} (hN : 0 < N) (m : MArr N) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (empiricalProb L κ N m : Measure ℝ) z = GN N (arrRoots L (κ / N) m) z := by
  have hdef : (empiricalProb L κ N m : Measure ℝ) = empiricalMeasure L (κ / N) m := by
    simp [empiricalProb, hN, empiricalMeasureκ]
  rw [hdef]
  exact QuantumNLS.EmpiricalRapidity.cauchyTransform_empiricalMeasure L (κ / N) hN m z hz.ne'

theorem GN_dist_le (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    {g s : ℂ} (hg : ‖g‖ ≤ (z.im)⁻¹) (hgs : fz L κ z g = s) :
    κ / 2 * ‖GN N q z - g‖ ≤ 3 * (κ / z.im) ^ 2 / N + ‖sProd L κ N q z - s‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  have h1 := fz_lower hκ hz (norm_GN_le q hη) hg
  rw [hgs] at h1
  have h2 := product_error hκ hz hN q
  have h3 : ‖fz L κ z (GN N q z) - s‖ ≤
      ‖fz L κ z (GN N q z) - sProd L κ N q z‖ + ‖sProd L κ N q z - s‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_sub_rev (fz L κ z (GN N q z)) (sProd L κ N q z)] at h3
  linarith

/-- **Concentration in probability** of `G_{ν_N}(z)` around `g(z)` (the printed `eq:root-G-concentration`, in probability form). -/
theorem tendsto_prob_G (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu
      {m : MArr N | δ ≤ ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z - gStar L κ hκ u hu z‖})
      atTop (𝓝 0) := by
  have hη : 0 < z.im := by linarith [hz.1]
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  set c := κ * δ / 4 with hc
  have hc0 : 0 < c := by positivity
  have hup : Tendsto (fun N : ℕ => ENNReal.ofReal (Cunif L κ 0 1 / N / c ^ 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => Cunif L κ 0 1 / (N : ℝ) / c ^ 2) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := Cunif L κ 0 1)).div_atTop tendsto_natCast_atTop_atTop
      simpa using this.div_const (c ^ 2)
    simpa using ENNReal.tendsto_ofReal h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop (⌈3 * (κ / z.im) ^ 2 / c⌉₊ + 1)] with N hN
  have hN1 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hceil : 3 * (κ / z.im) ^ 2 / c ≤ N := by
    have h1 := Nat.le_ceil (3 * (κ / z.im) ^ 2 / c)
    have h2 : ((⌈3 * (κ / z.im) ^ 2 / c⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈3 * (κ / z.im) ^ 2 / c⌉₊ ≤ N)
    linarith
  have hsmall : 3 * (κ / z.im) ^ 2 / N ≤ c := by
    rw [div_le_iff₀ hNr]
    rw [div_le_iff₀ hc0] at hceil
    linarith
  rw [physBasis_eq hκ (by omega : 1 ≤ N)]
  have hsub : {m : MArr N | δ ≤ ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z -
      gStar L κ hκ u hu z‖} ⊆ {m : MArr N | c ≤ ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖} := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [cauchy_empirical hN1 m hη] at hm
    have h := GN_dist_le hκ hz hN1 (arrRoots L (κ / N) m) hg1 hg2
    have : κ / 2 * δ ≤ κ / 2 * ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    rw [hc]
    linarith
  refine le_trans (measure_mono hsub) ?_
  have hb := born_chebyshev (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N (by omega) hκ) u hu
    (fun m => ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖) hc0
    (hasSum_born_variance hκ hN1 u z hη).summable (born_variance_le hκ hN1 u hu z hη)
  exact hb

/-! ### Existence of `μ_{κ,u}` -/

/-- **R-09E1EAE9, existence half**: for every unit `u` there is a probability measure `μ` on `ℝ` with `ν_N → μ` weakly in probability on the Born
spaces of the accepted physical basis (`IsLimitingRapidityMeasure`; unique by `IsLimitingRapidityMeasure.unique`). -/
theorem exists_limiting_measure (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    ∃ μ : ProbabilityMeasure ℝ, IsLimitingRapidityMeasure L κ hκ u hu μ := by
  set η₀ : ℝ := max (4 * κ) (Real.log 16 / L) with hη₀
  have hL : 0 < L := Fact.out
  have hη0 : 0 < η₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hhigh : ∀ y : ℝ, η₀ ≤ y → HighHalf L κ (Complex.I * (y : ℂ)) := by
    intro y hy
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    refine ⟨by rw [him]; exact (le_max_left _ _).trans hy, ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ y := (le_max_right _ _).trans hy
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hhighL : ∀ t : ℝ, HighHalf L κ ((t : ℂ) + η₀ * Complex.I) := by
    intro t
    have him : ((t : ℂ) + η₀ * Complex.I).im = η₀ := by simp
    refine ⟨by rw [him]; exact le_max_left _ _, ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ η₀ := le_max_right _ _
    rwa [div_le_iff₀ hL, mul_comm] at this
  let g : ℂ → ℂ := gStar L κ hκ u hu
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let Y : ℕ → ℝ := fun j => η₀ + j
  have hYpos : ∀ j, 0 < Y j := fun j => by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; simp only [Y]; linarith
  -- no loss of mass
  have hmassY : Tendsto (fun y : ℝ => 1 + y * (g (Complex.I * (y : ℂ))).im) atTop (𝓝 0) := by
    refine QuantumNLS.RootMeasureNoLoss.one_add_mul_im_tendsto hκ u hu (fun y => g (Complex.I * (y : ℂ))) ?_
    intro y hy
    obtain ⟨h1, h2⟩ := gStar_spec hκ u hu hy
    refine ⟨?_, h2⟩
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    simpa [him] using h1
  have hYtop : Tendsto Y atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hmass : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0) :=
    hmassY.comp hYtop
  have hZ : ∀ k, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu
        {m : MArr N | δ ≤ ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) ((q k : ℂ) + η₀ * Complex.I) -
          g ((q k : ℂ) + η₀ * Complex.I)‖}) atTop (𝓝 0) :=
    fun k δ hδ => tendsto_prob_G hκ u hu (hhighL (q k)) hδ
  have hW : ∀ j, ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu
        {m : MArr N | δ ≤ ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) (Complex.I * (Y j : ℂ)) -
          g (Complex.I * (Y j : ℂ))‖}) atTop (𝓝 0) :=
    fun j δ hδ => tendsto_prob_G hκ u hu (hhigh (Y j) (by simp only [Y]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)) hδ
  obtain ⟨μ, -, hμ⟩ := QuantumNLS.CauchyInProbability.exists_weak_limit_in_probability
    (Ω := fun N => MArr N) (fun N => bornMeasure (physBasis L hκ N) u hu)
    (fun N m => empiricalProb L κ N m) (g := g)
    (Z := fun k => (q k : ℂ) + η₀ * Complex.I) (W := fun j => Complex.I * (Y j : ℂ))
    (η₀ := η₀) (q := q) (Y := Y) hη0 (TopologicalSpace.denseRange_denseSeq ℝ) hYpos
    (fun _ => rfl) (fun _ => rfl) hmass hZ hW
  exact ⟨μ, hμ⟩

/-- **The measure and its Cauchy transform** (the printed characterization of `g`): the limiting measure has `G_μ(z) = g(z)` on the whole
high half-plane, where `g(z)` is the unique solution in `|w| ≤ (Im z)⁻¹` of `f_z(w) = s(z;u)`. -/
theorem cauchy_limiting_measure (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {z : ℂ} (hz : HighHalf L κ z) :
    cauchyTransform (μ : Measure ℝ) z = gStar L κ hκ u hu z := by
  have hη : 0 < z.im := by linarith [hz.1]
  -- continuity of `ρ ↦ G_ρ(z)` at `μ` for the Lévy-Prokhorov topology
  let F : LevyProkhorov (ProbabilityMeasure ℝ) → ℂ := fun ρ =>
    cauchyTransform ((LevyProkhorov.toMeasure ρ : ProbabilityMeasure ℝ) : Measure ℝ) z
  have hF : ContinuousAt F (LevyProkhorov.ofMeasure μ) := by
    have h1 := QuantumNLS.CauchyLimitCriterion.tendsto_cauchy_of_tendsto
      (ι := ProbabilityMeasure ℝ) (l := 𝓝 μ) (ρ := id) (μ := μ) tendsto_id hη
    have h2 : Tendsto (LevyProkhorov.toMeasure : LevyProkhorov (ProbabilityMeasure ℝ) → ProbabilityMeasure ℝ)
        (𝓝 (LevyProkhorov.ofMeasure μ)) (𝓝 μ) :=
      LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _
    unfold ContinuousAt
    exact h1.comp h2
  have hcomp := TendstoInProbability.comp_continuousAt (E := LevyProkhorov (ProbabilityMeasure ℝ)) hμ hF
  have hg : TendstoInProbability (fun N => bornMeasure (physBasis L hκ N) u hu)
      (fun N (m : MArr N) => cauchyTransform (empiricalProb L κ N m : Measure ℝ) z) (gStar L κ hκ u hu z) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_prob_G hκ u hu hz hε)
      (fun _ => zero_le) (fun N => measure_mono ?_)
    intro m hm
    simp only [Set.mem_setOf_eq, dist_eq_norm] at hm ⊢
    exact hm.le
  have hcomp' : TendstoInProbability (fun N => bornMeasure (physBasis L hκ N) u hu)
      (fun N (m : MArr N) => cauchyTransform (empiricalProb L κ N m : Measure ℝ) z) (F (LevyProkhorov.ofMeasure μ)) :=
    hcomp
  have hu' := TendstoInProbability.unique hcomp' hg
  exact hu'

end QuantumNLS.RootMeasureExistence

#print axioms QuantumNLS.RootMeasureExistence.born_chebyshev
#print axioms QuantumNLS.RootMeasureExistence.tendsto_prob_G
#print axioms QuantumNLS.RootMeasureExistence.exists_limiting_measure
#print axioms QuantumNLS.RootMeasureExistence.cauchy_limiting_measure
