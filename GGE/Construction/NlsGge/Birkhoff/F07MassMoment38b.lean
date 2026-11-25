import NlsGge.Birkhoff.F07MassMoment38
import NlsGge.Birkhoff.F05Identity38k
import NlsGge.Spectral.ChargeJensenSobolev38

/-! # F07 (v2 `C:lem:massmoment`), file b: the lowered rates, `d_δ`, and the tilt on `H^{m-1}`

Phi-free (no `BirkhoffInput38`).  Covers F07.03, F07.04, F07.05 and the identity
`V_m' = V_m - δ (Q_{2m-2} - Σ b_n |û(n)|²)` of v2 l.814.

`β' = β` with `β_{m-1}` replaced by `β_{m-1} - δ` (`lowerCoef38`), so `a'_n = a_{m,n} - δ b_n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core Filter Topology
open scoped ENNReal

/-- The coefficient vector with the coefficient of `Q_{2m-2}` lowered by `δ`, all others retained. -/
def lowerCoef38 (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) : ℕ → ℝ :=
  Function.update β (m - 1) (β (m - 1) - δ)

/-- `b_n = (2πn)^{2m-2}`. -/
def f07B38 (m : ℕ) (n : ℤ) : ℝ := (2 * Real.pi * (n : ℝ)) ^ (2 * (m - 1))

theorem f07B38_nonneg (m : ℕ) (n : ℤ) : 0 ≤ f07B38 m n := by
  unfold f07B38; rw [pow_mul]; positivity

section Rates

variable {m : ℕ} {β : ℕ → ℝ} {δ : ℝ}

/-- F07.03: all coefficients stay positive when `δ < β_{m-1}`. -/
theorem lowerCoef_pos38 (hβ : ∀ j ≤ m, 0 < β j) (hδ : δ < β (m - 1)) :
    ∀ j ≤ m, 0 < lowerCoef38 m β δ j := by
  intro j hj
  unfold lowerCoef38
  by_cases h : j = m - 1
  · subst h; rw [Function.update_self]; linarith
  · rw [Function.update_of_ne h]; exact hβ j hj

theorem lowerCoef_le38 (hδ : 0 ≤ δ) :
    ∀ j, lowerCoef38 m β δ j ≤ β j := by
  intro j
  unfold lowerCoef38
  by_cases h : j = m - 1
  · subst h; rw [Function.update_self]; linarith
  · rw [Function.update_of_ne h]

/-- `a'_n = a_{m,n} - δ b_n`. -/
theorem f07RateLower38 (hm : 2 ≤ m) (n : ℤ) :
    finiteHierarchyRate38 m (lowerCoef38 m β δ) n =
      finiteHierarchyRate38 m β n - δ * f07B38 m n := by
  unfold finiteHierarchyRate38 finiteHierarchyW38 f07B38
  set r : ℝ := 2 * Real.pi * (n : ℝ) with hr
  have hupd : ∀ j : ℕ, lowerCoef38 m β δ j * r ^ (2 * j) =
      β j * r ^ (2 * j) - (if j = m - 1 then δ * r ^ (2 * j) else 0) := by
    intro j
    unfold lowerCoef38
    by_cases h : j = m - 1
    · subst h; rw [Function.update_self]; simp; ring
    · rw [Function.update_of_ne h]; simp [h]
  rw [Finset.sum_congr rfl (fun j _ => hupd j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range (m + 1)) (m - 1) (fun j => δ * r ^ (2 * j))]
  simp only [Finset.mem_range, show m - 1 < m + 1 by omega, ite_true]

theorem rate_lower_pos38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ : δ < β (m - 1)) (n : ℤ) :
    0 < finiteHierarchyRate38 m (lowerCoef38 m β δ) n := by
  have hp := lowerCoef_pos38 hβ hδ
  exact finiteHierarchyRate38_pos m _ (fun j hj => (hp j hj).le) (by omega) (hp 0 (by omega))
    (hp m le_rfl) n

theorem f07RatePos38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (n : ℤ) :
    0 < finiteHierarchyRate38 m β n :=
  finiteHierarchyRate38_pos m β (fun j hj => (hβ j hj).le) (by omega) (hβ 0 (by omega))
    (hβ m le_rfl) n

theorem rate_lower_le38 (hm : 2 ≤ m) (hδ : 0 ≤ δ) (n : ℤ) :
    finiteHierarchyRate38 m (lowerCoef38 m β δ) n ≤ finiteHierarchyRate38 m β n := by
  rw [f07RateLower38 hm]
  have := f07B38_nonneg m n
  nlinarith

/-- Uniform positivity margin `ε a_{m,n} ≤ a'_n` with `ε = 1 - δ/β_{m-1}`. -/
theorem rate_margin38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ0 : 0 ≤ δ)
    (hδ : δ < β (m - 1)) (n : ℤ) :
    (1 - δ / β (m - 1)) * finiteHierarchyRate38 m β n ≤
      finiteHierarchyRate38 m (lowerCoef38 m β δ) n := by
  have hb := hβ (m - 1) (by omega)
  set ε : ℝ := 1 - δ / β (m - 1) with hε
  have hε1 : ε ≤ 1 := by
    have : 0 ≤ δ / β (m - 1) := div_nonneg hδ0 hb.le
    linarith
  have hε0 : 0 ≤ ε := by
    have : δ / β (m - 1) ≤ 1 := (div_le_one hb).2 hδ.le
    linarith
  unfold finiteHierarchyRate38 finiteHierarchyW38
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
  have hx : 0 ≤ (2 * Real.pi * (n : ℝ)) ^ (2 * j) := by rw [pow_mul]; positivity
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  unfold lowerCoef38
  by_cases h : j = m - 1
  · subst h; rw [Function.update_self]
    have : ε * β (m - 1) = β (m - 1) - δ := by
      rw [hε]; field_simp
    linarith
  · rw [Function.update_of_ne h]
    have := hβ j hjm
    nlinarith

/-- `Σ_n δ b_n / a_{m,n} < ∞`, i.e. the relative deficits are summable (F07.04). -/
theorem summable_deficit38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) :
    Summable (fun n : ℤ => f07B38 m n / finiteHierarchyRate38 m β n) := by
  have hs := summable_tailRatio38 m β hm (fun i hi => (hβ i hi).le) (hβ 0 (by omega))
    (hβ m le_rfl)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hs.mul_left (1 + (2 * Real.pi) ^ (2 * (m - 1))))
  · exact div_nonneg (f07B38_nonneg m n) (f07RatePos38 hm hβ n).le
  · have hpos := f07RatePos38 hm hβ n
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have := chargeQuad_weight_le38 (m - 1) (m - 1) le_rfl n
    have hb := f07B38_nonneg m n
    unfold f07B38 at hb ⊢
    linarith

theorem summable_lowerDeficit38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) :
    Summable (fun n : ℤ =>
      (finiteHierarchyRate38 m β n - finiteHierarchyRate38 m (lowerCoef38 m β δ) n) /
        finiteHierarchyRate38 m β n) := by
  have := (summable_deficit38 hm hβ).mul_left δ
  refine this.congr fun n => ?_
  rw [f07RateLower38 hm]
  ring

/-- `d_δ = ∏_n a'_n / a_{m,n}` (v2 l.800). -/
def dDelta38 (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) : ℝ :=
  ∏' n : ℤ, finiteHierarchyRate38 m (lowerCoef38 m β δ) n / finiteHierarchyRate38 m β n

/-- **F07.04.**  The product defining `d_δ` converges (with `0 < d_δ`; the factors are positive and
the relative deficits are summable). -/
theorem hasProd_dDelta38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ0 : 0 ≤ δ)
    (hδ : δ < β (m - 1)) :
    0 < dDelta38 m β δ ∧
      HasProd (fun n : ℤ => finiteHierarchyRate38 m (lowerCoef38 m β δ) n /
        finiteHierarchyRate38 m β n) (dDelta38 m β δ) := by
  have hb := hβ (m - 1) (by omega)
  obtain ⟨d, hd0, hd⟩ := hasProd_ratio38 (fun n => finiteHierarchyRate38 m β n)
    (fun n => finiteHierarchyRate38 m (lowerCoef38 m β δ) n)
    (fun n => rate_lower_pos38 hm hβ hδ n) (fun n => rate_lower_le38 hm hδ0 n)
    (1 - δ / β (m - 1)) (by
      have : δ / β (m - 1) < 1 := (div_lt_one hb).2 hδ
      linarith)
    (fun n => rate_margin38 hm hβ hδ0 hδ n) (summable_lowerDeficit38 hm hβ)
  have : dDelta38 m β δ = d := hd.tprod_eq
  rw [this]
  exact ⟨hd0, hd⟩

end Rates

/-! ### The mass term and the lowered remainder -/

theorem normalizedRemainder38_zero : (normalizedRemainder38 0).support = ∅ := by
  have h : formalChargeNonlinearRemainder 0 = 0 := by
    unfold formalChargeNonlinearRemainder formalChargeIntegrand formalChargeQuadraticMainTerm
    simp [p]
  unfold normalizedRemainder38 formalChargeRemainderNormalizedUniformNativeRecovery29Fourth
  rw [h]
  simp

/-- `Q_0(u) = Σ_n |û(n)|²` on `H^{m-1}` (the mass term has zero remainder, v2 `B:lem:local`). -/
theorem chargeSobolev38_zero (m : ℕ) (y : Hm1 m) :
    chargeSobolev38 m 0 y = ∑' n : ℤ,
      ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2 := by
  unfold chargeSobolev38
  rw [normalizedRemainder38_zero]
  simp [chargeQuad38]

section Tilt

variable {m : ℕ} {β : ℕ → ℝ} {δ : ℝ}

/-- v2 l.814: `V_m' = V_m - δ (Q_{2m-2} - Σ b_n |û(n)|²)`. -/
theorem Vm_lower38 (hm : 2 ≤ m) (u : Hm1 m) :
    Vm38 m (lowerCoef38 m β δ) u =
      Vm38 m β u - δ * (chargeSobolev38 m (m - 1) u - chargeQuad38 _ (m - 1) u) := by
  unfold Vm38 localRemainderSobolev38 chargeSobolev38
  set R : ℕ → ℝ := fun j => ∑ q ∈ (normalizedRemainder38 j).support,
    localRemainderMonomialValue38 m j q (toCarrier38 _ u) with hR
  have hupd : ∀ j : ℕ, lowerCoef38 m β δ j * R j =
      β j * R j - (if j = m - 1 then δ * R j else 0) := by
    intro j
    unfold lowerCoef38
    by_cases h : j = m - 1
    · subst h; rw [Function.update_self]; simp; ring
    · rw [Function.update_of_ne h]; simp [h]
  have e : chargeQuad38 _ (m - 1) u +
      ∑ q ∈ (normalizedRemainder38 (m - 1)).support,
        localRemainderMonomialValue38 m (m - 1) q (toCarrier38 _ u) - chargeQuad38 _ (m - 1) u =
      R (m - 1) := by simp [hR]
  rw [e]
  show ∑ j ∈ Finset.range (m + 1), lowerCoef38 m β δ j * R j = _
  rw [Finset.sum_congr rfl (fun j _ => hupd j), Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range (m + 1)) (m - 1) (fun j => δ * R j)]
  simp only [Finset.mem_range, show m - 1 < m + 1 by omega, ite_true]
  rfl

/-- The Fourier-side tilt density `d exp(δ Σ_n b_n |û(n)|²)` on `H^{m-1}`. -/
def tiltDensityH38 (m : ℕ) (δ d : ℝ) (u : Hm1 m) : ℝ≥0∞ :=
  ENNReal.ofReal d * ENNReal.ofReal (Real.exp (δ * chargeQuad38 _ (m - 1) u))

theorem measurable_tiltDensityH38 (m : ℕ) (δ d : ℝ) : Measurable (tiltDensityH38 m δ d) := by
  unfold tiltDensityH38
  exact measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (continuous_chargeQuad38 (m - 1) (m - 1) le_rfl).measurable)).ennreal_ofReal

/-- **F07.05 (v2 `C:eq:GaussianTilt`), Birkhoff-coordinate form**: `γ'` has density
`d_δ exp(δ Σ_n b_n |z_n|²)` with respect to `γ_m`. -/
theorem gammaM38_tilt (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)) :
    gammaM38 m (lowerCoef38 m β δ) = (gammaM38 m β).withDensity
      (gaussTiltDensity38 (fun n => δ * f07B38 m n) (dDelta38 m β δ)) := by
  obtain ⟨hd0, hd⟩ := hasProd_dDelta38 hm hβ hδ0 hδ
  have h := countableGaussian_tilt38 (fun n => finiteHierarchyRate38 m β n)
    (fun n => finiteHierarchyRate38 m (lowerCoef38 m β δ) n)
    (fun n => rate_lower_pos38 hm hβ hδ n) (fun n => rate_lower_le38 hm hδ0 n)
    (summable_lowerDeficit38 hm hβ) _ hd0 hd
  have hc : (fun n => finiteHierarchyRate38 m β n - finiteHierarchyRate38 m (lowerCoef38 m β δ) n) =
      fun n => δ * f07B38 m n := by
    funext n; rw [f07RateLower38 hm]; ring
  rw [hc] at h
  exact h

/-- Pushforward of a density under a measurable map, when the density factors through it a.e. -/
theorem map_withDensity_ae38 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {gr : X → Y} (hgr : Measurable gr) {F : X → ℝ≥0∞} {G : Y → ℝ≥0∞}
    (hG : Measurable G) (hFG : F =ᵐ[μ] G ∘ gr) :
    (μ.withDensity F).map gr = (μ.map gr).withDensity G := by
  ext A hA
  rw [Measure.map_apply hgr hA, withDensity_apply _ (hgr hA), withDensity_apply _ hA,
    setLIntegral_map hA hG hgr]
  exact lintegral_congr_ae (ae_restrict_of_ae hFG)

/-- **F07.05 (v2 `C:eq:GaussianTilt`) on `H^{m-1}`**: with `γ^F = gammaFM38 m β` and
`γ'^F = gammaFM38 m β'`, `dγ'^F/dγ^F (u) = d_δ exp(δ Σ_n b_n |û(n)|²)`, `Σ b_n |û(n)|²` being
`chargeQuad38 (m-1) (m-1) u` (the sum is finite `γ^F`-a.e.; see `lintegral_tiltDensityH38`). -/
theorem gammaFM38_tilt (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)) :
    gammaFM38 m (lowerCoef38 m β δ) =
      (gammaFM38 m β).withDensity (tiltDensityH38 m δ (dDelta38 m β δ)) := by
  have hβ0 : ∀ i ≤ m, 0 ≤ β i := fun i hi => (hβ i hi).le
  rw [gammaFM38_eq_realization, gammaFM38_eq_realization, gammaM38_tilt hm hβ hδ0 hδ]
  refine map_withDensity_ae38 (measurable_gaussianRealization38 (m := m)) (measurable_tiltDensityH38 m δ _) ?_
  have hq : ∀ n, 0 < finiteHierarchyRate38 m β n := f07RatePos38 hm hβ
  have hc0 : ∀ n, 0 ≤ δ * f07B38 m n := fun n => mul_nonneg hδ0 (f07B38_nonneg m n)
  have hsum : Summable (fun n : ℤ => δ * f07B38 m n / finiteHierarchyRate38 m β n) := by
    refine ((summable_deficit38 hm hβ).mul_left δ).congr fun n => ?_
    ring
  filter_upwards [ae_summable38 hm hβ0 (hβ 0 (by omega)) (hβ m le_rfl),
    ae_sequenceSummable (finiteHierarchyRate38 m β) (fun n => δ * f07B38 m n) hq hc0 hsum]
    with z hz1 hz2
  rw [gaussTiltDensity_eq38 _ hc0 _ z hz2]
  simp only [Function.comp, tiltDensityH38]
  congr 3
  have hcq : chargeQuad38 _ (m - 1) (gaussianRealization38 m z) =
      ∑' n : ℤ, f07B38 m n * ‖z n‖ ^ 2 := by
    unfold chargeQuad38
    refine tsum_congr fun n => ?_
    have := seqRealization_apply38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) z hz1 n
    unfold gaussianRealization38 f07B38
    rw [this]
  rw [hcq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-- On `H^{m-1}` the Fourier quadratic form `Σ_n b_n |û(n)|²` is a genuinely convergent series
(`b_n ≤ C ⟨n⟩^{2(m-1)}`), so `chargeQuad38` is not a totalized junk value. -/
theorem summable_chargeQuad38 (m : ℕ) (u : Hm1 m) :
    Summable (fun n : ℤ => f07B38 m n *
      ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n‖ ^ 2) := by
  have h := (weightedHilbert_hasSum (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u)).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (f07B38_nonneg m n) (sq_nonneg _))
    (fun n => ?_) (h.mul_left (1 + (2 * Real.pi) ^ (2 * (m - 1))))
  have := chargeQuad_weight_le38 (m - 1) (m - 1) le_rfl n
  have hb := f07B38_nonneg m n
  unfold f07B38 at hb ⊢
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  linarith

theorem chargeQuad38_eq_tsum (m : ℕ) (u : Hm1 m) :
    chargeQuad38 _ (m - 1) u = ∑' n : ℤ, f07B38 m n *
      ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n‖ ^ 2 := rfl

theorem chargeQuad38_nonneg (m : ℕ) (u : Hm1 m) : 0 ≤ chargeQuad38 _ (m - 1) u :=
  tsum_nonneg fun n => mul_nonneg (f07B38_nonneg m n) (sq_nonneg _)

/-- **v2 l.808-809**: `∫ exp(δ Σ_n b_n |û(n)|²) dγ^F = d_δ⁻¹ < ∞`; this also verifies that the
density in `C:eq:GaussianTilt` has total mass one. -/
theorem integral_exp_chargeQuad38 (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (hδ0 : 0 ≤ δ)
    (hδ : δ < β (m - 1)) :
    Integrable (fun u : Hm1 m => Real.exp (δ * chargeQuad38 _ (m - 1) u)) (gammaFM38 m β) ∧
      ∫ u, Real.exp (δ * chargeQuad38 _ (m - 1) u) ∂(gammaFM38 m β) = (dDelta38 m β δ)⁻¹ := by
  obtain ⟨hd0, -⟩ := hasProd_dDelta38 hm hβ hδ0 hδ
  set d := dDelta38 m β δ with hd
  have hβ' := lowerCoef_pos38 hβ hδ
  have hprob : IsProbabilityMeasure (gammaFM38 m (lowerCoef38 m β δ)) :=
    isProbabilityMeasure_gammaFM38 hm hβ'
  have hone : ∫⁻ u, tiltDensityH38 m δ d u ∂(gammaFM38 m β) = 1 := by
    have h1 := gammaFM38_tilt hm hβ hδ0 hδ
    have h2 := congrArg (fun μ : Measure (Hm1 m) => μ Set.univ) h1
    simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h2
    exact h2.symm
  have hcont : Continuous (fun u : Hm1 m => Real.exp (δ * chargeQuad38 _ (m - 1) u)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_chargeQuad38 (m - 1) (m - 1) le_rfl))
  have hL : ∫⁻ u, ENNReal.ofReal (Real.exp (δ * chargeQuad38 _ (m - 1) u)) ∂(gammaFM38 m β) =
      ENNReal.ofReal d⁻¹ := by
    have : ∫⁻ u, tiltDensityH38 m δ d u ∂(gammaFM38 m β) =
        ENNReal.ofReal d * ∫⁻ u, ENNReal.ofReal (Real.exp (δ * chargeQuad38 _ (m - 1) u))
          ∂(gammaFM38 m β) := by
      unfold tiltDensityH38
      rw [lintegral_const_mul _ (hcont.measurable.ennreal_ofReal)]
    rw [this] at hone
    rw [ENNReal.ofReal_inv_of_pos hd0]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hone)
  have hfin : Integrable (fun u : Hm1 m => Real.exp (δ * chargeQuad38 _ (m - 1) u))
      (gammaFM38 m β) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le), hL]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
    hcont.aestronglyMeasurable, hL, ENNReal.toReal_ofReal (inv_nonneg.2 hd0.le)]

end Tilt

end NlsGge.Birkhoff

end
