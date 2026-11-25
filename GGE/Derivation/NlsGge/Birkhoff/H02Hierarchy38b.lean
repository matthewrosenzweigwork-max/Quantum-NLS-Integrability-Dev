import NlsGge.Birkhoff.H02Hierarchy38

/-! # H02, part 2: the finite-order remainder `R_m`, the measures `γ_m`, `Z_m`, `μ_m`

v2 `B:eq:Rm`, `B:eq:mumeasures` (l.632-669), conditional on `B : BirkhoffTop38`.

* `R_m(u) = ∑_n (2/π)∫_{g_n(u)} [W_m(2λ) - a_{m,n}] v(λ;u) dλ` (`hierRemainder38`), the series of
  F04 (`spectralRemainder_F04_E02_38`: absolutely summable and nonnegative on `H^{m-1}`).
* `R̄_m z = R_m(Φ⁻¹ z)` on `h^{m-1}` (the support of `γ_m`) and `0` off it (an explicit `γ_m`-null set);
  measurable (limit of measurable partial sums), nonnegative.
* `Z_m = ∫ e^{-R̄_m} dγ_m`, `μ̂_m = Z_m⁻¹ e^{-R̄_m} γ_m`, `μ_m = (Φ⁻¹)_# μ̂_m`; `0 < Z_m ≤ 1`.
* Generic integral estimates for the gap integrals used in the pathwise argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open scoped ENNReal

/-! ### Gap integrals for an arbitrary continuous weight -/

/-- `(2/π) ∫_{g_n(u)} W(2λ) v(λ;u) dλ`. -/
def gapIntW38 (W : ℝ → ℝ) (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
    W (2 * x) * actualGapHeightE02_38 u x

theorem gapIntegral38_eq_gapIntW38 (c : ℕ → ℝ) (u : PhysicalL2) (n : ℤ) :
    gapIntegral38 c u n = gapIntW38 (weight c) u n := rfl

theorem gapRemainderTerm_eq_gapIntW38 (W : ℝ → ℝ) (hW : Continuous W) (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 W u n =
      gapIntW38 W u n - W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have h1 : IntervalIntegrable (fun x => W (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((hW.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => W (2 * Real.pi * (n : ℝ)) * actualGapHeightE02_38 u x)
      volume (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (continuous_const.mul hv).intervalIntegrable _ _
  unfold gapRemainderTermE02_38 gapIntW38 actualGapActionAllE02_38
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  ring

/-- `|(2/π)∫_{g_n} F v| ≤ K I_n(u)` if `|F| ≤ K` on the gap. -/
theorem abs_gap_integral_le38 (F : ℝ → ℝ) (u : PhysicalL2) (n : ℤ) (K : ℝ)
    (hF : ContinuousOn F (Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)))
    (hK : ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n), |F l| ≤ K) :
    |(2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        F x * actualGapHeightE02_38 u x| ≤ K * actualGapActionAllE02_38 u n := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hab := actualGapLower_le_upper38' u n
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hg : IntervalIntegrable (fun x => K * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (continuous_const.mul hv).intervalIntegrable _ _
  have hle := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun x => F x * actualGapHeightE02_38 u x)
    (g := fun x => K * actualGapHeightE02_38 u x)
    (Filter.Eventually.of_forall fun t ht => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (actualGapHeightE02_38_nonneg u t)]
      exact mul_le_mul_of_nonneg_right (hK t ⟨ht.1.le, ht.2⟩) (actualGapHeightE02_38_nonneg u t))
    hg
  rw [Real.norm_eq_abs] at hle
  unfold actualGapActionAllE02_38
  rw [intervalIntegral.integral_const_mul] at hle
  calc 2 / Real.pi * |∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        F x * actualGapHeightE02_38 u x|
      ≤ 2 / Real.pi * (K * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-- **v2 `B:eq:remainderbound`-type estimate.** If `|W(2λ) - W(2πn)| ≤ K` on the gap `g_n(u)`, the
`n`-th summand of `R` is bounded by `K I_n(u)`. -/
theorem abs_gapRemainderTerm_le38 (W : ℝ → ℝ) (hW : Continuous W) (u : PhysicalL2) (n : ℤ)
    (K : ℝ)
    (hK : ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |W (2 * l) - W (2 * Real.pi * (n : ℝ))| ≤ K) :
    |gapRemainderTermE02_38 W u n| ≤ K * actualGapActionAllE02_38 u n :=
  abs_gap_integral_le38 (fun x => W (2 * x) - W (2 * Real.pi * (n : ℝ))) u n K
    ((hW.comp (continuous_const.mul continuous_id)).sub continuous_const).continuousOn hK

/-- Difference of gap integrals for two continuous weights. -/
theorem abs_gapIntW_sub_le38 (W₁ W₂ : ℝ → ℝ) (h₁ : Continuous W₁) (h₂ : Continuous W₂)
    (u : PhysicalL2) (n : ℤ) (K : ℝ)
    (hK : ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |W₁ (2 * l) - W₂ (2 * l)| ≤ K) :
    |gapIntW38 W₁ u n - gapIntW38 W₂ u n| ≤ K * actualGapActionAllE02_38 u n := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have e1 : IntervalIntegrable (fun x => W₁ (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((h₁.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  have e2 : IntervalIntegrable (fun x => W₂ (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((h₂.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  have := abs_gap_integral_le38 (fun x => W₁ (2 * x) - W₂ (2 * x)) u n K
    ((h₁.comp (continuous_const.mul continuous_id)).sub
      (h₂.comp (continuous_const.mul continuous_id))).continuousOn hK
  unfold gapIntW38
  simp_rw [sub_mul] at this
  rw [intervalIntegral.integral_sub e1 e2] at this
  rw [← mul_sub]
  exact this

/-! ### The finite-order remainder and its cleaned version -/

/-- `R_m(u) = ∑_n (2/π)∫_{g_n(u)} [W_m(2λ) - a_{m,n}] v dλ` (v2 `B:eq:Rm`). -/
def hierRemainder38 (c : ℕ → ℝ) (m : ℕ) (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, gapRemainderTermE02_38 (partialWeight c m) u n

theorem continuous_partialWeight38 (c : ℕ → ℝ) (m : ℕ) : Continuous (partialWeight c m) := by
  unfold partialWeight weightTerm
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_id.pow _))

/-- **F04 for the project's hierarchy** (`B:lem:spectral` (i)): for `m ≥ 2` and `u ∈ H^{m-1}`, the
series `R_m(u)` converges absolutely and is nonnegative. -/
theorem hierRemainder38_F04 (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) (u : PhysicalL2)
    (hu : SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (partialWeight c m) u n|) ∧
      0 ≤ hierRemainder38 c m u := by
  have := spectralRemainder_F04_E02_38 m hm (coefficient c)
    (fun j _ => coefficient_pos lower c hlower hbound j) u hu
  rw [← partialWeight_eq_finiteWeightE02_38] at this
  exact this

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- `R̄_m z = R_m(Φ⁻¹ z)` on `h^{m-1}` (carrying `γ_m`), and `0` on the (`γ_m`-null) complement. -/
def hierRbar38 (c : ℕ → ℝ) (m : ℕ) (z : ℤ → ℂ) : ℝ := by
  classical exact if z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) then hierRemainder38 c m (B.cleanΦinv z)
    else 0

theorem hierRbar38_of_mem (c : ℕ → ℝ) (m : ℕ) {z : ℤ → ℂ} (hz : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)) :
    B.hierRbar38 c m z = hierRemainder38 c m (B.cleanΦinv z) := by
  unfold hierRbar38; simp only [hz, ↓reduceIte]

theorem hierRbar38_of_not_mem (c : ℕ → ℝ) (m : ℕ) {z : ℤ → ℂ}
    (hz : z ∉ seqSobolev38 ((m - 1 : ℕ) : ℝ)) : B.hierRbar38 c m z = 0 := by
  unfold hierRbar38; simp only [hz, ↓reduceIte]

theorem sobolev_cleanΦinv_hier38 (m : ℕ) {z : ℤ → ℂ} (hz : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)) :
    SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier (B.cleanΦinv z)) :=
  B.sobolev_cleanΦinv38 (m - 1) z hz

theorem hierRbar38_nonneg (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) (z : ℤ → ℂ) : 0 ≤ B.hierRbar38 c m z := by
  by_cases hz : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)
  · rw [B.hierRbar38_of_mem c m hz]
    exact (hierRemainder38_F04 lower c hlower hbound hm _ (B.sobolev_cleanΦinv_hier38 m hz)).2
  · rw [B.hierRbar38_of_not_mem c m hz]

theorem summable_hierRemainder38 (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) {z : ℤ → ℂ}
    (hz : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => gapRemainderTermE02_38 (partialWeight c m) (B.cleanΦinv z) n) :=
  (hierRemainder38_F04 lower c hlower hbound hm _ (B.sobolev_cleanΦinv_hier38 m hz)).1.of_abs

/-! ### Measurability of `R̄_m` -/

/-- The gap integral as a function on the real `h¹` carrier, for a general weight. -/
def gapFnW38 (W : ℝ → ℝ) (n : ℤ) (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  gapIntW38 W (NlsGge.Schur.physicalH1ComplexCarrierToL2Actual22 (reflH1_38 x)) n

theorem continuous_gapFnW38 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (gapFnW38 W n) :=
  (actualGapAction_continuous_E02_38 n W hW).comp continuous_reflH1_38

theorem gapIntW38_eq_gapFnW38 (W : ℝ → ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    gapIntW38 W u n = gapFnW38 W n (carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 u)
        ((fourierSeq38_mem_iff _ u).2 (by simpa using hu))) := by
  unfold gapFnW38
  rw [physicalH1_reflH1_fourierSeq38 u hu]

/-- The `n`-th summand of `R_m(Φ⁻¹ z)` written in the coordinates `z` (measurable in `z`). -/
def summandZW38 (W : ℝ → ℝ) (n : ℤ) (z : ℤ → ℂ) : ℝ :=
  gapFnW38 W n (B.cleanTinvC 1 z) - W (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2

theorem gapIntW38_cleanΦinv38 (W : ℝ → ℝ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (n : ℤ) : gapIntW38 W (B.cleanΦinv z) n = gapFnW38 W n (B.cleanTinvC 1 z) := by
  have hs : SobolevSquareSummable 1 (physicalFourier (B.cleanΦinv z)) := by
    simpa using B.sobolev_cleanΦinv38 1 z hz
  rw [gapIntW38_eq_gapFnW38 W _ hs n, B.cleanTinvC_of_mem 1 z hz]
  congr 1
  exact carrierExt38 (by
    show fourierSeq38 (B.cleanΦinv z) = B.Tinv z
    exact B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz))

theorem summandZW38_eq (W : ℝ → ℝ) (hW : Continuous W) (z : ℤ → ℂ)
    (hz : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    B.summandZW38 W n z = gapRemainderTermE02_38 W (B.cleanΦinv z) n := by
  rw [gapRemainderTerm_eq_gapIntW38 W hW, B.gapIntW38_cleanΦinv38 W z hz n,
    B.action_cleanΦinv38 z hz n]
  rfl

theorem measurable_summandZW38 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Measurable (B.summandZW38 W n) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((1 : ℕ) : ℝ)) := ⟨rfl⟩
  unfold summandZW38
  exact ((continuous_gapFnW38 W hW n).measurable.comp (B.measurable_cleanTinvC 1)).sub
    (((measurable_pi_apply n).norm.pow_const 2).const_mul _)

/-- **Explicit measurability of `R̄_m`** (everywhere limit of measurable partial sums). -/
theorem measurable_hierRbar38 (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) : Measurable (B.hierRbar38 c m) := by
  classical
  have hW := continuous_partialWeight38 c m
  have hΩ := measurableSet_seqSobolev38 ((m - 1 : ℕ) : ℝ)
  have h1m : ∀ {z : ℤ → ℂ}, z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) →
      z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun hz =>
    seqSobolev38_mono (by exact_mod_cast (by omega : 1 ≤ m - 1)) hz
  refine measurable_of_tendsto_metrizable (f := fun M : ℕ => fun z : ℤ → ℂ =>
    if z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) then
      ∑ n ∈ stdExh38 M, B.summandZW38 (partialWeight c m) n z else 0) (fun M => ?_) ?_
  · exact Measurable.ite hΩ (Finset.measurable_sum _
      (fun n _ => B.measurable_summandZW38 _ hW n)) measurable_const
  · rw [tendsto_pi_nhds]
    intro z
    by_cases hz : z ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ)
    · simp only [hz, ↓reduceIte]
      rw [B.hierRbar38_of_mem c m hz]
      have hs := B.summable_hierRemainder38 lower c hlower hbound hm hz
      have hs' : Summable (fun n : ℤ => B.summandZW38 (partialWeight c m) n z) :=
        hs.congr (fun n => (B.summandZW38_eq _ hW z (h1m hz) n).symm)
      have h : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, B.summandZW38 (partialWeight c m) n z) atTop
          (𝓝 (∑' n : ℤ, B.summandZW38 (partialWeight c m) n z)) := hs'.hasSum
      have e : ∑' n : ℤ, B.summandZW38 (partialWeight c m) n z =
          hierRemainder38 c m (B.cleanΦinv z) :=
        tsum_congr (fun n => B.summandZW38_eq _ hW z (h1m hz) n)
      rw [← e]
      exact h.comp isExhaustion_stdExh38.tendsto_atTop
    · simp only [hz, ↓reduceIte]
      rw [B.hierRbar38_of_not_mem c m hz]
      exact tendsto_const_nhds

/-! ### `γ_m`, `Z_m`, `μ̂_m`, `μ_m` (v2 `B:eq:mumeasures`) -/

/-- `Z_m = ∫ e^{-R_m(Φ⁻¹ z)} dγ_m(z)`. -/
def hierZ38 (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∫ z, Real.exp (-(B.hierRbar38 c m z)) ∂(NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c))

/-- `μ̂_m = Z_m⁻¹ e^{-R_m(Φ⁻¹ z)} γ_m`. -/
def hierMuHat38 (c : ℕ → ℝ) (m : ℕ) : Measure (ℤ → ℂ) :=
  (NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c)).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-(B.hierRbar38 c m z)) / B.hierZ38 c m))

/-- `μ_m = (Φ⁻¹)_# μ̂_m`. -/
def hierMu38 (c : ℕ → ℝ) (m : ℕ) : Measure PhysicalL2 := (B.hierMuHat38 c m).map B.cleanΦinv

theorem hierZ38_pos_le_one (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    0 < B.hierZ38 c m ∧ B.hierZ38 c m ≤ 1 :=
  exp_neg_integral_pos_le_one38 (NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c))
    (B.hierRbar38 c m) (B.measurable_hierRbar38 lower c hlower hbound hm)
    (B.hierRbar38_nonneg lower c hlower hbound hm)

theorem isProbabilityMeasure_hierMuHat38 (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure (B.hierMuHat38 c m) :=
  isProbabilityMeasure_withDensity_exp_neg38
    (NlsGge.HierarchyRiccati.Core.gammaM38 m (coefficient c)) (B.hierRbar38 c m)
    (B.measurable_hierRbar38 lower c hlower hbound hm) (B.hierRbar38_nonneg lower c hlower hbound hm)

theorem isProbabilityMeasure_hierMu38 (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure (B.hierMu38 c m) := by
  have := B.isProbabilityMeasure_hierMuHat38 lower c hlower hbound hm
  refine ⟨?_⟩
  unfold hierMu38
  rw [Measure.map_apply B.measurable_cleanΦinv MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

end BirkhoffTop38

end NlsGge.Birkhoff
end
