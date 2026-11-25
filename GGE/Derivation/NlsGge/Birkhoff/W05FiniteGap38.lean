import NlsGge.Birkhoff.S03Measure38c
import NlsGge.Birkhoff.W04WeightedSmoothing38c

/-! # W05 (`D:cor:Rcontinuous`), part 1: the domain `𝓕⁻¹ E_s` and the continuous inclusion into `h¹`

Source: `paper/v2.tex` l.1500-1520. Conditional on `B : BirkhoffInput38` and
`O : OneSmoothingInput38 B` where `B` appears.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights Filter Topology
open scoped ENNReal Real

section Domain

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem coef_lower38 (c : BoundedCoefficients lower upper) : 0 < lower := c.property.1
theorem coef_bound38 (c : BoundedCoefficients lower upper) : ∀ j : ℕ, lower ≤ c.val j :=
  fun j => (c.property.2.2 j).1
theorem coef_upper38 (c : BoundedCoefficients lower upper) : ∀ j : ℕ, c.val j ≤ upper :=
  fun j => (c.property.2.2 j).2

theorem sourceRate_eq_fullWeightRate38 (n : ℤ) : sourceRate c n = fullWeightRate c.val n := rfl

/-- `𝓕⁻¹` on `E_s`: the physical field whose reflected Fourier sequence is `x ∈ E_s`. -/
def physOfE38 (x : ECarrier38 c s) : PhysicalL2 :=
  physInv38 (eCoe38 c s x) (seqE38_subset_seqSobolev38 c s 0 (eCoe38_mem c s x))

theorem fourierSeq38_physOfE38 (x : ECarrier38 c s) :
    fourierSeq38 (physOfE38 c s x) = eCoe38 c s x :=
  fourierSeq38_physInv38 _ _

theorem sobolev_physOfE38 (r : ℝ) (x : ECarrier38 c s) :
    SobolevSquareSummable r (physicalFourier (physOfE38 c s x)) :=
  (fourierSeq38_mem_iff r _).1 (by
    rw [fourierSeq38_physOfE38]; exact seqE38_subset_seqSobolev38 c s r (eCoe38_mem c s x))

/-- The set `𝓕⁻¹ E_s` of physical fields. -/
def FinvE38 : Type := {u : PhysicalL2 // fourierSeq38 u ∈ seqE38 c s}

/-- The `E_s`-coordinate of a field of `𝓕⁻¹ E_s`. -/
def toE38 (u : FinvE38 c s) : ECarrier38 c s := eMk38 c s (fourierSeq38 u.1) u.2

theorem eCoe38_toE38 (u : FinvE38 c s) : eCoe38 c s (toE38 c s u) = fourierSeq38 u.1 := rfl

theorem physOfE38_toE38 (u : FinvE38 c s) : physOfE38 c s (toE38 c s u) = u.1 := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physOfE38]; rfl

/-- The topology of `𝓕⁻¹ E_s`: transported from `E_s` by `𝓕` (v2: "`𝓕⁻¹ E_s`"). -/
def topFinvE38 : TopologicalSpace (FinvE38 c s) :=
  TopologicalSpace.induced (toE38 c s) inferInstance

/-- The continuous inclusion `E_s → h¹` as a map of carriers. -/
def iotaE38 (x : ECarrier38 c s) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ) (eCoe38 c s x) (seqE38_subset_seqSobolev38 c s _ (eCoe38_mem c s x))

theorem iotaE38_sub (x y : ECarrier38 c s) : iotaE38 c s (x - y) = iotaE38 c s x - iotaE38 c s y :=
  carrierExt38 rfl

theorem norm_sq_iotaE38_le (y : ECarrier38 c s) :
    ‖iotaE38 c s y‖ ^ 2 ≤
      sourceSobolevBound lower upper ((1 : ℕ) : ℝ) s c.property.1 * ‖y‖ ^ 2 := by
  have h1 := (carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (iotaE38 c s y))
  have h2 := (mem_seqE38_iff c s _).1 (eCoe38_mem c s y)
  rw [norm_sq_eCarrier38, ← h1.tsum_eq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) h1.summable (h2.mul_left _)
  show sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖eCoe38 c s y n‖ ^ 2 ≤ _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (sourceSobolevBound_dominates lower upper _ s c.property.1 c n) (sq_nonneg _)

theorem continuous_iotaE38 : Continuous (iotaE38 c s) := by
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨Real.sqrt (sourceSobolevBound lower upper ((1 : ℕ) : ℝ) s c.property.1),
      Real.sqrt_nonneg _⟩) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, ← iotaE38_sub]
  have h := norm_sq_iotaE38_le c s (x - y)
  show ‖iotaE38 c s (x - y)‖ ≤ Real.sqrt _ * ‖x - y‖
  rw [← Real.sqrt_sq (norm_nonneg (iotaE38 c s (x - y))), ← Real.sqrt_sq (norm_nonneg (x - y)),
    ← Real.sqrt_mul (sourceSobolevBound_nonneg _ _ _ _ _)]
  exact Real.sqrt_le_sqrt h

theorem hasSum_norm_sq_eCarrier38 (y : ECarrier38 c s) :
    HasSum (fun n : ℤ => fullModeWeight c s n * ‖eCoe38 c s y n‖ ^ 2) (‖y‖ ^ 2) :=
  weightedHilbert_hasSum (fullModeWeight c s) y

/-- Coordinate norm bound `‖y_n‖ √(a_n ⟨n⟩^{-2s}) ≤ ‖y‖` on `E_s`. -/
theorem norm_eCoe_mul_sqrt_le38 (y : ECarrier38 c s) (n : ℤ) :
    ‖eCoe38 c s y n‖ * Real.sqrt (fullModeWeight c s n) ≤ ‖y‖ := by
  have hw := fullModeWeight_pos c s n
  have h1 : fullModeWeight c s n * ‖eCoe38 c s y n‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    exact le_hasSum (hasSum_norm_sq_eCarrier38 c s y) n
      (fun j _ => mul_nonneg (fullModeWeight_pos c s j).le (sq_nonneg _))
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 ?_
  rw [mul_pow, Real.sq_sqrt hw.le]
  linarith

theorem eCoe38_sub (x y : ECarrier38 c s) (n : ℤ) :
    eCoe38 c s (x - y) n = eCoe38 c s x n - eCoe38 c s y n := rfl

theorem continuous_eCoe_apply38 (n : ℤ) : Continuous (fun x : ECarrier38 c s => eCoe38 c s x n) := by
  have hw := fullModeWeight_pos c s n
  have hs : 0 < Real.sqrt (fullModeWeight c s n) := Real.sqrt_pos.2 hw
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨(Real.sqrt (fullModeWeight c s n))⁻¹, by positivity⟩) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have h := norm_eCoe_mul_sqrt_le38 c s (x - y) n
  rw [eCoe38_sub] at h
  show ‖eCoe38 c s x n - eCoe38 c s y n‖ ≤ (Real.sqrt (fullModeWeight c s n))⁻¹ * ‖x - y‖
  rw [inv_mul_eq_div, le_div_iff₀ hs]
  exact h

end Domain


/-! ## W05.01-W05.02: Birkhoff coordinates of `𝓕⁻¹ x`, domination and uniformly small tails -/

section Weighted

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem norm_physicalSobolevL2_physOfE38 (x : ECarrier38 c s)
    (h : SobolevSquareSummable 1 (physicalFourier (physOfE38 c s x))) :
    ‖physicalSobolevL2 1 (physOfE38 c s x) h‖ = ‖iotaE38 c s x‖ := by
  rw [norm_physicalSobolevL2_eq_carrier38]
  have hs : fourierSeq38 (physOfE38 c s x) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
    rw [seqSobolev38_natCast_one]; exact (fourierSeq38_mem_iff 1 _).2 h
  rw [norm_carrierMk_congr38 (Nat.cast_one (R := ℝ)).symm _ _ hs]
  have e : carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 (physOfE38 c s x)) hs = iotaE38 c s x := by
    apply carrierExt38
    rw [carrierCoe38_mk]
    unfold iotaE38
    rw [carrierCoe38_mk]
    exact fourierSeq38_physOfE38 c s x
  rw [e]

/-- `⟨n⟩ ≥ ⟨N⟩` when `|n| > N`. -/
theorem japaneseBracket_ge_of_not_mem_Icc38 (N : ℕ) (n : ℤ)
    (hn : n ∉ Finset.Icc (-(N : ℤ)) N) : japaneseBracket (N : ℤ) ≤ japaneseBracket n := by
  unfold japaneseBracket
  refine Real.sqrt_le_sqrt ?_
  have h : (N : ℤ) < |n| := by
    rw [Finset.mem_Icc] at hn
    rcases le_or_gt 0 n with h0 | h0
    · rw [abs_of_nonneg h0]; omega
    · rw [abs_of_neg h0]; omega
  have h2 : ((N : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have : (N : ℤ) ^ 2 ≤ n ^ 2 := by
      rw [← sq_abs n]; exact pow_le_pow_left₀ (by positivity) h.le 2
    exact_mod_cast this
  linarith

/-- The tail comparison of v2's proof of `D:cor:Rcontinuous`: for `⟨n⟩ ≥ t > 0`,
`a_n ⟨n⟩^{-3/2} |z_n|² ≤ t^{2s-3/2} · a_n ⟨n⟩^{-2s} |z_n|²` (uses `2s ≤ 3/2`). -/
theorem tailWeight_mul_le38 (hs : s ≤ 3 / 4) (t : ℝ) (ht : 0 < t) (n : ℤ)
    (hn : t ≤ japaneseBracket n) (w : ℂ) :
    tailWeight38 c.val n * ‖w‖ ^ 2 ≤ t ^ (2 * s - 3 / 2) * (fullModeWeight c s n * ‖w‖ ^ 2) := by
  have hj := japaneseBracket_pos n
  have h1 : japaneseBracket n ^ (-(3 / 2) : ℝ) =
      japaneseBracket n ^ (-2 * s) * japaneseBracket n ^ (2 * s - 3 / 2) := by
    rw [← Real.rpow_add hj]; congr 1; ring
  have h2 : japaneseBracket n ^ (2 * s - 3 / 2) ≤ t ^ (2 * s - 3 / 2) :=
    Real.rpow_le_rpow_of_nonpos ht hn (by linarith)
  have h3 : tailWeight38 c.val n = sourceRate c n * japaneseBracket n ^ (-2 * s) *
      japaneseBracket n ^ (2 * s - 3 / 2) := by
    unfold tailWeight38
    rw [h1, ← mul_assoc]; rfl
  rw [h3]
  unfold fullModeWeight
  have hsq : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hr := (sourceRate_pos c n).le
  have hp : 0 ≤ japaneseBracket n ^ (-2 * s) := (Real.rpow_pos_of_pos hj _).le
  calc sourceRate c n * japaneseBracket n ^ (-2 * s) * japaneseBracket n ^ (2 * s - 3 / 2) * ‖w‖ ^ 2
      = (japaneseBracket n ^ (2 * s - 3 / 2)) *
        (sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s) * ‖w‖ ^ 2) := by
        simp only [Real.rpow_eq_pow]; ring
    _ ≤ t ^ (2 * s - 3 / 2) *
        (sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s) * ‖w‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right h2 ?_
        exact mul_nonneg (mul_nonneg hr hp) hsq

theorem tendsto_japaneseBracket_rpow38 (e : ℝ) (he : e < 0) :
    Tendsto (fun N : ℕ => japaneseBracket (N : ℤ) ^ e) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => japaneseBracket (N : ℤ)) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    unfold japaneseBracket
    refine Real.le_sqrt_of_sq_le ?_
    push_cast; nlinarith
  have h2 : Tendsto (fun x : ℝ => x ^ (-(-e))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have h3 : Tendsto (fun x : ℝ => x ^ e) atTop (𝓝 0) := by simpa using h2
  exact h3.comp h1

end Weighted


/-! ## W05.04: the finite-gap approximation `Φ⁻¹(P_M Φ u)` converges in `𝓕⁻¹ E_s` -/

section Approx

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem finiteSupport_mem_seqE38 (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) :
    z ∈ seqE38 c s := by
  rw [mem_seqE38_iff]
  refine summable_of_ne_finset_zero (s := hz.toFinset) (fun n hn => ?_)
  have h : ¬ z n ≠ 0 := fun h => hn (hz.mem_toFinset.2 h)
  rw [not_not] at h
  simp [h]

theorem norm_sq_projE_sub38 (z : ℤ → ℂ) (hz : z ∈ seqE38 c s) (Λ : Finset ℤ) :
    ‖eMk38 c s (projFin38 Λ z) (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 Λ z)) -
        eMk38 c s z hz‖ ^ 2 =
      ‖eMk38 c s z hz‖ ^ 2 - ∑ n ∈ Λ, fullModeWeight c s n * ‖z n‖ ^ 2 := by
  set xN := eMk38 c s (projFin38 Λ z)
    (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 Λ z)) with hxN
  set x := eMk38 c s z hz with hx
  have h1 := hasSum_norm_sq_eCarrier38 c s (xN - x)
  have h2 := hasSum_norm_sq_eCarrier38 c s x
  have h3 : HasSum (fun n : ℤ => if n ∈ Λ then fullModeWeight c s n * ‖z n‖ ^ 2 else 0)
      (∑ n ∈ Λ, fullModeWeight c s n * ‖z n‖ ^ 2) := by
    have h : HasSum (fun n : ℤ => if n ∈ Λ then fullModeWeight c s n * ‖z n‖ ^ 2 else 0)
        (∑ n ∈ Λ, if n ∈ Λ then fullModeWeight c s n * ‖z n‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    have e : (∑ n ∈ Λ, if n ∈ Λ then fullModeWeight c s n * ‖z n‖ ^ 2 else 0) =
        ∑ n ∈ Λ, fullModeWeight c s n * ‖z n‖ ^ 2 :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rwa [e] at h
  have h4 := h2.sub h3
  have e : ∀ n : ℤ, fullModeWeight c s n * ‖eCoe38 c s (xN - x) n‖ ^ 2 =
      fullModeWeight c s n * ‖eCoe38 c s x n‖ ^ 2 -
        (if n ∈ Λ then fullModeWeight c s n * ‖z n‖ ^ 2 else 0) := by
    intro n
    by_cases hn : n ∈ Λ
    · have : eCoe38 c s (xN - x) n = 0 := by
        show projFin38 Λ z n - z n = 0
        rw [projFin38_apply_of_mem hn]; simp
      rw [this]; simp only [hn, ↓reduceIte]
      show _ = fullModeWeight c s n * ‖z n‖ ^ 2 - _
      simp
    · have : eCoe38 c s (xN - x) n = - z n := by
        show projFin38 Λ z n - z n = - z n
        rw [projFin38_apply_of_not_mem hn]; simp
      rw [this, norm_neg]; simp only [hn, ↓reduceIte]
      show _ = fullModeWeight c s n * ‖z n‖ ^ 2 - 0
      simp
  simp_rw [e] at h1
  exact h1.unique h4

/-- `P_Λ z → z` in `E_s` along every exhaustion (the `E_s` analogue of `tendsto_carrier_proj38`). -/
theorem tendsto_eMk_proj38 (z : ℤ → ℂ) (hz : z ∈ seqE38 c s) {Λ : ℕ → Finset ℤ}
    (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => eMk38 c s (projFin38 (Λ N) z)
      (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 (Λ N) z))) atTop
      (𝓝 (eMk38 c s z hz)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := hasSum_norm_sq_eCarrier38 c s (eMk38 c s z hz)
  have hF : Tendsto (fun F : Finset ℤ => ∑ n ∈ F, fullModeWeight c s n *
      ‖eCoe38 c s (eMk38 c s z hz) n‖ ^ 2) atTop (𝓝 (‖eMk38 c s z hz‖ ^ 2)) := h2
  have h5 := hF.comp hΛ.tendsto_atTop
  have h6 : Tendsto (fun N : ℕ => ‖eMk38 c s z hz‖ ^ 2 -
      ∑ n ∈ Λ N, fullModeWeight c s n * ‖z n‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ‖eMk38 c s z hz‖ ^ 2)).sub h5
    simpa using this
  have h7 : Tendsto (fun N : ℕ => ‖eMk38 c s (projFin38 (Λ N) z)
      (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 (Λ N) z)) -
        eMk38 c s z hz‖ ^ 2) atTop (𝓝 0) := by
    refine h6.congr (fun N => ?_)
    rw [norm_sq_projE_sub38 c s z hz (Λ N)]
  have h8 := (Real.continuous_sqrt.tendsto 0).comp h7
  simp only [Real.sqrt_zero, Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h8
  exact h8

theorem isExhaustion_Icc38 : IsExhaustion38 (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) :=
  ⟨fun a b hab => Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab),
    fun n => ⟨n.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩

end Approx

/-! ## W05.05: the spectral energy `E_W(u)` and its energy identity -/

section Energy

variable {lower upper : ℝ}

/-- `E_W(u) = (2/π) ∫_ℝ W(2λ) v(λ;u) dλ` as a nonnegative extended real (v2 `A:eq:finiteenergy`,
read for every `u`; the integrand is nonnegative, so the lower integral is the Lebesgue integral and
`E_W(u) < ∞` is exactly integrability). -/
def spectralEnergyW38 (c : ℕ → ℝ) (u : PhysicalL2) : ℝ≥0∞ :=
  ENNReal.ofReal (2 / Real.pi) *
    ∫⁻ l : ℝ, ENNReal.ofReal (weight c (2 * l) * actualGapHeightE02_38 u l)

theorem weight_pos38 (c : BoundedCoefficients lower upper) (r : ℝ) : 0 < weight c.val r :=
  NlsGge.Weights.weight_pos lower upper c.val (coef_lower38 c) (coef_bound38 c) (coef_upper38 c) r

theorem gapIntegral38_nonneg (c : BoundedCoefficients lower upper) (u : PhysicalL2) (n : ℤ) :
    0 ≤ gapIntegral38 c.val u n := by
  unfold gapIntegral38
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg
    (actualGapLower_le_upper38' u n) (fun x _ => ?_))
  exact mul_nonneg (weight_pos38 c _).le (actualGapHeightE02_38_nonneg u x)

/-- **The gap decomposition of the spectral energy:** `E_W(u) = ∑_n (2/π) ∫_{g_n} W(2λ) v dλ`,
a sum of nonnegative terms in `[0,∞]` (`v` vanishes off the pairwise disjoint open gaps). -/
theorem spectralEnergyW_eq_tsum38 (c : BoundedCoefficients lower upper) (u : PhysicalL2) :
    spectralEnergyW38 c.val u = ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 c.val u n) := by
  have hW := weight_continuous38 (coef_lower38 c) (coef_bound38 c) (coef_upper38 c)
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  set f : ℝ → ℝ := fun l => weight c.val (2 * l) * actualGapHeightE02_38 u l with hf
  have hfc : Continuous f := (hW.comp (continuous_const.mul continuous_id)).mul hv
  have hf0 : ∀ l, 0 ≤ f l := fun l =>
    mul_nonneg (weight_pos38 c _).le (actualGapHeightE02_38_nonneg u l)
  set G : ℤ → Set ℝ := fun n => Set.Ioo (actualGapLowerAllE02_38 u n)
    (actualGapUpperAllE02_38 u n) with hG
  have hlev : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
    intro n x hx
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hx
    exact hx
  have hdisj : Pairwise (Function.onFun Disjoint G) := by
    intro n m hnm
    refine Set.disjoint_left.2 (fun l hn hm => hnm ?_)
    have h1 := hlev n l ⟨hn.1.le, hn.2.le⟩
    have h2 := hlev m l ⟨hm.1.le, hm.2.le⟩
    have : (n : ℝ) = m := mul_right_cancel₀ Real.pi_ne_zero (h1.symm.trans h2)
    exact_mod_cast this
  have hsupp : (fun l => ENNReal.ofReal (f l)).support ⊆ ⋃ n, G n := by
    intro l hl
    have hne : f l ≠ 0 := by
      intro h0; apply hl; simp [h0]
    have hv0 : actualGapHeightE02_38 u l ≠ 0 := fun h0 => hne (by simp [hf, h0])
    obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u l hv0
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  have h1 : ∫⁻ l, ENNReal.ofReal (f l) = ∑' n, ∫⁻ l in G n, ENNReal.ofReal (f l) := by
    rw [← setLIntegral_eq_of_support_subset hsupp,
      lintegral_iUnion (fun n => measurableSet_Ioo) hdisj]
  have h2 : ∀ n, ENNReal.ofReal (2 / Real.pi) * ∫⁻ l in G n, ENNReal.ofReal (f l) =
      ENNReal.ofReal (gapIntegral38 c.val u n) := by
    intro n
    have hab := actualGapLower_le_upper38' u n
    have hint : Integrable f (volume.restrict (G n)) :=
      (hfc.continuousOn.integrableOn_Icc (a := actualGapLowerAllE02_38 u n)
        (b := actualGapUpperAllE02_38 u n)).mono_set Set.Ioo_subset_Icc_self
    have h3 : ∫⁻ l in G n, ENNReal.ofReal (f l) = ENNReal.ofReal (∫ l in G n, f l) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)).symm
    have h4 : ∫ l in G n, f l = ∫ l in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        f l := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    rw [h3, h4, ← ENNReal.ofReal_mul (by positivity)]
    rfl
  unfold spectralEnergyW38
  show ENNReal.ofReal (2 / Real.pi) * ∫⁻ l, ENNReal.ofReal (f l) = _
  rw [h1, ← ENNReal.tsum_mul_left]
  exact tsum_congr h2

theorem gapIntegral38_eq_remainderSummand_add (c : BoundedCoefficients lower upper) (u : PhysicalL2)
    (n : ℤ) : gapIntegral38 c.val u n =
      remainderSummand38 c.val u n + fullWeightRate c.val n * actualGapActionAllE02_38 u n := by
  unfold remainderSummand38; ring

end Energy

namespace BirkhoffInput38

open BirkhoffTop38

variable {lower upper : ℝ} (B : BirkhoffInput38)
  (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The Birkhoff coordinates of `𝓕⁻¹ x` are `T x`: `Φ(𝓕⁻¹ x) = T x`. -/
theorem Φ_physOfE38 (x : ECarrier38 c s) : B.Φ (physOfE38 c s x) = B.T (eCoe38 c s x) := by
  rw [Φ_def, fourierSeq38_physOfE38]

/-- `Φ_n(u) ∈ E_s` for `u ∈ 𝓕⁻¹ E_s` (W04: `T` preserves `E_s`). -/
theorem Φ_mem_E38 (O : OneSmoothingInput38 B) (x : ECarrier38 c s) : B.Φ (physOfE38 c s x) ∈ seqE38 c s := by
  rw [B.Φ_physOfE38 c s x]; exact B.T_mem_E38 O c s _ (eCoe38_mem c s x)

/-- `I_n(𝓕⁻¹ x) = |(T x)_n|²` (field `action`). -/
theorem action_physOfE38 (x : ECarrier38 c s) (n : ℤ) :
    actualGapActionAllE02_38 (physOfE38 c s x) n = ‖B.T (eCoe38 c s x) n‖ ^ 2 := by
  rw [← B.sq_norm_Φ_eq_action _ (sobolev_physOfE38 c s 1 x) n, B.Φ_physOfE38]

/-- The coordinates `Φ`, as a carrier map `E_s → E_s` (W04 homeomorphism). -/
theorem eCoe_weightedHomeoE38 (O : OneSmoothingInput38 B) (x : ECarrier38 c s) :
    eCoe38 c s (B.weightedHomeoE38 O c s x) = B.T (eCoe38 c s x) :=
  B.weightedHomeoE38_apply O c s x

/-- **W05.01 (domination, physical form).** For every `Bd ≥ 1` there is `C_B` such that every
`u ∈ H¹` with `‖u‖_{H¹} ≤ Bd` has all summands of `A:eq:remainder` dominated by
`C_B a_n ⟨n⟩^{-3/2} |Φ_n(u)|²` (v2 `A:eq:remainderbound`). -/
theorem remainderSummand_dominated_phys38 (Bd : ℝ) (hBd : 1 ≤ Bd) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ u : PhysicalL2, ∀ hu : SobolevSquareSummable 1 (physicalFourier u),
      ‖physicalSobolevL2 1 u hu‖ ≤ Bd → ∀ n : ℤ,
      |remainderSummand38 c.val u n| ≤ CB * (tailWeight38 c.val n * ‖B.Φ u n‖ ^ 2) := by
  obtain ⟨CB, hCB, hdom⟩ := B.remainderSummand_dominated38 lower upper c.val (coef_lower38 c)
    (coef_bound38 c) (coef_upper38 c) Bd hBd
  refine ⟨CB, hCB, fun u hu hn n => ?_⟩
  have hw : B.Φ u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    B.Φ_mem_seqSobolev38 1 u (by rw [Nat.cast_one]; exact hu)
  have e : B.cleanΦinv (B.Φ u) = u := by
    rw [B.cleanΦinv_of_mem _ (B.Φ_mem_zero u), B.Φinv_Φ]
  have key : ∀ v : PhysicalL2, v = u → ∀ h : SobolevSquareSummable 1 (physicalFourier v),
      ‖physicalSobolevL2 1 v h‖ ≤ Bd := by
    rintro v rfl h; exact hn
  have := hdom (B.Φ u) hw (fun h => key _ e h) n
  rwa [e] at this

theorem continuous_gapIntegral_physOfE38 (n : ℤ) :
    Continuous (fun x : ECarrier38 c s => gapIntegral38 c.val (physOfE38 c s x) n) := by
  have hW := weight_continuous38 (coef_lower38 c) (coef_bound38 c) (coef_upper38 c)
  have e : (fun x : ECarrier38 c s => gapIntegral38 c.val (physOfE38 c s x) n) =
      fun x => gapFn38 c.val n (iotaE38 c s x) := by
    funext x
    rw [gapIntegral38_eq_gapFn38 c.val _ (sobolev_physOfE38 c s 1 x) n]
    congr 1
    apply carrierExt38
    rw [carrierCoe38_mk]
    unfold iotaE38
    rw [carrierCoe38_mk]
    exact fourierSeq38_physOfE38 c s x
  rw [e]
  exact (continuous_gapFn38 c.val hW n).comp (continuous_iotaE38 c s)

theorem continuous_remainderSummand_physOfE38 (O : OneSmoothingInput38 B) (n : ℤ) :
    Continuous (fun x : ECarrier38 c s => remainderSummand38 c.val (physOfE38 c s x) n) := by
  have h1 := continuous_gapIntegral_physOfE38 c s n
  have h2 : Continuous (fun x : ECarrier38 c s => ‖B.T (eCoe38 c s x) n‖ ^ 2) := by
    have : (fun x : ECarrier38 c s => ‖B.T (eCoe38 c s x) n‖ ^ 2) =
        fun x => ‖eCoe38 c s (B.weightedHomeoE38 O c s x) n‖ ^ 2 := by
      funext x; rw [B.eCoe_weightedHomeoE38 c s O x]
    rw [this]
    exact ((continuous_eCoe_apply38 c s n).comp (B.weightedHomeoE38 O c s).continuous).norm.pow 2
  unfold remainderSummand38
  simp_rw [B.action_physOfE38 c s]
  exact h1.sub (continuous_const.mul h2)

/-- **W05.02 (summability and uniformly small tails).** Let `s ≤ 3/4` (v2: `2s < 3/2`) and
`Bd ≥ 1`. There is `C_B` such that for every `u = 𝓕⁻¹ x ∈ 𝓕⁻¹ E_s` with `‖u‖_{H¹} ≤ Bd` the series
`A:eq:remainder` is (absolutely) summable and its tail outside `[-N,N]` is at most
`C_B ⟨N⟩^{2s-3/2} ‖Φ u‖²_{E_s}`. -/
theorem remainder_summable_tail38 (O : OneSmoothingInput38 B) (hs : s ≤ 3 / 4) (Bd : ℝ)
    (hBd : 1 ≤ Bd) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ x : ECarrier38 c s, ‖iotaE38 c s x‖ ≤ Bd →
      Summable (fun n : ℤ => remainderSummand38 c.val (physOfE38 c s x) n) ∧
      ∀ N : ℕ, ‖∑' n : ℤ, (↑(Finset.Icc (-(N : ℤ)) N) : Set ℤ)ᶜ.indicator
          (fun n => remainderSummand38 c.val (physOfE38 c s x) n) n‖ ≤
        CB * (japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) * ‖B.weightedHomeoE38 O c s x‖ ^ 2) := by
  obtain ⟨CB, hCB, hdom⟩ := B.remainderSummand_dominated_phys38 c Bd hBd
  refine ⟨CB, hCB, fun x hx => ?_⟩
  set zx := B.weightedHomeoE38 O c s x with hzx
  have hsob := sobolev_physOfE38 c s 1 x
  have hn : ‖physicalSobolevL2 1 (physOfE38 c s x) hsob‖ ≤ Bd := by
    rw [norm_physicalSobolevL2_physOfE38]; exact hx
  have hf : ∀ n, |remainderSummand38 c.val (physOfE38 c s x) n| ≤
      CB * (tailWeight38 c.val n * ‖eCoe38 c s zx n‖ ^ 2) := by
    intro n
    have := hdom (physOfE38 c s x) hsob hn n
    rwa [B.Φ_physOfE38 c s x, ← B.eCoe_weightedHomeoE38 c s O x] at this
  have hsum := hasSum_norm_sq_eCarrier38 c s zx
  have hpt : ∀ (t : ℝ), 0 < t → ∀ n : ℤ, t ≤ japaneseBracket n →
      |remainderSummand38 c.val (physOfE38 c s x) n| ≤
        CB * (t ^ (2 * s - 3 / 2) * (fullModeWeight c s n * ‖eCoe38 c s zx n‖ ^ 2)) := by
    intro t ht n htn
    exact (hf n).trans (mul_le_mul_of_nonneg_left (tailWeight_mul_le38 c s hs t ht n htn _) hCB.le)
  refine ⟨?_, fun N => ?_⟩
  · refine Summable.of_norm_bounded ((hsum.summable.mul_left (1 ^ (2 * s - 3 / 2))).mul_left CB)
      (fun n => ?_)
    rw [Real.norm_eq_abs]
    exact hpt 1 one_pos n (japaneseBracket_one_le n)
  · have hN := japaneseBracket_pos (N : ℤ)
    refine tsum_of_norm_bounded
      (g := fun n => CB * (japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) *
        (fullModeWeight c s n * ‖eCoe38 c s zx n‖ ^ 2)))
      (a := CB * (japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) * ‖zx‖ ^ 2))
      ((hsum.mul_left _).mul_left _) (fun n => ?_)
    by_cases hmem : n ∈ Finset.Icc (-(N : ℤ)) N
    · rw [Set.indicator_of_notMem (by simpa using hmem), norm_zero]
      exact mul_nonneg hCB.le (mul_nonneg (Real.rpow_nonneg hN.le _)
        (mul_nonneg (fullModeWeight_pos c s n).le (sq_nonneg _)))
    · rw [Set.indicator_of_mem (by simpa using hmem), Real.norm_eq_abs]
      exact hpt _ hN n (japaneseBracket_ge_of_not_mem_Icc38 N n hmem)

/-- **W05.03 (continuity on `𝓕⁻¹ E_s`).** For `s ≤ 3/4` (v2: `1/2 < s < 3/4`), the spectral
remainder `x ↦ R_W(𝓕⁻¹ x)` is continuous on `E_s`. -/
theorem continuous_remainder_physOfE38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4) :
    Continuous (fun x : ECarrier38 c s => remainder38 c.val (physOfE38 c s x)) := by
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  set M : ℝ := ‖B.weightedHomeoE38 O c s x0‖ + 1 with hM
  set Bd : ℝ := max 1 (‖iotaE38 c s x0‖ + 1) with hBd
  obtain ⟨CB, hCB, hbound⟩ := B.remainder_summable_tail38 c s O hs.le Bd (le_max_left _ _)
  let V : Set (ECarrier38 c s) := {x | ‖B.weightedHomeoE38 O c s x‖ < M} ∩
    {x | ‖iotaE38 c s x‖ < ‖iotaE38 c s x0‖ + 1}
  have hVopen : IsOpen V :=
    (isOpen_lt (B.weightedHomeoE38 O c s).continuous.norm continuous_const).inter
      (isOpen_lt (continuous_iotaE38 c s).norm continuous_const)
  have hx0V : x0 ∈ V := ⟨by simp [hM], by show ‖iotaE38 c s x0‖ < ‖iotaE38 c s x0‖ + 1; linarith⟩
  have hVn : V ∈ 𝓝 x0 := hVopen.mem_nhds hx0V
  let F : ℕ → ECarrier38 c s → ℝ := fun N x =>
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, remainderSummand38 c.val (physOfE38 c s x) n
  have hFc : ∀ N, Continuous (F N) := fun N =>
    continuous_finsetSum _ (fun n _ => B.continuous_remainderSummand_physOfE38 c s O n)
  have hunif : TendstoUniformlyOn F (fun x => remainder38 c.val (physOfE38 c s x)) atTop V := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim := tendsto_japaneseBracket_rpow38 (2 * s - 3 / 2) (by linarith)
    have h2 : Tendsto (fun N : ℕ => CB * (japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) * M ^ 2))
        atTop (𝓝 0) := by
      simpa using (hlim.mul_const (M ^ 2)).const_mul CB
    filter_upwards [h2.eventually (gt_mem_nhds hε)] with N hN x hx
    have hxB : ‖iotaE38 c s x‖ ≤ Bd := le_trans hx.2.le (le_max_right _ _)
    obtain ⟨hsum, htail⟩ := hbound x hxB
    set f : ℤ → ℝ := fun n => remainderSummand38 c.val (physOfE38 c s x) n with hf
    set S : Set ℤ := ↑(Finset.Icc (-(N : ℤ)) N) with hS
    have hind : ∑' n, S.indicator f n = F N x := by
      rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)
        (fun n hn => Set.indicator_of_notMem (by simpa [hS] using hn) _)]
      exact Finset.sum_congr rfl (fun n hn => Set.indicator_of_mem (by simpa [hS] using hn) _)
    have hsplit : ∑' n, f n = ∑' n, S.indicator f n + ∑' n, Sᶜ.indicator f n := by
      rw [← (hsum.indicator S).tsum_add (hsum.indicator Sᶜ)]
      congr 1
      funext n
      exact (Set.indicator_self_add_compl_apply S f n).symm
    have hdist : dist (remainder38 c.val (physOfE38 c s x)) (F N x) =
        ‖∑' n, Sᶜ.indicator f n‖ := by
      rw [dist_eq_norm]
      unfold remainder38
      rw [hsplit, hind, add_sub_cancel_left]
    rw [hdist]
    refine lt_of_le_of_lt ((htail N).trans ?_) hN
    have hxM : ‖B.weightedHomeoE38 O c s x‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hx.1.le 2
    have hN0 : 0 ≤ japaneseBracket (N : ℤ) ^ (2 * s - 3 / 2) :=
      Real.rpow_nonneg (japaneseBracket_pos _).le _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxM hN0) hCB.le
  exact (hunif.continuousOn (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun N => (hFc N).continuousOn))).continuousAt hVn

/-- The finite-gap approximant `Φ⁻¹(P_Λ Φ u)` of `u = 𝓕⁻¹ x`, as a point of `E_s`
(its reflected Fourier sequence `T⁻¹(P_Λ T x) ∈ E_s`, by W04). -/
def finiteGapApproxE38 (O : OneSmoothingInput38 B) (x : ECarrier38 c s) (Λ : Finset ℤ) :
    ECarrier38 c s :=
  eMk38 c s (B.Tinv (projFin38 Λ (B.T (eCoe38 c s x))))
    (B.Tinv_mem_E38 O c s _ (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 Λ _)))

/-- `𝓕⁻¹` of the approximant is literally `Φ⁻¹(P_Λ Φ u)` (cleaned inverse of S03). -/
theorem physOfE_finiteGapApproxE38 (O : OneSmoothingInput38 B) (x : ECarrier38 c s)
    (Λ : Finset ℤ) :
    physOfE38 c s (B.finiteGapApproxE38 c s O x Λ) =
      B.cleanΦinv (projFin38 Λ (B.Φ (physOfE38 c s x))) := by
  rw [B.Φ_physOfE38 c s x, B.cleanΦinv_of_mem _
    (finiteSupport_mem_seqSobolev38 0 _ (finite_support_projFin38 Λ _))]
  rfl

/-- **W05.04 (convergence of the approximants in `𝓕⁻¹ E_s`; v2: "Theorem `D:thm:weighted` gives
convergence in `𝓕⁻¹ E_s`").** -/
theorem tendsto_finiteGapApproxE38 (O : OneSmoothingInput38 B) (x : ECarrier38 c s)
    {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => B.finiteGapApproxE38 c s O x (Λ N)) atTop (𝓝 x) := by
  have hzx : B.T (eCoe38 c s x) ∈ seqE38 c s := B.T_mem_E38 O c s _ (eCoe38_mem c s x)
  have h1 := tendsto_eMk_proj38 c s _ hzx hΛ
  have h2 := (((B.weightedHomeoE38 O c s).symm.continuous.tendsto _).comp h1)
  have e1 : ∀ N : ℕ, (B.weightedHomeoE38 O c s).symm
      (eMk38 c s (projFin38 (Λ N) (B.T (eCoe38 c s x)))
        (finiteSupport_mem_seqE38 c s _ (finite_support_projFin38 (Λ N) _))) =
      B.finiteGapApproxE38 c s O x (Λ N) := by
    intro N
    apply eExt38
    rw [B.weightedHomeoE38_symm_apply O c s]
    rfl
  have e2 : (B.weightedHomeoE38 O c s).symm (eMk38 c s (B.T (eCoe38 c s x)) hzx) = x := by
    apply eExt38
    rw [B.weightedHomeoE38_symm_apply O c s]
    exact B.Tinv_T_E38 c s (eCoe38_mem c s x)
  rw [e2] at h2
  exact h2.congr (fun N => e1 N)

/-- **W05.04 + W05.05 input (finite-gap approximation of the remainder).** For `u = 𝓕⁻¹ x`
with `x ∈ E_s`, `s < 3/4`, and every exhaustion `Λ_N ↑ ℤ` (in particular `Λ_M = [-M,M]`, i.e.
`P_M`): the finite-gap fields `u_N = Φ⁻¹(P_{Λ_N} Φ u)` converge to `u` in `𝓕⁻¹ E_s`; their
remainders are summable and `≥ 0` (S02/`A:lem:convex`); `R_W(u_N) → R_W(u)` (continuity); hence
`R_W(u) ≥ 0`. -/
theorem finiteGap_approximation_W05_38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4)
    (x : ECarrier38 c s) {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ) :
    Tendsto (fun N : ℕ => B.finiteGapApproxE38 c s O x (Λ N)) atTop (𝓝 x) ∧
    (∀ N : ℕ,
      physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N)) =
        B.cleanΦinv (projFin38 (Λ N) (B.Φ (physOfE38 c s x)))) ∧
    (∀ N : ℕ, Summable (fun n : ℤ => remainderSummand38 c.val
        (physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N))) n) ∧
      0 ≤ remainder38 c.val (physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N)))) ∧
    Tendsto (fun N : ℕ => remainder38 c.val (physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N))))
      atTop (𝓝 (remainder38 c.val (physOfE38 c s x))) ∧
    0 ≤ remainder38 c.val (physOfE38 c s x) := by
  have hT := B.tendsto_finiteGapApproxE38 c s O x hΛ
  have hfin : ∀ N : ℕ, Summable (fun n : ℤ => remainderSummand38 c.val
        (physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N))) n) ∧
      0 ≤ remainder38 c.val (physOfE38 c s (B.finiteGapApproxE38 c s O x (Λ N))) := by
    intro N
    rw [B.physOfE_finiteGapApproxE38 c s O x (Λ N)]
    obtain ⟨h1, -, h3⟩ := B.remainder38_finiteGap_proj lower upper c.val (coef_lower38 c)
      (coef_bound38 c) (coef_upper38 c) (Λ N) (B.Φ (physOfE38 c s x))
    exact ⟨h1, h3⟩
  have hlim := ((B.continuous_remainder_physOfE38 c s O hs).tendsto x).comp hT
  exact ⟨hT, fun N => B.physOfE_finiteGapApproxE38 c s O x (Λ N), hfin, hlim,
    ge_of_tendsto' hlim (fun N => (hfin N).2)⟩

/-- **W05.05 (finite-energy identity, `D:eq:energyidentity`).** For `u = 𝓕⁻¹ x ∈ 𝓕⁻¹ E_s`
(`s < 3/4`): `E_W(u) < ∞` holds iff the quadratic action series `∑ a_n |Φ_n(u)|²` is summable,
and then `E_W(u) = ∑_n a_n |Φ_n(u)|² + R_W(u)` (real parts; the sum of differences `R_W(u)` is
absolutely summable by W05.02, so no `∞ - ∞` is formed). -/
theorem energy_identity_W05_38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4)
    (x : ECarrier38 c s) :
    (spectralEnergyW38 c.val (physOfE38 c s x) ≠ ⊤ ↔
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖B.Φ (physOfE38 c s x) n‖ ^ 2)) ∧
    (spectralEnergyW38 c.val (physOfE38 c s x) ≠ ⊤ →
      (spectralEnergyW38 c.val (physOfE38 c s x)).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖B.Φ (physOfE38 c s x) n‖ ^ 2 +
          remainder38 c.val (physOfE38 c s x)) := by
  obtain ⟨CB, hCB, hbound⟩ := B.remainder_summable_tail38 c s O hs.le (max 1 ‖iotaE38 c s x‖)
    (le_max_left _ _)
  have hr : Summable (fun n : ℤ => remainderSummand38 c.val (physOfE38 c s x) n) :=
    (hbound x (le_max_right _ _)).1
  have hsob := sobolev_physOfE38 c s 1 x
  have hI : ∀ n, actualGapActionAllE02_38 (physOfE38 c s x) n =
      ‖B.Φ (physOfE38 c s x) n‖ ^ 2 := fun n => (B.sq_norm_Φ_eq_action _ hsob n).symm
  set g : ℤ → ℝ := fun n => gapIntegral38 c.val (physOfE38 c s x) n with hg
  set A : ℤ → ℝ := fun n => fullWeightRate c.val n * ‖B.Φ (physOfE38 c s x) n‖ ^ 2 with hA
  have hgA : ∀ n, g n = A n + remainderSummand38 c.val (physOfE38 c s x) n := by
    intro n
    simp only [hg, hA]
    rw [gapIntegral38_eq_remainderSummand_add, hI]; ring
  have hg0 : ∀ n, 0 ≤ g n := fun n => gapIntegral38_nonneg c _ n
  have hE : spectralEnergyW38 c.val (physOfE38 c s x) = ∑' n, ENNReal.ofReal (g n) :=
    spectralEnergyW_eq_tsum38 c _
  have hiff : spectralEnergyW38 c.val (physOfE38 c s x) ≠ ⊤ ↔ Summable g := by
    rw [hE]
    constructor
    · intro h
      have := ENNReal.summable_toReal h
      exact this.congr (fun n => ENNReal.toReal_ofReal (hg0 n))
    · intro h
      rw [← ENNReal.ofReal_tsum_of_nonneg hg0 h]
      exact ENNReal.ofReal_ne_top
  have hsumA : Summable g ↔ Summable A := by
    constructor
    · intro h
      have := h.sub hr
      exact this.congr (fun n => by simp only [hgA]; ring)
    · intro h
      have := h.add hr
      exact this.congr (fun n => (hgA n).symm)
  refine ⟨hiff.trans hsumA, fun hfin => ?_⟩
  have hgs : Summable g := hiff.1 hfin
  have hAs : Summable A := hsumA.1 hgs
  rw [hE, ← ENNReal.ofReal_tsum_of_nonneg hg0 hgs, ENNReal.toReal_ofReal (tsum_nonneg hg0)]
  unfold remainder38
  rw [← hAs.tsum_add hr]
  exact tsum_congr hgA

/-- The series `A:eq:remainder` is absolutely summable on all of `𝓕⁻¹ E_s` (`s ≤ 3/4`). -/
theorem summable_remainder_physOfE38 (O : OneSmoothingInput38 B) (hs : s ≤ 3 / 4)
    (x : ECarrier38 c s) :
    Summable (fun n : ℤ => remainderSummand38 c.val (physOfE38 c s x) n) := by
  obtain ⟨CB, hCB, hbound⟩ := B.remainder_summable_tail38 c s O hs (max 1 ‖iotaE38 c s x‖)
    (le_max_left _ _)
  exact (hbound x (le_max_right _ _)).1

/-- **W05, headline form on `𝓕⁻¹ E_s` (v2 `D:cor:Rcontinuous`), conditional on `B`, `O`.**
Let `c` be bounded coefficients and `s < 3/4` (v2: `1/2 < s < 3/4`). On the space `𝓕⁻¹ E_s` with the
topology transported from `E_s` by `𝓕`:
1. `u ↦ R_W(u)` is a well defined (absolutely summable series) continuous function;
2. `R_W(u) ≥ 0`;
3. if `E_W(u) < ∞` then `∑ a_n |Φ_n(u)|² < ∞` and `E_W(u) = ∑ a_n |Φ_n(u)|² + R_W(u)`. -/
theorem W05_38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4) :
    (∀ u : FinvE38 c s,
      Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) _ (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, spectralEnergyW38 c.val u.1 ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖B.Φ u.1 n‖ ^ 2) ∧
      (spectralEnergyW38 c.val u.1).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖B.Φ u.1 n‖ ^ 2 + remainder38 c.val u.1) := by
  refine ⟨fun u => ?_, ?_, fun u => ?_, fun u hE => ?_⟩
  · have := B.summable_remainder_physOfE38 c s O hs.le (toE38 c s u)
    rwa [physOfE38_toE38] at this
  · let _ := topFinvE38 c s
    have h1 : Continuous (fun u : FinvE38 c s => toE38 c s u) := continuous_induced_dom
    have h2 := (B.continuous_remainder_physOfE38 c s O hs).comp h1
    have e : (fun u : FinvE38 c s => remainder38 c.val u.1) =
        (fun x : ECarrier38 c s => remainder38 c.val (physOfE38 c s x)) ∘ (toE38 c s) := by
      funext u; simp only [Function.comp_apply, physOfE38_toE38]
    rw [e]; exact h2
  · have := (B.finiteGap_approximation_W05_38 c s O hs (toE38 c s u) isExhaustion_Icc38).2.2.2.2
    rwa [physOfE38_toE38] at this
  · have h := B.energy_identity_W05_38 c s O hs (toE38 c s u)
    simp only [physOfE38_toE38] at h
    exact ⟨h.1.1 hE, h.2 hE⟩

/-- **W05.04, `P_M` form.** For `u = 𝓕⁻¹ x ∈ 𝓕⁻¹ E_s`, the finite-gap fields
`u_M = Φ⁻¹(P_M Φ u)` (`P_M` = coordinate projection onto `[-M, M]`) converge to `u` in `𝓕⁻¹ E_s`,
`R_W(u_M) ≥ 0` (S02), `R_W(u_M) → R_W(u)`, hence `R_W(u) ≥ 0`. -/
theorem finiteGap_approximation_PM_W05_38 (O : OneSmoothingInput38 B) (hs : s < 3 / 4)
    (x : ECarrier38 c s) :
    Tendsto (fun M : ℕ => eMk38 c s
      (fourierSeq38 (B.cleanΦinv (projFin38 (Finset.Icc (-(M : ℤ)) M) (B.Φ (physOfE38 c s x)))))
      (by
        rw [← B.physOfE_finiteGapApproxE38 c s O x (Finset.Icc (-(M : ℤ)) M),
          fourierSeq38_physOfE38]
        exact eCoe38_mem c s _)) atTop (𝓝 x) ∧
    (∀ M : ℕ, 0 ≤ remainder38 c.val
      (B.cleanΦinv (projFin38 (Finset.Icc (-(M : ℤ)) M) (B.Φ (physOfE38 c s x))))) ∧
    Tendsto (fun M : ℕ => remainder38 c.val
      (B.cleanΦinv (projFin38 (Finset.Icc (-(M : ℤ)) M) (B.Φ (physOfE38 c s x)))))
      atTop (𝓝 (remainder38 c.val (physOfE38 c s x))) ∧
    0 ≤ remainder38 c.val (physOfE38 c s x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := B.finiteGap_approximation_W05_38 c s O hs x isExhaustion_Icc38
  refine ⟨?_, fun M => ?_, ?_, h5⟩
  · refine h1.congr (fun M => eExt38 c s ?_)
    rw [eCoe38_mk, ← B.physOfE_finiteGapApproxE38 c s O x (Finset.Icc (-(M : ℤ)) M),
      fourierSeq38_physOfE38]
  · rw [← h2 M]; exact (h3 M).2
  · exact h4.congr (fun M => by rw [h2 M])

end BirkhoffInput38

end NlsGge.Birkhoff
end
