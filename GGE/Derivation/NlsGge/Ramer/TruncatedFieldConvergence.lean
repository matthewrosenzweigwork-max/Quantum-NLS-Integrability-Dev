import NlsGge.Ramer.CylindricalDivergence
import NlsGge.Measure.CountableReconstruction
import NlsGge.Sobolev.PhysicalProjection
import NlsGge.Sobolev.RealBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- Coordinate truncation `P_N : H → P_N H` as a linear map. -/
def cmTruncLin (c : BoundedCoefficients lower upper) (N : ℕ) :
    ActualCM c →ₗ[ℝ] actualCMHead c N :=
  LinearMap.codRestrict (actualCMHead c N)
    (weightedRealProjectionLinear (cmModeWeight c) (symmetricModes N))
    (fun x => weightedProjection_mem_actualCMHead c N x)

/-- Coordinate truncation `P_N : H → P_N H`, a continuous linear map. -/
def cmTrunc (c : BoundedCoefficients lower upper) (N : ℕ) :
    ActualCM c →L[ℝ] actualCMHead c N :=
  (cmTruncLin c N).mkContinuous 1 (fun x => by
    have := weightedProjection_norm_le (cmModeWeight c) (symmetricModes N)
      (show WeightedHilbert (cmModeWeight c) from x)
    rw [one_mul]
    exact this)

theorem cmCoord_cmTrunc (c : BoundedCoefficients lower upper) (N : ℕ) (x : ActualCM c)
    (n : ℤ) : cmCoord ((cmTrunc c N x : actualCMHead c N) : ActualCM c) n =
      if n ∈ symmetricModes N then cmCoord x n else 0 :=
  weightedProjection_apply (cmModeWeight c) (symmetricModes N)
    (show WeightedHilbert (cmModeWeight c) from x) n

theorem norm_cmTrunc_le (c : BoundedCoefficients lower upper) (N : ℕ) (x : ActualCM c) :
    ‖cmTrunc c N x‖ ≤ ‖x‖ :=
  weightedRealProjection_norm_le (cmModeWeight c) (symmetricModes N) x

/-- The head `P_N H` seen in `E_s`: same coordinates (finite support). -/
def headToELin (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    actualCMHead c N →ₗ[ℝ] FullWeightedHilbert c s where
  toFun v := (⟨fun n => cmCoord (v : ActualCM c) n, by
    classical
    change Memℓp (weightedCoordinates (fullModeWeight c s)
      (fun n => cmCoord (v : ActualCM c) n)) 2
    refine memℓp_gen (summable_of_ne_finset_zero (s := symmetricModes N) ?_)
    intro n hn
    have := v.2 n hn
    simp [weightedCoordinates, this]⟩ : WeightedHilbert (fullModeWeight c s))
  map_add' v w := rfl
  map_smul' r v := rfl

def headToE (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    actualCMHead c N →L[ℝ] FullWeightedHilbert c s :=
  LinearMap.toContinuousLinearMap (headToELin c s N)


theorem headToE_coord (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (v : actualCMHead c N) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c s) from headToE c s N v) n =
      cmCoord (v : ActualCM c) n := rfl

theorem fullWeighted_ext (c : BoundedCoefficients lower upper) (s : ℝ)
    {x y : FullWeightedHilbert c s}
    (h : ∀ n, (show WeightedHilbert (fullModeWeight c s) from x) n =
      (show WeightedHilbert (fullModeWeight c s) from y) n) : x = y :=
  Subtype.ext (funext h)

/-- For a sample whose realization has the sample as coordinates, the embedded head point is the
coordinate truncation of the realization in `E_s`. -/
theorem headToE_headPt_eq (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (show WeightedHilbert (fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s z) n = z n) :
    headToE c s N (headPt c N z) =
      (show FullWeightedHilbert c s from
        weightedProjection (fullModeWeight c s) (symmetricModes N)
          (NlsGge.Measure.fullWeightedSequenceRealization c s z)) := by
  apply fullWeighted_ext
  intro n
  rw [headToE_coord, cmCoord_headPt]
  have h := weightedProjection_apply (fullModeWeight c s) (symmetricModes N)
    (NlsGge.Measure.fullWeightedSequenceRealization c s z) n
  rw [hz n] at h
  exact h.symm

theorem tendsto_headToE_headPt (c : BoundedCoefficients lower upper) (s : ℝ)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (show WeightedHilbert (fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s z) n = z n) :
    Tendsto (fun N : ℕ => headToE c s N (headPt c N z)) atTop
      (𝓝 (NlsGge.Measure.fullWeightedSequenceRealization c s z)) := by
  have ht := weightedProjection_tendsto (fullModeWeight c s)
    (show WeightedHilbert (fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s z)
  have heq : (fun N : ℕ => headToE c s N (headPt c N z)) = fun N : ℕ =>
      (show FullWeightedHilbert c s from
        weightedProjection (fullModeWeight c s) (symmetricModes N)
          (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
    funext fun N => headToE_headPt_eq c s N z hz
  rw [heq]
  exact ht

/-- Deterministic core: `P_N G(x_N) → G(x)` in `H` whenever `x_N → x` in `E_s`. -/
theorem tendsto_cmTrunc_comp (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G)
    (xs : ℕ → FullWeightedHilbert c s) (x : FullWeightedHilbert c s)
    (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun N : ℕ => ((cmTrunc c N (G (xs N)) : actualCMHead c N) : ActualCM c))
      atTop (𝓝 (G x)) := by
  set h := G x
  have h1 : Tendsto (fun N => G (xs N)) atTop (𝓝 h) := (hG.tendsto x).comp hx
  have h2 : Tendsto (fun N : ℕ =>
      (show ActualCM c from weightedProjection (cmModeWeight c) (symmetricModes N)
        (show WeightedHilbert (cmModeWeight c) from h))) atTop (𝓝 h) :=
    weightedProjection_tendsto (cmModeWeight c) (show WeightedHilbert (cmModeWeight c) from h)
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using h1.add h2)
  have hlin : ((cmTrunc c N (G (xs N)) : actualCMHead c N) : ActualCM c) - h =
      ((cmTrunc c N (G (xs N) - h) : actualCMHead c N) : ActualCM c) +
      ((show ActualCM c from weightedProjection (cmModeWeight c) (symmetricModes N)
        (show WeightedHilbert (cmModeWeight c) from h)) - h) := by
    rw [map_sub]
    change _ = ((cmTrunc c N (G (xs N)) : actualCMHead c N) : ActualCM c) -
      ((cmTrunc c N h : actualCMHead c N) : ActualCM c) + _
    have : ((cmTrunc c N h : actualCMHead c N) : ActualCM c) =
      (show ActualCM c from weightedProjection (cmModeWeight c) (symmetricModes N)
        (show WeightedHilbert (cmModeWeight c) from h)) := rfl
    rw [this]
    abel
  rw [hlin]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact norm_cmTrunc_le c N (G (xs N) - h)


/-- **Truncated-field convergence** (v2: `G_N → G` in `L²(γ; H)`), `G_N(x) = P_N G(P_N x)`.
The integrand is `‖cylField … z − G(ξ(z))‖_H`, where `cylField` already takes values in
`ActualCM c` (the head `P_N H` is coerced there by the subspace inclusion), so no further
coercion is needed. -/
theorem tendsto_eLpNorm_truncatedField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1:ℝ)/2 < s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z => ‖cylField c N
        (fun v => cmTrunc c N (G (headToE c s N v))) z
        - G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z => ‖cylField c N
        (fun v => cmTrunc c N (G (headToE c s N v))) z - G (R z)‖
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have h1 : Measurable (fun z => cylField c N
        (fun v => cmTrunc c N (G (headToE c s N v))) z) := by
      have hc : Continuous (fun v : actualCMHead c N =>
          ((cmTrunc c N (G (headToE c s N v)) : actualCMHead c N) : ActualCM c)) :=
        continuous_subtype_val.comp ((cmTrunc c N).continuous.comp
          (hG.comp (headToE c s N).continuous))
      exact hc.measurable.comp (measurable_headPt c N)
    have h2 : Measurable (fun z => G (R z)) := hG.measurable.comp hRm
    exact (h1.sub h2).norm
  have hae := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := tendsto_cmTrunc_comp c s G hG _ _ (tendsto_headToE_headPt c s z hz)
    have h2 : Tendsto (fun N => ‖cylField c N
        (fun v => cmTrunc c N (G (headToE c s N v))) z - G (R z)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h1)
      exact this
    exact h2
  have hbd : ∀ N z, ‖F N z‖ₑ ≤ ENNReal.ofReal (2 * B) := by
    intro N z
    have hb0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    rw [enorm_norm, ← ofReal_norm]
    have : ‖cylField c N (fun v => cmTrunc c N (G (headToE c s N v))) z - G (R z)‖ ≤ 2 * B := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖cylField c N (fun v => cmTrunc c N (G (headToE c s N v))) z‖ ≤ B :=
        (norm_cmTrunc_le c N _).trans (hB _)
      linarith [hB (R z)]
    exact ENNReal.ofReal_le_ofReal this
  have hint : ∀ N, eLpNorm (F N) 2 γ =
      (∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂γ) ^ (1 / (2 : ℝ)) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hFm N).aestronglyMeasurable]
    simp
  have hlim2 : ∀ᵐ z ∂γ, Tendsto (fun N => ‖F N z‖ₑ ^ (2 : ℝ)) atTop (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hlim] with z hz
    have h0 : Tendsto (fun N => ‖F N z‖ₑ) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal hz
      rw [ENNReal.ofReal_zero] at h
      exact h.congr (fun N => (Real.enorm_of_nonneg (norm_nonneg _)).symm)
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have hDCT : Tendsto (fun N => ∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂γ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := γ)
      (F := fun N z => ‖F N z‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal (2 * B) ^ (2 : ℝ))
      (fun N => (hFm N).enorm.pow_const _)
      (fun N => Eventually.of_forall fun z =>
        ENNReal.rpow_le_rpow (hbd N z) (by norm_num))
      (by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      hlim2
    simpa using this
  show Tendsto (fun N => eLpNorm (F N) 2 γ) atTop (𝓝 0)
  simp only [hint]
  have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hDCT
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

end NlsGge.Ramer
