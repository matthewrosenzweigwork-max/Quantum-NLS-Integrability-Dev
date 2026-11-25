import NlsGge.Ramer.General.CylindricalDivergenceG
import NlsGge.Ramer.General.RamerSettingMeasure

/-!
# Truncated-field convergence on the general source law (GB1)

Generalization of `NlsGge/Ramer/TruncatedFieldConvergence.lean` to a `RamerSetting S`.
`headToE N = S.incl ∘ (S.head N).subtype`; the isotropy-dependent bound is replaced by
`S.incl_norm_le` (constant `√ratioSup`). Only continuity of `headToE` is needed downstream.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Coordinate truncation `P_N : H → P_N H` as a linear map. -/
def cmTruncLin (N : ℕ) : S.H →ₗ[ℝ] S.head N :=
  LinearMap.codRestrict (S.head N) (S.headProj N : S.H →ₗ[ℝ] S.H)
    (fun x => S.headProj_mem_head N x)

/-- Coordinate truncation `P_N : H → P_N H`, a continuous linear map. -/
def cmTrunc (N : ℕ) : S.H →L[ℝ] S.head N :=
  (S.cmTruncLin N).mkContinuous 1 (fun x => by
    rw [one_mul]
    exact weightedRealProjection_norm_le S.cmWeight (symmetricModes N) x)

theorem hcoord_cmTrunc (N : ℕ) (x : S.H) (n : ℤ) :
    S.hcoord ((S.cmTrunc N x : S.head N) : S.H) n =
      if n ∈ symmetricModes N then S.hcoord x n else 0 :=
  S.hcoord_headProj N x n

theorem norm_cmTrunc_le (N : ℕ) (x : S.H) : ‖S.cmTrunc N x‖ ≤ ‖x‖ :=
  weightedRealProjection_norm_le S.cmWeight (symmetricModes N) x

/-- The head `P_N H` seen in `E`: `S.incl ∘ subtype`. -/
def headToE (N : ℕ) : S.head N →L[ℝ] S.E :=
  S.incl.comp (S.head N).subtypeL

theorem headToE_apply (N : ℕ) (v : S.head N) : S.headToE N v = S.incl (v : S.H) := rfl

/-- The anisotropy-sensitive bound, from `incl_norm_le`. -/
theorem norm_headToE_le (N : ℕ) (v : S.head N) :
    ‖S.headToE N v‖ ≤ Real.sqrt S.ratioSup * ‖v‖ :=
  S.incl_norm_le (v : S.H)

theorem headToE_coord (N : ℕ) (v : S.head N) (n : ℤ) :
    S.coord n (S.headToE N v) = S.hcoord (v : S.H) n :=
  S.coord_incl _ n

theorem headToE_headPt_eq (N : ℕ) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, S.coord n (S.R z) = z n) :
    S.headToE N (S.headPt N z) = S.projE N (S.R z) := by
  apply S.E_ext
  intro n
  rw [headToE_coord, S.hcoord_headPt, S.coord_projE, hz n]

theorem tendsto_headToE_headPt (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, S.coord n (S.R z) = z n) :
    Tendsto (fun N : ℕ => S.headToE N (S.headPt N z)) atTop (𝓝 (S.R z)) := by
  have heq : (fun N : ℕ => S.headToE N (S.headPt N z)) = fun N : ℕ => S.projE N (S.R z) :=
    funext fun N => S.headToE_headPt_eq N z hz
  rw [heq]
  exact S.projE_tendsto _

/-- Deterministic core: `P_N G(x_N) → G(x)` in `H` whenever `x_N → x` in `E`. -/
theorem tendsto_cmTrunc_comp
    (G : S.E → S.H) (hG : Continuous G)
    (xs : ℕ → S.E) (x : S.E)
    (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun N : ℕ => ((S.cmTrunc N (G (xs N)) : S.head N) : S.H))
      atTop (𝓝 (G x)) := by
  set h := G x
  have h1 : Tendsto (fun N => G (xs N)) atTop (𝓝 h) := (hG.tendsto x).comp hx
  have h2 : Tendsto (fun N : ℕ => (S.headProj N h : S.H)) atTop (𝓝 h) :=
    weightedProjection_tendsto S.cmWeight (show WeightedHilbert S.cmWeight from h)
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using h1.add h2)
  have hlin : ((S.cmTrunc N (G (xs N)) : S.head N) : S.H) - h =
      ((S.cmTrunc N (G (xs N) - h) : S.head N) : S.H) + (S.headProj N h - h) := by
    rw [map_sub]
    change _ = ((S.cmTrunc N (G (xs N)) : S.head N) : S.H) -
      ((S.cmTrunc N h : S.head N) : S.H) + _
    have : ((S.cmTrunc N h : S.head N) : S.H) = S.headProj N h := rfl
    rw [this]
    abel
  rw [hlin]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact S.norm_cmTrunc_le N (G (xs N) - h)

/-- **Truncated-field convergence** (`G_N → G` in `L²(γ; H)`), `G_N(x) = P_N G(P_N x)`. -/
theorem tendsto_eLpNorm_truncatedField
    (G : S.E → S.H) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z => ‖S.cylField N
        (fun v => S.cmTrunc N (G (S.headToE N v))) z
        - G (S.R z)‖) 2 S.γ) atTop (𝓝 0) := by
  set γ := S.γ with hγ
  let _ : MeasurableSpace S.H := borel _
  have _ : BorelSpace S.H := ⟨rfl⟩
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z => ‖S.cylField N
        (fun v => S.cmTrunc N (G (S.headToE N v))) z - G (R z)‖
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have h1 : Measurable (fun z => S.cylField N
        (fun v => S.cmTrunc N (G (S.headToE N v))) z) := by
      have hc : Continuous (fun v : S.head N =>
          ((S.cmTrunc N (G (S.headToE N v)) : S.head N) : S.H)) :=
        continuous_subtype_val.comp ((S.cmTrunc N).continuous.comp
          (hG.comp (S.headToE N).continuous))
      exact hc.measurable.comp (S.measurable_headPt N)
    have h2 : Measurable (fun z => G (R z)) := hG.measurable.comp hRm
    exact (h1.sub h2).norm
  have hae := S.coord_R_ae
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := S.tendsto_cmTrunc_comp G hG _ _ (S.tendsto_headToE_headPt z hz)
    have h2 : Tendsto (fun N => ‖S.cylField N
        (fun v => S.cmTrunc N (G (S.headToE N v))) z - G (R z)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h1)
      exact this
    exact h2
  have hbd : ∀ N z, ‖F N z‖ₑ ≤ ENNReal.ofReal (2 * B) := by
    intro N z
    have hb0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    rw [enorm_norm, ← ofReal_norm]
    have : ‖S.cylField N (fun v => S.cmTrunc N (G (S.headToE N v))) z - G (R z)‖ ≤ 2 * B := by
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖S.cylField N (fun v => S.cmTrunc N (G (S.headToE N v))) z‖ ≤ B :=
        (S.norm_cmTrunc_le N _).trans (hB _)
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

end NlsGge.Ramer.General.RamerSetting
