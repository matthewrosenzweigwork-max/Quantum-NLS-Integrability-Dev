import NlsGge.Ramer.General.CylindricalClosabilityG
import NlsGge.Ramer.General.TruncatedFieldConvergenceG
import NlsGge.Ramer.DivergenceProductRule

/-!
# Closed divergence: uniqueness (GB6, part a)

Generalization of the first part of `NlsGge/Ramer/ClosedDivergenceProductRule.lean` to a
`RamerSetting S`: `S.IsClosedDiv`, generic `L²` helpers (namespace `NlsGge.Ramer.Gen`) and
uniqueness of the closed divergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer.Gen

/-! ### Generic `L²` helpers -/

/-- `L²` dominated convergence for real-valued functions. -/
theorem tendsto_eLpNorm_two_of_dominated_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hFm : ∀ N, AEStronglyMeasurable (F N) μ) (D : α → ℝ)
    (hD : Integrable (fun z => D z ^ 2) μ)
    (hbd : ∀ N, ∀ᵐ z ∂μ, ‖F N z‖ ≤ D z)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => F N z) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (F N) 2 μ) atTop (𝓝 0) := by
  have hint : ∀ N, eLpNorm (F N) 2 μ = (∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hFm N)]
    simp
  have hlim2 : ∀ᵐ z ∂μ, Tendsto (fun N => ‖F N z‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hlim] with z hz
    have h0 : Tendsto (fun N => ‖F N z‖ₑ) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_norm_zero.comp hz)
      rw [ENNReal.ofReal_zero] at h
      exact h.congr (fun N => ofReal_norm _)
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have hDfin : ∫⁻ z, ENNReal.ofReal (D z ^ 2) ∂μ ≠ ∞ := by
    have := hD.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ?_) this)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hDCT : Tendsto (fun N => ∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun N z => ‖F N z‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun z => ENNReal.ofReal (D z ^ 2))
      (fun N => (hFm N).enorm.pow_const _)
      (fun N => by
        filter_upwards [hbd N] with z hz
        have h1 : ‖F N z‖ₑ ≤ ENNReal.ofReal (D z) := by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hz
        have hD0 : 0 ≤ D z := (norm_nonneg _).trans hz
        calc ‖F N z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (D z) ^ (2 : ℝ) :=
              ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal (D z ^ 2) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num)]
              norm_cast)
      hDfin hlim2
    simpa using this
  simp only [hint]
  have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hDCT
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

/-- Squeeze for `eLpNorm`: a pointwise bound by a function whose `eLpNorm` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b : ℕ → α → ℝ) (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (hab : ∀ k z, ‖a k z‖ ≤ ‖b k z‖)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (a k) 2 μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    (fun k => eLpNorm_mono (ha k) (fun z => hab k z))

/-- Sums of `L²`-null sequences are `L²`-null. -/
theorem tendsto_eLpNorm_zero_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b d : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0))
    (hd : Tendsto (fun k => eLpNorm (d k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => b k z + d k z) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => eLpNorm (b k) 2 μ + eLpNorm (d k) 2 μ) atTop (𝓝 0) := by
    simpa using hb.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun k => bot_le)
    (fun k => eLpNorm_add_le (f := b k) (g := d k) (by norm_num))

/-- Differences of `L²`-null sequences are `L²`-null. -/
theorem tendsto_eLpNorm_zero_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b d : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0))
    (hd : Tendsto (fun k => eLpNorm (d k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => b k z - d k z) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => eLpNorm (b k) 2 μ + eLpNorm (d k) 2 μ) atTop (𝓝 0) := by
    simpa using hb.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le)
    (fun k => eLpNorm_sub_le (f := b k) (g := d k) (by norm_num))

/-- A constant multiple of an `L²`-null sequence is `L²`-null. -/
theorem tendsto_eLpNorm_zero_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (B : ℝ) (b : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => B * b k z) 2 μ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul hb (Or.inr (by simp : ‖B‖ₑ ≠ ⊤))
  rw [mul_zero] at h
  refine h.congr (fun k => ?_)
  exact (eLpNorm_const_smul (μ := μ) (p := 2) B (b k)).symm

/-- Bounded a.e.-null multipliers of an `L²` function give an `L²`-null sequence. -/
theorem tendsto_eLpNorm_zero_of_bdd_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (hum : ∀ k, AEStronglyMeasurable (u k) μ) (M : ℝ)
    (hu : ∀ k z, |u k z| ≤ M) (hu0 : ∀ᵐ z ∂μ, Tendsto (fun k => u k z) atTop (𝓝 0))
    (w : α → ℝ) (hw : MemLp w 2 μ) :
    Tendsto (fun k => eLpNorm (fun z => u k z * w z) 2 μ) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_dominated_ae (fun k z => u k z * w z)
    (fun k => (hum k).mul hw.aestronglyMeasurable) (fun z => |M| * ‖w z‖) ?_ ?_ ?_
  · have h := (hw.integrable_sq).const_mul (M ^ 2)
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [mul_pow, sq_abs, Real.norm_eq_abs]
  · intro k
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hu k z).trans (le_abs_self M)) (norm_nonneg _)
  · filter_upwards [hu0] with z hz
    simpa using hz.mul_const (w z)


end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### The closed divergence -/

/-- `F : Ω → H` has closed divergence `η` for the actual source law `γ`: `η ∈ L²(γ)` and there are cylindrical `C²` fields `g k` of levels `N k` with
polynomially bounded value and derivative, `cylField (g k) → F` in `L²(γ;H)` and
`cylDiv (g k) → η` in `L²(γ)`. -/
def IsClosedDiv (F : (ℤ → ℂ) → S.H)
    (η : (ℤ → ℂ) → ℝ) : Prop :=
  MemLp η 2 S.γ ∧
  ∃ (N : ℕ → ℕ) (g : ∀ k, S.head (N k) → S.head (N k)) (C : ℕ → ℝ) (p : ℕ → ℕ),
    (∀ k, ContDiff ℝ 2 (g k)) ∧ (∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    (∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    Tendsto (fun k => eLpNorm (fun z => ‖S.cylField (N k) (g k) z - F z‖) 2
      S.γ) atTop (𝓝 0) ∧
    Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2
      S.γ) atTop (𝓝 0)

/-! ### Measurability facts -/

/-- A cylindrical field with continuous profile is a.e. strongly measurable. -/
theorem aestronglyMeasurable_cylField {N : ℕ}
    (g : S.head N → S.head N) (hg : Continuous g) :
    AEStronglyMeasurable (S.cylField N g) S.γ :=
  ((continuous_subtype_val.comp hg).comp_stronglyMeasurable
    (S.measurable_headPt N).stronglyMeasurable).aestronglyMeasurable

theorem aestronglyMeasurable_norm_cylField_sub {N : ℕ}
    (g : S.head N → S.head N) (hg : Continuous g) (F : (ℤ → ℂ) → S.H)
    (hF : AEStronglyMeasurable F S.γ) :
    AEStronglyMeasurable (fun z => ‖S.cylField N g z - F z‖)
      S.γ :=
  ((S.aestronglyMeasurable_cylField g hg).sub hF).norm

/-- If cylindrical fields with continuous profiles converge to `F` in the sense
`eLpNorm ‖cylField - F‖ → 0` then `F` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_cylField 
    {N : ℕ → ℕ} (g : ∀ k, S.head (N k) → S.head (N k))
    (hg : ∀ k, Continuous (g k)) (F : (ℤ → ℂ) → S.H)
    (hF : Tendsto (fun k => eLpNorm (fun z => ‖S.cylField (N k) (g k) z - F z‖) 2
      S.γ) atTop (𝓝 0)) :
    AEStronglyMeasurable F S.γ := by
  set γ := S.γ with hγ
  have hmeas : TendstoInMeasure γ (fun k z => ‖S.cylField (N k) (g k) z - F z‖) atTop
      (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    refine hF.congr (fun k => ?_)
    congr 1
    funext z
    simp
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun i => S.aestronglyMeasurable_cylField (g (ns i)) (hg (ns i))) ?_
  filter_upwards [hns] with z hz
  have : Tendsto (fun i => S.cylField (N (ns i)) (g (ns i)) z - F z) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 hz
  simpa using this.add_const (F z)

/-! ### Goal 1: uniqueness of the closed divergence -/

variable {S} in
theorem IsClosedDiv.aestronglyMeasurable 
    {F : (ℤ → ℂ) → S.H} {η : (ℤ → ℂ) → ℝ} (h : S.IsClosedDiv F η) :
    AEStronglyMeasurable F S.γ := by
  obtain ⟨-, N, g, C, p, hg, -, -, hF, -⟩ := h
  exact S.aestronglyMeasurable_of_tendsto_cylField g
    (fun k => (hg k).continuous) F hF

variable {S} in
/-- **Uniqueness of the closed divergence.** -/
theorem IsClosedDiv.ae_eq 
    {F : (ℤ → ℂ) → S.H} {η η' : (ℤ → ℂ) → ℝ} (h : S.IsClosedDiv F η)
    (h' : S.IsClosedDiv F η') :
    η =ᵐ[S.γ] η' := by
  set γ := S.γ with hγ
  have hFm := h.aestronglyMeasurable
  obtain ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hδ⟩ := h
  obtain ⟨hη', N', g', C', p', hg', hgg', hDg', hF', hδ'⟩ := h'
  refine S.cylDiv_closure_unique g g' (fun k => (hg k).of_le (by norm_num))
    (fun k => (hg' k).of_le (by norm_num)) C C' p p' hgg hDg hgg' hDg' η η' hη hη' ?_ hδ hδ'
  refine tendsto_eLpNorm_zero_of_le
    (fun k z => ‖S.cylField (N k) (g k) z - S.cylField (N' k) (g' k) z‖)
    (fun k z => ‖S.cylField (N k) (g k) z - F z‖ + ‖S.cylField (N' k) (g' k) z - F z‖)
    (fun k => ?_) (fun k z => ?_) (tendsto_eLpNorm_zero_add _ _ hF hF')
  · exact ((S.aestronglyMeasurable_cylField (g k) (hg k).continuous).sub
      (S.aestronglyMeasurable_cylField (g' k) (hg' k).continuous)).norm
  · rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖S.cylField (N k) (g k) z - S.cylField (N' k) (g' k) z‖
        = ‖(S.cylField (N k) (g k) z - F z) - (S.cylField (N' k) (g' k) z - F z)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _

end NlsGge.Ramer.General.RamerSetting
