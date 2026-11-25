import NlsGge.GK38.ActionCompactHeight
import NlsGge.GK38.EigenvalueCompactnessStrong

/-! # A4 real helper: weighted integrals with both moving endpoints

All finite-interval integrability is earned before integral differences.
Uniform convergence controls the moving-interval error, while the limiting
continuous primitive controls both endpoint errors.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapWeighted_intervalIntegrable38 (u : PhysicalL2) (W : ℝ → ℝ)
    (hW : Continuous W) (a b : ℝ) :
    IntervalIntegrable (fun x => W (2 * x) * actualGapHeightE02_38 u x) volume a b :=
  ((hW.comp (continuous_const.mul continuous_id)).mul
    (continuous_actualGapHeightE02_38 u)).intervalIntegrable a b

theorem gapWeighted_uniform_weak38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (W : ℝ → ℝ) (hW : Continuous W)
    (A B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ Icc A B,
      |W (2 * x) * actualGapHeightE02_38 (u k) x -
        W (2 * x) * actualGapHeightE02_38 u₀ x| < ε := by
  let : CompactSpace (Icc A B) := isCompact_iff_compactSpace.mp isCompact_Icc
  let H (v : PhysicalL2) : C(Icc A B, ℝ) :=
    ⟨fun x => actualGapHeightE02_38 v x,
      (continuous_actualGapHeightE02_38 v).comp continuous_subtype_val⟩
  have hh : Tendsto (fun k => H (u k)) atTop (𝓝 (H u₀)) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [gapHeight_uniform_weak38 u u₀ hw A B δ hδ] with k hk x
    simpa only [H, ContinuousMap.coe_mk, Real.dist_eq, abs_sub_comm] using hk x x.property
  let V : C(Icc A B, ℝ) := ⟨fun x => W (2 * x.val),
    hW.comp (continuous_const.mul continuous_subtype_val)⟩
  have he : ∀ᶠ k in atTop, dist (V * H (u k)) (V * H u₀) < ε :=
    (tendsto_const_nhds.mul hh).eventually (ball_mem_nhds _ hε)
  filter_upwards [he] with k hk x hx
  have hp := (ContinuousMap.dist_apply_le_dist (f := V * H (u k))
    (g := V * H u₀) ⟨x, hx⟩).trans_lt hk
  simpa only [ContinuousMap.mul_apply, H, V, ContinuousMap.coe_mk, Real.dist_eq] using hp

/-- Uniform convergence on every finite interval and convergence of both
endpoints imply convergence of honest interval integrals. -/
theorem intervalIntegral_tendsto_of_uniform38 (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : ∀ k, Continuous (F k)) (hf : Continuous f)
    (huni : ∀ A B ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ x ∈ Icc A B, |F k x - f x| < ε)
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun k => ∫ x in a k..b k, F k x) atTop (𝓝 (∫ x in a₀..b₀, f x)) := by
  have hiF (k : ℕ) (s t : ℝ) : IntervalIntegrable (F k) volume s t :=
    (hF k).intervalIntegrable s t
  have hif (s t : ℝ) : IntervalIntegrable f volume s t := hf.intervalIntegrable s t
  let A := min a₀ b₀ - 1
  let B := max a₀ b₀ + 1
  have hAB : A < B := by dsimp [A, B]; have : min a₀ b₀ ≤ max a₀ b₀ := min_le_max; linarith
  have hends : ∀ᶠ k in atTop, a k ∈ Icc A B ∧ b k ∈ Icc A B := by
    filter_upwards [ha.eventually (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1)),
      hb.eventually (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))] with k hka hkb
    have hka' : |a k - a₀| < 1 := by simpa only [mem_ball, Real.dist_eq] using hka
    have hkb' : |b k - b₀| < 1 := by simpa only [mem_ball, Real.dist_eq] using hkb
    have hma := min_le_left a₀ b₀
    have hmb := min_le_right a₀ b₀
    have hMa := le_max_left a₀ b₀
    have hMb := le_max_right a₀ b₀
    rcases abs_lt.mp hka' with ⟨ha1, ha2⟩
    rcases abs_lt.mp hkb' with ⟨hb1, hb2⟩
    dsimp [A, B]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have herr : Tendsto (fun k => ∫ x in a k..b k, F k x - f x) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hC : 0 < B - A + 1 := by linarith
    filter_upwards [hends, huni A B (ε / (B - A + 1)) (div_pos hε hC)] with k hk hu
    have hsub : uIoc (a k) (b k) ⊆ Icc A B := by
      intro x hx
      exact ⟨(le_min hk.1.1 hk.2.1).trans hx.1.le,
        hx.2.trans (max_le hk.1.2 hk.2.2)⟩
    have hlen : |b k - a k| ≤ B - A := by
      apply abs_le.mpr
      constructor <;> linarith [hk.1.1, hk.1.2, hk.2.1, hk.2.2]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => (Real.norm_eq_abs (F k x - f x)).symm ▸ (hu x (hsub hx)).le)
    rw [dist_zero_right]
    calc
      _ ≤ (ε / (B - A + 1)) * |b k - a k| := hn
      _ ≤ (ε / (B - A + 1)) * (B - A) :=
        mul_le_mul_of_nonneg_left hlen (div_pos hε hC).le
      _ < ε := by
        have hp : (ε / (B - A + 1)) * (B - A + 1) = ε := div_mul_cancel₀ ε hC.ne'
        nlinarith [div_pos hε hC]
  have hp := intervalIntegral.continuous_primitive hif 0
  have hlim : Tendsto (fun k => ∫ x in a k..b k, f x) atTop
      (𝓝 (∫ x in a₀..b₀, f x)) := by
    have he (s t : ℝ) : (∫ x in s..t, f x) =
        (∫ x in (0 : ℝ)..t, f x) - ∫ x in (0 : ℝ)..s, f x :=
      (intervalIntegral.integral_interval_sub_left (hif 0 t) (hif 0 s)).symm
    have heq : (fun k => ∫ x in a k..b k, f x) =
        fun k => (∫ x in (0 : ℝ)..b k, f x) - ∫ x in (0 : ℝ)..a k, f x :=
      funext (fun k => he (a k) (b k))
    rw [heq, he a₀ b₀]
    exact (hp.tendsto b₀ |>.comp hb).sub (hp.tendsto a₀ |>.comp ha)
  have he (k : ℕ) : (∫ x in a k..b k, F k x) =
      (∫ x in a k..b k, F k x - f x) + ∫ x in a k..b k, f x := by
    rw [intervalIntegral.integral_sub (hiF k _ _) (hif _ _)]
    ring
  simpa only [he, zero_add] using herr.add hlim

theorem gapWeighted_weak_tendsto38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Tendsto (fun k => (2 / Real.pi) *
      ∫ x in actualGapLowerAllE02_38 (u k) n..actualGapUpperAllE02_38 (u k) n,
        W (2 * x) * actualGapHeightE02_38 (u k) x) atTop
      (𝓝 ((2 / Real.pi) *
        ∫ x in actualGapLowerAllE02_38 u₀ n..actualGapUpperAllE02_38 u₀ n,
          W (2 * x) * actualGapHeightE02_38 u₀ x)) := by
  have hc (v : PhysicalL2) : Continuous (fun x => W (2 * x) * actualGapHeightE02_38 v x) :=
    (hW.comp (continuous_const.mul continuous_id)).mul (continuous_actualGapHeightE02_38 v)
  have _hi (v : PhysicalL2) (s t : ℝ) := gapWeighted_intervalIntegrable38 v W hW s t
  exact (intervalIntegral_tendsto_of_uniform38 _ _ (fun k => hc (u k)) (hc u₀)
    (gapWeighted_uniform_weak38 u u₀ hw W hW) _ _ _ _
    (gapEndpoints_weak_tendsto38 u u₀ hw n).1
    (gapEndpoints_weak_tendsto38 u u₀ hw n).2).const_mul (2 / Real.pi)

end
end NlsGge.GK38
