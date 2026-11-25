import NlsGge.GK38.AbelianCompactPeriodEstimates
import NlsGge.GK38.AbelianQuantitativeInteriorZero
import NlsGge.GK38.AbelianActualBoundedInverseTube
import Mathlib.Topology.MetricSpace.Thickening

/-! Common INTERIOR complex level lifting on the genuine full real gap cube. The
signed operator limit is explicit until its separately authored concrete
proof is compiled. Literal padded base levels include the missing coordinate. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
open scoped NNReal
namespace NlsGge.GK38
noncomputable section

theorem p6FullGap_common_interior_complex_level_lifts_of_signed_limit38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| →
        ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
          p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ r δ B : ℝ, 0 < r ∧ 0 < δ ∧ 0 < B ∧ ball (realSlice u) δ ⊆ gkW ∧
      ∀ b ∈ p6RealInclude38 '' p5FullRealGapCube38 u,
        ∀ φ ∈ ball (realSlice u) δ, ∀ n : ℤ,
          ∃ x : Lib.L2Seq, x ∈ closedBall b (r/2) ∧
            p6PaddedFn38 n (φ,x)=p6PaddedFn38 n (realSlice u,b) ∧
            (∀ y ∈ closedBall b r,
              p6PaddedFn38 n (φ,y)=p6PaddedFn38 n (realSlice u,b) → y=x) ∧
            ∀ y ∈ closedBall b r, (p6PaddedJacobian38 n φ y).IsInvertible ∧
              ‖(p6PaddedJacobian38 n φ y).inverse‖ ≤ B := by
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K := (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  obtain ⟨B,U,V,hB,hU,hV,hφU,_hUW,hKV,hInv⟩ :=
    p6FullGap_complex_uniform_inverse_bound_tube_of_signed_limit38 u C R hfam hlimit
  obtain ⟨v,hv,hvV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨p,hp,hpU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hφU)
  let c : ℝ≥0 := ⟨B⁻¹/2,by positivity⟩
  have hc : 0 < c := by change 0 < B⁻¹/2; positivity
  have hcgap : (c : ℝ) < B⁻¹ := by
    change B⁻¹/2 < B⁻¹
    exact half_lt_self (inv_pos.mpr hB)
  obtain ⟨a,M,ha,hM,hW,hest⟩ :=
    p6PaddedFn_compact_common_estimates38 (realSlice u) (realSlice_mem_gkW u) K hK c hc
  let r : ℝ := min a v
  have hr : 0 < r := lt_min ha hv
  have hra : r ≤ a := min_le_left _ _
  have hrv : r ≤ v := min_le_right _ _
  have htarget : 0 < (B⁻¹-(c : ℝ))*(r/2) := mul_pos (sub_pos.mpr hcgap) (half_pos hr)
  have hMp : 0 < M+1 := by linarith
  let δ : ℝ := min r (min p (((B⁻¹-(c : ℝ))*(r/2))/(M+1)))
  have hδ : 0 < δ := lt_min hr (lt_min hp (div_pos htarget hMp))
  have hδr : δ ≤ r := min_le_left _ _
  have hδp : δ ≤ p := (min_le_right _ _).trans (min_le_left _ _)
  have hδbound : δ ≤ ((B⁻¹-(c : ℝ))*(r/2))/(M+1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,δ,B,hr,hδ,hB,(ball_subset_ball (hδr.trans hra)).trans hW,?_⟩
  intro b hb φ hφ n
  have hφa : φ ∈ ball (realSlice u) a := ball_subset_ball (hδr.trans hra) hφ
  obtain ⟨hAa,hres⟩ := hest b hb φ hφa n
  have hA := hAa.mono_set (closedBall_subset_closedBall hra)
  obtain ⟨hT,hTbound⟩ := hInv (realSlice u) hφU b (hKV hb) n
  obtain ⟨e,he⟩ := hT
  have heB : ‖(e.symm : Lib.L2Seq →L[ℂ] Lib.L2Seq)‖ ≤ B := by
    simpa only [← he,ContinuousLinearMap.inverse_equiv] using hTbound
  have hsmall : ‖p6PaddedFn38 n (φ,b)-p6PaddedFn38 n (realSlice u,b)‖ ≤
      (B⁻¹-(c : ℝ))*(r/2) := by
    have hd : ‖φ-realSlice u‖ < ((B⁻¹-(c : ℝ))*(r/2))/(M+1) :=
      (mem_ball_iff_norm.mp hφ).trans_le hδbound
    have hh := (lt_div_iff₀ hMp).mp hd
    have hMle : M*‖φ-realSlice u‖ ≤ ‖φ-realSlice u‖*(M+1) := by
      nlinarith [norm_nonneg (φ-realSlice u)]
    exact hres.trans ((hMle.trans_lt hh).le)
  let f : Lib.L2Seq → Lib.L2Seq := fun x =>
    p6PaddedFn38 n (φ,x)-p6PaddedFn38 n (realSlice u,b)
  have hf : ApproximatesLinearOn f (e : Lib.L2Seq →L[ℂ] Lib.L2Seq) (closedBall b r) c := by
    intro x hx y hy
    have h := hA x hx y hy
    rw [← he] at h
    convert h using 1 <;> congr 1 <;> dsimp [f] <;> abel
  obtain ⟨x,hx,hfx,hunique⟩ :=
    P6QuantitativeInverse.exists_interior_zero_unique_on_closedBall
      f e b r B c hr hB heB hcgap hf hsmall
  refine ⟨x,hx,sub_eq_zero.mp hfx,?_,?_⟩
  · intro y hy hfy
    exact hunique y hy (sub_eq_zero.mpr hfy)
  · intro y hy
    have hyv : y ∈ closedBall b v := closedBall_subset_closedBall hrv hy
    exact hInv φ (hpU (ball_subset_ball hδp hφ)) y
      (hvV (closedBall_subset_cthickening hb v hyv)) n

end
end NlsGge.GK38
