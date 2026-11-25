import NlsGge.GK38.GradTauGammaComponents
import NlsGge.GK38.GradTauGammaCommonQuotient

/-! Book I.12 Lemma12.4: actual full complex L2 tau and squared-gap gradients
have one common locally uniform fixed-time square-sequence bound. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aTau_center_bound38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    ‖tauN φ n - C n‖ ≤ R n := by
  obtain ⟨c, N, hg, hs⟩ := hf
  have hm := mem_ball_iff_norm.mp ((hs.1 n).1 (left_mem_segment ℝ _ _))
  have hp := mem_ball_iff_norm.mp ((hs.1 n).1 (right_mem_segment ℝ _ _))
  have he : tauN φ n - C n = ((lamPlus φ n - C n) + (lamMinus φ n - C n)) / 2 := by
    rw [tauN_value38 φ hφ n]
    ring
  rw [he, norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  exact (norm_add_le _ _).trans (by linarith)

theorem k4aContour_center_bound38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (z : ℂ) (hz : z ∈ sphere (C n) (R n)) :
    ‖z - tauN φ n‖ ≤ 2 * R n := by
  have he : z - tauN φ n = (z - C n) - (tauN φ n - C n) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by
    rw [mem_sphere_iff_norm.mp hz]
    linarith [k4aTau_center_bound38 φ hφ C R hf n])

theorem tauGamma_gradient_l2 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ U ⊆ gkW ∧ IsOpen U ∧
      ∃ B : ℝ, 0 < B ∧ ∀ φ : PotPair, φ ∈ U → ∀ t : Icc (0 : ℝ) 1,
        k1SquareBound38 (fun n : ℤ => pairPointMass38 (gradTau38 φ n t)) B ∧
        k1SquareBound38 (fun n : ℤ => pairPointMass38 (gradGamma2_38 φ n t)) B := by
  obtain ⟨U₀, hU₀, hUW, hUo, C, R, K, hK, hcommon⟩ := k4aCommonCircleQuotient38 φ₀ hφ₀
  let R₀ : ℝ := ‖φ₀‖ + 1
  obtain ⟨Bt, hBt, ht⟩ := k4aWeightedDiscrimContourMass38 R₀ K K K hK.le hK.le
  obtain ⟨Bg, hBg, hg⟩ := k4aWeightedDiscrimContourMass38 R₀ K K (2 * K ^ 2) hK.le (by positivity)
  let B : ℝ := Bt + 64 * Bg + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨U₀ ∩ ball φ₀ 1, inter_mem hU₀ (ball_mem_nhds φ₀ zero_lt_one),
    fun φ hφ => hUW hφ.1, hUo.inter isOpen_ball, B, hB, ?_⟩
  intro φ hφ t
  have hφW := hUW hφ.1
  obtain ⟨hf, hb⟩ := hcommon φ hφ.1
  have hφR : ‖φ‖ ≤ R₀ := by
    have hd := (mem_ball_iff_norm.mp hφ.2).le
    have hn := norm_add_le (φ - φ₀) φ₀
    rw [sub_add_cancel] at hn
    dsimp [R₀]
    linarith
  have hρ (n : ℤ) : 0 < R n ∧ R n ≤ K := ⟨isolating_radius_pos38 hf n, (hb n).1⟩
  have hshift (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) :
      ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ K := ((hb n).2 z hz).1
  have hratio (n : ℤ) : ContinuousOn (fun z => discrim φ z / perChar φ z) (sphere (C n) (R n)) :=
    ((analyticOnNhd_discrim_z φ).continuousOn.mono (subset_univ _)).div
      ((analyticOnNhd_perChar_z φ).continuousOn.mono (subset_univ _))
      (isolating_periodic_boundary38 hf n)
  have hratioK (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) :
      ‖discrim φ z / perChar φ z‖ ≤ K := ((hb n).2 z hz).2.2
  have hgammaK (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) :
      ‖(z - tauN φ n) * (discrim φ z / perChar φ z)‖ ≤ 2 * K ^ 2 := by
    rw [norm_mul]
    have hc : ‖z - tauN φ n‖ ≤ 2 * K :=
      (k4aContour_center_bound38 φ hφW C R hf n z hz).trans (by linarith [(hb n).1])
    calc
      _ ≤ (2 * K) * K := mul_le_mul hc (hratioK n z hz) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hτ := ht φ hφR C R hρ hshift (fun _ z => discrim φ z / perChar φ z) hratio hratioK t
  have hγ := hg φ hφR C R hρ hshift
    (fun n z => (z - tauN φ n) * (discrim φ z / perChar φ z))
    (fun n => (continuousOn_id.sub continuousOn_const).mul (hratio n)) hgammaK t
  have hBtB : Bt ≤ B := by dsimp [B]; nlinarith
  have hBgB : 64 * Bg ≤ B := by dsimp [B]; nlinarith
  constructor
  · apply k1SquareBound38_of_finite (fun n => pairPointMass38_nonneg _)
    intro T
    calc
      _ = ∑ n ∈ T, pairPointMass38 (k4aDiscrimContourVec38 φ
          (fun z => discrim φ z / perChar φ z) (C n) (R n) t) :=
        Finset.sum_congr rfl fun n _ => k4aTau_gradient_mass_eq38 φ hφW C R hf n t
      _ ≤ Bt := hτ.1 T
      _ ≤ B := hBtB
  · apply k1SquareBound38_of_finite (fun n => pairPointMass38_nonneg _)
    intro T
    calc
      _ = 64 * ∑ n ∈ T, pairPointMass38 (k4aDiscrimContourVec38 φ
          (fun z => (z - tauN φ n) * (discrim φ z / perChar φ z)) (C n) (R n) t) := by
        simp only [k4aGamma_gradient_mass_eq38 φ hφW C R hf, Finset.mul_sum]
      _ ≤ 64 * Bg := mul_le_mul_of_nonneg_left (hγ.1 T) (by norm_num)
      _ ≤ B := hBgB

end
end NlsGge.GK38
