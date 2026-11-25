import Mathlib
import NlsGge.GK38.XiSqCenteredKernel
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.IsolatingTopology

                                                                                                                                                                                                  
                                                                                                          
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G2032B1
noncomputable section

def jk (c h u : ℂ) : ℂ := c + h * (u + u⁻¹)

theorem re_ratio_pos (x : ℂ) (hx : 1 < ‖x‖) : 0 < ((x - 1) / (x + 1)).re := by
  have hne : x + 1 ≠ 0 := by
    intro h
    have : x = -1 := by linear_combination h
    rw [this] at hx; simp at hx
  have hn0 : 0 < Complex.normSq (x + 1) := Complex.normSq_pos.2 hne
  have hsq : 1 < Complex.normSq x := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  rw [Complex.div_re, ← add_div]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im]
  rw [Complex.normSq_apply] at hsq
  refine div_pos ?_ hn0
  nlinarith

theorem inv_facts (u : ℂ) (hu : 1 < ‖u‖) :
    u ≠ 0 ∧ u + u⁻¹ ≠ 0 ∧ u - u⁻¹ ≠ 0 ∧ (u + u⁻¹) ^ 2 - (u - u⁻¹) ^ 2 = 4 := by
  have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; linarith
  have hu2 : 1 < ‖u ^ 2‖ := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have huv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  refine ⟨hu0, ?_, ?_, by linear_combination 4 * huv⟩
  · intro hs
    have : u ^ 2 = -1 := by linear_combination u * hs - huv
    rw [this] at hu2; simp at hu2
  · intro hs
    have : u ^ 2 = 1 := by linear_combination u * hs + huv
    rw [this] at hu2; simp at hu2

theorem sqrt_sq_of_re_pos (s : ℂ) (hs : 0 < s.re) : Complex.sqrt (s ^ 2) = s := by
  have h1 : Complex.sqrt (s ^ 2) ^ 2 = s ^ 2 := Lib.sqrt_sq _
  have hre0 := Lib.re_sqrt_nonneg (s ^ 2)
  have hfac : (Complex.sqrt (s ^ 2) - s) * (Complex.sqrt (s ^ 2) + s) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have : Complex.sqrt (s ^ 2) = -s := by linear_combination h2
    rw [this] at hre0
    simp only [Complex.neg_re] at hre0
    linarith

theorem sqrt_joukowski (h u : ℂ) (hh : h ≠ 0) (hu : 1 < ‖u‖) :
    Complex.sqrt (1 - (16 * h ^ 2 / 4) / (-(h * (u + u⁻¹))) ^ 2) = (u - u⁻¹) / (u + u⁻¹) := by
  obtain ⟨hu0, hA, hB, hAB⟩ := inv_facts u hu
  have hu2 : 1 < ‖u ^ 2‖ := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have huv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  have hs : (u - u⁻¹) / (u + u⁻¹) = (u ^ 2 - 1) / (u ^ 2 + 1) := by
    rw [show u ^ 2 - 1 = u * (u - u⁻¹) by linear_combination huv,
      show u ^ 2 + 1 = u * (u + u⁻¹) by linear_combination (-1 : ℂ) * huv, mul_div_mul_left _ _ hu0]
  have hre : 0 < ((u - u⁻¹) / (u + u⁻¹)).re := by rw [hs]; exact re_ratio_pos _ hu2
  have hsq : 1 - (16 * h ^ 2 / 4) / (-(h * (u + u⁻¹))) ^ 2 = ((u - u⁻¹) / (u + u⁻¹)) ^ 2 := by
    have e1 : (16 * h ^ 2 / 4) / (-(h * (u + u⁻¹))) ^ 2 = 4 / (u + u⁻¹) ^ 2 := by
      rw [show (-(h * (u + u⁻¹))) ^ 2 = h ^ 2 * (u + u⁻¹) ^ 2 by ring]
      field_simp
      ring
    rw [e1, div_pow, eq_div_iff (pow_ne_zero 2 hA), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hA)]
    linear_combination hAB
  rw [hsq]
  exact sqrt_sq_of_re_pos _ hre

theorem kernel_algebra (h u χ L : ℂ) (hh : h ≠ 0) (hu : 1 < ‖u‖) :
    (Complex.I * χ * L) / (4 * (-(h * (u + u⁻¹))) ^ 2 * ((u - u⁻¹) / (u + u⁻¹)) *
      (1 + (u - u⁻¹) / (u + u⁻¹))) * (h * (1 - (u ^ 2)⁻¹)) =
      Complex.I * χ * L / (8 * h * u ^ 2) := by
  obtain ⟨hu0, hA, hB, hAB⟩ := inv_facts u hu
  have huv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  rw [show (u ^ 2)⁻¹ = u⁻¹ * u⁻¹ by rw [sq, mul_inv]]
  generalize u⁻¹ = v at *
  have hq1 : 1 + (u - v) / (u + v) = 2 * u / (u + v) := by
    rw [one_add_div hA]; congr 1; ring
  have hden : 4 * (-(h * (u + v))) ^ 2 * ((u - v) / (u + v)) * (2 * u / (u + v)) =
      8 * h ^ 2 * u * (u - v) := by
    field_simp
    ring
  have h1 : 1 - v * v = (u - v) / u := by
    rw [eq_div_iff hu0]
    linear_combination (-v) * huv
  rw [hq1, hden, h1]
  field_simp


theorem kernel_joukowski (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hgap : lamPlus φ n ≠ lamMinus φ n) (u : ℂ) (hu : 1 < ‖u‖) :
    a5CenteredKernel38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
        (((lamPlus φ n - lamMinus φ n) / 4) * (1 - (u ^ 2)⁻¹)) =
      Complex.I * a5Chi38 n (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) *
          (lamDot φ n - jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) /
        (8 * ((lamPlus φ n - lamMinus φ n) / 4) * u ^ 2) := by
  set h : ℂ := (lamPlus φ n - lamMinus φ n) / 4 with hh
  have hh0 : h ≠ 0 := by
    rw [hh]; exact div_ne_zero (sub_ne_zero.2 hgap) (by norm_num)
  have hg2 : gamma2 φ n = 16 * h ^ 2 := by rw [gamma2_value38 φ hφ n, hh]; ring
  have hz : tauN φ n - jk (tauN φ n) h u = -(h * (u + u⁻¹)) := by unfold jk; ring
  have hA := a5CriticalA_identity38 n φ hφ
  have hlin : (tauN φ n - jk (tauN φ n) h u) + gamma2 φ n * a5CriticalA38 n φ =
      lamDot φ n - jk (tauN φ n) h u := by linear_combination -hA
  unfold a5CenteredKernel38 a5CenteredAnalyticTerm38 a5BoundaryQ38
  simp only
  rw [hlin, hz, hg2, sqrt_joukowski h u hh0 hu]
  have hI : -(a5Chi38 n (φ, jk (tauN φ n) h u) / Complex.I) =
      Complex.I * a5Chi38 n (φ, jk (tauN φ n) h u) := by
    field_simp
    simp
  rw [hI]
  exact kernel_algebra h u _ _ hh0 hu


theorem jk_unit_mem_segment (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (u : ℂ) (hu : ‖u‖ = 1) :
    jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  have hτ := tauN_value38 φ hφ n
  have hconj : u⁻¹ = (starRingEnd ℂ) u := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]; simp
  refine ⟨1 - (1 + u.re) / 2, (1 + u.re) / 2, ?_, ?_, by ring, ?_⟩
  · have := Complex.abs_re_le_norm u; rw [hu] at this; have := (abs_le.1 this).2; linarith
  · have := Complex.abs_re_le_norm u; rw [hu] at this; have := (abs_le.1 this).1; linarith
  · unfold jk
    rw [hτ, hconj]
    have : u + (starRingEnd ℂ) u = (2 * u.re : ℝ) := by
      apply Complex.ext <;> simp <;> ring
    rw [this]
    push_cast
    simp only [Complex.real_smul]
    push_cast
    ring

theorem H_analytic_annulus (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ u : ℂ, 1 - ε < ‖u‖ → ‖u‖ < 1 + ε →
      u ≠ 0 ∧ (φ, jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) u) ∈ a5OmittedRootDomain38 n := by
  obtain ⟨C, R, hf⟩ : ∃ C R, IsolatingFamily38 φ C R :=
    ⟨discC φ, discR φ, isolating_family38 φ hφ⟩
  obtain ⟨c0, N0, hg, hs⟩ := hf
  set J : ℂ → ℂ := jk (tauN φ n) ((lamPlus φ n - lamMinus φ n) / 4) with hJ
  have hJc : ContinuousOn J {0}ᶜ := by
    rw [hJ]; unfold jk
    exact continuousOn_const.add (continuousOn_const.mul (continuousOn_id.add continuousOn_inv₀))
  have hSo : IsOpen ({0}ᶜ ∩ J ⁻¹' ball (C n) (R n)) :=
    hJc.isOpen_inter_preimage isOpen_compl_singleton isOpen_ball
  have hK : sphere (0 : ℂ) 1 ⊆ {0}ᶜ ∩ J ⁻¹' ball (C n) (R n) := by
    intro u hu
    have hn : ‖u‖ = 1 := by simpa using hu
    refine ⟨?_, (hs.1 n).1 (jk_unit_mem_segment φ hφ n u hn)⟩
    intro h0; rw [Set.mem_singleton_iff] at h0; rw [h0] at hn; simp at hn
  obtain ⟨δ, hδ, hth⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hSo hK
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun u h1 h2 => ?_⟩
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; have := min_le_right δ 1; linarith
  have hmem : u ∈ thickening δ (sphere (0 : ℂ) 1) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(‖u‖)⁻¹ • u, ?_, ?_⟩
    · simp [norm_smul, hu0]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu0
      rw [dist_eq_norm]
      have : u - (‖u‖)⁻¹ • u = (1 - (‖u‖)⁻¹) • u := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs]
      have : |1 - (‖u‖)⁻¹| * ‖u‖ = |‖u‖ - 1| := by
        rw [show 1 - (‖u‖)⁻¹ = (‖u‖ - 1) / ‖u‖ by field_simp, abs_div, abs_of_pos hpos]
        field_simp
      rw [this]
      have := min_le_left δ 1
      rw [abs_lt]; constructor <;> linarith [min_le_left δ 1]
  have hSu := hth hmem
  refine ⟨hu0, ?_⟩
  exact a5OwnClosedBall_omittedDomain38 φ hφ C R ⟨c0, N0, hg, hs⟩ n _ (ball_subset_closedBall hSu.2)

end
end G2032B1
end NlsGge.GKDefinitionDesign
