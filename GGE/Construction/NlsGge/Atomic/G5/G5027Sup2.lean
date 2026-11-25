import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Endpoint

                                                                                       
                                                                                        
                                                                                                                         
                                                                                                                  
                                                                                                                               
                                                                                                                                    
                                                                                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5027Aux
noncomputable section
open G3024Endpoint

/-- The delta-fixed root with explicit rotation `c`. -/
def tipRoot (n : ℤ) (b : PotPair → ℂ) (c : ℂ) (φ : PotPair) : ℂ :=
  antiDiscrim φ (muSeq φ n) /
    (2 * Complex.I * rootProduct n (φ, muSeq φ n) * G3014Aux.sqrtB c (muSeq φ n - b φ))

/-- The joint integrand factor. -/
def tipG (p n : ℤ) (b : PotPair → ℂ) (c : ℂ) (q : PotPair × ℂ) : ℂ :=
  psi p q.1 q.2 / (2 * Complex.I * rootProduct n q * G3014Aux.sqrtB c (q.2 - b q.1))

theorem roots_explicit (n : ℤ) (V : Set PotPair) (a b : PotPair → ℂ) (hVo : IsOpen V)
    (hVsub : V ⊆ sourceW \ collapsedSet n)
    (haA : AnalyticOnNhd ℂ a V) (hbA : AnalyticOnNhd ℂ b V)
    (hVp : ∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n} ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖gap φ n‖ / 3 ≤ ‖a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ‖)
    (φ0 : PotPair) (hφ0 : φ0 ∈ V) :
    ∃ U : Set PotPair, ∃ c : ℂ, c ≠ 0 ∧ IsOpen U ∧ φ0 ∈ U ∧ U ⊆ V ∧
      AnalyticOnNhd ℂ (tipRoot n b c) U ∧
      ∀ φ ∈ U, tipRoot n b c φ ^ 2 = muSeq φ n - a φ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, c * (a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ) ∈ Complex.slitPlane := by
  classical
  have hgk : ∀ φ ∈ V, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hVsub hφ).1
  have hμA : ∀ φ ∈ V, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ :=
    fun φ hφ => (analyticOnNhd_muSeq_complex38 n) φ (hgk φ hφ)
  have hgap : ∀ φ ∈ V, gap φ n ≠ 0 := fun φ hφ => gap_ne n φ (hVsub hφ)
  have hG : ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ ≠ 0 := by
    intro φ hφ t ht h
    have hb := (hVp φ hφ).2 t ht
    rw [h, norm_zero] at hb
    have : 0 < ‖gap φ n‖ := norm_pos_iff.2 (hgap φ hφ)
    linarith
  have hdom : ∀ φ ∈ V, (φ, muSeq φ n) ∈ a5OmittedRootDomain38 n := fun φ hφ =>
    ⟨hgk φ hφ, G3014Aux.avoids_other φ (hgk φ hφ) n⟩
  have hrPJ : AnalyticOnNhd ℂ (rootProduct n) (a5OmittedRootDomain38 n) := (G2_021 n).2.1
  have hrPN : ∀ p ∈ a5OmittedRootDomain38 n, rootProduct n p ≠ 0 := (G2_021 n).2.2
  set G : PotPair → ℝ → ℂ := fun φ t => a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ with hGdef
  have hG0 : ∀ φ ∈ V, a φ - b φ ≠ 0 := by
    intro φ hφ h
    exact hG φ hφ 0 ⟨le_rfl, zero_le_one⟩ (by simpa using h)
  have hG1 : ∀ φ ∈ V, muSeq φ n - b φ ≠ 0 := by
    intro φ hφ h
    exact hG φ hφ 1 ⟨zero_le_one, le_rfl⟩ (by simpa using h)
  obtain ⟨c, hc0, hcr0, hcr1⟩ := G3014Aux.exists_pos_rot (a φ0 - b φ0) (muSeq φ0 n - b φ0)
    (hG0 φ0 hφ0) (hG1 φ0 hφ0) (by
      intro t ht h
      apply hG φ0 hφ0 t ht
      rw [← h]; ring)
  have hAc : ∀ φ ∈ V, AnalyticAt ℂ a φ := fun φ hφ => haA φ hφ
  have hBc : ∀ φ ∈ V, AnalyticAt ℂ b φ := fun φ hφ => hbA φ hφ
  have hV0 : V ∈ 𝓝 φ0 := hVo.mem_nhds hφ0
  have hcont_re : ∀ (f : PotPair → ℂ), ContinuousAt f φ0 → ∀ (k : ℂ), 0 < (k * f φ0).re →
      ∀ᶠ φ in 𝓝 φ0, 0 < (k * f φ).re := by
    intro f hf k hk
    have : ContinuousAt (fun φ => (k * f φ).re) φ0 :=
      Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hf)
    exact this.eventually (lt_mem_nhds hk)
  have hAcont : ContinuousAt (fun φ => a φ - b φ) φ0 :=
    ((hAc φ0 hφ0).continuousAt).sub (hBc φ0 hφ0).continuousAt
  have hBcont : ContinuousAt (fun φ => muSeq φ n - b φ) φ0 :=
    (hμA φ0 hφ0).continuousAt.sub (hBc φ0 hφ0).continuousAt
  have ev0 := hcont_re _ hAcont c hcr0
  have ev1 := hcont_re _ hBcont c hcr1
  have hgood : ∀ φ ∈ V, 0 < (c * (a φ - b φ)).re → 0 < (c * (muSeq φ n - b φ)).re →
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < (c * G φ t).re := by
    intro φ hφ h0 h1 t ht
    have e : c * G φ t = ((1 - t : ℝ) : ℂ) * (c * (a φ - b φ)) +
        (t : ℂ) * (c * (muSeq φ n - b φ)) := by
      simp only [hGdef]; push_cast; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rcases ht with ⟨ht0, ht1⟩
    rcases lt_or_eq_of_le ht1 with h | h
    · nlinarith [mul_pos (sub_pos.2 h) h0, mul_nonneg ht0 h1.le]
    · rw [h]; simpa using h1
  have hev : ∀ᶠ φ in 𝓝 φ0, φ ∈ V ∧ 0 < (c * (a φ - b φ)).re ∧ 0 < (c * (muSeq φ n - b φ)).re := by
    filter_upwards [hV0, ev0, ev1] with φ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨U, hUsub, hUopen, hφ0U⟩ := _root_.mem_nhds_iff.1 hev
  have hUV : U ⊆ V := fun φ hφ => (hUsub hφ).1
  have hGslit : ∀ φ ∈ U, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → c * G φ t ∈ Complex.slitPlane := by
    intro φ hφ t ht
    obtain ⟨hφV, h0, h1⟩ := hUsub hφ
    exact Complex.mem_slitPlane_iff.2 (Or.inl (hgood φ hφV h0 h1 t ht))
  have hGan : ∀ t : ℝ, ∀ φ ∈ V, AnalyticAt ℂ (fun ψ => G ψ t) φ := by
    intro t φ hφ
    simp only [hGdef]
    exact ((hAc φ hφ).add (analyticAt_const.mul ((hμA φ hφ).sub (hAc φ hφ)))).sub (hBc φ hφ)
  -- the explicit delta-fixed root
  have hs1 : ∀ φ ∈ U, c * (muSeq φ n - b φ) ∈ Complex.slitPlane := by
    intro φ hφ
    have h := hGslit φ hφ 1 ⟨zero_le_one, le_rfl⟩
    have e : G φ 1 = muSeq φ n - b φ := by simp only [hGdef]; push_cast; ring
    rw [e] at h
    exact h
  have hS1ne : ∀ φ ∈ V, G3014Aux.sqrtB c (muSeq φ n - b φ) ≠ 0 := fun φ hφ =>
    G3014Aux.sqrtB_ne hc0 (hG1 φ hφ)
  set D : PotPair → ℂ := fun φ =>
    2 * Complex.I * rootProduct n (φ, muSeq φ n) * G3014Aux.sqrtB c (muSeq φ n - b φ) with hD
  have hDne : ∀ φ ∈ V, D φ ≠ 0 := by
    intro φ hφ
    have hrp0 : rootProduct n (φ, muSeq φ n) ≠ 0 := hrPN _ (hdom φ hφ)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hrp0) (hS1ne φ hφ)
  have hsw : ∀ φ ∈ V, (muSeq φ n - a φ) * (muSeq φ n - b φ) =
      (muSeq φ n - lamMinus φ n) * (muSeq φ n - lamPlus φ n) := by
    intro φ hφ
    rcases Set.pair_eq_pair_iff.1 (hVp φ hφ).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ring
  have hI : (2 * Complex.I) ^ 2 = -4 := by
    rw [mul_pow, Complex.I_sq]; norm_num
  have hDsq : ∀ φ ∈ V, D φ ^ 2 =
      -4 * rootProduct n (φ, muSeq φ n) ^ 2 * (muSeq φ n - b φ) := by
    intro φ hφ
    have hex : D φ ^ 2 = (2 * Complex.I) ^ 2 * rootProduct n (φ, muSeq φ n) ^ 2 *
        G3014Aux.sqrtB c (muSeq φ n - b φ) ^ 2 := by simp only [hD]; ring
    rw [hex, hI, G3014Aux.sqrtB_sq hc0]
  have hAD : ∀ φ ∈ V, antiDiscrim φ (muSeq φ n) ^ 2 = (muSeq φ n - a φ) * D φ ^ 2 := by
    intro φ hφ
    rw [anti_sq n φ (hgk φ hφ), hDsq φ hφ]
    have := hsw φ hφ
    linear_combination (4 * rootProduct n (φ, muSeq φ n) ^ 2) * this
  have hrωsq : ∀ φ ∈ V, tipRoot n b c φ ^ 2 = muSeq φ n - a φ := by
    intro φ hφ
    have hd2 : D φ ^ 2 ≠ 0 := pow_ne_zero 2 (hDne φ hφ)
    show (antiDiscrim φ (muSeq φ n) / D φ) ^ 2 = _
    rw [div_pow, hAD φ hφ]
    exact mul_div_cancel_right₀ _ hd2
  have hμ' : ∀ φ ∈ V, AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ := fun φ hφ =>
    (analyticAt_id (𝕜 := ℂ)).prod (hμA φ hφ)
  refine ⟨U, c, hc0, hUopen, hφ0U, hUV, ?_, fun φ hφ => ⟨hrωsq φ (hUV hφ), fun t ht => hGslit φ hφ t ht⟩⟩
  intro φ hφ
  have hφV := hUV hφ
  have hanti : AnalyticAt ℂ (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ n)) φ :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (analyticOnNhd_antiDiscrim (φ, muSeq φ n) (Set.mem_univ _)) (hμ' φ hφV)
  have hrP : AnalyticAt ℂ (fun ψ : PotPair => rootProduct n (ψ, muSeq ψ n)) φ :=
    AnalyticAt.comp (g := rootProduct n) (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (hrPJ _ (hdom φ hφV)) (hμ' φ hφV)
  have hr1 : AnalyticAt ℂ (fun ψ : PotPair => G3014Aux.sqrtB c (muSeq ψ n - b ψ)) φ :=
    G3014Aux.sqrtB_analyticAt ((hμA φ hφV).sub (hBc φ hφV)) (hs1 φ hφ)
  have hDan : AnalyticAt ℂ D φ := ((analyticAt_const.mul hrP).mul hr1)
  exact hanti.div hDan (hDne φ hφV)

theorem mem_disc_of_pair (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (a b : ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ n, lamPlus φ n}) :
    a ∈ ball (discC φ n) (discR φ n) := by
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hφ
  have h : a ∈ ({lamMinus φ n, lamPlus φ n} : Set ℂ) := by rw [← hab]; simp
  rcases h with h | h
  · rw [h]; exact (hspec.1 n).1 (left_mem_segment ℝ _ _)
  · rw [h]; exact (hspec.1 n).1 (right_mem_segment ℝ _ _)

theorem tipG_analyticAt (p n : ℤ) (b : PotPair → ℂ) (c : ℂ) (hc : c ≠ 0) (φ : PotPair) (z : ℂ)
    (hφ : φ ∈ sourceW) (hz : z ∈ ball (discC φ n) (discR φ n)) (hb : AnalyticAt ℂ b φ)
    (hs : c * (z - b φ) ∈ Complex.slitPlane) (hzb : z - b φ ≠ 0) :
    AnalyticAt ℂ (tipG p n b c) (φ, z) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hdom : (φ, z) ∈ a5OmittedRootDomain38 n :=
    ⟨hgk, fun k hk => closedBall_avoids_other_gaps φ hgk n k hk z (ball_subset_closedBall hz)⟩
  have hψ : AnalyticAt ℂ (fun q : PotPair × ℂ => psi p q.1 q.2) (φ, z) :=
    (G2_075.2.2.2.1 p) (φ, z) ⟨hφ, mem_univ _⟩
  have hrP : AnalyticAt ℂ (rootProduct n) (φ, z) := (G2_021 n).2.1 _ hdom
  have hbq : AnalyticAt ℂ (fun q : PotPair × ℂ => b q.1) (φ, z) :=
    AnalyticAt.comp (g := b) (f := fun q : PotPair × ℂ => q.1) hb analyticAt_fst
  have hS : AnalyticAt ℂ (fun q : PotPair × ℂ => G3014Aux.sqrtB c (q.2 - b q.1)) (φ, z) :=
    G3014Aux.sqrtB_analyticAt (h := fun q : PotPair × ℂ => q.2 - b q.1) (analyticAt_snd.sub hbq) hs
  have hden : 2 * Complex.I * rootProduct n (φ, z) * G3014Aux.sqrtB c (z - b φ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) ((G2_021 n).2.2 _ hdom))
      (G3014Aux.sqrtB_ne hc hzb)
  exact hψ.div ((analyticAt_const.mul hrP).mul hS) hden

theorem a_eq_mu_of_lower (n : ℤ) (φ : PotPair) (a b : ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ n, lamPlus φ n})
    (hsep : ‖gap φ n‖ / 3 ≤ ‖a + ((1 : ℝ) : ℂ) * (muSeq φ n - a) - b‖) (hgap : gap φ n ≠ 0)
    (hμ : muSeq φ n = lamMinus φ n) : a = muSeq φ n := by
  have hmb : muSeq φ n ≠ b := by
    intro h
    have e : a + ((1 : ℝ) : ℂ) * (muSeq φ n - a) - b = 0 := by rw [← h]; push_cast; ring
    rw [e, norm_zero] at hsep
    have : 0 < ‖gap φ n‖ := norm_pos_iff.2 hgap
    linarith
  have hmem : muSeq φ n ∈ ({a, b} : Set ℂ) := by rw [hab, hμ]; simp
  rcases hmem with h | h
  · exact h.symm
  · exact absurd h hmb

end
end G5027Aux
end NlsGge.GKDefinitionDesign
