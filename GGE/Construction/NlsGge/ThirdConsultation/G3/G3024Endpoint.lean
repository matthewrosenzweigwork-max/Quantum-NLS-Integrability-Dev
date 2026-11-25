import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Transport
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.ThirdConsultation.G3.G3006Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G2.RootProductSq
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G3.G3005
import NlsGge.Atomic.G3.G3013
import NlsGge.Atomic.G3.G3014
import NlsGge.Atomic.G4.G4012

                                                                                                                       
                                                                                                                       
                                                                                                                         
                                                                                                                         
                                                                        
                                                                                               
                                                                                                              
                                                                                                                               
                                                                             
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3024Endpoint
noncomputable section

/-- `antiDiscrim(mu)^2 = -4 (mu - lam-)(mu - lam+) rootProduct^2` (no nonvanishing needed). -/
theorem anti_sq (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    antiDiscrim φ (muSeq φ n) ^ 2 =
      -4 * ((muSeq φ n - lamMinus φ n) * (muSeq φ n - lamPlus φ n)) *
        rootProduct n (φ, muSeq φ n) ^ 2 := by
  have hrp := rootProduct_sq_identity n φ hφ (muSeq φ n) (G3014Aux.avoids_other φ hφ n)
  have hA := dirichlet_perChar_eq_anti_sq38 φ (muSeq φ n) (muSeq_root38 φ n)
  rw [← hA, hrp]

/-- M1 without the hypothesis `rw ≠ 0`: when `rw = 0` the segment is degenerate (`mu = a`) and `Z+ = b - a`. -/
theorem seg_exp_any (n : ℤ) (phi : PotPair) (hphi : phi ∈ sourceW)
    (hgam : lamPlus phi n - lamMinus phi n ≠ 0) (a b rw : ℂ) (rs : ℝ → ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus phi n, lamPlus phi n})
    (hwsq : rw ^ 2 = muSeq phi n - a)
    (hc : ContinuousOn rs (Icc (0 : ℝ) 1)) (h0 : ∀ t ∈ Icc (0 : ℝ) 1, rs t ≠ 0)
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, rs t ^ 2 = a + (t : ℂ) * (muSeq phi n - a) - b)
    (hsign : 2 * Complex.I * rootProduct n (phi, muSeq phi n) * rw * rs 1 =
      antiDiscrim phi (muSeq phi n))
    (hint : IntervalIntegrable (fun t : ℝ =>
      (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
        (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
        (Real.sqrt t : ℂ)) volume 0 1) :
    gk16ActualScalarZPlus38 sourceF n phi = (b - a) * Complex.exp (Complex.I *
      ∫ t in (0 : ℝ)..1,
        (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
          (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
          (Real.sqrt t : ℂ)) := by
  by_cases hw0 : rw = 0
  · have hgk : phi ∈ gkW := sourceFamily.W_gk hphi
    have hμa : muSeq phi n = a := by
      have h := hwsq
      rw [hw0] at h
      linear_combination -h
    have hsum : a + b = lamMinus phi n + lamPlus phi n := (G3024Transport.pair_sum n phi a b hab).1
    have hH : gk16TerminalRoot38 n phi = 0 := by
      unfold gk16TerminalRoot38
      rw [← hsign, hw0]
      simp
    have hI : (∫ t in (0 : ℝ)..1,
        (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
          (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
          (Real.sqrt t : ℂ)) = 0 := by
      simp [hw0]
    rw [hI, mul_zero, Complex.exp_zero, mul_one]
    unfold gk16ActualScalarZPlus38
    rw [hH, tauN_value38 phi hgk n, hμa]
    simp only [mul_zero, add_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    linear_combination (-1 : ℂ) * hsum
  · exact G3024Transport.g3024_segment_exponential n phi hphi hgam a b rw rs hab hw0 hwsq hc h0
      hsq hsign hint

/-- Analytic endpoint labels near any point of `sourceW \ collapsedSet n` (also at `endpointSet n`): the landed G3-013
`finish_core` (which does not use `mu <> lam±`) with `x` the endpoint nearest to `mu(phi0)`. -/
theorem labels_any (n : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW \ collapsedSet n) :
    ∃ V : Set PotPair, ∃ a b : PotPair → ℂ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW \ collapsedSet n ∧
      AnalyticOnNhd ℂ a V ∧ AnalyticOnNhd ℂ b V ∧
      ∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖gap φ n‖ / 3 ≤ ‖a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ‖ := by
  obtain ⟨hW, hnot⟩ := hφ0
  have hgk : φ0 ∈ gkW := sourceFamily.W_gk hW
  have hg2 : gamma2 φ0 n = (lamPlus φ0 n - lamMinus φ0 n) ^ 2 := gamma2_value38 φ0 hgk n
  have hZ : lamPlus φ0 n ≠ lamMinus φ0 n := by
    intro h
    apply hnot
    refine ⟨hW, ?_⟩
    rw [hg2, h]
    simp
  have hlab : ∃ V : Set PotPair, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ gkW ∧
      ∃ ρm ρp : PotPair → ℂ, AnalyticOnNhd ℂ ρm V ∧ AnalyticOnNhd ℂ ρp V ∧
        ∀ ψ ∈ V,
          ((ρm ψ = lamMinus ψ n ∧ ρp ψ = lamPlus ψ n) ∨
            (ρm ψ = lamPlus ψ n ∧ ρp ψ = lamMinus ψ n)) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            ‖lamPlus ψ n - lamMinus ψ n‖ / 3 ≤
              ‖ρp ψ - ((t : ℂ) * muSeq ψ n + (1 - (t : ℂ)) * ρm ψ)‖ := by
    obtain ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ := hgk
    have hRpos : ∀ k, 0 < R k := fun k => (hg.1 k).1
    have ha : lamMinus φ0 n ∈ ball (C n) (R n) :=
      ((hspec φ0 hmem).1 n).1 (left_mem_segment ℝ _ _)
    have hb : lamPlus φ0 n ∈ ball (C n) (R n) :=
      ((hspec φ0 hmem).1 n).1 (right_mem_segment ℝ _ _)
    obtain ⟨κa, Ua, hUa, hφUa, hκa, hκa0, hra⟩ :=
      NlsGge.Atomic.G3013S3.exists_endpoint_branch φ0 ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ n hZ
        (lamMinus φ0 n) (Or.inl rfl)
    obtain ⟨κb, Ub, hUb, hφUb, hκb, hκb0, hrb⟩ :=
      NlsGge.Atomic.G3013S3.exists_endpoint_branch φ0 ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ n hZ
        (lamPlus φ0 n) (Or.inr rfl)
    have hab : lamMinus φ0 n ≠ lamPlus φ0 n := fun h => hZ h.symm
    have hVgk : ∀ ψ ∈ ball (realSlice u) ρ, ψ ∈ gkW :=
      fun ψ hψ => ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hψ⟩
    have hφ₀ : φ0 ∈ gkW := ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩
    rcases le_total ‖muSeq φ0 n - lamMinus φ0 n‖ ‖muSeq φ0 n - lamPlus φ0 n‖ with hle | hle
    · obtain ⟨V, hVo, -, h1, h2, ρm, ρp, hρm, hρp, hs⟩ :=
        NlsGge.Atomic.G3013S3.finish_core n φ0 u ρ C R hRpos hVgk hspec hmem hφ₀ _ _ hab hle ha hb
          κa κb (Ua ∩ Ub) (hUa.inter hUb) ⟨hφUa, hφUb⟩ (hκa.mono inter_subset_left)
          (hκb.mono inter_subset_right) hκa0 hκb0 (fun ψ hψ => hra ψ hψ.1)
          (fun ψ hψ => hrb ψ hψ.2)
      exact ⟨V, hVo, h1, h2, ρm, ρp, hρm, hρp, hs⟩
    · obtain ⟨V, hVo, -, h1, h2, ρm, ρp, hρm, hρp, hs⟩ :=
        NlsGge.Atomic.G3013S3.finish_core n φ0 u ρ C R hRpos hVgk hspec hmem hφ₀ _ _ hab.symm hle hb ha
          κb κa (Ub ∩ Ua) (hUb.inter hUa) ⟨hφUb, hφUa⟩ (hκb.mono inter_subset_left)
          (hκa.mono inter_subset_right) hκb0 hκa0 (fun ψ hψ => hrb ψ hψ.1)
          (fun ψ hψ => hra ψ hψ.2)
      exact ⟨V, hVo, h1, h2, ρm, ρp, hρm, hρp, hs⟩
  obtain ⟨V0, hV0o, hφV0, hV0gk, ρm, ρp, hρm, hρp, hspec⟩ := hlab
  have hcg : ContinuousAt (fun φ : PotPair => (lamPlus φ n - lamMinus φ n) ^ 2) φ0 :=
    (NlsGge.Atomic.G3012S3.gammaSq_analytic n φ0 hgk).continuousAt
  have hgne : (lamPlus φ0 n - lamMinus φ0 n) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hZ)
  have h1 : ∀ᶠ φ in 𝓝 φ0, (lamPlus φ n - lamMinus φ n) ^ 2 ≠ 0 := hcg.eventually_ne hgne
  have h3 : ∀ᶠ φ in 𝓝 φ0, φ ∈ sourceW := sourceFamily.W_open.mem_nhds hW
  have h4 : ∀ᶠ φ in 𝓝 φ0, φ ∈ V0 := hV0o.mem_nhds hφV0
  obtain ⟨V, hVsub, hVo, hφV⟩ := _root_.mem_nhds_iff.1 (h1.and (h3.and h4))
  refine ⟨V, ρm, ρp, hVo, hφV, ?_, hρm.mono fun φ hφ => (hVsub hφ).2.2,
    hρp.mono fun φ hφ => (hVsub hφ).2.2, ?_⟩
  · intro φ hφ
    obtain ⟨hg1, hW', -⟩ := hVsub hφ
    refine ⟨hW', ?_⟩
    rintro ⟨-, hz⟩
    apply hg1
    rw [← gamma2_value38 φ (sourceFamily.W_gk hW') n]
    exact hz
  · intro φ hφ
    obtain ⟨-, -, hV0'⟩ := hVsub hφ
    obtain ⟨hord, hsep⟩ := hspec φ hV0'
    refine ⟨?_, ?_⟩
    · rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Set.pair_comm]
    · intro t ht
      have := hsep t ht
      have e : ρm φ + (t : ℂ) * (muSeq φ n - ρm φ) - ρp φ =
          -(ρp φ - ((t : ℂ) * muSeq φ n + (1 - (t : ℂ)) * ρm φ)) := by ring
      rw [e, norm_neg]
      exact this


theorem gap_ne (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW \ collapsedSet n) : gap φ n ≠ 0 := by
  intro h
  apply hφ.2
  refine ⟨hφ.1, ?_⟩
  rw [gamma2_value38 φ (sourceFamily.W_gk hφ.1) n]
  have h' : lamPlus φ n - lamMinus φ n = 0 := h
  rw [h']
  simp

/-- Rotated analytic square roots of the segment and the delta-fixed root `rω` (analytic across `endpointSet n`). -/
theorem roots_any (n : ℤ) (V : Set PotPair) (a b : PotPair → ℂ) (hVo : IsOpen V)
    (hVsub : V ⊆ sourceW \ collapsedSet n)
    (haA : AnalyticOnNhd ℂ a V) (hbA : AnalyticOnNhd ℂ b V)
    (hVp : ∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n} ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖gap φ n‖ / 3 ≤ ‖a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ‖)
    (φ0 : PotPair) (hφ0 : φ0 ∈ V) :
    ∃ U : Set PotPair, ∃ rω : PotPair → ℂ, ∃ rseg : PotPair → ℝ → ℂ,
      IsOpen U ∧ φ0 ∈ U ∧ U ⊆ V ∧ AnalyticOnNhd ℂ rω U ∧
      (∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => rseg φ t) U) ∧
      ContinuousOn (fun p : PotPair × ℝ => rseg p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ φ ∈ U, rω φ ^ 2 = muSeq φ n - a φ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, rseg φ t ≠ 0 ∧
          rseg φ t ^ 2 = a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ) ∧
        2 * Complex.I * rootProduct n (φ, muSeq φ n) * rω φ * rseg φ 1 =
          antiDiscrim φ (muSeq φ n) := by
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
  set r0 : PotPair → ℝ → ℂ := fun φ t => G3014Aux.sqrtB c (G φ t) with hr0
  have hr0sq : ∀ φ ∈ V, ∀ t : ℝ, r0 φ t ^ 2 = G φ t := fun φ _ t => G3014Aux.sqrtB_sq hc0 _
  have hr0ne : ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → r0 φ t ≠ 0 := fun φ hφ t ht =>
    G3014Aux.sqrtB_ne hc0 (hG φ hφ t ht)
  have hr0an : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ φ ∈ U, AnalyticAt ℂ (fun ψ => r0 ψ t) φ :=
    fun t ht φ hφ => G3014Aux.sqrtB_analyticAt (hGan t φ (hUV hφ)) (hGslit φ hφ t ht)
  -- the delta-fixed root
  set D : PotPair → ℂ := fun φ => 2 * Complex.I * rootProduct n (φ, muSeq φ n) * r0 φ 1 with hD
  have hDne : ∀ φ ∈ V, D φ ≠ 0 := by
    intro φ hφ
    have hrp0 : rootProduct n (φ, muSeq φ n) ≠ 0 := hrPN _ (hdom φ hφ)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hrp0)
      (hr0ne φ hφ 1 ⟨zero_le_one, le_rfl⟩)
  set rω0 : PotPair → ℂ := fun φ => antiDiscrim φ (muSeq φ n) / D φ with hrω0
  have hr1sq : ∀ φ ∈ V, r0 φ 1 ^ 2 = muSeq φ n - b φ := by
    intro φ hφ
    rw [hr0sq φ hφ 1]
    simp only [hGdef]; push_cast; ring
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
        r0 φ 1 ^ 2 := by simp only [hD]; ring
    rw [hex, hI, hr1sq φ hφ]
  have hAD : ∀ φ ∈ V, antiDiscrim φ (muSeq φ n) ^ 2 = (muSeq φ n - a φ) * D φ ^ 2 := by
    intro φ hφ
    rw [anti_sq n φ (hgk φ hφ), hDsq φ hφ]
    have := hsw φ hφ
    linear_combination (4 * rootProduct n (φ, muSeq φ n) ^ 2) * this
  have hrωsq : ∀ φ ∈ V, rω0 φ ^ 2 = muSeq φ n - a φ := by
    intro φ hφ
    have hd2 : D φ ^ 2 ≠ 0 := pow_ne_zero 2 (hDne φ hφ)
    show (antiDiscrim φ (muSeq φ n) / D φ) ^ 2 = _
    rw [div_pow, hAD φ hφ]
    exact mul_div_cancel_right₀ _ hd2
  have hsign : ∀ φ ∈ V, 2 * Complex.I * rootProduct n (φ, muSeq φ n) * rω0 φ * r0 φ 1 =
      antiDiscrim φ (muSeq φ n) := by
    intro φ hφ
    have hd := hDne φ hφ
    have e : 2 * Complex.I * rootProduct n (φ, muSeq φ n) * rω0 φ * r0 φ 1 = D φ * rω0 φ := by
      simp only [hD]; ring
    rw [e]
    show D φ * (antiDiscrim φ (muSeq φ n) / D φ) = _
    field_simp
  have hμ' : ∀ φ ∈ V, AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ := fun φ hφ =>
    (analyticAt_id (𝕜 := ℂ)).prod (hμA φ hφ)
  refine ⟨U, rω0, r0, hUopen, hφ0U, hUV, ?_, fun t ht φ hφ => hr0an t ht φ hφ, ?_, ?_⟩
  · intro φ hφ
    have hφV := hUV hφ
    have hanti : AnalyticAt ℂ (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ n)) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
        (f := fun ψ : PotPair => (ψ, muSeq ψ n))
        (analyticOnNhd_antiDiscrim (φ, muSeq φ n) (Set.mem_univ _)) (hμ' φ hφV)
    have hrP : AnalyticAt ℂ (fun ψ : PotPair => rootProduct n (ψ, muSeq ψ n)) φ :=
      AnalyticAt.comp (g := rootProduct n) (f := fun ψ : PotPair => (ψ, muSeq ψ n))
        (hrPJ _ (hdom φ hφV)) (hμ' φ hφV)
    have hr1 : AnalyticAt ℂ (fun ψ : PotPair => r0 ψ 1) φ :=
      hr0an 1 ⟨zero_le_one, le_rfl⟩ φ hφ
    have hDan : AnalyticAt ℂ D φ := ((analyticAt_const.mul hrP).mul hr1)
    exact hanti.div hDan (hDne φ hφV)
  · have hGc : ContinuousOn (fun p : PotPair × ℝ => c * G p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hpV : p.1 ∈ V := hUV hp.1
      have h1 : ContinuousAt (fun q : PotPair × ℝ => a q.1) p :=
        (hAc p.1 hpV).continuousAt.comp continuousAt_fst
      have h2 : ContinuousAt (fun q : PotPair × ℝ => b q.1) p :=
        (hBc p.1 hpV).continuousAt.comp continuousAt_fst
      have h3 : ContinuousAt (fun q : PotPair × ℝ => muSeq q.1 n) p :=
        (hμA p.1 hpV).continuousAt.comp continuousAt_fst
      have h4 : ContinuousAt (fun q : PotPair × ℝ => ((q.2 : ℝ) : ℂ)) p :=
        Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
      simp only [hGdef]
      exact continuousAt_const.mul ((h1.add (h4.mul (h3.sub h1))).sub h2)
    have hcp : ContinuousOn (fun p : PotPair × ℝ => (c * G p.1 p.2) ^ (2⁻¹ : ℂ))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.cpow hGc continuousOn_const (fun p hp => hGslit p.1 hp.1 p.2 hp.2)
    simp only [hr0, G3014Aux.sqrtB]
    exact continuousOn_const.mul hcp
  · intro φ hφ
    have hφV := hUV hφ
    refine ⟨hrωsq φ hφV, fun t ht => ⟨hr0ne φ hφV t ht, ?_⟩, ?_⟩
    · rw [hr0sq φ hφV t]
    · exact hsign φ hφV

/-- Uniform bound and the pointwise exponential formula for the diagonal integrand on a small neighbourhood. -/
theorem param_data (n : ℤ) (φ0 : PotPair) (U : Set PotPair) (a b rω : PotPair → ℂ)
    (rseg : PotPair → ℝ → ℂ) (hUo : IsOpen U) (hφU : φ0 ∈ U)
    (hUsub : U ⊆ sourceW \ collapsedSet n)
    (haA : AnalyticOnNhd ℂ a U) (hbA : AnalyticOnNhd ℂ b U)
    (hUp : ∀ φ ∈ U, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n})
    (hrωA : AnalyticOnNhd ℂ rω U)
    (hrsegA : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => rseg φ t) U)
    (hrsegC : ContinuousOn (fun p : PotPair × ℝ => rseg p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1))
    (hall : ∀ φ ∈ U, rω φ ^ 2 = muSeq φ n - a φ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, rseg φ t ≠ 0 ∧
          rseg φ t ^ 2 = a φ + (t : ℂ) * (muSeq φ n - a φ) - b φ) ∧
        2 * Complex.I * rootProduct n (φ, muSeq φ n) * rω φ * rseg φ 1 =
          antiDiscrim φ (muSeq φ n)) :
    ∃ V : Set PotPair, ∃ C : ℝ, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ U ∧ 0 < C ∧
      let G : PotPair → ℝ → ℂ := fun φ t =>
        let z := a φ + (t : ℂ) * (muSeq φ n - a φ)
        psi n φ z * rω φ / (2 * Complex.I * rootProduct n (φ, z) * rseg φ t)
      (∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => G φ t) V) ∧
      (∀ φ ∈ V, ContinuousOn (G φ) (Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ ≤ C) ∧
        IntervalIntegrable (fun t => G φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
        gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
          Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, G φ t / (Real.sqrt t : ℂ))) := by
  have hUW : ∀ φ ∈ U, φ ∈ sourceW := fun φ hφ => (hUsub hφ).1
  have hUgk : ∀ φ ∈ U, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hUW φ hφ)
  have hγ : ∀ φ ∈ U, lamPlus φ n - lamMinus φ n ≠ 0 := fun φ hφ => gap_ne n φ (hUsub hφ)
  have hμA : ∀ φ ∈ U, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ := fun φ hφ =>
    analyticOnNhd_muSeq_complex38 n φ (hUgk φ hφ)
  have hpsiJ : AnalyticOnNhd ℂ (fun p : PotPair × ℂ => psi n p.1 p.2) (sourceW ×ˢ (univ : Set ℂ)) :=
    G2_075.2.2.2.1 n
  have hrPJ : AnalyticOnNhd ℂ (rootProduct n) (a5OmittedRootDomain38 n) := (G2_021 n).2.1
  have hrPN : ∀ p ∈ a5OmittedRootDomain38 n, rootProduct n p ≠ 0 := (G2_021 n).2.2
  obtain ⟨G, hG⟩ : ∃ G : PotPair → ℝ → ℂ, ∀ φ t, G φ t =
      psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t) :=
    ⟨fun φ t => psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t),
      fun _ _ => rfl⟩
  have hzball : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      a φ + (t : ℂ) * (muSeq φ n - a φ) ∈ ball (discC φ n) (discR φ n) :=
    fun φ hφ t ht => G3015Aux.seg_mem_ball n φ (hUgk φ hφ) (a φ) (b φ) (hUp φ hφ) t ht
  have hdom : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ∈ a5OmittedRootDomain38 n := fun φ hφ t ht =>
    ⟨hUgk φ hφ, fun k hk => closedBall_avoids_other_gaps φ (hUgk φ hφ) n k hk _
      (ball_subset_closedBall (hzball φ hφ t ht))⟩
  have hrP0 : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ≠ 0 := fun φ hφ t ht =>
    hrPN _ (hdom φ hφ t ht)
  have hden : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t ≠ 0 :=
    fun φ hφ t ht => mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (hrP0 φ hφ t ht)) (((hall φ hφ).2.1 t ht).1)
  -- joint continuity of G on U × [0,1]
  have hμC : ContinuousOn (fun ψ : PotPair => muSeq ψ n) U :=
    fun φ hφ => (hμA φ hφ).continuousAt.continuousWithinAt
  have hSt : ∀ p ∈ U ×ˢ Icc (0 : ℝ) 1, p.1 ∈ U := fun p hp => hp.1
  have hzzC : ContinuousOn (fun p : PotPair × ℝ => a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1))
      (U ×ˢ Icc (0 : ℝ) 1) := by
    have ha_c : ContinuousOn (fun p : PotPair × ℝ => a p.1) (U ×ˢ Icc (0 : ℝ) 1) :=
      haA.continuousOn.comp continuousOn_fst hSt
    have hm_c : ContinuousOn (fun p : PotPair × ℝ => muSeq p.1 n) (U ×ˢ Icc (0 : ℝ) 1) :=
      hμC.comp continuousOn_fst hSt
    exact ha_c.add ((Complex.continuous_ofReal.comp_continuousOn continuousOn_snd).mul
      (hm_c.sub ha_c))
  have hmaps : MapsTo (fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
      (U ×ˢ Icc (0 : ℝ) 1) (a5OmittedRootDomain38 n) := fun p hp => hdom p.1 hp.1 p.2 hp.2
  have hGc : ContinuousOn (fun p : PotPair × ℝ => G p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
    have hpsi : ContinuousOn (fun p : PotPair × ℝ =>
        psi n p.1 (a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1))) (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := fun q : PotPair × ℂ => psi n q.1 q.2)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        hpsiJ.continuousOn (continuousOn_fst.prodMk hzzC)
        (fun p hp => ⟨hUW p.1 hp.1, mem_univ _⟩)
    have hrP : ContinuousOn (fun p : PotPair × ℝ =>
        rootProduct n (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := rootProduct n)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        hrPJ.continuousOn (continuousOn_fst.prodMk hzzC) hmaps
    have hω : ContinuousOn (fun p : PotPair × ℝ => rω p.1) (U ×ˢ Icc (0 : ℝ) 1) :=
      hrωA.continuousOn.comp continuousOn_fst hSt
    have hnum := (hpsi.mul hω)
    have hc2 : ContinuousOn (fun _ : PotPair × ℝ => (2 * Complex.I)) (U ×ˢ Icc (0 : ℝ) 1) :=
      continuousOn_const
    have hdenC := ((hc2.mul hrP).mul hrsegC)
    have := hnum.div hdenC (fun p hp => hden p.1 hp.1 p.2 hp.2)
    refine this.congr (fun p _ => ?_)
    exact hG p.1 p.2
  -- uniform bound by the tube lemma
  obtain ⟨K, hK⟩ := (isCompact_singleton (x := φ0)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    |>.exists_bound_of_continuousOn (hGc.mono (by
      rintro ⟨φ, t⟩ ⟨hφ, ht⟩
      rw [mem_singleton_iff] at hφ
      subst hφ
      exact ⟨hφU, ht⟩))
  obtain ⟨cl, hcl⟩ : ∃ cl : ℝ → ℝ, cl = fun t => max 0 (min t 1) := ⟨_, rfl⟩
  have hclc : Continuous cl := by rw [hcl]; fun_prop
  have hcl_mem : ∀ t, cl t ∈ Icc (0 : ℝ) 1 := fun t => by
    rw [hcl]; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcl_id : ∀ t ∈ Icc (0 : ℝ) 1, cl t = t := fun t ht => by
    rw [hcl]; simp only [min_eq_left ht.2, max_eq_right ht.1]
  have hG'c : ContinuousOn (fun p : PotPair × ℝ => G p.1 (cl p.2)) (U ×ˢ (univ : Set ℝ)) :=
    hGc.comp (continuousOn_fst.prodMk (hclc.comp continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, hcl_mem _⟩)
  have hopen : IsOpen ((U ×ˢ (univ : Set ℝ)) ∩
      (fun p : PotPair × ℝ => ‖G p.1 (cl p.2)‖) ⁻¹' Iio (K + 1)) :=
    ContinuousOn.isOpen_inter_preimage hG'c.norm (hUo.prod isOpen_univ) isOpen_Iio
  have hsub : ({φ0} : Set PotPair) ×ˢ Icc (0 : ℝ) 1 ⊆ ((U ×ˢ (univ : Set ℝ)) ∩
      (fun p : PotPair × ℝ => ‖G p.1 (cl p.2)‖) ⁻¹' Iio (K + 1)) := by
    rintro ⟨φ, t⟩ ⟨hφ, ht⟩
    rw [mem_singleton_iff] at hφ
    subst hφ
    refine ⟨⟨hφU, mem_univ _⟩, ?_⟩
    simp only [mem_preimage, mem_Iio]
    rw [hcl_id t ht]
    linarith [hK (φ, t) ⟨rfl, ht⟩]
  obtain ⟨u, v, huo, hvo, hφu, hIv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  have hφ0u : φ0 ∈ u := singleton_subset_iff.1 hφu
  have huU : u ⊆ U := fun φ hφ =>
    (huv (show (φ, (0 : ℝ)) ∈ u ×ˢ v from ⟨hφ, hIv ⟨le_refl _, zero_le_one⟩⟩)).1.1
  have hbd : ∀ φ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ < K + 1 := by
    intro φ hφ t ht
    have h := (huv (show (φ, t) ∈ u ×ˢ v from ⟨hφ, hIv ht⟩)).2
    simp only [mem_preimage, mem_Iio] at h
    rwa [hcl_id t ht] at h
  have hC : 0 < max K 0 + 1 := by positivity
  refine ⟨u, max K 0 + 1, huo, hφ0u, huU, hC, ?_⟩
  intro H
  have hHH : H = G := by
    funext φ t
    exact (hG φ t).symm
  rw [hHH]
  have hbound : ∀ φ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ ≤ max K 0 + 1 := by
    intro φ hφ t ht
    have := hbd φ hφ t ht
    have h2 : K + 1 ≤ max K 0 + 1 := by linarith [le_max_left K 0]
    linarith
  have hcont : ∀ φ ∈ u, ContinuousOn (G φ) (Icc (0 : ℝ) 1) := by
    intro φ hφ
    exact hGc.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨huU hφ, ht⟩)
  refine ⟨?_, fun φ hφ => ?_⟩
  · intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    intro φ hφ
    have hφU' : φ ∈ U := huU hφ
    have hzA : AnalyticAt ℂ (fun ψ : PotPair => a ψ + (t : ℂ) * (muSeq ψ n - a ψ)) φ :=
      (haA φ hφU').add (analyticAt_const.mul ((hμA φ hφU').sub (haA φ hφU')))
    have hpair : AnalyticAt ℂ (fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      analyticAt_id.prod hzA
    have hpsi : AnalyticAt ℂ (fun ψ : PotPair =>
        psi n ψ (a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => psi n p.1 p.2)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ)))
        (hpsiJ (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ⟨hUW φ hφU', mem_univ _⟩) hpair
    have hrP : AnalyticAt ℂ (fun ψ : PotPair =>
        rootProduct n (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      AnalyticAt.comp (g := rootProduct n)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ)))
        (hrPJ _ (hdom φ hφU' t htc)) hpair
    have := (hpsi.mul (hrωA φ hφU')).div
      ((analyticAt_const.mul hrP).mul (hrsegA t htc φ hφU')) (hden φ hφU' t htc)
    exact this.congr (Filter.Eventually.of_forall fun ψ => (hG ψ t).symm)
  · have hφU' : φ ∈ U := huU hφ
    have hint : IntervalIntegrable (fun t : ℝ => G φ t / (Real.sqrt t : ℂ)) volume 0 1 :=
      G3015Aux.integrable_of_bound (G φ) _ (hcont φ hφ) (hbound φ hφ)
    refine ⟨hcont φ hφ, hbound φ hφ, hint, ?_⟩
    obtain ⟨hωsq, hseg, hsign⟩ := hall φ hφU'
    have hρc : ContinuousOn (rseg φ) (Icc (0 : ℝ) 1) :=
      hrsegC.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hφU', ht⟩)
    simp only [hG] at hint ⊢
    exact seg_exp_any n φ (hUW φ hφU') (hγ φ hφU') (a φ) (b φ)
      (rω φ) (rseg φ) (hUp φ hφU') hωsq hρc (fun t ht => (hseg t ht).1)
      (fun t ht => (hseg t ht).2) hsign hint

theorem g3024_endpoint_package (n : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW \ collapsedSet n) :
    ∃ V : Set PotPair, ∃ a b rω : PotPair → ℂ, ∃ rseg : PotPair → ℝ → ℂ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW \ collapsedSet n ∧
      (∀ φ ∈ V, ({a φ, b φ} : Set ℂ) = {lamMinus φ n, lamPlus φ n}) ∧
      AnalyticOnNhd ℂ (fun φ : PotPair => ∫ t in (0 : ℝ)..1,
        (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
          (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
          (Real.sqrt t : ℂ)) V ∧
      ∀ φ ∈ V, gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) * Complex.exp (Complex.I *
        ∫ t in (0 : ℝ)..1,
          (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
            (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
            (Real.sqrt t : ℂ)) := by
  obtain ⟨V1, a, b, hV1o, hφV1, hV1sub, haA, hbA, hVp⟩ := labels_any n φ0 hφ0
  obtain ⟨U, rω, rseg, hUo, hφU, hUV, hrωA, hrsegA, hrsegC, hroots⟩ :=
    roots_any n V1 a b hV1o hV1sub haA hbA hVp φ0 hφV1
  have hUsub : U ⊆ sourceW \ collapsedSet n := fun φ hφ => hV1sub (hUV hφ)
  obtain ⟨V, C, hVo, hφV, hVU, hC, hHan, hHφ⟩ :=
    param_data n φ0 U a b rω rseg hUo hφU hUsub (haA.mono hUV) (hbA.mono hUV)
      (fun φ hφ => (hVp φ (hUV hφ)).1) hrωA hrsegA hrsegC hroots
  obtain ⟨Gf, hGf⟩ : ∃ Gf : PotPair → ℝ → ℂ, Gf = fun (φ : PotPair) (t : ℝ) =>
      psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t) :=
    ⟨_, rfl⟩
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => Gf φ t) V := by
    subst hGf; exact hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (Gf φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Gf φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => Gf φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
        Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) := by
    subst hGf; exact hHφ
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V)
    (a := fun (t : ℝ) (φ : PotPair) => Gf φ t / (Real.sqrt t : ℂ)) C hC.le hVo
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
      (hHan' t ht φ hφ).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
    (fun φ hφ => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hHφ' φ hφ).1.mono Ioo_subset_Icc_self).div
        (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    (fun φ hφ => by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo φ hφ
      refine ⟨r, hr, hball, fun v hv => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' v (hball hv)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact g3005_rpow_neg_half_eq ht.1
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
  refine ⟨V, a, b, rω, rseg, hVo, hφV, fun φ hφ => hUsub (hVU hφ), fun φ hφ => (hVp φ (hUV (hVU hφ))).1, ?_, ?_⟩
  · intro φ hφ
    have h1 := (hmain φ hφ).congr (g := fun φ : PotPair => ∫ t in (0 : ℝ)..1,
      Gf φ t / (Real.sqrt t : ℂ)) (by
        filter_upwards [hVo.mem_nhds hφ] with ψ hψ
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo])
    rw [hGf] at h1
    exact h1
  · intro φ hφ
    have h := (hHφ' φ hφ).2.2.2
    rw [hGf] at h
    exact h

/-- Analytic lift of the eta exponential near every point of `sourceBetaW \ collapsedSet n`, endpoint set included. -/
theorem g3024_exp_lift (n : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceBetaW \ collapsedSet n) :
    ∃ V : Set PotPair, ∃ e : PotPair → ℂ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      ∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ := by
  have hW : φ0 ∈ sourceW := sourceFamily.V_W hφ0.1
  obtain ⟨V, a, b, rω, rseg, hVo, hφV, hVsub, hpair, hAn, hZ⟩ :=
    g3024_endpoint_package n φ0 ⟨hW, hφ0.2⟩
  refine ⟨V ∩ sourceBetaW, fun φ : PotPair => ∫ t in (0 : ℝ)..1,
    (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
      (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
      (Real.sqrt t : ℂ), hVo.inter sourceFamily.V_open, ⟨hφV, hφ0.1⟩, ?_,
    hAn.mono inter_subset_left, ?_⟩
  · intro φ hφ
    exact ⟨hφ.2, (hVsub hφ.1).2⟩
  · intro φ hφ
    have hgam : lamPlus φ n - lamMinus φ n ≠ 0 := gap_ne n φ (hVsub hφ.1)
    have hZφ := hZ φ hφ.1
    set X : ℂ := ∫ t in (0 : ℝ)..1,
      (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
        (Real.sqrt t : ℂ) with hX
    have hE : etaExponential n φ = gk16ActualScalarZPlus38 sourceF n φ / (lamPlus φ n - lamMinus φ n) :=
      rfl
    rcases Set.pair_eq_pair_iff.1 (hpair φ hφ.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      show Complex.exp (Complex.I * X) = 1 * etaExponential n φ
      rw [h1, h2] at hZφ
      rw [hE, one_mul, hZφ]
      field_simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show Complex.exp (Complex.I * X) = -1 * etaExponential n φ
      rw [h1, h2] at hZφ
      rw [hE, hZφ]
      field_simp
      ring

end
end G3024Endpoint
end NlsGge.GKDefinitionDesign
