import Mathlib
import NlsGge.Atomic.KSN.KSN013Core
import NlsGge.Atomic.G2.G2032
import NlsGge.Atomic.G2.G2033
import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.XiSqChi
import NlsGge.GK38.XiSqLocal

/- KSN014 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN014Core.lean.
   Supporting (non-packet) PotPair-level core of KSN-014 (KSN Lemma 3.1(iii)), route of Pro round 15 Q1 "KSN-014 and
   KSN-017": the action-ratio integral is evaluated along the gap segment, which lies in the common nth disc.
   * ksn014_chi_eq: on the own closed disc, the GK38 omitted-root quotient a5Chi38 (symmetric products) equals the
     unconditional criticalOmittedProduct (termwise (λ̇-z)/π · ... ; unconditional HasProd ⇒ symmetricIcc HasProd).
   * Non-collapsed gap: G2-033 (ξ² = 4I/γ²) and G2-032 (4I/γ² = (2/π)∫_{-1}^{1}(t-ε)²χ/√(1-t²)), the landed arcsine
     substitution and ∫_0^{2π} cos² = π give ξ²-1 = (1/π)∫_0^{2π}((cosθ-ε)²χ - cos²θ); ε = 2(λ̇-τ)/γ = 2γa.
   * Collapsed gap: G2-033 ξ² = χ(τ).
   * ‖√w - 1‖ ≤ ‖w - 1‖ (landed Lib.norm_sqrt_one_sub_sub_one_le).
   Quantities: |χ-1| ≤ A/⟨n⟩ from KSN013Core.ksn013_disc_estimate; |γ_n| ≤ √Γ/⟨n⟩, |a| ≤ Aa. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open scoped Real
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- On the omitted-root domain, with unconditional multipliability, the GK38 quotient is the critical product. -/
theorem ksn014_chi_eq (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (hdom : (φ, z) ∈ a5OmittedRootDomain38 n)
    (hmul : Multipliable (fun k : ℤ => criticalOmittedFactor n k φ z)) :
    a5Chi38 n (φ, z) = criticalOmittedProduct n φ z := by
  have hg : HasProd (fun j => a5OmittedRootFactor38 n j (φ, z)) (a5OmittedRootProduct38 n (φ, z))
      (SummationFilter.symmetricIcc ℤ) :=
    (a5OmittedRoot_multipliable38 n (φ, z) hdom).hasProd
  have hf : HasProd (fun k : ℤ => criticalOmittedFactor n k φ z) (criticalOmittedProduct n φ z)
      (SummationFilter.symmetricIcc ℤ) :=
    hmul.hasProd.mono_left SummationFilter.le_atTop
  have hfg := hf.mul hg
  have hterm : (fun k : ℤ => criticalOmittedFactor n k φ z * a5OmittedRootFactor38 n k (φ, z)) =
      fun k => if k = n then 1 else Lib.prodFactor (Lib.sigmaOf (a5CriticalShift38 φ)) z k := by
    funext k
    by_cases hkn : k = n
    · simp [hkn, criticalOmittedFactor, a5OmittedRootFactor38]
    · have hne : rootFactor38 k (φ, z) ≠ 0 := a5RootFactor_ne_zero38 k (φ, z) hφ (hdom.2 k hkn)
      have hpi : (Lib.piN k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero k)
      have hS : stdRoot38 (tauN φ k) (gamma2 φ k) z ≠ 0 := by
        intro h; apply hne; simp [rootFactor38, h]
      simp only [criticalOmittedFactor, a5OmittedRootFactor38, if_neg hkn, rootFactor38,
        Lib.prodFactor, Lib.sigmaOf]
      rw [a5CriticalShift_value38 φ hφ k]
      field_simp
      ring
  rw [hterm] at hfg
  have hnum : a5CriticalNumerator38 n (φ, z) =
      criticalOmittedProduct n φ z * a5OmittedRootProduct38 n (φ, z) := by
    unfold a5CriticalNumerator38 Lib.omitProd
    rw [hfg.tprod_eq]
    have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
    field_simp
  have hden : a5OmittedRootProduct38 n (φ, z) ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, z) hdom
  unfold a5Chi38
  rw [hnum]
  field_simp

theorem ksn014_sqrt_bound (w : ℂ) : ‖Complex.sqrt w - 1‖ ≤ ‖w - 1‖ := by
  have h := Lib.norm_sqrt_one_sub_sub_one_le (1 - w)
  rw [sub_sub_cancel] at h
  rwa [norm_sub_rev w 1]

theorem ksn014_cos_sq_integral :
    ∫ θ in (0 : ℝ)..(2 * π), ((Real.cos θ : ℝ) : ℂ) ^ 2 = (π : ℂ) := by
  have h : ∫ θ in (0 : ℝ)..(2 * π), Real.cos θ ^ 2 = π := by
    rw [integral_cos_sq]
    simp
  have e : (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) ^ 2) = fun θ => ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    funext θ; push_cast; rfl
  rw [e, intervalIntegral.integral_ofReal, h]

/-- The polynomial perturbation bound on [-1,1]. -/
theorem ksn014_poly_bound (t : ℝ) (ht : |t| ≤ 1) (ε χ : ℂ) :
    ‖((t : ℂ) - ε) ^ 2 * χ - (t : ℂ) ^ 2‖ ≤ ‖ε‖ * (2 + ‖ε‖) * (1 + ‖χ - 1‖) + ‖χ - 1‖ := by
  have ht' : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact ht
  have e : ((t : ℂ) - ε) ^ 2 * χ - (t : ℂ) ^ 2 = (ε * (ε - 2 * t)) * χ + (t : ℂ) ^ 2 * (χ - 1) := by ring
  have hχ : ‖χ‖ ≤ 1 + ‖χ - 1‖ := by
    have := norm_add_le (χ - 1) 1
    rw [sub_add_cancel, norm_one] at this
    linarith
  have h1 : ‖ε - 2 * (t : ℂ)‖ ≤ ‖ε‖ + 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [this]; linarith
  have ht2 : ‖(t : ℂ) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht'
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  have hε0 := norm_nonneg ε
  have hc0 := norm_nonneg (χ - 1)
  have hA : ‖ε‖ * ‖ε - 2 * (t : ℂ)‖ * ‖χ‖ ≤ ‖ε‖ * (2 + ‖ε‖) * (1 + ‖χ - 1‖) := by
    apply mul_le_mul _ hχ (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hε0
  have hB : ‖(t : ℂ) ^ 2‖ * ‖χ - 1‖ ≤ ‖χ - 1‖ := by
    have := mul_le_mul_of_nonneg_right ht2 hc0
    linarith
  linarith

/-- KSN-014 at the PotPair level for one common geometry. -/
theorem ksn014_xi_estimate (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ)
    (hg : IsolatingGeometry38 C R c J) (Aa Γ : ℝ) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ φ : PotPair, φ ∈ gkW → IsolatingSpectral38 φ C R →
      (∀ k, ‖a5CriticalA38 k φ‖ ≤ Aa) → (∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ) →
      ∀ n : ℤ, ‖xiN38 n φ - 1‖ ≤ C1 / japaneseBracket n := by
  obtain ⟨A0, hA0, hest⟩ := ksn013_disc_estimate C R c J hg Aa Γ
  set e : ℝ := 2 * Real.sqrt (max Γ 0) * max Aa 0 with he
  have he0 : 0 ≤ e := by positivity
  set C1 : ℝ := 2 * (e * (2 + e) * (1 + A0) + A0) with hC1
  refine ⟨C1, by positivity, ?_⟩
  intro φ hφ hsp ha hΓ n
  have hjn := NlsGge.Atomic.KSN011.br_pos n
  have hjn1 : 1 ≤ japaneseBracket n := by
    unfold japaneseBracket
    have h1 : (1 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + (n : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
  have hfam : IsolatingFamily38 φ C R := ⟨c, J, hg, hsp⟩
  have hchi : ∀ z ∈ closedBall (C n) (R n), ‖a5Chi38 n (φ, z) - 1‖ ≤ A0 / japaneseBracket n := by
    intro z hz
    obtain ⟨hm, -, hb⟩ := hest φ hφ hsp ha hΓ n z hz
    rw [ksn014_chi_eq φ hφ n z (a5OwnClosedBall_omittedDomain38 φ hφ C R hfam n z hz) hm]
    exact hb
  have hseg := (hsp.1 n).1
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hγ : gamma2 φ n = gap φ n ^ 2 := gamma2_value38 φ hφ n
  have hsegpt : ∀ t : ℝ, t ∈ Icc (-1 : ℝ) 1 →
      tauN φ n + (t : ℂ) * gap φ n / 2 ∈ closedBall (C n) (R n) := by
    intro t ht
    apply ball_subset_closedBall
    apply hseg
    refine ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, ?_⟩
    simp only [Complex.real_smul, gap]
    push_cast
    rw [hτ]
    ring
  have hA0C1 : A0 ≤ C1 := by
    have : 0 ≤ e * (2 + e) * (1 + A0) := by positivity
    rw [hC1]; linarith
  have hxiSq : ‖xiSq38 n φ - 1‖ ≤ C1 / japaneseBracket n := by
    obtain ⟨-, h2⟩ := G2_033 n
    obtain ⟨-, hq, hcol⟩ := h2 φ hφ
    by_cases hgap : gap φ n = 0
    · have h0 : gamma2 φ n = 0 := by rw [hγ, hgap]; ring
      rw [hcol h0]
      have hz : tauN φ n ∈ closedBall (C n) (R n) := by
        have := hsegpt 0 ⟨by norm_num, by norm_num⟩
        simpa using this
      exact (hchi _ hz).trans (div_le_div_of_nonneg_right hA0C1 hjn.le)
    · obtain ⟨hg2, -, hres⟩ := G2_032 φ hφ n hgap
      rw [hq hg2, hres]
      have hFc := arcF_continuousOn φ hφ n
      have hsub := G2032Arcsine.arcsine_substitution (arcF φ n) hFc
      have hI : ∫ t in (-1 : ℝ)..1, rescaledActionIntegrand φ n t =
          (1 / 2) * ∫ θ in (0 : ℝ)..(2 * π), arcF φ n (Real.cos θ) := by
        have e1 : (fun t => rescaledActionIntegrand φ n t) =
            fun t => arcF φ n t / ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) := rfl
        rw [e1, hsub]
        ring
      have hcont : Continuous (fun θ : ℝ => arcF φ n (Real.cos θ)) :=
        hFc.comp_continuous Real.continuous_cos
          (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
      have hcos2 : Continuous (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) ^ 2) := by fun_prop
      have hdiff : (∫ θ in (0 : ℝ)..(2 * π), arcF φ n (Real.cos θ)) - (π : ℂ) =
          ∫ θ in (0 : ℝ)..(2 * π), (arcF φ n (Real.cos θ) - ((Real.cos θ : ℝ) : ℂ) ^ 2) := by
        rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) (hcos2.intervalIntegrable _ _),
          ksn014_cos_sq_integral]
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hval : rescaledActionIntegral φ n - 1 =
          (1 / (π : ℂ)) * ∫ θ in (0 : ℝ)..(2 * π),
            (arcF φ n (Real.cos θ) - ((Real.cos θ : ℝ) : ℂ) ^ 2) := by
        unfold rescaledActionIntegral
        rw [hI, ← hdiff]
        field_simp
      rw [hval]
      -- pointwise bound
      set M : ℝ := (e * (2 + e) * (1 + A0) + A0) / japaneseBracket n with hM
      have hε : ‖2 * (lamDot φ n - tauN φ n) / gap φ n‖ ≤ e / japaneseBracket n := by
        have hid := a5CriticalA_identity38 n φ hφ
        rw [hid, hγ]
        have e2 : 2 * (gap φ n ^ 2 * a5CriticalA38 n φ) / gap φ n = 2 * gap φ n * a5CriticalA38 n φ := by
          field_simp
        rw [e2, norm_mul, norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        have hgapb : ‖gap φ n‖ ≤ Real.sqrt (max Γ 0) / japaneseBracket n := by
          rw [le_div_iff₀ hjn]
          have hsq : (‖gap φ n‖ * japaneseBracket n) ^ 2 ≤ max Γ 0 := by
            have := hΓ n
            rw [hγ, norm_pow] at this
            nlinarith [le_max_left Γ 0]
          have := Real.abs_le_sqrt hsq
          rwa [abs_of_nonneg (by positivity)] at this
        have hab : ‖a5CriticalA38 n φ‖ ≤ max Aa 0 := (ha n).trans (le_max_left _ _)
        calc 2 * ‖gap φ n‖ * ‖a5CriticalA38 n φ‖
            ≤ 2 * (Real.sqrt (max Γ 0) / japaneseBracket n) * max Aa 0 := by gcongr
          _ = e / japaneseBracket n := by rw [he]; ring
      have hpt : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π),
          ‖arcF φ n (Real.cos θ) - ((Real.cos θ : ℝ) : ℂ) ^ 2‖ ≤ M := by
        intro θ _
        have hct : Real.cos θ ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
        have hpb := ksn014_poly_bound (Real.cos θ) (abs_le.mpr hct)
          (2 * (lamDot φ n - tauN φ n) / gap φ n)
          (a5Chi38 n (φ, tauN φ n + ((Real.cos θ : ℝ) : ℂ) * gap φ n / 2))
        have hχ := hchi _ (hsegpt _ hct)
        unfold arcF
        refine hpb.trans ?_
        set x := ‖2 * (lamDot φ n - tauN φ n) / gap φ n‖ with hx
        set y := ‖a5Chi38 n (φ, tauN φ n + ((Real.cos θ : ℝ) : ℂ) * gap φ n / 2) - 1‖ with hy
        have hx0 : 0 ≤ x := norm_nonneg _
        have hy0 : 0 ≤ y := norm_nonneg _
        have hxe : x ≤ e := hε.trans (div_le_self he0 hjn1)
        have hyA : y ≤ A0 := hχ.trans (div_le_self hA0 hjn1)
        have h1 : x * (2 + x) * (1 + y) ≤ (e / japaneseBracket n) * (2 + e) * (1 + A0) := by
          apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
          exact mul_le_mul hε (by linarith) (by positivity) (by positivity)
        rw [hM]
        have h3 : (e * (2 + e) * (1 + A0) + A0) / japaneseBracket n =
            (e / japaneseBracket n) * (2 + e) * (1 + A0) + A0 / japaneseBracket n := by
          field_simp
        rw [h3]
        linarith
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [norm_mul]
      have hn1 : ‖(1 / (π : ℂ))‖ = 1 / π := by
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [hn1]
      have habs : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
      rw [habs] at hint
      calc 1 / π * ‖∫ θ in (0 : ℝ)..(2 * π), (arcF φ n (Real.cos θ) - ((Real.cos θ : ℝ) : ℂ) ^ 2)‖
          ≤ 1 / π * (M * (2 * π)) := by gcongr
        _ = 2 * M := by field_simp
        _ = C1 / japaneseBracket n := by rw [hM, hC1]; ring
  exact (ksn014_sqrt_bound _).trans hxiSq

end
end NlsGge.ThirdConsultation.KSN
