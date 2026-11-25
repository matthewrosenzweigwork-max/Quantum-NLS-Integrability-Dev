import Mathlib
import NlsGge.ThirdConsultation.G2.Round5
import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiCommonDomain
import NlsGge.GK38.XiSqFinalProbe

                                                                                                                           
                                                                                                                                                   
                                                                                                
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g2035_local (φ₀ : PotPair) (h₀ : φ₀ ∈ actionPositiveDomain) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ actionPositiveDomain ∧
      ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
        ∀ φ : PotPair, φ ∈ U →
          (∀ n : ℤ, δ ≤ (xiSq38 n φ).re ∧ xiN38 n φ ≠ 0 ∧
            (xiN38 n φ) ^ 2 = xiSq38 n φ) ∧
          Summable (fun n : ℤ => ‖xiN38 n φ - 1‖ ^ 2) ∧
          (∑' n : ℤ, ‖xiN38 n φ - 1‖ ^ 2) ≤ C := by
  obtain ⟨hV₀, hpos₀⟩ := h₀
  have hVopen : IsOpen sourceBetaW := sourceFamily.V_open
  have hgk : φ₀ ∈ gkW := (sourceFamily.V_xi hV₀).1
  obtain ⟨U1, hU1, -, N, htail⟩ := xiSq38_near_one φ₀ hgk
  obtain ⟨U2, hU2, c, hc⟩ := xiN38_l2_near_one φ₀ hgk
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hI : I.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  let δ : ℝ := min (1 / 2) (I.inf' hI (fun n => (xiSq38 n φ₀).re / 2))
  have hδpos : 0 < δ := by
    refine lt_min (by norm_num) ?_
    rw [Finset.lt_inf'_iff]
    intro n _
    linarith [hpos₀ n]
  have hδhead : ∀ n ∈ I, δ ≤ (xiSq38 n φ₀).re / 2 := fun n hn =>
    (min_le_right _ _).trans (Finset.inf'_le _ hn)
  have hhead : ∀ᶠ ψ in 𝓝 φ₀, ∀ n ∈ I, δ ≤ (xiSq38 n ψ).re := by
    refine (Filter.eventually_all_finset I).2 (fun n hn => ?_)
    have hcont : ContinuousAt (fun ψ => (xiSq38 n ψ).re) φ₀ :=
      Complex.continuous_re.continuousAt.comp
        (xiSq38_analytic n φ₀ hgk).continuousAt
    have := hcont.eventually (lt_mem_nhds (a := (xiSq38 n φ₀).re / 2)
      (b := (xiSq38 n φ₀).re) (by linarith [hpos₀ n]))
    filter_upwards [this] with ψ hψ
    exact (hδhead n hn).trans hψ.le
  have hVn : sourceBetaW ∈ 𝓝 φ₀ := hVopen.mem_nhds hV₀
  have hev : ∀ᶠ ψ in 𝓝 φ₀, ψ ∈ sourceBetaW ∧ ψ ∈ U1 ∧ ψ ∈ U2 ∧
      ∀ n ∈ I, δ ≤ (xiSq38 n ψ).re := by
    filter_upwards [hVn, hU1, hU2, hhead] with ψ a b c d
    exact ⟨a, b, c, d⟩
  have hall : ∀ ψ : PotPair, ψ ∈ sourceBetaW → ψ ∈ U1 → (∀ n ∈ I, δ ≤ (xiSq38 n ψ).re) →
      ∀ n : ℤ, δ ≤ (xiSq38 n ψ).re := by
    intro ψ hV hU hh n
    by_cases hn : N < n.natAbs
    · have h := (htail ψ hU n hn).2
      have h1 : |(xiSq38 n ψ).re - 1| < 1 / 2 := by
        have := Complex.abs_re_le_norm (xiSq38 n ψ - 1)
        simp only [Complex.sub_re, Complex.one_re] at this
        exact lt_of_le_of_lt this h
      have h2 := (abs_lt.mp h1).1
      exact (min_le_left _ _).trans (by linarith)
    · have habs : n.natAbs ≤ N := le_of_not_gt hn
      have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs
      have hpos : n ≤ (n.natAbs : ℤ) := Int.le_natAbs
      have hneg : -n ≤ (n.natAbs : ℤ) := by
        simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
      exact hh n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  refine ⟨{ψ | ψ ∈ sourceBetaW ∧ ψ ∈ U1 ∧ ψ ∈ U2 ∧ ∀ n ∈ I, δ ≤ (xiSq38 n ψ).re},
    hev, ?_, δ, max c 1, hδpos, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  · intro ψ hψ
    exact ⟨hψ.1, fun n => lt_of_lt_of_le hδpos (hall ψ hψ.1 hψ.2.1 hψ.2.2.2 n)⟩
  · intro ψ hψ
    obtain ⟨hs, hb⟩ := hc ψ hψ.2.2.1
    refine ⟨fun n => ⟨hall ψ hψ.1 hψ.2.1 hψ.2.2.2 n, ?_, xiN38_sq n ψ⟩, hs, hb.trans (le_max_left _ _)⟩
    intro h0
    have h1 := hall ψ hψ.1 hψ.2.1 hψ.2.2.2 n
    have h2 := xiN38_sq n ψ
    rw [h0] at h2
    have h3 : xiSq38 n ψ = 0 := by rw [← h2]; ring
    rw [h3] at h1
    simp at h1
    linarith

theorem G2_035 :
    IsOpen actionPositiveDomain ∧
    Set.range (fun u : PhysicalL2 => NlsGge.GK38.realSlice u)
      ⊆ actionPositiveDomain ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ (xiN38 n) actionPositiveDomain) ∧
    (∀ n : ℤ, xiN38 n (0 : PotPair) = 1) ∧
    ∀ φ₀ : PotPair, φ₀ ∈ actionPositiveDomain →
      ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ actionPositiveDomain ∧
        ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
          ∀ φ : PotPair, φ ∈ U →
            (∀ n : ℤ, δ ≤ (xiSq38 n φ).re ∧ xiN38 n φ ≠ 0 ∧
              (xiN38 n φ) ^ 2 = xiSq38 n φ) ∧
            Summable (fun n : ℤ => ‖xiN38 n φ - 1‖ ^ 2) ∧
            (∑' n : ℤ, ‖xiN38 n φ - 1‖ ^ 2) ≤ C := by
  refine ⟨?_, ?_, ?_, ?_, g2035_local⟩
  · rw [isOpen_iff_mem_nhds]
    intro φ hφ
    obtain ⟨U, hU, hUD, -⟩ := g2035_local φ hφ
    exact Filter.mem_of_superset hU hUD
  · rintro _ ⟨u, rfl⟩
    exact ⟨sourceFamily.V_real ⟨u, rfl⟩, fun n => by
      linarith [(xiSq38_real_ge_one u n).2]⟩
  · intro n
    refine (xiN38_analytic n).mono ?_
    intro φ hφ
    exact ⟨(sourceFamily.V_xi hφ.1).1, Complex.mem_slitPlane_iff.mpr (Or.inl (hφ.2 n))⟩
  · intro n
    exact A5FinalFixture.canonical_sqrt_free_one n

end
end NlsGge.GKDefinitionDesign
