import Mathlib
import NlsGge.Atomic.G2.G2020
import NlsGge.Atomic.G2.G2072
import NlsGge.Atomic.G4.G4013
import NlsGge.Atomic.G4.G4NormalizedHost

/- G4-020 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G4/G4020.lean.
   Head: followup5 STATEMENTS/G4.md, G4-020, verbatim except the lexical rename lambda -> lam (Lean keyword).
   Route (proof development/G4020_MAP01.md): conjuncts 2 and 4 from G2_020 with m = n; conjuncts 3 and the sphere identity
   from the G4013 proof (chunk copied byte-identically, G4013.lean lines 42-118); conjunct 1 from G2_072.1, transported
   along the sphere identity by circleIntegrable_congr, with CircleIntegrable.const_smul by -I.
   No hypothesis beyond the head. -/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4020 (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
  CircleIntegrable (fun lam => normalizedZeta n φ lam / localRoot n φ lam)
    (discC φ n) (discR φ n) ∧
  CircleIntegrable (fun lam => (1 : ℂ) / localRoot n φ lam)
    (discC φ n) (discR φ n) ∧
  gapContourMean n φ (normalizedZeta n φ) = 1 ∧
  gapContourMean n φ (fun _ => 1) = 1 := by
  have hφW : φ ∈ sourceW := sourceFamily.V_W hφ
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφW
  have hR0 : (0 : ℝ) ≤ discR φ n := (isolating_radius_pos38 (isolating_family38 φ hgk) n).le
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hother : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), ∀ k : ℤ, k ≠ n →
      lam' ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) :=
    fun lam' hlam' k hk => closedBall_avoids_other_gaps φ hgk n k hk lam' hlam'
  have hnotgap : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      lam' ∉ gapSegments38 φ := by
    intro lam' hlam' hc hmem
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    by_cases hkn : k = n
    · rw [hkn] at hk
      exact hc hk
    · exact hother lam' hlam' k hkn hk
  have hRmem : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      (φ, lam') ∈ rootDomain38 := by
    intro lam' hlam' hc
    show φ ∈ gkW ∧ lam' ∉ gapSegments38 φ
    exact ⟨hgk, hnotgap lam' hlam' hc⟩
  have hOmem : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n),
      (φ, lam') ∈ a5OmittedRootDomain38 n := by
    intro lam' hlam'
    show φ ∈ gkW ∧ ∀ m : ℤ, m ≠ n → lam' ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)
    exact ⟨hgk, fun m hm => hother lam' hlam' m hm⟩
  have hwfac : ∀ lam' : ℂ, localRoot n φ lam' = (Lib.piN n : ℂ) * rootFactor38 n (φ, lam') := by
    intro lam'
    unfold localRoot standardRoot rootFactor38
    dsimp only
    field_simp
  have hid : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam' =
        Complex.I * normalizedZeta n φ lam' / localRoot n φ lam' := by
    intro lam' hlam' hc
    have hR := hRmem lam' hlam' hc
    have hO := hOmem lam' hlam'
    have hfac : canonRoot38 φ lam' =
        2 * Complex.I * rootFactor38 n (φ, lam') * a5OmittedRootProduct38 n (φ, lam') :=
      a5CanonRoot_omitted_factorization38 n (φ, lam') hR
    have hQ : a5OmittedRootProduct38 n (φ, lam') ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, lam') hO
    have hRf : rootFactor38 n (φ, lam') ≠ 0 := rootFactor_ne_zero38 n (φ, lam') hR
    have hpsi : p6PsiNumerator38 n (sourceF n) φ lam' =
        -2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) lam' := rfl
    have hK : normalizedZeta n φ lam' =
        (Lib.piN n : ℂ) * Lib.omitProd n (p2Extend38 n (sourceF n φ)) lam' /
          a5OmittedRootProduct38 n (φ, lam') := rfl
    have h2 : (-2 : ℂ) = 2 * Complex.I * Complex.I := by
      linear_combination (-2 : ℂ) * Complex.I_mul_I
    rw [hpsi, hfac, hK, hwfac lam', h2]
    field_simp
    try ring
  have hsph : ∀ lam' ∈ Metric.sphere (discC φ n) (discR φ n),
      normalizedZeta n φ lam' / localRoot n φ lam' =
        -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam') := by
    intro lam' hlam'
    have hc : lam' ∉ gapSegment φ n := sphere_avoids_own_gap φ hgk n lam' hlam'
    rw [hid lam' (Metric.sphere_subset_closedBall hlam') hc]
    linear_combination (normalizedZeta n φ lam' / localRoot n φ lam') * Complex.I_mul_I
  have hEq : Set.EqOn (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (fun lam' => -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam'))
      (Metric.sphere (discC φ n) (discR φ n)) := by
    intro lam' hlam'
    exact hsph lam' hlam'
  have hper : circleIntegral (fun lam' => p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam')
      (discC φ n) (discR φ n) = 2 * (Real.pi : ℂ) := (G2_072 φ hφW n).2
  have hcirc : circleIntegral (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (discC φ n) (discR φ n) = -Complex.I * (2 * (Real.pi : ℂ)) := by
    rw [circleIntegral.integral_congr hR0 hEq, circleIntegral.integral_const_mul, hper]
  have hgap : gapContourMean n φ (normalizedZeta n φ) = 1 := by
    unfold gapContourMean
    rw [hcirc]
    have hne : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi') Complex.I_ne_zero
    rw [show -Complex.I * (2 * (Real.pi : ℂ)) = -2 * (Real.pi : ℂ) * Complex.I by ring]
    exact inv_mul_cancel₀ hne
  have hint0 : CircleIntegrable (fun lam' => p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam')
      (discC φ n) (discR φ n) := (G2_072 φ hφW n).1
  have hint1 : CircleIntegrable (fun lam' => -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam'))
      (discC φ n) (discR φ n) := by
    simpa only [Pi.smul_def, smul_eq_mul] using hint0.const_smul (a := -Complex.I)
  have hsphR : Set.EqOn (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (fun lam' => -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam'))
      (Metric.sphere (discC φ n) |discR φ n|) := by
    rw [abs_of_nonneg hR0]
    exact hEq
  have hint : CircleIntegrable (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (discC φ n) (discR φ n) :=
    (circleIntegrable_congr hsphR).mpr hint1
  have hCR : IsolatingFamily38 φ (discC φ) (discR φ) := isolating_family38 φ hgk
  obtain ⟨hI, hV⟩ := G2_020 φ hgk (discC φ) (discR φ) hCR n n
  have hfun : (fun lam' => (1 : ℂ) / localRoot n φ lam') = (fun z => (standardRoot φ n z)⁻¹) :=
    funext fun z => one_div _
  have hint2 : CircleIntegrable (fun lam' => (1 : ℂ) / localRoot n φ lam') (discC φ n) (discR φ n) := by
    rw [hfun]
    exact hI
  have hval : circleIntegral (fun lam' => (1 : ℂ) / localRoot n φ lam') (discC φ n) (discR φ n) =
      -2 * (Real.pi : ℂ) * Complex.I := by
    rw [hfun, hV, if_pos rfl]
  have hmean1 : gapContourMean n φ (fun _ => 1) = 1 := by
    show (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun lam' => (1 : ℂ) / localRoot n φ lam') (discC φ n) (discR φ n) = 1
    rw [hval]
    have hne : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi') Complex.I_ne_zero
    exact inv_mul_cancel₀ hne
  exact ⟨hint, hint2, hgap, hmean1⟩

end
end NlsGge.GKDefinitionDesign
