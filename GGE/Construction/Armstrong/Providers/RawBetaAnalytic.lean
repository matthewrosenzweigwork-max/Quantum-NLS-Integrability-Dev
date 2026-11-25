import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38
import Armstrong.Work.RawBetaFixedAnalytic
import Armstrong.Work.RawBetaOriginalValue
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.GradFundamentalDefs

/-! Provider for the exact approved scalar raw-beta analyticity anchor.
Local fixed circles preserve the supplied numerator. The full-Q overlap
identity transfers their terminal values to the original all-path predicate;
frozen uniqueness then glues local analytic values on the unchanged W.
-/

set_option autoImplicit false
open Set Filter Metric
open scoped Topology
open NlsGge NlsGge.GK38

namespace Armstrong.Providers.RawBetaAnalytic
noncomputable section

theorem gkSourceBeta_analytic38
    (W : Set PotPair := by assumption)
    (hWopen : IsOpen W := by assumption)
    (hreal : range realSlice ⊆ W := by assumption)
    (hWgk : W ⊆ gkW := by assumption)
    (F : (n : ℤ) → PotPair → P2Space38 n := by assumption)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W := by assumption)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0 := by assumption)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0 := by assumption) :
    ∀ n m : ℤ, ∀ hmn : m ≠ n,
      ∃ b : PotPair → ℂ,
        AnalyticOnNhd ℂ b W ∧
        ∀ φ : {ψ : PotPair // ψ ∈ W},
          b φ.1 =
            NlsGge.GK38.gkSourceBeta38 W hWopen hreal hWgk F
              hFanalytic hFn hperiod n m hmn φ := by
  intro n m hmn
  let f : W → ℂ := fun φ =>
    NlsGge.GK38.gkSourceBeta38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m hmn φ
  apply rawBetaAmbientAnalyticOfLocal38 W hWopen f
  intro φ
  obtain ⟨V₀, hV₀nhds, hV₀g, hV₀open, hV₀connected,
      C, ρ, c, N, hgeom, hspec⟩ :=
    local_isolatingFamily_common38 φ.1 (hWgk φ.2)
  let V : Set PotPair := V₀ ∩ W
  have hVopen : IsOpen V := hV₀open.inter hWopen
  have hφV : φ.1 ∈ V := ⟨mem_of_mem_nhds hV₀nhds, φ.2⟩
  have hVW : V ⊆ W := inter_subset_right
  have hVg : V ⊆ gkW := hVW.trans hWgk
  have hfamily : ∀ ψ ∈ V, IsolatingFamily38 ψ C ρ :=
    fun ψ hψ => ⟨c, N, hgeom, hspec ψ hψ.1⟩
  have hRjoint := rawBetaFixedCoefficient_same_family_joint_analytic38
    W V hVopen hVW hWgk C ρ hfamily F hFanalytic n m
  let g : PotPair → ℂ := fun ψ =>
    antiDiscrim ψ (muSeq ψ m) *
      rawBetaFixedCoefficient38 n m (F n) ψ (C m) (ρ m) (muSeq ψ m)
  have hμ : AnalyticOnNhd ℂ (fun ψ : PotPair => muSeq ψ m) V :=
    (analyticOnNhd_muSeq_complex38 m).mono hVg
  have hg : AnalyticOnNhd ℂ g V := by
    intro ψ hψ
    have hmap : AnalyticAt ℂ (fun η : PotPair => (η, muSeq η m)) ψ :=
      analyticAt_id.prod (hμ ψ hψ)
    have hμball : muSeq ψ m ∈ ball (C m) (ρ m) := by
      obtain ⟨c', N', hgeom', hspec'⟩ := hfamily ψ hψ
      exact (hspec'.1 m).2.1
    have hδ : AnalyticAt ℂ
        (fun η : PotPair => antiDiscrim η (muSeq η m)) ψ :=
      AnalyticAt.comp
        (g := fun q : PotPair × ℂ => antiDiscrim q.1 q.2)
        (f := fun η : PotPair => (η, muSeq η m)) (x := ψ)
        (analyticOnNhd_antiDiscrim (ψ, muSeq ψ m) (mem_univ _)) hmap
    have hRμ : AnalyticAt ℂ
        (fun η : PotPair =>
          rawBetaFixedCoefficient38 n m (F n) η (C m) (ρ m) (muSeq η m)) ψ :=
      AnalyticAt.comp
        (g := fun q : PotPair × ℂ =>
          rawBetaFixedCoefficient38 n m (F n) q.1 (C m) (ρ m) q.2)
        (f := fun η : PotPair => (η, muSeq η m)) (x := ψ)
        (hRjoint (ψ, muSeq ψ m) ⟨hψ, hμball⟩) hmap
    exact hδ.mul hRμ
  refine ⟨V, hVopen, hφV, g, hg, ?_⟩
  intro ψ hψV
  have hzero : abelianPeriod38 m ψ.1 (p6PsiNumerator38 n (F n) ψ.1) = 0 := by
    simpa only [if_neg hmn] using hperiod n ψ.1 ψ.2 m
  have hc := rawBetaFixedCoefficientOfZeroPeriod38 n m (F n) ψ.1 (hWgk ψ.2)
    C ρ (hfamily ψ.1 hψV) hzero
  have hvalue : GKSourceBetaValue38 n m hmn F ⟨ψ.1, hWgk ψ.2⟩ (g ψ.1) :=
    rawBetaSourceValueOfFixedCoefficient38 n m hmn F ⟨ψ.1, hWgk ψ.2⟩
      C ρ (hfamily ψ.1 hψV) hzero
      (rawBetaFixedCoefficient38 n m (F n) ψ.1 (C m) (ρ m)) hc.2.2.1 hc.2.2.2
  exact (NlsGge.GK38.gkSourceBeta_characterization38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n m hmn ψ).2.1 (g ψ.1) hvalue

end
end Armstrong.Providers.RawBetaAnalytic
