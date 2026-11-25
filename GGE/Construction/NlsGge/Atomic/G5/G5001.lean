import Mathlib
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5024
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.AbelianOriginalChartGraph
import NlsGge.GK38.AbelianRestriction
import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.Lib.EntireProductsParamd

                                                                                                                  
                                                                                                                 
                                                                                                           
                                                                                                     
                                                                                                       
                                                                                                          
                                                                                                          
                                                                                                          
                                                                                                           
                                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Two distinct labels have disjoint isolating discs. -/
theorem g5001_ball_disjoint {C : ℤ → ℂ} {R : ℤ → ℝ} {c : ℝ} {N : ℕ}
    (hgeom : IsolatingGeometry38 C R c N) {m n : ℤ} (hmn : m ≠ n)
    {z : ℂ} (hz : z ∈ Metric.ball (C m) (R m)) (hw : z ∈ Metric.ball (C n) (R n)) :
    False := by
  obtain ⟨-, -, hc1, hsep, -⟩ := hgeom
  have hc : 0 < c := by linarith
  have hpos : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| := by
    apply mul_pos (inv_pos.mpr hc)
    rw [abs_pos]
    exact_mod_cast sub_ne_zero.mpr hmn
  have hbdd : BddBelow {v : ℝ | ∃ a ∈ Metric.ball (C m) (R m),
      ∃ b ∈ Metric.ball (C n) (R n), v = dist a b} :=
    ⟨0, fun v hv => by
      obtain ⟨a, -, b, -, rfl⟩ := hv
      exact dist_nonneg⟩
  have hle : ballDistance38 (C m) (C n) (R m) (R n) ≤ 0 := by
    unfold ballDistance38
    exact csInf_le hbdd ⟨z, hz, z, hw, (dist_self z).symm⟩
  linarith [(hsep m n hmn).1]

/-- Restriction and re-extension do not change the labels with index other than n. -/
theorem g5001_sigma_extend (n m : ℤ) (hmn : m ≠ n) (s : Lib.L2Seq) :
    Lib.sigmaOf (p2Extend38 n (p2Restrict38 n s)) m = Lib.sigmaOf s m := by
  have h : p2Extend38 n (p2Restrict38 n s) m = s m :=
    p2Extend_at38 n (p2Restrict38 n s) ⟨m, hmn⟩
  simp only [Lib.sigmaOf, h]

theorem g5001_gk (φ : PotPair) (hφ : φ ∈ sourceBetaW) : φ ∈ gkW :=
  sourceFamily.W_gk (sourceFamily.V_W hφ)

theorem g5001_mu_mem (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    muSeq φ n ∈ Metric.ball (discC φ n) (discR φ n) := by
  obtain ⟨c, N, -, hs⟩ := isolating_family38 φ hφ
  exact (hs.1 n).2.1

theorem g5001_dom (φ : PotPair) (hφ : φ ∈ sourceBetaW) (n : ℤ) :
    (φ, muSeq φ n) ∈ a5OmittedRootDomain38 n :=
  a5OwnClosedBall_omittedDomain38 φ (g5001_gk φ hφ) (discC φ) (discR φ)
    (isolating_family38 φ (g5001_gk φ hφ)) n (muSeq φ n)
    (Metric.ball_subset_closedBall (g5001_mu_mem φ (g5001_gk φ hφ) n))

/-- The canonical numerator does not vanish at the own Dirichlet point of a real potential. -/
theorem g5001_psi_ne_zero_real (n : ℤ) (u : PhysicalL2) :
    psiAt n (muSeq (realSlice u) n) (realSlice u) ≠ 0 := by
  have hW : realSlice u ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u)
  have hgk : realSlice u ∈ gkW := sourceFamily.W_gk hW
  have hfam := isolating_family38 (realSlice u) hgk
  obtain ⟨t, ht, hzero, hFeq⟩ := sourceFamily.F_real n u
  obtain ⟨s, -, hres, hown, -⟩ :=
    (p5Actual_gap_zero_iff_original_full_chart38 n u (discC (realSlice u))
      (discR (realSlice u)) hfam t).mp ⟨ht, hzero⟩
  have hmu := g5001_mu_mem (realSlice u) hgk n
  obtain ⟨c, N, hgeom, -⟩ := hfam
  have hF : sourceF n (realSlice u) = p2Restrict38 n s := by
    rw [hres]
    exact hFeq
  have hω : Lib.omitProd n (p2Extend38 n (sourceF n (realSlice u))) (muSeq (realSlice u) n) ≠ 0 := by
    rw [Ne, Lib.omitProd_eq_zero_iff]
    rintro ⟨m, hmn, hm⟩
    rw [hF, g5001_sigma_extend n m hmn s] at hm
    have hz : muSeq (realSlice u) n ∈ Metric.ball (discC (realSlice u) m) (discR (realSlice u) m) := by
      rw [← hm]
      exact hown m
    exact g5001_ball_disjoint hgeom hmn hz hmu
  show -2 * Lib.omitProd n (p2Extend38 n (sourceF n (realSlice u))) (muSeq (realSlice u) n) ≠ 0
  exact mul_ne_zero (by norm_num) hω

theorem g5001_psi_analytic (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    AnalyticAt ℂ (fun ψ : PotPair => psiAt n (muSeq ψ n) ψ) φ := by
  have hJ : AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ :=
    analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n φ (g5001_gk φ hφ))
  exact AnalyticAt.comp (g := fun q : PotPair × ℂ => p6PsiNumerator38 n (sourceF n) q.1 q.2)
    (f := fun ψ : PotPair => (ψ, muSeq ψ n))
    (p6PsiNumerator_joint_analytic38 n sourceW (sourceF n) (sourceFamily.F_analytic n)
      (φ, muSeq φ n) ⟨sourceFamily.V_W hφ, Set.mem_univ _⟩) hJ

theorem g5001_ext_analytic (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    AnalyticAt ℂ (fun ψ : PotPair => p2Extend38 n (sourceF n ψ)) φ :=
  AnalyticAt.comp (g := p2Extend38 n) (f := sourceF n)
    ((p2Extend38 n).analyticAt (sourceF n φ))
    (sourceFamily.F_analytic n φ (sourceFamily.V_W hφ))

theorem g5001_zeta_analytic (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    AnalyticAt ℂ (fun ψ : PotPair => normalizedZeta n ψ (muSeq ψ n)) φ := by
  have hG : AnalyticAt ℂ (fun ψ : PotPair => ((ψ, p2Extend38 n (sourceF n ψ)), muSeq ψ n)) φ :=
    (analyticAt_id.prod (g5001_ext_analytic n φ hφ)).prod
      (analyticOnNhd_muSeq_complex38 n φ (g5001_gk φ hφ))
  have hO := p2OmittedRatio_analytic38 n (((φ, p2Extend38 n (sourceF n φ)), muSeq φ n))
    (g5001_dom φ hφ n)
  exact AnalyticAt.comp (g := p2OmittedRatio38 n)
    (f := fun ψ : PotPair => ((ψ, p2Extend38 n (sourceF n ψ)), muSeq ψ n)) hO hG

/-- Exact cancellation of the omitted product on the nonvanishing locus (Pro helper, proof). -/
theorem radiusQuotient_cancel (n : ℤ) (φ : PotPair)
    (hφ : φ ∈ sourceBetaW)
    (hpsi : psiAt n (muSeq φ n) φ ≠ 0) :
  radiusQuotient n φ = -(Lib.piN n : ℂ) /
    (2 * a5OmittedRootProduct38 n (φ, muSeq φ n)) := by
  have hA : a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
    a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ n)
  have hψ : psiAt n (muSeq φ n) φ =
      -2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) (muSeq φ n) := rfl
  have hω : Lib.omitProd n (p2Extend38 n (sourceF n φ)) (muSeq φ n) ≠ 0 := by
    intro h
    apply hpsi
    rw [hψ, h, mul_zero]
  have hK : radiusQuotient n φ =
      ((Lib.piN n : ℂ) * Lib.omitProd n (p2Extend38 n (sourceF n φ)) (muSeq φ n)) /
        a5OmittedRootProduct38 n (φ, muSeq φ n) /
        (-2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) (muSeq φ n)) := rfl
  rw [hK]
  field_simp

theorem signedRadius_eq_radiusQuotient_mul_antiDiscrim
    (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (hpsi : psiAt n (muSeq φ n) φ ≠ 0) :
  signedRadius n φ = radiusQuotient n φ * antiDiscrim φ (muSeq φ n) := by
  have hA : a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
    a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ n)
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [radiusQuotient_cancel n φ hφ hpsi]
  unfold signedRadius terminalRoot
  field_simp

/-- Main theorem: G5-001 head (verbatim) with proof. -/
theorem G5001 (n : ℤ) (u : PhysicalL2) :
  ∃ V : Set PotPair,
    V ∈ 𝓝 (realSlice u) ∧ IsOpen V ∧ V ⊆ sourceBetaW ∧
    AnalyticOnNhd ℂ (radiusQuotient n) V ∧
    (∀ φ : PotPair, φ ∈ V → psiAt n (muSeq φ n) φ ≠ 0) ∧
    (InteriorRealDirichletGap n u →
      signedRadius n (realSlice u) = radiusQuotient n (realSlice u) *
        antiDiscrim (realSlice u) (muSeq (realSlice u) n)) := by
  classical
  have hVopen : IsOpen (sourceBetaW ∩ {φ : PotPair | psiAt n (muSeq φ n) φ ≠ 0}) := by
    rw [isOpen_iff_mem_nhds]
    rintro φ ⟨hφB, hφψ⟩
    have hφψ' : psiAt n (muSeq φ n) φ ≠ 0 := hφψ
    have hev : ∀ᶠ ψ in 𝓝 φ, psiAt n (muSeq ψ n) ψ ≠ 0 :=
      ((g5001_psi_analytic n φ hφB).continuousAt).eventually_ne hφψ'
    filter_upwards [sourceFamily.V_open.mem_nhds hφB, hev] with ψ hψB hψne
    exact ⟨hψB, hψne⟩
  refine ⟨sourceBetaW ∩ {φ : PotPair | psiAt n (muSeq φ n) φ ≠ 0}, ?_, hVopen,
    Set.inter_subset_left, ?_, ?_, ?_⟩
  · exact hVopen.mem_nhds ⟨sourceFamily.V_real (Set.mem_range_self u),
      g5001_psi_ne_zero_real n u⟩
  · intro φ hφ
    have hB : φ ∈ sourceBetaW := hφ.1
    have hψ0 : psiAt n (muSeq φ n) φ ≠ 0 := hφ.2
    exact (g5001_zeta_analytic n φ hB).div (g5001_psi_analytic n φ hB) hψ0
  · intro φ hφ
    have hψ0 : psiAt n (muSeq φ n) φ ≠ 0 := hφ.2
    exact hψ0
  · intro _hgap
    exact signedRadius_eq_radiusQuotient_mul_antiDiscrim n (realSlice u)
      (sourceFamily.V_real (Set.mem_range_self u)) (g5001_psi_ne_zero_real n u)

end
end NlsGge.GKDefinitionDesign
