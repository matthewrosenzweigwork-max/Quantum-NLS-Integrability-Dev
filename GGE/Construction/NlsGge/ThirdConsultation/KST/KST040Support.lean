import Mathlib
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Analysis.NaturalCover
import NlsGge.Schur.FourierMultiplier
import NlsGge.Atomic.DM.DM009
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST006
import NlsGge.Atomic.KST.KST007
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST032
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Real

                                                                               
                                                                                             
                                                                                                               
                                                                                                                  
                                                                                                  
                                                                                                                    
                                                                                                                         
                                                                                                         
                                                                                                                        
                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory NlsGge.Schur NlsGge.Analysis NlsGge.Pilot
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST006 NlsGge.Atomic.KST007 NlsGge.Atomic.KST012
open NlsGge.DM009Psi
open NlsGge.Atomic.KST016 (localQ localCorrection localFreeFactor qParameter_apply
  potentialParameter_apply compMult_component)
open NlsGge.ThirdConsultation.KST.KST033R
open scoped InnerProductSpace

namespace NlsGge.ThirdConsultation.KST.KST040S

lemma psiG_Q (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hzb : star z ∈ spectralStrip n) (f : KSTPairL2) :
    PsiMap ε (NlsGge.Atomic.KST006.qOperator φ n z hz f) =
      NlsGge.Atomic.KST006.qOperator φ' n (star z) hzb (PsiMap ε f) := by
  have hεε := epsilon_sq ε hε
  have hrelF : ∀ k, potentialCoeff φ' false k = (ε : ℂ) * star (potentialCoeff φ true (-k)) := by
    intro k
    rw [potentialCoeff_eq, potentialCoeff_eq, hF, map_smul, cover_star, spectralCoeff_smul,
      spectralCoeff_star]
  have hrelT0 : ∀ k, potentialCoeff φ' true k = (ε : ℂ) * star (potentialCoeff φ false (-k)) := by
    intro k
    rw [potentialCoeff_eq, potentialCoeff_eq, hT, map_smul, cover_star, spectralCoeff_smul,
      spectralCoeff_star]
  have hrelT : ∀ k, star (potentialCoeff φ true k) = (ε : ℂ) * potentialCoeff φ' false (-k) := by
    intro k
    rw [hrelF (-k), neg_neg, ← mul_assoc, hεε, one_mul]
  have hrelF' : ∀ k, star (potentialCoeff φ false k) = (ε : ℂ) * potentialCoeff φ' true (-k) := by
    intro k
    rw [hrelT0 (-k), neg_neg, ← mul_assoc, hεε, one_mul]
  apply PiLp.ext
  intro b
  cases b
  · -- false component
    apply scalar_ext
    intro l
    rw [PsiMap_false, spectralCoeff_smul, spectralCoeff_star, Q_true_coeff φ n z hz f (-l),
      Q_false_coeff φ' n (star z) hzb (PsiMap ε f) l]
    simp only [PsiMap_true, spectralCoeff_star]
    have hR : ∑' m : ℤ, potentialCoeff φ' false (l - m) *
          (complementaryResolventCoeff n (star z) (-m) * star (spectralCoeff (f false) (-m))) =
        ∑' m : ℤ, potentialCoeff φ' false (l + m) *
          (complementaryResolventCoeff n (star z) m * star (spectralCoeff (f false) m)) := by
      rw [← tsum_neg_reindex (fun m : ℤ => potentialCoeff φ' false (l - m) *
          (complementaryResolventCoeff n (star z) (-m) * star (spectralCoeff (f false) (-m))))]
      refine tsum_congr (fun m => ?_)
      simp only [neg_neg, sub_neg_eq_add]
    rw [hR, star_tsum_int, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    simp only [star_mul']
    have e : -(-l - m) = l + m := by ring
    rw [hrelT, e, star_compl]
    linear_combination (potentialCoeff φ' false (l + m) *
      (complementaryResolventCoeff n (star z) m * star (spectralCoeff (f false) m))) * hεε
  · -- true component
    apply scalar_ext
    intro l
    rw [PsiMap_true, spectralCoeff_star, Q_false_coeff φ n z hz f (-l),
      Q_true_coeff φ' n (star z) hzb (PsiMap ε f) l]
    simp only [PsiMap_false, spectralCoeff_smul, spectralCoeff_star]
    have hR : ∑' m : ℤ, potentialCoeff φ' true (l - m) *
          (complementaryResolventCoeff n (star z) m *
            ((ε : ℂ) * star (spectralCoeff (f true) (-m)))) =
        ∑' m : ℤ, potentialCoeff φ' true (l + m) *
          (complementaryResolventCoeff n (star z) (-m) *
            ((ε : ℂ) * star (spectralCoeff (f true) m))) := by
      rw [← tsum_neg_reindex (fun m : ℤ => potentialCoeff φ' true (l - m) *
          (complementaryResolventCoeff n (star z) m *
            ((ε : ℂ) * star (spectralCoeff (f true) (-m)))))]
      refine tsum_congr (fun m => ?_)
      simp only [neg_neg, sub_neg_eq_add]
    rw [hR, star_tsum_int]
    refine tsum_congr (fun m => ?_)
    simp only [star_mul']
    have e : -(-l - m) = l + m := by ring
    rw [hrelF', e, star_compl]
    ring

lemma psiG_potential (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (u : KSTPairL2) :
    PsiMap ε (NlsGge.Atomic.KST012.potentialOnPn φ n u) =
      NlsGge.Atomic.KST012.potentialOnPn φ' n (PsiMap ε u) := by
  have hεε := epsilon_sq ε hε
  have hcF : naturalPhysicalCoverL2 (φ' false) =
      (ε : ℂ) • star (naturalPhysicalCoverL2 (φ true)) := by
    rw [hF, map_smul, cover_star]
  have hcT : naturalPhysicalCoverL2 (φ' true) =
      (ε : ℂ) • star (naturalPhysicalCoverL2 (φ false)) := by
    rw [hT, map_smul, cover_star]
  have hst : star (naturalPhysicalCoverL2 (φ false)) =
      (ε : ℂ) • naturalPhysicalCoverL2 (φ' true) := by
    rw [hcT, smul_smul, hεε, one_smul]
  have hst' : star (naturalPhysicalCoverL2 (φ true)) =
      (ε : ℂ) • naturalPhysicalCoverL2 (φ' false) := by
    rw [hcF, smul_smul, hεε, one_smul]
  apply PiLp.ext
  intro b
  cases b
  · rw [PsiMap_false, potentialOnPn_true, starS_smul, starS_mult, hst', map_smul,
      potentialOnPn_false, inner_upper_Psi ε hε]
    have key : ∀ (X : ℂ) (M : SpectralScalarL2),
        (ε : ℂ) • (X • ((ε : ℂ) • M)) = X • M := by
      intro X M
      rw [smul_comm X (ε : ℂ) M, smul_smul, hεε, one_smul]
    exact key _ _
  · rw [PsiMap_true, potentialOnPn_false, starS_smul, starS_mult, hst, neg_neg, map_smul,
      potentialOnPn_true, inner_lower_Psi ε hε]
    module

theorem psiG_qOperator (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (z z' : ℂ) (hz : z ∈ spectralStrip n) (hz' : z' ∈ spectralStrip n)
    (hzz : star z = z') (f : KSTPairL2) :
    PsiMap ε (qOperator φ n z hz f) = qOperator φ' n z' hz' (PsiMap ε f) := by
  subst hzz
  exact psiG_Q φ φ' ε hε hT hF n z hz hz' f

theorem psiG_localQ (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (w : ℂ) (x : KSTPairL2) :
    PsiMap ε (localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ') (PsiMap ε x) := by
  unfold localQ
  simp only [ContinuousLinearMap.mul_apply, qParameter_apply]
  rw [localFreeFactor_eq_sub, localFreeFactor_eq_sub,
    psiG_qOperator φ φ' ε hε hT hF n _ _ (NlsGge.ThirdConsultation.KST.center_mem_strip n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n),
    psiE_freeInv ε hε n _ (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n)]

theorem psiG_localQ_inv (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (w : ℂ) (y : KSTPairL2) :
    PsiMap ε (Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ)) y) =
      Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ')) (PsiMap ε y) :=
  (NlsGge.DM009Transport.transport_inverse (psiEBij ε hε)
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ))
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ'))
    (fun u => (psiG_localQ φ φ' ε hε hT hF n w u).symm) y).symm

theorem psiG_localCorrection (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (w : ℂ) (x : KSTPairL2) :
    PsiMap ε (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ') (PsiMap ε x) := by
  unfold localCorrection
  simp only [ContinuousLinearMap.mul_apply]
  rw [PsiMap_Pn ε hε, psiG_localQ_inv φ φ' ε hε hT hF n w,
    show PsiMap ε (NlsGge.Atomic.KST016.potentialParameter n φ x) =
      NlsGge.Atomic.KST016.potentialParameter n φ' (PsiMap ε x) from
      psiG_potential φ φ' ε hε hT hF n x]

theorem a_conj_G (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (u : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ' n u =
      star (NlsGge.ThirdConsultation.KST.a φ n (star u)) := by
  have h1 := PsiMap_inner ε hε (kstPnLower n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star u, φ) (kstPnLower n))
  rw [psiG_localCorrection φ φ' ε hε hT hF n (star u) (kstPnLower n), PsiMap_lower,
    star_star] at h1
  rw [← NlsGge.DM009Diag.diag_identity n φ' u, a_formula φ n (star u)]
  exact h1

theorem c_conj_G (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (u : ℂ) :
    NlsGge.ThirdConsultation.KST.c φ' n u =
      (ε : ℂ) * star (NlsGge.ThirdConsultation.KST.b φ n (star u)) := by
  have hεε := epsilon_sq ε hε
  have h1 := PsiMap_inner ε hε (kstPnLower n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star u, φ) (kstPnUpper n))
  rw [PsiMap_lower, psiG_localCorrection φ φ' ε hε hT hF n (star u) (kstPnUpper n),
    PsiMap_upper, star_star, map_smul, inner_smul_right] at h1
  have hb : star (NlsGge.ThirdConsultation.KST.b φ n (star u)) =
      (ε : ℂ) * NlsGge.ThirdConsultation.KST.c φ' n u := by
    rw [b_formula, c_formula]
    exact h1.symm
  rw [hb, ← mul_assoc, hεε, one_mul]

theorem b_conj_G (φ φ' : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (n : ℤ) (u : ℂ) :
    NlsGge.ThirdConsultation.KST.b φ' n u =
      (ε : ℂ) * star (NlsGge.ThirdConsultation.KST.c φ n (star u)) := by
  have hεε := epsilon_sq ε hε
  have h1 := PsiMap_inner ε hε (kstPnUpper n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star u, φ) (kstPnLower n))
  rw [PsiMap_upper, psiG_localCorrection φ φ' ε hε hT hF n (star u) (kstPnLower n),
    PsiMap_lower, star_star, inner_smul_left, Complex.conj_ofReal] at h1
  have hc : star (NlsGge.ThirdConsultation.KST.c φ n (star u)) =
      (ε : ℂ) * NlsGge.ThirdConsultation.KST.b φ' n u := by
    rw [c_formula, b_formula]
    exact h1.symm
  rw [hc, ← mul_assoc, hεε, one_mul]

theorem diagonalZero_conj (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : NlsGge.ThirdConsultation.KST.UnboundedWeight w) (φ φ' : PhysicalPairLp)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hT : φ' true = (ε : ℂ) • star (φ false)) (hF : φ' false = (ε : ℂ) • star (φ true))
    (hφ : φ ∈ NlsGge.ThirdConsultation.KST.physicalComponentBall w (2*M))
    (hφ' : φ' ∈ NlsGge.ThirdConsultation.KST.physicalComponentBall w (2*M))
    (n : ℤ) (hn : NlsGge.ThirdConsultation.KST.diagonalThreshold w M ≤ n.natAbs) :
    NlsGge.ThirdConsultation.KST.diagonalZero n φ' =
      star (NlsGge.ThirdConsultation.KST.diagonalZero n φ) := by
  obtain ⟨-, -, hmem, hfix, -⟩ := NlsGge.ThirdConsultation.KST.kst032 w M hM hw φ hφ n hn
  obtain ⟨-, -, -, -, huniq⟩ := NlsGge.ThirdConsultation.KST.kst032 w M hM hw φ' hφ' n hn
  set σ := NlsGge.ThirdConsultation.KST.diagonalZero n φ with hσ
  have hcen : star (NlsGge.ThirdConsultation.KST.center n) = NlsGge.ThirdConsultation.KST.center n :=
    center_star n
  have hmem' : star σ ∈ Metric.closedBall (NlsGge.ThirdConsultation.KST.center n) (Real.pi/48) := by
    have h1 : ‖σ - NlsGge.ThirdConsultation.KST.center n‖ ≤ Real.pi / 48 := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : star σ - NlsGge.ThirdConsultation.KST.center n =
        star (σ - NlsGge.ThirdConsultation.KST.center n) := by
      rw [star_sub, hcen]
    rw [e, norm_star]
    exact h1
  have hfix' : star σ =
      NlsGge.ThirdConsultation.KST.center n + NlsGge.ThirdConsultation.KST.a φ' n (star σ) := by
    rw [a_conj_G φ φ' ε hε hT hF n (star σ), star_star]
    calc star σ = star (NlsGge.ThirdConsultation.KST.center n +
          NlsGge.ThirdConsultation.KST.a φ n σ) := congrArg star hfix
      _ = _ := by rw [star_add, hcen]
  exact (huniq (star σ) hmem' hfix').symm

end NlsGge.ThirdConsultation.KST.KST040S
end
