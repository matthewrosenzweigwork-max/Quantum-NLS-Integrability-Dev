import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G5.G5017Support1
import NlsGge.Atomic.G5.G5017Host
import NlsGge.Atomic.G5.G5018Host
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5019Sup3
import NlsGge.Atomic.G5.G5024
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5029Host
import NlsGge.Atomic.G6.G6020

                                                                                
                                                                                                
                                                                                                                      
                                                                                            
                                                                                                                              
                                                                                                                                                   
                                                                                                       
                                                                                                                          
                                                                                                                                  
                                                                                                                               
                                                                                                                                
                                                                                                                           
                                                                                                                            
                                                                                                                           
                                                                                                                       
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5029Sup7Aux
noncomputable section

/-- The bilinear Poisson form on gradients. -/
theorem pairPoissonCLM_eq_omega (L M : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM L M =
      inner ℂ (star (pairGradientCLM L).1) (-Complex.I • (pairGradientCLM M).2) +
        inner ℂ (star (pairGradientCLM L).2) (Complex.I • (pairGradientCLM M).1) := by
  unfold pairPoissonCLM
  rw [clm_eq_bilinPair L]

theorem continuous_omega :
    Continuous (fun p : PotPair × PotPair =>
      inner ℂ (star p.1.1) (-Complex.I • p.2.2) + inner ℂ (star p.1.2) (Complex.I • p.2.1)) := by
  have hs : Continuous (fun x : PhysicalL2 => star x) := NlsGge.GK38.starLp.continuous
  have h1 : Continuous (fun p : PotPair × PotPair => star p.1.1) :=
    hs.comp (continuous_fst.comp continuous_fst)
  have h2 : Continuous (fun p : PotPair × PotPair => star p.1.2) :=
    hs.comp (continuous_snd.comp continuous_fst)
  have h3 : Continuous (fun p : PotPair × PotPair => -Complex.I • p.2.2) :=
    (continuous_snd.comp continuous_snd : Continuous (fun p : PotPair × PotPair => p.2.2)).const_smul (-Complex.I)
  have h4 : Continuous (fun p : PotPair × PotPair => Complex.I • p.2.1) :=
    (continuous_fst.comp continuous_snd : Continuous (fun p : PotPair × PotPair => p.2.1)).const_smul Complex.I
  exact (h1.inner h3).add (h2.inner h4)

theorem pairGradientCLM_sub (L M : PotPair →L[ℂ] ℂ) :
    pairGradientCLM (L - M) = pairGradientCLM L - pairGradientCLM M :=
  (NlsGge.ThirdConsultation.G5017Support1.pairGradientL).map_sub L M

theorem pairPoisson_eq_clm (f g : PotPair → ℂ) (φ : PotPair) :
    pairPoisson f g φ = pairPoissonCLM (fderiv ℂ f φ) (fderiv ℂ g φ) := rfl

theorem pairPoissonCLM_left (a : ℂ) (L1 L2 N : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM (a • (L1 - L2)) N = a * (pairPoissonCLM L1 N - pairPoissonCLM L2 N) := by
  unfold pairPoissonCLM
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]

theorem pairPoissonCLM_right (b : ℂ) (L M1 M2 : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM L (b • (M1 - M2)) = b * (pairPoissonCLM L M1 - pairPoissonCLM L M2) := by
  rw [pairPoissonCLM_antisymm, pairPoissonCLM_left, pairPoissonCLM_antisymm M1 L,
    pairPoissonCLM_antisymm M2 L]
  ring

theorem pairPoissonCLM_expand (a b : ℂ) (L1 L2 M1 M2 : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM (a • (L1 - L2)) (b • (M1 - M2)) =
      a * b * (pairPoissonCLM L1 M1 - pairPoissonCLM L1 M2 - pairPoissonCLM L2 M1 +
        pairPoissonCLM L2 M2) := by
  rw [pairPoissonCLM_left, pairPoissonCLM_right, pairPoissonCLM_right]
  ring

theorem pairPoissonCLM_self (L : PotPair →L[ℂ] ℂ) : pairPoissonCLM L L = 0 := by
  have h := pairPoissonCLM_antisymm L L
  linear_combination h / 2

/-- Gradient of a scaled difference of two differentials. -/
theorem grad_smul_sub (a : ℂ) (f g : PotPair → ℂ) (φ : PotPair) :
    a • (pairGradient f φ - pairGradient g φ) =
      pairGradientCLM (a • (fderiv ℂ f φ - fderiv ℂ g φ)) := by
  unfold pairGradient
  rw [NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_smul, pairGradientCLM_sub]

theorem grad_limit (A : PotPair →L[ℂ] ℂ) (Ai Li : ℕ → (PotPair →L[ℂ] ℂ))
    (hA : Tendsto Ai atTop (𝓝 A))
    (hT : Tendsto (fun i => pairGradientCLM (Ai i) - pairGradientCLM (Li i)) atTop (𝓝 0)) :
    Tendsto (fun i => pairGradientCLM (Li i)) atTop (𝓝 (pairGradientCLM A)) := by
  have C := (G5019Sup3.continuous_pairGradientCLM.tendsto _).comp hA
  have h := C.sub hT
  rw [sub_zero] at h
  refine h.congr (fun i => ?_)
  simp only [Function.comp_apply]
  abel

theorem bracket_limit (A B : PotPair →L[ℂ] ℂ) (Li Mi : ℕ → (PotPair →L[ℂ] ℂ))
    (hL : Tendsto (fun i => pairGradientCLM (Li i)) atTop (𝓝 (pairGradientCLM A)))
    (hM : Tendsto (fun i => pairGradientCLM (Mi i)) atTop (𝓝 (pairGradientCLM B))) :
    Tendsto (fun i => pairPoissonCLM (Li i) (Mi i)) atTop (𝓝 (pairPoissonCLM A B)) := by
  have h := (continuous_omega.tendsto _).comp (hL.prodMk_nhds hM)
  rw [pairPoissonCLM_eq_omega]
  refine h.congr (fun i => ?_)
  simp only [Function.comp_apply]
  rw [pairPoissonCLM_eq_omega]

theorem expand_diag (a b : ℂ) (L1 L2 : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM (a • (L1 - L2)) (b • (L1 - L2)) = 0 := by
  rw [pairPoissonCLM_expand, pairPoissonCLM_self, pairPoissonCLM_self,
    pairPoissonCLM_antisymm L2 L1]
  ring

theorem expand_offdiag (p q dk dl : ℂ) (hk : dk ≠ 0) (hl : dl ≠ 0) (L1 L2 M1 M2 : PotPair →L[ℂ] ℂ)
    (e1 : pairPoissonCLM L1 M1 = 0) (e2 : pairPoissonCLM L2 M2 = 0) :
    pairPoissonCLM ((p / dk) • (L1 - L2)) ((q / dl) • (M1 - M2)) =
      p * q * (pairPoissonCLM M1 L2 / (dl * dk) - pairPoissonCLM L1 M2 / (dk * dl)) := by
  rw [pairPoissonCLM_expand, e1, e2, pairPoissonCLM_antisymm L2 M1]
  field_simp
  ring

theorem psi_limit (m : ℤ) (x : ℕ → PotPair) (x0 : PotPair) (z : ℕ → ℂ) (z0 : ℂ)
    (h : ContinuousAt (fun q : PotPair × ℂ => psiAt m q.2 q.1) (x0, z0))
    (hx : Tendsto x atTop (𝓝 x0)) (hz : Tendsto z atTop (𝓝 z0)) :
    Tendsto (fun i => psiAt m (z i) (x i)) atTop (𝓝 (psiAt m z0 x0)) := by
  have hp : Tendsto (fun i => ((x i, z i) : PotPair × ℂ)) atTop (𝓝 ((x0, z0) : PotPair × ℂ)) :=
    hx.prodMk_nhds hz
  have h1 := h.tendsto.comp hp
  exact h1

/-- The scaled differences `a_i (d mu_k - d lam_k)` along an approximating sequence. -/
def scaledDiff (k m : ℤ) (φ : ℕ → PhysicalL2) (i : ℕ) : PotPair →L[ℂ] ℂ :=
  (psiAt m (muSeq (realSlice (φ i)) k) (realSlice (φ i)) /
      antiDiscrim (realSlice (φ i)) (muSeq (realSlice (φ i)) k)) •
    (fderiv ℂ (fun ψ => muSeq ψ k) (realSlice (φ i)) -
      fderiv ℂ (fun ψ => lamMinus ψ k) (realSlice (φ i)))

theorem scaledDiff_grad_limit (k m : ℤ) (w : PhysicalL2) (φ : ℕ → PhysicalL2)
    (hA : Tendsto (fun i => angleIntegralDerivative k m (realSlice (φ i))) atTop
      (𝓝 (angleIntegralDerivative k m (realSlice w))))
    (T : Tendsto (fun j : ℕ =>
        let ψ0 := realSlice (φ j)
        pairGradientCLM (angleIntegralDerivative k m ψ0) -
          (psiAt m (muSeq ψ0 k) ψ0 / antiDiscrim ψ0 (muSeq ψ0 k)) •
            (pairGradient (fun ψ => muSeq ψ k) ψ0 -
              pairGradient (fun ψ => lamMinus ψ k) ψ0)) atTop (𝓝 0)) :
    Tendsto (fun i => pairGradientCLM (scaledDiff k m φ i)) atTop
      (𝓝 (pairGradientCLM (angleIntegralDerivative k m (realSlice w)))) := by
  refine grad_limit (angleIntegralDerivative k m (realSlice w))
    (fun i => angleIntegralDerivative k m (realSlice (φ i))) (scaledDiff k m φ) hA ?_
  refine T.congr (fun i => ?_)
  simp only [scaledDiff, grad_smul_sub]

theorem lim0_offdiag (ψ1 ψ2 dk dl : ℕ → ℂ) (L1 L2 M1 M2 : ℕ → (PotPair →L[ℂ] ℂ)) (c1 c2 : ℂ)
    (hP1 : Tendsto ψ1 atTop (𝓝 c1)) (hP2 : Tendsto ψ2 atTop (𝓝 c2))
    (hdk : ∀ i, dk i ≠ 0) (hdl : ∀ i, dl i ≠ 0)
    (e1 : ∀ i, pairPoissonCLM (L1 i) (M1 i) = 0) (e2 : ∀ i, pairPoissonCLM (L2 i) (M2 i) = 0)
    (Q1 : Tendsto (fun i => pairPoissonCLM (L1 i) (M2 i) / (dk i * dl i)) atTop (𝓝 0))
    (Q2 : Tendsto (fun i => pairPoissonCLM (M1 i) (L2 i) / (dl i * dk i)) atTop (𝓝 0)) :
    Tendsto (fun i => pairPoissonCLM ((ψ1 i / dk i) • (L1 i - L2 i)) ((ψ2 i / dl i) • (M1 i - M2 i)))
      atTop (𝓝 0) := by
  have hlim := (hP1.mul hP2).mul (Q2.sub Q1)
  rw [sub_self, mul_zero] at hlim
  refine hlim.congr (fun i => ?_)
  exact (expand_offdiag _ _ _ _ (hdk i) (hdl i) _ _ _ _ (e1 i) (e2 i)).symm

/-- Step 1: the open-gap all-left case. -/
theorem open_left_bracket_zero
    (h27 : ∀ (k m : ℤ) (u₀ : PhysicalL2) (u : ℕ → PhysicalL2),
      gamma2 (realSlice u₀) k ≠ 0 →
      gkMu u₀ k = actualGapLowerAllE02_38 u₀ k →
      (∀ j : ℕ, u j ∈ isospectralSet u₀) →
      (∀ j : ℕ, InteriorRealDirichletGap k (u j)) →
      Tendsto u atTop (𝓝 u₀) →
      (∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0) ∧
      Tendsto (fun j : ℕ =>
        let φ := realSlice (u j)
        pairGradientCLM (angleIntegralDerivative k m φ) -
          (psiAt m (muSeq φ k) φ / antiDiscrim φ (muSeq φ k)) •
            (pairGradient (fun ψ => muSeq ψ k) φ -
              pairGradient (fun ψ => lamMinus ψ k) φ)) atTop (𝓝 0))
    (h28 : ∀ (k l : ℤ), k ≠ l → ∀ (u₀ : PhysicalL2) (u : ℕ → PhysicalL2),
      gamma2 (realSlice u₀) k ≠ 0 → gamma2 (realSlice u₀) l ≠ 0 →
      gkMu u₀ k = actualGapLowerAllE02_38 u₀ k →
      gkMu u₀ l = actualGapLowerAllE02_38 u₀ l →
      (∀ j : ℕ, u j ∈ isospectralSet u₀) →
      (∀ j : ℕ, InteriorRealDirichletGap k (u j) ∧ InteriorRealDirichletGap l (u j)) →
      Tendsto u atTop (𝓝 u₀) →
      (∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0 ∧
        antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) l) ≠ 0) ∧
      Tendsto (fun j : ℕ =>
        let φ := realSlice (u j)
        pairPoisson (fun ψ => muSeq ψ k) (fun ψ => lamMinus ψ l) φ /
          (antiDiscrim φ (muSeq φ k) * antiDiscrim φ (muSeq φ l))) atTop (𝓝 0))
    (happ : ∀ (w : PhysicalL2) (k l : ℤ),
      gkMu w k = actualGapLowerAllE02_38 w k → gkMu w l = actualGapLowerAllE02_38 w l →
      actualGapLowerAllE02_38 w k < actualGapUpperAllE02_38 w k →
      actualGapLowerAllE02_38 w l < actualGapUpperAllE02_38 w l →
      ∃ φ : ℕ → PhysicalL2, (∀ i : ℕ, φ i ∈ isospectralSet w) ∧
        (∀ i : ℕ, InteriorRealDirichletGap k (φ i) ∧ InteriorRealDirichletGap l (φ i)) ∧
        Tendsto φ atTop (𝓝 w))
    (hmumu : ∀ (v : PhysicalL2) (k l : ℤ),
      pairPoisson (fun ψ : PotPair => muSeq ψ k) (fun ψ : PotPair => muSeq ψ l) (realSlice v) = 0)
    (hlamlam : ∀ (v : PhysicalL2) (k l : ℤ),
      InteriorRealDirichletGap k v → InteriorRealDirichletGap l v →
      pairPoisson (fun ψ : PotPair => lamMinus ψ k) (fun ψ : PotPair => lamMinus ψ l) (realSlice v) = 0)
    (hpsi : ∀ (m : ℤ) (u : PhysicalL2) (z : ℂ),
      ContinuousAt (fun q : PotPair × ℂ => psiAt m q.2 q.1) (realSlice u, z))
    (hmu : ∀ (u₀ : PhysicalL2) (u : ℕ → PhysicalL2), Tendsto u atTop (𝓝 u₀) → ∀ n : ℤ,
      Tendsto (fun j : ℕ => muSeq (realSlice (u j)) n) atTop (𝓝 (muSeq (realSlice u₀) n)))
    (hcont : ∀ (k m : ℤ) (u : PhysicalL2), gamma2 (realSlice u) m ≠ 0 →
      ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative k m (realSlice w)) u)
    (hlow : ∀ (u : PhysicalL2) (n : ℤ), gamma2 (realSlice u) n ≠ 0 →
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n)
    (w : PhysicalL2) (k l m n : ℤ) (hleft : AllDirichletLeft w)
    (hk : gamma2 (realSlice w) k ≠ 0) (hl : gamma2 (realSlice w) l ≠ 0)
    (hm : gamma2 (realSlice w) m ≠ 0) (hn : gamma2 (realSlice w) n ≠ 0) :
    pairPoissonCLM (angleIntegralDerivative k m (realSlice w))
      (angleIntegralDerivative l n (realSlice w)) = 0 := by
  obtain ⟨φ, hiso, hint, hφ⟩ := happ w k l (hleft k) (hleft l) (hlow w k hk) (hlow w l hl)
  obtain ⟨hδk, T1⟩ := h27 k m w φ hk (hleft k) hiso (fun i => (hint i).1) hφ
  obtain ⟨hδl, T2⟩ := h27 l n w φ hl (hleft l) hiso (fun i => (hint i).2) hφ
  have hX0 := (realSlice.continuous.tendsto w).comp hφ
  have hX : Tendsto (fun i => realSlice (φ i)) atTop (𝓝 (realSlice w)) := hX0
  have hA1 := (hcont k m w hm).tendsto.comp hφ
  have hA2 := (hcont l n w hn).tendsto.comp hφ
  have G1 := scaledDiff_grad_limit k m w φ hA1 T1
  have G2 := scaledDiff_grad_limit l n w φ hA2 T2
  have Lim1 := bracket_limit (angleIntegralDerivative k m (realSlice w))
    (angleIntegralDerivative l n (realSlice w)) (scaledDiff k m φ) (scaledDiff l n φ) G1 G2
  have Lim0 : Tendsto (fun i => pairPoissonCLM (scaledDiff k m φ i) (scaledDiff l n φ i)) atTop (𝓝 0) := by
    by_cases hkl : k = l
    · subst hkl
      exact tendsto_const_nhds.congr (fun i => (expand_diag _ _ _ _).symm)
    · obtain ⟨hδ, Q1⟩ := h28 k l hkl w φ hk hl (hleft k) (hleft l) hiso hint hφ
      obtain ⟨-, Q2⟩ := h28 l k (Ne.symm hkl) w φ hl hk (hleft l) (hleft k) hiso
        (fun i => ⟨(hint i).2, (hint i).1⟩) hφ
      have P1 := psi_limit m (fun i => realSlice (φ i)) (realSlice w)
        (fun i => muSeq (realSlice (φ i)) k) (muSeq (realSlice w) k)
        (hpsi m w (muSeq (realSlice w) k)) hX (hmu w φ hφ k)
      have P2 := psi_limit n (fun i => realSlice (φ i)) (realSlice w)
        (fun i => muSeq (realSlice (φ i)) l) (muSeq (realSlice w) l)
        (hpsi n w (muSeq (realSlice w) l)) hX (hmu w φ hφ l)
      exact lim0_offdiag _ _ _ _ _ _ _ _ _ _ P1 P2 (fun i => (hδ i).1) (fun i => (hδ i).2)
        (fun i => hmumu (φ i) k l) (fun i => hlamlam (φ i) k l (hint i).1 (hint i).2) Q1 Q2
  exact tendsto_nhds_unique Lim1 Lim0

/-- Step 2: the retained G5029 head from step 1, the all-left open-gap density and the continuity of the bracket. -/
theorem g5029_core
    (hopen : ∀ (w : PhysicalL2) (k l m n : ℤ), AllDirichletLeft w →
      gamma2 (realSlice w) k ≠ 0 → gamma2 (realSlice w) l ≠ 0 →
      gamma2 (realSlice w) m ≠ 0 → gamma2 (realSlice w) n ≠ 0 →
      pairPoissonCLM (angleIntegralDerivative k m (realSlice w))
        (angleIntegralDerivative l n (realSlice w)) = 0)
    (happF : ∀ (u : PhysicalL2), AllDirichletLeft u → ∀ (F : Finset ℤ),
      ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧
        (∀ j : ℕ, AllDirichletLeft (v j)) ∧
        ∀ (j : ℕ) (n : ℤ), n ∈ F → gamma2 (realSlice (v j)) n ≠ 0)
    (hcontOn : ∀ (k l m n : ℤ),
      ContinuousOn
        (fun u : PhysicalL2 =>
          pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
            (angleIntegralDerivative l n (realSlice u)))
        {u : PhysicalL2 | gamma2 (realSlice u) m ≠ 0 ∧
          gamma2 (realSlice u) n ≠ 0})
    (u : PhysicalL2) (k l m n : ℤ)
    (hleft : AllDirichletLeft u) (hm : gamma2 (realSlice u) m ≠ 0)
    (hn : gamma2 (realSlice u) n ≠ 0) :
    pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
      (angleIntegralDerivative l n (realSlice u)) = 0 := by
  obtain ⟨v, hv, hvleft, hvopen⟩ := happF u hleft {k, l, m, n}
  have hz : ∀ j : ℕ, pairPoissonCLM (angleIntegralDerivative k m (realSlice (v j)))
      (angleIntegralDerivative l n (realSlice (v j))) = 0 := fun j =>
    hopen (v j) k l m n (hvleft j) (hvopen j k (by simp)) (hvopen j l (by simp))
      (hvopen j m (by simp)) (hvopen j n (by simp))
  have hvS : Tendsto v atTop (𝓝[{u : PhysicalL2 | gamma2 (realSlice u) m ≠ 0 ∧
      gamma2 (realSlice u) n ≠ 0}] u) :=
    tendsto_nhdsWithin_iff.2 ⟨hv, Eventually.of_forall fun j =>
      ⟨hvopen j m (by simp), hvopen j n (by simp)⟩⟩
  have hT := ((hcontOn k l m n) u ⟨hm, hn⟩).tendsto.comp hvS
  have h0 : Tendsto (fun j : ℕ => pairPoissonCLM (angleIntegralDerivative k m (realSlice (v j)))
      (angleIntegralDerivative l n (realSlice (v j)))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun j => (hz j).symm)
  exact tendsto_nhds_unique hT h0

end
end G5029Sup7Aux
end NlsGge.GKDefinitionDesign
