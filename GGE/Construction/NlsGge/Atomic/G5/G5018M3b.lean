import Mathlib
import NlsGge.Atomic.G5.G5018M3a
import NlsGge.Atomic.G5.G5024
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5.G5033Support1

                                                                                                             
                                                                                                          
                                                                                                                                          
                                                                                                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018_sourceF_fderiv_eq_zero
    (n : ℤ) (φ v : PotPair) (hφ : φ ∈ sourceW)
    (hΔ : ∀ z : ℂ,
      fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ v = 0) :
    fderiv ℂ (sourceF n) φ v = 0 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hFa : AnalyticAt ℂ (sourceF n) φ := sourceFamily.F_analytic n φ hφ
  have hFd : HasFDerivAt (sourceF n) (fderiv ℂ (sourceF n) φ) φ := hFa.differentiableAt.hasFDerivAt
  have hP : AnalyticAt ℂ (p2Fn38 n) (φ, sourceF n φ) :=
    (p2Fn_analytic38 n) (φ, sourceF n φ) ⟨hgk, mem_univ _⟩
  have hPd := hP.differentiableAt.hasFDerivAt
  have hidφ : HasFDerivAt (fun x : PotPair => x) (ContinuousLinearMap.id ℂ PotPair) φ :=
    hasFDerivAt_id φ
  have hidS : HasFDerivAt (fun x : P2Space38 n => x) (ContinuousLinearMap.id ℂ (P2Space38 n))
      (sourceF n φ) := hasFDerivAt_id _
  have hcomp : HasFDerivAt (fun ψ : PotPair => p2Fn38 n (ψ, sourceF n ψ))
      ((fderiv ℂ (p2Fn38 n) (φ, sourceF n φ)).comp
        ((ContinuousLinearMap.id ℂ PotPair).prod (fderiv ℂ (sourceF n) φ))) φ :=
    HasFDerivAt.comp (g := p2Fn38 n) (f := fun ψ : PotPair => (ψ, sourceF n ψ)) φ hPd
      (hidφ.prodMk hFd)
  have hzero : (fun ψ : PotPair => p2Fn38 n (ψ, sourceF n ψ)) =ᶠ[𝓝 φ] fun _ => 0 := by
    filter_upwards [sourceFamily.W_open.mem_nhds hφ] with ψ hψ
    exact sourceFamily.F_zero n ψ hψ
  have h0 := (hzero.hasFDerivAt_iff).mp hcomp
  have h1 := h0.unique (hasFDerivAt_const (0 : P2Space38 n) φ)
  have h2 := congrArg (fun L : PotPair →L[ℂ] P2Space38 n => L v) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at h2
  -- split the joint derivative
  set P := fderiv ℂ (p2Fn38 n) (φ, sourceF n φ) with hPdef
  have hsplit : P (v, fderiv ℂ (sourceF n) φ v) =
      P (v, 0) + P (0, fderiv ℂ (sourceF n) φ v) := by
    rw [← map_add]; simp
  -- phi-partial vanishes by M3'a
  have hpartφ : P (v, 0) = 0 := by
    have hd : HasFDerivAt (fun ψ : PotPair => p2Fn38 n (ψ, sourceF n φ))
        (P.comp ((ContinuousLinearMap.id ℂ PotPair).prod (0 : PotPair →L[ℂ] P2Space38 n))) φ :=
      HasFDerivAt.comp (g := p2Fn38 n) (f := fun ψ : PotPair => (ψ, sourceF n φ)) φ hPd
        (hidφ.prodMk (hasFDerivAt_const (sourceF n φ) φ))
    have hm3 := g5018_fixedNumerator_period_fderiv_eq_zero n (sourceF n φ) φ v hgk hΔ
    rw [hd.fderiv] at hm3
    simpa using hm3
  -- s-partial is injective
  have hpartS : fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ, y)) (sourceF n φ)
      (fderiv ℂ (sourceF n) φ v) = 0 := by
    have hd : HasFDerivAt (fun y : P2Space38 n => p2Fn38 n (φ, y))
        (P.comp ((0 : P2Space38 n →L[ℂ] PotPair).prod (ContinuousLinearMap.id ℂ (P2Space38 n))))
        (sourceF n φ) :=
      HasFDerivAt.comp (g := p2Fn38 n) (f := fun y : P2Space38 n => (φ, y)) (sourceF n φ) hPd
        ((hasFDerivAt_const φ (sourceF n φ)).prodMk hidS)
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]
    have : P (v, fderiv ℂ (sourceF n) φ v) = 0 := h2
    rw [hsplit, hpartφ, zero_add] at this
    exact this
  obtain ⟨M, hM⟩ := sourceFamily.F_inverse n φ hφ
  have hinj : Function.Injective (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ, y)) (sourceF n φ)) := by
    have hM' : (M : P2Space38 n →L[ℂ] P2Space38 n) =
        fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ, y)) (sourceF n φ) := hM
    rw [← hM']; exact M.injective
  exact hinj (by rw [hpartS, map_zero])

theorem g5018_normalizedRoot_offDiagonal_fderiv_eq_zero
    (n m : ℤ) (hmn : m ≠ n) (φ v : PotPair)
    (hφ : φ ∈ sourceW)
    (hΔ : ∀ z : ℂ,
      fderiv ℂ (fun ψ : PotPair => discrim ψ z) φ v = 0) :
    fderiv ℂ (fun ψ : PotPair => normalizedRoot n m ψ) φ v = 0 := by
  have hF := g5018_sourceF_fderiv_eq_zero n φ v hφ hΔ
  have hFd : DifferentiableAt ℂ (sourceF n) φ :=
    (sourceFamily.F_analytic n φ hφ).differentiableAt
  have hev : HasFDerivAt (fun ψ => sourceF n ψ ⟨m, hmn⟩)
      ((lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 ⟨m, hmn⟩).comp (fderiv ℂ (sourceF n) φ)) φ :=
    (lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 ⟨m, hmn⟩).hasFDerivAt.comp φ hFd.hasFDerivAt
  have hfun : (fun ψ : PotPair => normalizedRoot n m ψ) =
      fun ψ => countingCenter38 m + sourceF n ψ ⟨m, hmn⟩ := by
    funext ψ
    simp only [normalizedRoot, dif_pos hmn]
  rw [hfun, (hev.const_add (countingCenter38 m)).fderiv]
  simp [hF]

theorem g5018_psiAt_fderiv_eq_zero
    (n : ℤ) (z : ℂ) (φ v : PotPair) (hφ : φ ∈ sourceW)
    (hΔ : ∀ w : ℂ,
      fderiv ℂ (fun ψ : PotPair => discrim ψ w) φ v = 0) :
    fderiv ℂ (psiAt n z) φ v = 0 := by
  have hF := g5018_sourceF_fderiv_eq_zero n φ v hφ hΔ
  have hFd : DifferentiableAt ℂ (sourceF n) φ :=
    (sourceFamily.F_analytic n φ hφ).differentiableAt
  have h := NlsGge.ThirdConsultation.G5033Support1.fderiv_psiNumerator n (sourceF n) φ hFd z v
  have e : psiAt n z = fun ψ => p6PsiNumerator38 n (sourceF n) ψ z := rfl
  rw [e, h, hF]
  simp [p4NumeratorVariation38, Prod.mk_zero_zero]

end
end NlsGge.GKDefinitionDesign
