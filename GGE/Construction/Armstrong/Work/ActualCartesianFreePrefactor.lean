import Armstrong.Work.CartesianTerminalRootSpec
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.GK38.GradFundamentalFree
import NlsGge.GK38.GradTauGammaKernelContinuity
import NlsGge.GK38.AbelianFreeProbe
import NlsGge.GK38.Lib.EntireProductsC34a
import NlsGge.GK38.GradEigenClosedKernelAlgebra
import NlsGge.GK38.PairAsymptoticsSeqFourier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The actual free terminal denominator and half-minus Cartesian prefactor.
All labels are signed integers; the two potential directions are independent
complex L2 classes. No family, beta, physical map or Poisson premise is used. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- First missing literal calibration: the denominator of the actual
terminal root at the free Dirichlet label, retaining every signed label. -/
theorem gk16_terminal_denominator_at_zero38 (n : ℤ) :
    (((2*Complex.I)/(Lib.piN n : ℂ)) *
      a5OmittedRootProduct38 n ((0 : PotPair),muSeq 0 n)) =
        2*Complex.I*Complex.cos ((n : ℂ)*(Real.pi : ℂ)) := by
  have hprod : a5OmittedRootProduct38 n ((0 : PotPair),muSeq 0 n) =
      (Lib.piN n : ℂ)*Complex.cos ((n : ℂ)*(Real.pi : ℂ)) := by
    rw [← a5CriticalNumerator_free38 n (muSeq 0 n)]
    simp only [a5CriticalNumerator38,P2FreeProbe.criticalShift_zero,
      muSeq_zero38,countingCenter38,Lib.omitProd_zero_at_root]
  rw [hprod]
  field_simp [Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)] <;> ring

/-- First useful derivative bridge. The half-minus algebraic prefactor
already has the desired reflected Fourier differential. Differentiability
is included explicitly before the displayed fderiv identity. -/
theorem gk16_minus_prefactor_at_zero_derivative38 (n : ℤ) :
    DifferentiableAt ℂ
      (fun phi : PotPair => tauN phi n-muSeq phi n-gk16TerminalRoot38 n phi) 0 ∧
    ∀ h : PotPair,
      (fderiv ℂ
        (fun phi : PotPair => tauN phi n-muSeq phi n-gk16TerminalRoot38 n phi)
        (0 : PotPair)) h = -physicalFourier h.1 (-n) := by
  classical
  have hzero : (0 : PotPair) ∈ gkW := by
    simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)
  let k : ℂ := (n : ℂ)*(Real.pi : ℂ)
  let c : ℂ := Complex.cos k
  let e : ℤ → ℝ → ℂ := fun m t =>
    Complex.exp (-(2*Complex.I*(Real.pi : ℂ)*(m : ℂ)*(t : ℂ)))
  have hmu0 : muSeq (0 : PotPair) n = k := by
    rw [muSeq_zero38]
    rfl
  have hsin : Complex.sin k = 0 := Complex.sin_int_mul_pi n
  have hexp : Complex.exp (Complex.I*k) = c := by
    rw [mul_comm Complex.I k,Complex.exp_mul_I,hsin,zero_mul,add_zero]
  have hexpneg : Complex.exp (-Complex.I*k) = c := by
    rw [show -Complex.I*k=(-k)*Complex.I by ring,Complex.exp_mul_I,
      Complex.cos_neg,Complex.sin_neg,hsin,neg_zero,zero_mul,add_zero]
  have hecont (m : ℤ) : Continuous (e m) := by
    dsimp [e]
    fun_prop
  have hei (v : PhysicalL2) (m : ℤ) :
      IntervalIntegrable (fun t => e m t*coverRep38 v t) volume 0 1 :=
    (intervalIntegrable_coverRep38_one v).continuousOn_mul (hecont m).continuousOn
  have heFourier (v : PhysicalL2) (m : ℤ) :
      (∫ t in (0 : ℝ)..1, e m t*coverRep38 v t)=physicalFourier v m := by
    rw [physicalFourier,fourierCoeff_eq_intervalIntegral _ _ (0 : ℝ)]
    simp only [zero_add,div_one,one_smul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_ae_phys v] with t ht _
    rw [ht]
    simp only [smul_eq_mul,seqFourierNegative38]
    rfl
  let w : PairKernelCont38 :=
    GradEigen38.state (0 : PotPair) (muSeq 0 n) (![1,1] : PairVec38)
  have hw (t : GradEigen38.Time) : w t =
      ![Complex.exp (-Complex.I*k*(t : ℝ)),Complex.exp (Complex.I*k*(t : ℝ))] := by
    dsimp [w]
    rw [hmu0,GradEigen38.probe_free_state]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mul_one]
  have hwprod (t : GradEigen38.Time) : w t 0*w t 1=1 := by
    rw [hw]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,← Complex.exp_add]
    convert Complex.exp_zero using 1 <;> congr 1 <;> ring
  have hQ : GradEigen38.Q w=2 := by
    have hp (s : ℝ) : pairKernelExt38 w s 0*pairKernelExt38 w s 1=1 := by
      change w (projIcc 0 1 zero_le_one s) 0*w (projIcc 0 1 zero_le_one s) 1=1
      exact hwprod _
    simp [GradEigen38.Q,hp]
  have hsquare (t : GradEigen38.Time) :
      GradEigen38.square w t=![e (-n) t,e n t] := by
    change starProd38 (w t) (w t)=_
    rw [hw]
    funext i
    fin_cases i
    · change Complex.exp (Complex.I*k*(t : ℝ)) *
        Complex.exp (Complex.I*k*(t : ℝ)) = e (-n) t
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      dsimp [e,k]
      push_cast
      ring
    · change Complex.exp (-Complex.I*k*(t : ℝ)) *
        Complex.exp (-Complex.I*k*(t : ℝ)) = e n t
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      dsimp [e,k]
      ring
  have hpair (h : PotPair) :
      integralPairCLM38 (GradEigen38.square w) GradEigen38.t1 h =
        physicalFourier h.1 (-n)+physicalFourier h.2 n := by
    change (∫ s in (0 : ℝ)..1,
      pairKernelExt38 (GradEigen38.square w) s 0*coverRep38 h.1 s+
        pairKernelExt38 (GradEigen38.square w) s 1*coverRep38 h.2 s)=_
    calc
      _ = ∫ s in (0 : ℝ)..1,
          e (-n) s*coverRep38 h.1 s+e n s*coverRep38 h.2 s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using hs
        change pairKernelExt38 (GradEigen38.square w) s 0*coverRep38 h.1 s+
          pairKernelExt38 (GradEigen38.square w) s 1*coverRep38 h.2 s =
            e (-n) s*coverRep38 h.1 s+e n s*coverRep38 h.2 s
        simp only [pairKernelExt38_of_mem _ hs',hsquare,
          Matrix.cons_val_zero,Matrix.cons_val_one]
      _ = _ := by
        rw [intervalIntegral.integral_add (hei h.1 (-n)) (hei h.2 n),
          heFourier,heFourier]
  let M : PotPair →L[ℂ] ℂ := GradEigen38.bilinearGradient w
  have hMu : HasFDerivAt (fun phi : PotPair => muSeq phi n) M 0 :=
    (angleDirichlet_analytic_derivative38 0 hzero n).2
  have hM (h : PotPair) : M h=
      (physicalFourier h.1 (-n)+physicalFourier h.2 n)/2 := by
    change (GradEigen38.Q w)⁻¹*
      integralPairCLM38 (GradEigen38.square w) GradEigen38.t1 h=_
    rw [hQ,hpair]
    ring
  have hTauKernel : gradTauCont38 0 n=0 := by
    ext t i
    rw [gradTauCont38_apply 0 hzero n t,gradTau38_zero]
    rfl
  have hTau : HasFDerivAt (fun phi : PotPair => tauN phi n)
      (0 : PotPair →L[ℂ] ℂ) (0 : PotPair) := by
    have ht := hasFDerivAt_gradTauCont38 0 hzero n
    rw [hTauKernel] at ht
    have hz : integralPairCLM38 (0 : PairKernelCont38) ⟨1,zero_le_one,le_rfl⟩=0 := by
      change k4aKernelPairingMap38 (0 : PairKernelCont38) = 0
      exact map_zero k4aKernelPairingMap38
    simpa only [hz] using ht
  have hAntiKernel (t : GradEigen38.Time) :
      gradAntiDiscrim38 0 k t=![Complex.I*c*e (-n) t,-Complex.I*c*e n t] := by
    have hp : Complex.exp (-Complex.I*k*(1-2*(t : ℝ)))=c*e (-n) t := by
      rw [show -Complex.I*k*(1-2*(t : ℝ))=
        -Complex.I*k+(-(2*Complex.I*(Real.pi : ℂ)*((-n : ℤ) : ℂ)*(t : ℂ))) by
          dsimp [k]
          push_cast
          ring,Complex.exp_add,hexpneg]
    have hm : Complex.exp (Complex.I*k*(1-2*(t : ℝ)))=c*e n t := by
      rw [show Complex.I*k*(1-2*(t : ℝ))=
        Complex.I*k+(-(2*Complex.I*(Real.pi : ℂ)*(n : ℂ)*(t : ℂ))) by
          dsimp [k]
          push_cast
          ring,Complex.exp_add,hexp]
    have hg := scaled_gradAntiDiscrim38_zero k t
    rw [hp,hm] at hg
    have hh : gradAntiDiscrim38 0 k t=
        (-Complex.I) • (![-(c*e (-n) t),c*e n t] : PairVec38) := by
      calc
        _ = ((-Complex.I)*Complex.I) • gradAntiDiscrim38 0 k t := by
          simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]
        _ = (-Complex.I) • (Complex.I • gradAntiDiscrim38 0 k t) := by
          rw [smul_smul]
        _ = _ := congrArg (fun v : PairVec38 => (-Complex.I) • v) hg
    rw [hh]
    funext i
    fin_cases i
    · change (-Complex.I)*(-(c*e (-n) t)) = Complex.I*c*e (-n) t
      ring
    · change (-Complex.I)*(c*e n t) = -Complex.I*c*e n t
      ring
  have hAntiValue (h : PotPair) : gradAntiDiscrimCLM 0 k h=
      Complex.I*c*(physicalFourier h.1 (-n)-physicalFourier h.2 n) := by
    rw [gradAntiDiscrimCLM_apply]
    calc
      _ = ∫ s in (0 : ℝ)..1,
          (Complex.I*c)*(e (-n) s*coverRep38 h.1 s)+
            (-Complex.I*c)*(e n s*coverRep38 h.2 s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using hs
        change gradAntiDiscrim38 0 k s 0*coverRep38 h.1 s+
          gradAntiDiscrim38 0 k s 1*coverRep38 h.2 s =
            (Complex.I*c)*(e (-n) s*coverRep38 h.1 s)+
              (-Complex.I*c)*(e n s*coverRep38 h.2 s)
        have hk : gradAntiDiscrim38 0 k s =
            ![Complex.I*c*e (-n) s,-Complex.I*c*e n s] :=
          hAntiKernel ⟨s,hs'⟩
        simp only [hk,Matrix.cons_val_zero,Matrix.cons_val_one]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hei h.1 (-n)).const_mul (Complex.I*c))
          ((hei h.2 n).const_mul (-Complex.I*c)),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          heFourier,heFourier]
        ring
  have hAntiFree : antiDiscrim (0 : PotPair)=fun _ => (0 : ℂ) := by
    funext z
    simp [antiDiscrim,monodromyPair_zero_potential,freeE]
  have hspec : spectralAntiDiscrimIntegral38 0 k=0 := by
    rw [← deriv_antiDiscrim_spectral38,hAntiFree]
    simp
  let J : PotPair × ℂ →L[ℂ] ℂ :=
    fderiv ℂ (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (0,k)
  have hJ (h : PotPair) : J (h,M h)=gradAntiDiscrimCLM 0 k h := by
    have hp : J (h,0)=gradAntiDiscrimCLM 0 k h := by
      exact congrArg (fun L : PotPair →L[ℂ] ℂ => L h)
        (GradEigen38.anti_joint_potential_partial 0 k)
    have hs : J (0,1)=0 :=
      (GradEigen38.anti_joint_spectral_partial 0 k).trans hspec
    calc
      J (h,M h)=J ((h,0)+(M h) • ((0 : PotPair),(1 : ℂ))) := by
        congr 1
        simp
      _ = J (h,0)+(M h)*J (0,1) := by rw [map_add,map_smul]; rfl
      _ = _ := by rw [hp,hs,mul_zero,add_zero]
  let A : PotPair → ℂ := fun phi => antiDiscrim phi (muSeq phi n)
  let L : PotPair →L[ℂ] ℂ :=
    J.comp ((ContinuousLinearMap.id ℂ PotPair).prod M)
  have hA : HasFDerivAt A L 0 := by
    have hj : HasFDerivAt (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) J (0,k) :=
      (analyticOnNhd_antiDiscrim (0,k) (mem_univ _)).differentiableAt.hasFDerivAt
    have hgraph := (hasFDerivAt_id (0 : PotPair)).prodMk hMu
    have hj' : HasFDerivAt (fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
        J ((0 : PotPair),muSeq 0 n) := by simpa only [hmu0] using hj
    exact hj'.comp 0 hgraph
  have hL (h : PotPair) : L h=
      Complex.I*c*(physicalFourier h.1 (-n)-physicalFourier h.2 n) := by
    change J (h,M h)=_
    rw [hJ,hAntiValue]
  let D : PotPair → ℂ := fun phi => ((2*Complex.I)/(Lib.piN n : ℂ))*
    a5OmittedRootProduct38 n (phi,muSeq phi n)
  have hD0 : D 0=2*Complex.I*c := gk16_terminal_denominator_at_zero38 n
  have hDne : D 0 ≠ 0 := gk16_terminal_denominator_ne_zero38 n 0 hzero
  have hDanalytic : AnalyticAt ℂ D 0 := by
    have hdom : ((0 : PotPair),muSeq 0 n) ∈ a5OmittedRootDomain38 n := by
      rw [muSeq_zero38]
      exact a5OmittedRoot_free_center_mem38 n
    have hgraph : AnalyticAt ℂ (fun phi : PotPair => (phi,muSeq phi n)) 0 :=
      analyticAt_id.prod (angleDirichlet_analytic_derivative38 0 hzero n).1
    have hOmittedGraph : AnalyticAt ℂ
        (fun phi : PotPair => a5OmittedRootProduct38 n (phi,muSeq phi n)) (0 : PotPair) :=
      AnalyticAt.comp (g := a5OmittedRootProduct38 n)
        (f := fun phi : PotPair => (phi,muSeq phi n)) (x := (0 : PotPair))
        (a5OmittedRoot_analytic38 n ((0 : PotPair),muSeq 0 n) hdom) hgraph
    exact analyticAt_const.mul hOmittedGraph
  have hH : HasFDerivAt (gk16TerminalRoot38 n)
      (fderiv ℂ (gk16TerminalRoot38 n) 0) 0 :=
    (gk16_terminal_root_analytic38 n 0 hzero).differentiableAt.hasFDerivAt
  have hH0 : gk16TerminalRoot38 n 0=0 := by
    simp only [gk16TerminalRoot38,hAntiFree,zero_div]
  have hproduct : (fun phi => gk16TerminalRoot38 n phi*D phi)=ᶠ[𝓝 (0 : PotPair)] A := by
    filter_upwards [isOpen_gkW.mem_nhds hzero] with phi hphi
    exact div_mul_cancel₀ _ (gk16_terminal_denominator_ne_zero38 n phi hphi)
  have hrelation :=
    ((hH.mul hDanalytic.differentiableAt.hasFDerivAt).congr_of_eventuallyEq
      hproduct.symm).unique hA
  have hHvalue (h : PotPair) : (fderiv ℂ (gk16TerminalRoot38 n) 0) h=
      (physicalFourier h.1 (-n)-physicalFourier h.2 n)/2 := by
    have hr := congrArg (fun T : PotPair →L[ℂ] ℂ => T h) hrelation
    change gk16TerminalRoot38 n 0*(fderiv ℂ D 0) h+
      D 0*(fderiv ℂ (gk16TerminalRoot38 n) 0) h=L h at hr
    rw [hH0,zero_mul,zero_add] at hr
    apply mul_left_cancel₀ hDne
    calc
      D 0*(fderiv ℂ (gk16TerminalRoot38 n) 0) h=L h := hr
      _ = Complex.I*c*(physicalFourier h.1 (-n)-physicalFourier h.2 n) := hL h
      _ = D 0*((physicalFourier h.1 (-n)-physicalFourier h.2 n)/2) := by
        rw [hD0]
        ring
  have hfinal := (hTau.sub hMu).sub hH
  change HasFDerivAt
    (fun phi : PotPair => tauN phi n-muSeq phi n-gk16TerminalRoot38 n phi)
    ((0 : PotPair →L[ℂ] ℂ)-M-fderiv ℂ (gk16TerminalRoot38 n) 0)
    (0 : PotPair) at hfinal
  refine ⟨hfinal.differentiableAt,?_⟩
  intro h
  rw [hfinal.fderiv]
  change (0 : ℂ)-M h-(fderiv ℂ (gk16TerminalRoot38 n) 0) h=_
  rw [hM,hHvalue]
  ring

end
end NlsGge.GK38
