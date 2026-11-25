import NlsGge.Atomic.G1.G1104Host
import NlsGge.Atomic.G1.G1104Sup
import NlsGge.Atomic.G1.G1104ODE
import NlsGge.GK38.GradFundamentalDet
import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.GradEigenStateL2
import NlsGge.GK38.GradEigenStateODE
import NlsGge.Atomic.LIB.LIB026
import NlsGge.Atomic.IntervalZSBoundary

   
                                                       

                                                                                 
                                                                               

                                                                                              
                                                                               
                                                                                    
                                                

         
                                                                                              
                            
                                                                                       
                                                
                                                                                               
                                                                                   
                                                                      
                                                                                               
                                                            
                                                                                    
                                                                                          
                                             
  

set_option autoImplicit false

open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026
open NlsGge.Pilot NlsGge.GK38 MeasureTheory Set
open NlsGge.Atomic.LIB033
open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1104ODE

namespace NlsGge.Atomic.G1104Ker
noncomputable section

/-- Component convention: `Bool.true` (upper) is index `0`, `Bool.false` is index `1`. -/
def pairIdx (b : Bool) : Fin 2 := if b then 0 else 1

/-- The fundamental matrix extended from `[0,1]`. -/
abbrev Mext (φ : PotPair) (z : ℂ) : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z)

theorem Mext_of_mem (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Mext φ z t = fundPair φ z ⟨t, ht⟩ :=
  IccExtend_of_mem zero_le_one _ ht

theorem Mext_zero (φ : PotPair) (z : ℂ) : Mext φ z 0 = 1 := by
  rw [Mext_of_mem φ z ⟨le_rfl, zero_le_one⟩]
  exact fundPair_zero φ z

theorem Mext_one (φ : PotPair) (z : ℂ) : Mext φ z 1 = monodromyPair φ z := by
  rw [Mext_of_mem φ z ⟨zero_le_one, le_rfl⟩]
  rfl

theorem det_Mext (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Mext φ z t).det = 1 := by
  rw [Mext_of_mem φ z ht]
  exact det_fundPair38 φ z _

theorem zsCoeffPot_entries (φ : PotPair) (z : ℂ) (s : ℝ) :
    zsCoeffPot38 φ z s 0 0 = -(Complex.I * z) ∧
    zsCoeffPot38 φ z s 0 1 = Complex.I * potRepFst38 φ s ∧
    zsCoeffPot38 φ z s 1 0 = -(Complex.I * potRepSnd38 φ s) ∧
    zsCoeffPot38 φ z s 1 1 = Complex.I * z := by
  simp [zsCoeffPot38, zsCoeffPair]

/-- U1: an AC pair solution of the ZS ODE on `[0,1]` is the fundamental matrix times its
initial value. -/
theorem pairSolution_eq_Mext {φ : PotPair} {z : ℂ} {f : ℝ → PairVec38}
    (hf : IsPairSolution38 φ z f) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    f t = (Mext φ z t).mulVec (f 0) := by
  have hM := fundPair_ac_and_ae_ode φ z
  have ac0 : AbsolutelyContinuousOnInterval
      (fun s => Mext φ z s 1 1 * f s 0 - Mext φ z s 0 1 * f s 1) 0 1 :=
    (((hM 1 1).1).smul (hf.1 0)).sub (((hM 0 1).1).smul (hf.1 1))
  have ac1 : AbsolutelyContinuousOnInterval
      (fun s => Mext φ z s 0 0 * f s 1 - Mext φ z s 1 0 * f s 0) 0 1 :=
    (((hM 0 0).1).smul (hf.1 1)).sub (((hM 1 0).1).smul (hf.1 0))
  have hd0 : ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) 1 → HasDerivAt
      (fun s => Mext φ z s 1 1 * f s 0 - Mext φ z s 0 1 * f s 1) 0 s := by
    filter_upwards [(hM 1 1).2, (hM 0 1).2, (hM 1 0).2, (hM 0 0).2, hf.2 0, hf.2 1]
      with s h11 h01 h10 h00 hf0 hf1 hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at hs
    have := ((h11 hs').mul (hf0 hs')).sub ((h01 hs').mul (hf1 hs'))
    convert this using 1
    obtain ⟨e00, e01, e10, e11⟩ := zsCoeffPot_entries φ z s
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e00, e01, e10, e11]
    ring
  have hd1 : ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) 1 → HasDerivAt
      (fun s => Mext φ z s 0 0 * f s 1 - Mext φ z s 1 0 * f s 0) 0 s := by
    filter_upwards [(hM 1 1).2, (hM 0 1).2, (hM 1 0).2, (hM 0 0).2, hf.2 0, hf.2 1]
      with s h11 h01 h10 h00 hf0 hf1 hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one] at hs
    have := ((h00 hs').mul (hf1 hs')).sub ((h10 hs').mul (hf0 hs'))
    convert this using 1
    obtain ⟨e00, e01, e10, e11⟩ := zsCoeffPot_entries φ z s
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e00, e01, e10, e11]
    ring
  obtain ⟨C0, hC0⟩ := ac0.const_of_ae_hasDerivAt_zero hd0
  obtain ⟨C1, hC1⟩ := ac1.const_of_ae_hasDerivAt_zero hd1
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have htu : t ∈ uIcc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one]
  have y0 := (hC0 t htu).trans (hC0 0 h0).symm
  have y1 := (hC1 t htu).trans (hC1 0 h0).symm
  simp only [Mext_zero, Matrix.one_apply_eq, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at y0 y1
  have hdet := det_Mext φ z ht
  rw [Matrix.det_fin_two] at hdet
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change f t 0 = Mext φ z t 0 0 * f 0 0 + Mext φ z t 0 1 * f 0 1
    linear_combination (-(f t 0)) * hdet + Mext φ z t 0 0 * y0 + Mext φ z t 0 1 * y1
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    change f t 1 = Mext φ z t 1 0 * f 0 0 + Mext φ z t 1 1 * f 0 1
    linear_combination (-(f t 1)) * hdet + Mext φ z t 1 0 * y0 + Mext φ z t 1 1 * y1

/-! ### AC functions as H1 elements -/

theorem acH1_weak {F G : ℝ → ℂ}
    (hFm : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hGm : MemLp G 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (G x) x) :
    HasWeakDerivative (hFm.toLp F) (hGm.toLp G) := by
  intro ψ hψs hψc hψU
  have hGi : IntervalIntegrable G volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hGm.integrable (by norm_num))
  have hχd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => (ψ x : ℂ)) ((deriv ψ t : ℝ) : ℂ) t := fun t _ =>
    ((hψs.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have hχdi : IntervalIntegrable (fun x => ((deriv ψ x : ℝ) : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp (hψs.continuous_deriv (by simp))).intervalIntegrable _ _
  have hparts := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
    hF hGi hd hχd hχdi
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (hψU h).1.false)
  have hψ1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl (1 : ℝ)) (hψU h).2)
  simp only [hψ0, hψ1, Complex.ofReal_zero, mul_zero, sub_self, zero_sub] at hparts
  have hv : (∫ x in (0 : ℝ)..1, (hFm.toLp F) x * ((deriv ψ x : ℝ) : ℂ)) =
      ∫ x in (0 : ℝ)..1, F x * ((deriv ψ x : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le zero_le_one]
    filter_upwards [hFm.coeFn_toLp] with x hx
    rw [hx]
  have hdd : (∫ x in (0 : ℝ)..1, (hGm.toLp G) x * (ψ x : ℂ)) =
      ∫ x in (0 : ℝ)..1, G x * (ψ x : ℂ) := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le zero_le_one]
    filter_upwards [hGm.coeFn_toLp] with x hx
    rw [hx]
  rw [hv, hdd]
  exact hparts

/-- The H1 element with value `F` and derivative `G` (AC `F`, `F' = G` a.e., both L2). -/
def acH1 {F G : ℝ → ℂ}
    (hFm : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hGm : MemLp G 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (G x) x) : H1 where
  value := hFm.toLp F
  derivative := hGm.toLp G
  weak := acH1_weak hFm hGm hF hd

theorem acH1_representative {F G : ℝ → ℂ}
    (hFm : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hGm : MemLp G 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (G x) x)
    (x : Icc (0 : ℝ) 1) :
    representative (acH1 hFm hGm hF hd) x = F x := by
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hF.continuousOn
  let Fc : C(Icc (0 : ℝ) 1, ℂ) := ⟨_, hFc.domRestrict⟩
  have heq : Fc = representative (acH1 hFm hGm hF hd) := by
    apply representative_eq_of_ae
    filter_upwards [hFm.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with y hy hmem
    rw [IccExtend_of_mem zero_le_one Fc ⟨hmem.1.le, hmem.2⟩]
    exact hy.symm
  exact congrArg (fun f : C(Icc (0 : ℝ) 1, ℂ) => f x) heq.symm

theorem acH1_traceLeft {F G : ℝ → ℂ}
    (hFm : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hGm : MemLp G 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (G x) x) :
    traceLeft (acH1 hFm hGm hF hd) = F 0 :=
  acH1_representative hFm hGm hF hd ⟨0, by norm_num⟩

theorem acH1_traceRight {F G : ℝ → ℂ}
    (hFm : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hGm : MemLp G 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (G x) x) :
    traceRight (acH1 hFm hGm hF hd) = F 1 :=
  acH1_representative hFm hGm hF hd ⟨1, by norm_num⟩

/-! ### The ZS action as an a.e. equation -/

theorem zsApply_eq_smul_iff (φ : SourcePairL2) (f : H1Pair) (z : ℂ) :
    zsApply φ f = z • h1PairValue f ↔
      ∀ b : Bool, ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        zsExpression φ (fun c x => (f c).value x) (fun c x => (f c).derivative x) b x =
          z * (f b).value x := by
  constructor
  · intro h b
    have hb : (zsApply φ f) b = z • (f b).value := congrArg (fun v : SourcePairL2 => v b) h
    filter_upwards [zsApply_ae φ f b, Lp.coeFn_smul z (f b).value] with x h1 h2
    rw [← h1, hb, h2]
    rfl
  · intro h
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [zsApply_ae φ f b, Lp.coeFn_smul z (f b).value, h b] with x h1 h2 h3
    change (zsApply φ f b) x = (z • (f b).value) x
    rw [h1, h2, h3]
    rfl

theorem intervalPotential_ae (φ : PotPair) :
    ((fun x => intervalPotential φ true x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] potRepFst38 φ) ∧
    ((fun x => intervalPotential φ false x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] potRepSnd38 φ) :=
  ⟨(NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec φ.1).2,
   (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec φ.2).2⟩

theorem hasZS_iff_bcRelation (bc : ZSBoundaryCondition) (f : H1Pair) (c w : Fin 2 → ℂ)
    (hL : ∀ b : Bool, traceLeft (f b) = c (pairIdx b))
    (hR : ∀ b : Bool, traceRight (f b) = w (pairIdx b)) :
    HasZSBoundaryCondition bc f ↔ bcRelation bc c w := by
  cases bc <;>
    simp [HasZSBoundaryCondition, bcRelation, hL, hR, pairIdx, Bool.forall_bool,
      Fin.forall_fin_two, and_comm]

/-! ### Forward direction -/

/-- The continuous representative of an interval H1 function, extended to `ℝ`. -/
abbrev Fext (g : H1) : ℝ → ℂ := IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (representative g)

/-- The vector of representatives of an H1 pair, in the `pairIdx` convention. -/
def repVec (f : H1Pair) (x : ℝ) : PairVec38 := ![Fext (f true) x, Fext (f false) x]

theorem repVec_zero (f : H1Pair) (x : ℝ) : repVec f x 0 = Fext (f true) x := rfl

theorem repVec_one (f : H1Pair) (x : ℝ) : repVec f x 1 = Fext (f false) x := rfl

theorem repVec_pairIdx (f : H1Pair) (x : ℝ) (b : Bool) :
    repVec f x (pairIdx b) = Fext (f b) x := by
  cases b <;> rfl

theorem isPairSolution_repVec (φ : PotPair) (z : ℂ) (f : H1Pair)
    (h : zsApply (intervalPotential φ) f = z • h1PairValue f) :
    IsPairSolution38 φ z (repVec f) := by
  have hz := (zsApply_eq_smul_iff _ f z).1 h
  have hP := intervalPotential_ae φ
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact (representative_spec (f true)).1
    · exact (representative_spec (f false)).1
  · have hrt := representative_spec (f true)
    have hrf := representative_spec (f false)
    have hzt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 →
        zsExpression (intervalPotential φ) (fun c x => (f c).value x)
          (fun c x => (f c).derivative x) true x = z * (f true).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hz true)
    have hzf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 →
        zsExpression (intervalPotential φ) (fun c x => (f c).value x)
          (fun c x => (f c).derivative x) false x = z * (f false).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (hz false)
    have hVt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → Fext (f true) x = (f true).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (representative_ae (f true))
    have hVf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → Fext (f false) x = (f false).value x :=
      (ae_restrict_iff' measurableSet_Ioc).1 (representative_ae (f false))
    have hPt : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → intervalPotential φ true x = potRepFst38 φ x :=
      (ae_restrict_iff' measurableSet_Ioc).1 hP.1
    have hPf : ∀ᵐ x ∂volume, x ∈ Ioc (0 : ℝ) 1 → intervalPotential φ false x = potRepSnd38 φ x :=
      (ae_restrict_iff' measurableSet_Ioc).1 hP.2
    have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by simp [ae_iff]
    intro i
    filter_upwards [hrt.2, hrf.2, hzt, hzf, hVt, hVf, hPt, hPf, h0]
      with x dt df ezt ezf vt vf pt pf hx0 hx
    have hxI : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
    have hxu : x ∈ uIcc (0 : ℝ) 1 := by rwa [uIcc_of_le zero_le_one]
    have ezt' := ezt hxI
    have ezf' := ezf hxI
    simp only [zsExpression, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at ezt' ezf'
    rw [pt hxI, ← vf hxI, ← vt hxI] at ezt'
    rw [pf hxI, ← vf hxI, ← vt hxI] at ezf'
    obtain ⟨e00, e01, e10, e11⟩ := zsCoeffPot_entries φ z x
    fin_cases i
    · have mv : (zsCoeffPot38 φ z x).mulVec (repVec f x) 0 =
          -(Complex.I * z) * Fext (f true) x +
            Complex.I * potRepFst38 φ x * Fext (f false) x := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e00, e01]
        rfl
      have hd := dt hxu
      change HasDerivAt (Fext (f true)) ((zsCoeffPot38 φ z x).mulVec (repVec f x) 0) x
      rw [mv]
      refine hd.congr_deriv ?_
      linear_combination (-Complex.I) * ezt' + ((f true).derivative x) * Complex.I_mul_I
    · have mv : (zsCoeffPot38 φ z x).mulVec (repVec f x) 1 =
          -(Complex.I * potRepSnd38 φ x) * Fext (f true) x +
            Complex.I * z * Fext (f false) x := by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e10, e11]
        rfl
      have hd := df hxu
      change HasDerivAt (Fext (f false)) ((zsCoeffPot38 φ z x).mulVec (repVec f x) 1) x
      rw [mv]
      refine hd.congr_deriv ?_
      linear_combination Complex.I * ezf' + ((f false).derivative x) * Complex.I_mul_I

theorem eigen_forward {φ : PotPair} {bc : ZSBoundaryCondition} {z : ℂ} {u : SourcePairL2}
    (f : H1Pair) (hf : HasZSBoundaryCondition bc f) (hu : h1PairValue f = u)
    (h : zsApply (intervalPotential φ) f = z • u) :
    ∃ c : Fin 2 → ℂ,
      (∀ b : Bool, (fun t => u b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t => (Mext φ z t).mulVec c (pairIdx b)) ∧
      bcRelation bc c ((monodromyPair φ z).mulVec c) := by
  subst hu
  have hsol := isPairSolution_repVec φ z f h
  refine ⟨repVec f 0, ?_, ?_⟩
  · intro b
    filter_upwards [representative_ae (f b), ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have hmem' : t ∈ Icc (0 : ℝ) 1 := ⟨hmem.1.le, hmem.2⟩
    have e := congrFun (pairSolution_eq_Mext hsol hmem') (pairIdx b)
    rw [repVec_pairIdx] at e
    rw [← e]
    exact ht.symm
  · rw [← hasZS_iff_bcRelation bc f (repVec f 0) ((monodromyPair φ z).mulVec (repVec f 0))
      (fun b => ?_) (fun b => ?_)]
    · exact hf
    · rw [repVec_pairIdx]
      exact (IccExtend_left zero_le_one (representative (f b))).symm
    · have e := congrFun (pairSolution_eq_Mext hsol (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1))
        (pairIdx b)
      rw [repVec_pairIdx, Mext_one] at e
      rw [← e]
      exact (IccExtend_right zero_le_one (representative (f b))).symm

/-! ### Backward direction -/

theorem pairKernelExt_state (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (s : ℝ) :
    pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) s = (Mext φ z s).mulVec c :=
  NlsGge.GK38.GradEigen38.state_eq_mulVec φ z c _

/-- Component `b` of the state with initial value `c`. -/
def stateF (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) (s : ℝ) : ℂ :=
  pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) s (pairIdx b)

/-- Component `b` of the coefficient times the state. -/
def stateG (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) (s : ℝ) : ℂ :=
  (zsCoeffPot38 φ z s).mulVec (pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) s)
    (pairIdx b)

theorem stateF_memLp (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    MemLp (stateF φ z c b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  refine MemLp.of_bound
    (NlsGge.GK38.GradEigen38.continuous_component
      (NlsGge.GK38.GradEigen38.state φ z c) (pairIdx b)).aestronglyMeasurable
    ‖NlsGge.GK38.GradEigen38.state φ z c‖ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact norm_pairKernelExt38_le _ ⟨hs.1.le, hs.2⟩ _

theorem stateG_memLp (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    MemLp (stateG φ z c b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (NlsGge.GK38.GradEigen38.state_derivative_L2 φ z c (pairIdx b)).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

theorem stateF_ac (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    AbsolutelyContinuousOnInterval (stateF φ z c b) 0 1 :=
  NlsGge.GK38.GradEigen38.ac_state_component φ z c (pairIdx b)

theorem stateF_deriv (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (stateF φ z c b) (stateG φ z c b x) x := by
  filter_upwards [NlsGge.GK38.GradEigen38.ae_hasDerivAt_state_component φ z c (pairIdx b)]
    with x hx hxu
  exact hx (by rwa [uIcc_of_le zero_le_one] at hxu)

/-- The H1 pair with initial value `c` solving the ZS equation. -/
def fc (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) : H1Pair := fun b =>
  acH1 (stateF_memLp φ z c b) (stateG_memLp φ z c b) (stateF_ac φ z c b)
    (stateF_deriv φ z c b)

theorem fc_value_ae (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    (fun x => (fc φ z c b).value x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] stateF φ z c b :=
  (stateF_memLp φ z c b).coeFn_toLp

theorem fc_derivative_ae (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    (fun x => (fc φ z c b).derivative x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] stateG φ z c b :=
  (stateG_memLp φ z c b).coeFn_toLp

theorem fc_traceLeft (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    traceLeft (fc φ z c b) = c (pairIdx b) := by
  rw [fc, acH1_traceLeft]
  change pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) 0 (pairIdx b) = _
  rw [pairKernelExt_state, Mext_zero, Matrix.one_mulVec]

theorem fc_traceRight (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    traceRight (fc φ z c b) = ((monodromyPair φ z).mulVec c) (pairIdx b) := by
  rw [fc, acH1_traceRight]
  change pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) 1 (pairIdx b) = _
  rw [pairKernelExt_state, Mext_one]

theorem stateG_true (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (x : ℝ) :
    stateG φ z c true x = -(Complex.I * z) * stateF φ z c true x +
      Complex.I * potRepFst38 φ x * stateF φ z c false x := by
  simp only [stateG, stateF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rfl

theorem stateG_false (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (x : ℝ) :
    stateG φ z c false x = -(Complex.I * potRepSnd38 φ x) * stateF φ z c true x +
      Complex.I * z * stateF φ z c false x := by
  simp only [stateG, stateF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rfl

theorem zsApply_fc (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) :
    zsApply (intervalPotential φ) (fc φ z c) = z • h1PairValue (fc φ z c) := by
  rw [zsApply_eq_smul_iff]
  have hP := intervalPotential_ae φ
  intro b
  cases b
  · filter_upwards [hP.2, fc_value_ae φ z c false, fc_value_ae φ z c true,
      fc_derivative_ae φ z c false] with x pf vf vt df
    simp only [zsExpression, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rw [pf, df, vf, vt, stateG_false]
    linear_combination (potRepSnd38 φ x * stateF φ z c true x - z * stateF φ z c false x) *
      Complex.I_mul_I
  · filter_upwards [hP.1, fc_value_ae φ z c false, fc_value_ae φ z c true,
      fc_derivative_ae φ z c true] with x pt vf vt dt
    simp only [zsExpression, Bool.not_true, ↓reduceIte]
    rw [pt, dt, vf, vt, stateG_true]
    linear_combination (potRepFst38 φ x * stateF φ z c false x - z * stateF φ z c true x) *
      Complex.I_mul_I

/-! ### The kernel bridge (M2) -/

/-- M2: `u` is an eigenvector (or zero) of the `bc`-realization with eigenvalue `z` iff it is
a.e. a column combination of the fundamental matrix whose initial value `c` and final value
`M(1) c` satisfy the endpoint relation. Components: `Bool.true` is index `0`. -/
theorem zsRealization_eigen_iff (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ)
    (u : SourcePairL2) :
    (∃ hu : u ∈ (zsRealization (intervalPotential φ) bc).domain,
        zsRealization (intervalPotential φ) bc ⟨u, hu⟩ = z • u) ↔
      ∃ c : Fin 2 → ℂ,
        (∀ b : Bool, (fun t => u b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
          fun t => (Mext φ z t).mulVec c (pairIdx b)) ∧
        bcRelation bc c ((monodromyPair φ z).mulVec c) := by
  constructor
  · rintro ⟨hu, h⟩
    obtain ⟨f, hf, hfu⟩ : u ∈ zsBoundaryDomain bc := hu
    subst hfu
    exact eigen_forward f hf rfl ((zsRealization_apply (intervalPotential φ) bc f hf).symm.trans h)
  · rintro ⟨c, hae, hbc⟩
    have hf : HasZSBoundaryCondition bc (fc φ z c) :=
      (hasZS_iff_bcRelation bc (fc φ z c) c ((monodromyPair φ z).mulVec c)
        (fc_traceLeft φ z c) (fc_traceRight φ z c)).2 hbc
    have hfu : h1PairValue (fc φ z c) = u := by
      refine PiLp.ext fun b => Lp.ext ?_
      filter_upwards [fc_value_ae φ z c b, hae b] with t h1 h2
      change (fc φ z c b).value t = u b t
      rw [h1, h2]
      change pairKernelExt38 (NlsGge.GK38.GradEigen38.state φ z c) t (pairIdx b) = _
      rw [pairKernelExt_state]
    refine ⟨⟨fc φ z c, hf, hfu⟩, ?_⟩
    subst hfu
    exact (zsRealization_apply (intervalPotential φ) bc (fc φ z c) hf).trans (zsApply_fc φ z c)

/-! ### Uniqueness of the initial value and the kernel dimension -/

theorem eigen_c_unique {φ : PotPair} {z : ℂ} {u : SourcePairL2} {c c' : Fin 2 → ℂ}
    (h : ∀ b : Bool, (fun t => u b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => (Mext φ z t).mulVec c (pairIdx b))
    (h' : ∀ b : Bool, (fun t => u b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => (Mext φ z t).mulVec c' (pairIdx b)) : c = c' := by
  have : (ae (volume.restrict (Ioc (0 : ℝ) 1))).NeBot :=
    ae_restrict_neBot.2 (by simp)
  obtain ⟨t, ht, hmem⟩ := (((h true).symm.trans (h' true)).and
    (((h false).symm.trans (h' false)).and (ae_restrict_mem measurableSet_Ioc))).exists
  have hv : (Mext φ z t).mulVec c = (Mext φ z t).mulVec c' := by
    funext i
    fin_cases i
    · exact ht
    · exact hmem.1
  have hu : IsUnit (Mext φ z t) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_Mext φ z ⟨hmem.2.1.le, hmem.2.2⟩]
    exact isUnit_one
  exact Matrix.mulVec_injective_iff_isUnit.2 hu hv

/-- The eigenspace of `A` at `z` (including `0`) as a submodule. -/
def zsKer (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) : Submodule ℂ SourcePairL2 where
  carrier := {u | ∃ hu : u ∈ A.domain, A ⟨u, hu⟩ = z • u}
  add_mem' := by
    rintro u v ⟨hu, h1⟩ ⟨hv, h2⟩
    refine ⟨A.domain.add_mem hu hv, ?_⟩
    have := A.map_add ⟨u, hu⟩ ⟨v, hv⟩
    rw [smul_add, ← h1, ← h2, ← this]
    rfl
  zero_mem' := ⟨A.domain.zero_mem, by
    have := A.map_zero
    rw [smul_zero]
    exact this⟩
  smul_mem' := by
    rintro a u ⟨hu, h1⟩
    refine ⟨A.domain.smul_mem a hu, ?_⟩
    have := A.map_smul a ⟨u, hu⟩
    rw [smul_comm, ← h1, ← this]
    rfl

theorem mem_zsKer {A : SourcePairL2 →ₗ.[ℂ] SourcePairL2} {z : ℂ} {u : SourcePairL2} :
    u ∈ zsKer A z ↔ ∃ hu : u ∈ A.domain, A ⟨u, hu⟩ = z • u := Iff.rfl

/-- The class of `t ↦ M(t) c` as an element of the pair space. -/
def eigenClass (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) : SourcePairL2 :=
  WithLp.toLp 2 (fun b : Bool => (stateF_memLp φ z c b).toLp (stateF φ z c b))

theorem eigenClass_ae (φ : PotPair) (z : ℂ) (c : Fin 2 → ℂ) (b : Bool) :
    (fun t => eigenClass φ z c b t) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      fun t => (Mext φ z t).mulVec c (pairIdx b) := by
  filter_upwards [(stateF_memLp φ z c b).coeFn_toLp] with t ht
  change (stateF_memLp φ z c b).toLp (stateF φ z c b) t = _
  rw [ht]
  exact congrFun (pairKernelExt_state φ z c t) (pairIdx b)

/-- `c ↦ [t ↦ M(t) c]` as a linear map. -/
def eigenMap (φ : PotPair) (z : ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] SourcePairL2 where
  toFun := eigenClass φ z
  map_add' := by
    intro c c'
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [eigenClass_ae φ z (c + c') b, eigenClass_ae φ z c b,
      eigenClass_ae φ z c' b, Lp.coeFn_add (eigenClass φ z c b) (eigenClass φ z c' b)]
      with t h1 h2 h3 h4
    change eigenClass φ z (c + c') b t = (eigenClass φ z c b + eigenClass φ z c' b) t
    rw [h1, h4, Pi.add_apply, h2, h3, Matrix.mulVec_add]
    rfl
  map_smul' := by
    intro a c
    refine PiLp.ext fun b => Lp.ext ?_
    filter_upwards [eigenClass_ae φ z (a • c) b, eigenClass_ae φ z c b,
      Lp.coeFn_smul a (eigenClass φ z c b)] with t h1 h2 h4
    change eigenClass φ z (a • c) b t = (a • eigenClass φ z c b) t
    rw [h1, h4, Pi.smul_apply, h2, Matrix.mulVec_smul]
    rfl

/-- M2 (dimension form): the eigenspace of the `bc`-realization at `z` is linearly equivalent
to the kernel of the `2 × 2` characteristic matrix `B0 + B1 M(1,z)`. -/
def zsKerEquiv (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    LinearMap.ker (charMatrix bc (monodromyPair φ z)).mulVecLin ≃ₗ[ℂ]
      zsKer (zsRealization (intervalPotential φ) bc) z :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (zsKer (zsRealization (intervalPotential φ) bc) z)
      ((eigenMap φ z).comp (LinearMap.ker (charMatrix bc (monodromyPair φ z)).mulVecLin).subtype)
      (fun c => by
        have hc : (charMatrix bc (monodromyPair φ z)).mulVec (c : Fin 2 → ℂ) = 0 := c.2
        exact (zsRealization_eigen_iff φ bc z _).2
          ⟨c, eigenClass_ae φ z c, (bcRelation_iff_charMatrix bc _ _).2 hc⟩))
    ⟨fun c c' h => by
      have h' : eigenClass φ z c = eigenClass φ z c' := congrArg Subtype.val h
      exact Subtype.ext (eigen_c_unique (eigenClass_ae φ z c) (fun b => by
        rw [h']; exact eigenClass_ae φ z c' b)),
     fun ⟨u, hu⟩ => by
      obtain ⟨c, hae, hbc⟩ := (zsRealization_eigen_iff φ bc z u).1 hu
      refine ⟨⟨c, (bcRelation_iff_charMatrix bc _ _).1 hbc⟩, Subtype.ext ?_⟩
      change eigenClass φ z c = u
      refine PiLp.ext fun b => Lp.ext ?_
      filter_upwards [eigenClass_ae φ z c b, hae b] with t h1 h2
      exact h1.trans h2.symm⟩

theorem zsKer_finiteDimensional (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    FiniteDimensional ℂ (zsKer (zsRealization (intervalPotential φ) bc) z) :=
  LinearEquiv.finiteDimensional (zsKerEquiv φ bc z)

theorem zsKer_finrank_eq (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    Module.finrank ℂ (zsKer (zsRealization (intervalPotential φ) bc) z) =
      Module.finrank ℂ (LinearMap.ker (charMatrix bc (monodromyPair φ z)).mulVecLin) :=
  (zsKerEquiv φ bc z).finrank_eq.symm

/-- A nonzero eigenfunction exists iff the boundary characteristic vanishes. -/
theorem nontrivial_zsKer_iff (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    Nontrivial (zsKer (zsRealization (intervalPotential φ) bc) z) ↔
      boundaryCharacteristic φ bc z = 0 := by
  have hk : (charMatrix bc (monodromyPair φ z)).det = 0 ↔ boundaryCharacteristic φ bc z = 0 := by
    rw [det_charMatrix_monodromy]
    simp [charConstant_ne_zero bc]
  rw [← hk, ← Matrix.exists_mulVec_eq_zero_iff,
    (zsKerEquiv φ bc z).toEquiv.nontrivial_congr.symm]
  constructor
  · intro hn
    obtain ⟨⟨c, hc⟩, hne⟩ := exists_ne (0 : LinearMap.ker (charMatrix bc (monodromyPair φ z)).mulVecLin)
    exact ⟨c, fun h => hne (Subtype.ext h), hc⟩
  · rintro ⟨v, hv, hD⟩
    exact ⟨⟨v, hD⟩, 0, fun h => hv (congrArg Subtype.val h)⟩

end
end NlsGge.Atomic.G1104Ker
