import Mathlib
import NlsGge.Atomic.G1.G1033
import NlsGge.GK38.DirichletRealGapProbe
import NlsGge.GK38.GradFundamentalFree
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.GK38.GradFundamental
import NlsGge.GK38.DirichletRealAnalytic
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.PairPotentialProbe
import NlsGge.Spectral.ActualGapsActionsE02_38

/- G1-082 Sup4 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1082Sup4.lean.
   Witness lemma `exists_deltaMu_ne_zero : ∀ n, ∃ w, deltaMu w n ≠ 0`.
   Route: deltaMu · n has Frechet derivative at 0 equal to h ↦ Re (gradAntiDiscrimCLM 0 (nπ) (realSlice h))
   (the mu_n-variation drops because antiDiscrim 0 z = 0 for all z); the free anti-gradient kernel (GradFundamentalFree)
   paired with h = I e^{-2πi n ·} is the nonzero constant -2(-1)^n. If deltaMu · n were 0 everywhere the derivative would vanish. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.Atomic.G1082Sup4
noncomputable section

theorem antiDiscrim_zero_potential (z : ℂ) : antiDiscrim 0 z = 0 := by
  rw [antiDiscrim, monodromyPair_zero_potential]
  simp [freeE]

/-- The mixed partial: pairing `(a, b)` with the derivative of `antiDiscrim` at `(0, z0)`. -/
theorem fderiv_antiDiscrim_pair (z0 : ℂ) (a : PotPair) (b : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (0, z0)) (a, b) =
      gradAntiDiscrimCLM 0 z0 a := by
  set J : PotPair × ℂ → ℂ := fun p => antiDiscrim p.1 p.2 with hJdef
  have hJd : DifferentiableAt ℂ J (0, z0) :=
    (analyticOnNhd_antiDiscrim (0, z0) (mem_univ _)).differentiableAt
  have hJ := hJd.hasFDerivAt
  have h1 : HasFDerivAt (fun φ : PotPair => J (φ, z0))
      ((fderiv ℂ J (0, z0)).comp (ContinuousLinearMap.inl ℂ PotPair ℂ)) 0 :=
    HasFDerivAt.comp (g := J) (f := fun φ : PotPair => (φ, z0)) 0 hJ
      (hasFDerivAt_prodMk_left (0 : PotPair) z0)
  have e1 := h1.unique (hasFDerivAt_antiDiscrim z0 0)
  have h2 : HasFDerivAt (fun z : ℂ => J (0, z))
      ((fderiv ℂ J (0, z0)).comp (ContinuousLinearMap.inr ℂ PotPair ℂ)) z0 :=
    HasFDerivAt.comp (g := J) (f := fun z : ℂ => ((0 : PotPair), z)) z0 hJ
      (hasFDerivAt_prodMk_right (0 : PotPair) z0)
  have hz : (fun z : ℂ => J (0, z)) = fun _ => (0 : ℂ) := funext antiDiscrim_zero_potential
  rw [hz] at h2
  have e2 := h2.unique (hasFDerivAt_const (0 : ℂ) z0)
  have hab : (a, b) = (ContinuousLinearMap.inl ℂ PotPair ℂ) a + (ContinuousLinearMap.inr ℂ PotPair ℂ) b := by
    simp
  rw [hab, map_add]
  have e1' := congrArg (fun L => L a) e1
  have e2' := congrArg (fun L => L b) e2
  simp only [ContinuousLinearMap.comp_apply] at e1' e2'
  rw [e1', e2']
  simp

/-- Frechet derivative of `deltaMu · n` at the free potential. -/
theorem hasFDerivAt_deltaMu_zero (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => deltaMu v n)
      (Complex.reCLM.comp ((gradAntiDiscrimCLM 0 (((n : ℝ) * Real.pi : ℝ) : ℂ)).restrictScalars ℝ ∘L
        (realSlice : PhysicalL2 →L[ℝ] PotPair))) 0 := by
  set z0 : ℂ := (((n : ℝ) * Real.pi : ℝ) : ℂ) with hz0
  have hmu0 : gkMu 0 n = (n : ℝ) * Real.pi := (dirichlet_free_labels_probe38 n).1
  let J : PotPair × ℂ → ℂ := fun p => antiDiscrim p.1 p.2
  have hJd : DifferentiableAt ℂ J (0, z0) :=
    (analyticOnNhd_antiDiscrim (0, z0) (mem_univ _)).differentiableAt
  have hJR := hJd.hasFDerivAt.restrictScalars ℝ
  have hΦ : HasFDerivAt (fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ)))
      ((realSlice : PhysicalL2 →L[ℝ] PotPair).prod
        (Complex.ofRealCLM.comp (fderiv ℝ (fun v : PhysicalL2 => gkMu v n) 0))) 0 := by
    refine (realSlice : PhysicalL2 →L[ℝ] PotPair).hasFDerivAt.prodMk ?_
    exact Complex.ofRealCLM.hasFDerivAt.comp 0 ((analyticAt_gkMu38 0 n).differentiableAt.hasFDerivAt)
  have hc : HasFDerivAt (fun v : PhysicalL2 => J (realSlice v, ((gkMu v n : ℝ) : ℂ)))
      (((fderiv ℂ J (0, z0)).restrictScalars ℝ).comp
        ((realSlice : PhysicalL2 →L[ℝ] PotPair).prod
          (Complex.ofRealCLM.comp (fderiv ℝ (fun v : PhysicalL2 => gkMu v n) 0)))) 0 := by
    have hΦ0 : (fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ))) 0 = ((0 : PotPair), z0) := by
      simp only [realSlice_zero, hmu0, hz0]
    have hJ0 : HasFDerivAt J ((fderiv ℂ J (0, z0)).restrictScalars ℝ)
        ((fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ))) 0) := by
      rw [hΦ0]; exact hJR
    exact HasFDerivAt.comp (g := J) (f := fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ))) 0 hJ0 hΦ
  have hre := Complex.reCLM.hasFDerivAt.comp 0 hc
  refine hre.congr_fderiv ?_
  ext1 h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_restrictScalars', Function.comp_apply]
  rw [fderiv_antiDiscrim_pair]


open NlsGge.Atomic.G1033S1.Aux in
/-- A potential on which the free anti-gradient pairing is a nonzero real number. -/
theorem exists_pair_re_ne_zero (n : ℤ) :
    ∃ h : PhysicalL2,
      (gradAntiDiscrimCLM 0 (((n : ℝ) * Real.pi : ℝ) : ℂ) (realSlice h)).re ≠ 0 := by
  set z : ℂ := (n : ℂ) * (Real.pi : ℂ) with hz
  have hzr : (((n : ℝ) * Real.pi : ℝ) : ℂ) = z := by rw [hz]; push_cast; ring
  rw [hzr]
  let u : ℝ → ℂ := fun s => Complex.I * Complex.exp (-(2 * Complex.I * z * (s : ℂ)))
  have hu : ContinuousOn u (Set.Icc 0 1) :=
    (Continuous.mul continuous_const (Complex.continuous_exp.comp (by fun_prop))).continuousOn
  have hper : Function.Periodic u 1 := by
    intro s
    have e : -(2 * Complex.I * z * (((s + 1 : ℝ)) : ℂ)) =
        -(2 * Complex.I * z * (s : ℂ)) + ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hz]; push_cast; ring
    show Complex.I * Complex.exp (-(2 * Complex.I * z * (((s + 1 : ℝ)) : ℂ))) =
      Complex.I * Complex.exp (-(2 * Complex.I * z * (s : ℂ)))
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  refine ⟨liftPD u hu hper, ?_⟩
  have hI : (fun s : ℝ =>
      gradAntiDiscrim38 0 z s 0 * potRepFst38 (realSlice (liftPD u hu hper)) s +
        gradAntiDiscrim38 0 z s 1 * potRepSnd38 (realSlice (liftPD u hu hper)) s) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun _ => -(Complex.exp (-(Complex.I * z)) + Complex.exp (Complex.I * z)) := by
    filter_upwards [ae_restrict_of_ae (liftPD_cover_ae u hu hper),
      ae_restrict_of_ae (coverRep38_star_ae (liftPD u hu hper)),
      ae_restrict_mem measurableSet_Ioc] with s h1 h2 hm
    beta_reduce
    have hc1 := h1 hm
    have hg := scaled_gradAntiDiscrim38_zero z ⟨s, hm.1.le, hm.2⟩
    have hg0 := congrArg (fun v : PairVec38 => v 0) hg
    have hg1 := congrArg (fun v : PairVec38 => v 1) hg
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at hg0 hg1
    have e0 : gradAntiDiscrim38 0 z s 0 =
        Complex.I * Complex.exp (-Complex.I * z * (1 - 2 * (s : ℂ))) := by
      linear_combination (-Complex.I) * hg0 + (gradAntiDiscrim38 0 z s 0) * Complex.I_sq
    have e1 : gradAntiDiscrim38 0 z s 1 =
        -Complex.I * Complex.exp (Complex.I * z * (1 - 2 * (s : ℂ))) := by
      linear_combination (-Complex.I) * hg1 + (gradAntiDiscrim38 0 z s 1) * Complex.I_sq
    have hF : potRepFst38 (realSlice (liftPD u hu hper)) s = u s := hc1
    have hS : potRepSnd38 (realSlice (liftPD u hu hper)) s = star (u s) := by
      show coverRep38 (star (liftPD u hu hper)) s = _
      rw [h2, hc1]
    have hzc : star z = z := by
      rw [hz]; simp [Complex.star_def]
    have hstar : star (u s) = -Complex.I * Complex.exp (2 * Complex.I * z * (s : ℂ)) := by
      simp only [u, Complex.star_def, map_mul, Complex.conj_I, ← Complex.exp_conj, map_neg]
      rw [show (starRingEnd ℂ) z = z from hzc]
      congr 2
      rw [Complex.conj_ofReal s, Complex.conj_ofNat 2]; ring
    have h1 : Complex.exp (-Complex.I * z * (1 - 2 * (s : ℂ))) *
        Complex.exp (-(2 * Complex.I * z * (s : ℂ))) = Complex.exp (-(Complex.I * z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2' : Complex.exp (Complex.I * z * (1 - 2 * (s : ℂ))) *
        Complex.exp (2 * Complex.I * z * (s : ℂ)) = Complex.exp (Complex.I * z) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hF, hS, e0, e1, hstar]
    have hu' : u s = Complex.I * Complex.exp (-(2 * Complex.I * z * (s : ℂ))) := rfl
    rw [hu']
    calc _ = Complex.I * Complex.I * (Complex.exp (-Complex.I * z * (1 - 2 * (s : ℂ))) *
          Complex.exp (-(2 * Complex.I * z * (s : ℂ)))) +
        (-Complex.I) * (-Complex.I) * (Complex.exp (Complex.I * z * (1 - 2 * (s : ℂ))) *
          Complex.exp (2 * Complex.I * z * (s : ℂ))) := by ring
      _ = _ := by
        rw [h1, h2']
        linear_combination (Complex.exp (-(Complex.I * z)) + Complex.exp (Complex.I * z)) * Complex.I_sq
  rw [gradAntiDiscrimCLM_apply, intervalIntegral.integral_congr_ae_restrict
    (by simpa only [uIoc_of_le zero_le_one] using hI)]
  have hcos : Complex.exp (-(Complex.I * z)) + Complex.exp (Complex.I * z) =
      ((2 * Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
    have := Complex.two_cos (x := z)
    rw [show Complex.exp (-(Complex.I * z)) + Complex.exp (Complex.I * z) =
      Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I) by
        rw [add_comm]; congr 2 <;> ring] 
    rw [← this, hz]
    push_cast
    rfl
  rw [hcos]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, Complex.neg_re, Complex.ofReal_re]
  have hc2 := real_cos_int_mul_pi_sq_E02_38 n
  intro h0
  have : Real.cos ((n : ℝ) * Real.pi) = 0 := by linarith
  rw [this] at hc2; norm_num at hc2

/-- Witness: for every `n` some real potential has `deltaMu w n ≠ 0`. -/
theorem exists_deltaMu_ne_zero (n : ℤ) : ∃ w : PhysicalL2, deltaMu w n ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hd := hasFDerivAt_deltaMu_zero n
  have hz : (fun v : PhysicalL2 => deltaMu v n) = fun _ => (0 : ℝ) := funext hcon
  rw [hz] at hd
  have hu := hd.unique (hasFDerivAt_const (0 : ℝ) (0 : PhysicalL2))
  obtain ⟨h, hh⟩ := exists_pair_re_ne_zero n
  have := congrArg (fun L => L h) hu
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    Function.comp_apply, Complex.reCLM_apply, ContinuousLinearMap.zero_apply] at this
  exact hh this

end
end NlsGge.Atomic.G1082Sup4
