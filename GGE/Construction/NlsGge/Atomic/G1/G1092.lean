import Mathlib
import NlsGge.Atomic.G1.G1091
import NlsGge.Analysis.RegularizedDeterminant.RealHilbertSchmidt
import NlsGge.GK38.PairPotential
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.PoissonMixedCalibration
import NlsGge.GK38.GradEigenKernelProbe
import NlsGge.GK38.MolnarLocalizationC

                                                                                                  
                                                                                                                     
                                                                                                                            
                                                                                                             
                                                                                                               
                                                                                                                          
                                                                                                                        
                                                                                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonSpectral38

namespace NlsGge.GKDefinitionDesign
noncomputable section
section G1092L3Sec
open Filter Topology
open scoped InnerProductSpace
open NlsGge.Analysis.RegularizedDeterminant

namespace G1092L3

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem rankOne_compact (a : E) (w : F) :
    IsCompactOperator (((innerSL ℝ a).smulRight w : E →L[ℝ] F)) := by
  have h : ((innerSL ℝ a).smulRight w : E →L[ℝ] F) =
      (ContinuousLinearMap.toSpanSingleton ℝ w).comp (innerSL ℝ a) := by
    ext v; simp
  rw [h]
  have H := (isCompactOperator_of_locallyCompactSpace_rng (ContinuousLinearMap.toSpanSingleton ℝ w)).comp_clm (innerSL ℝ a)
  exact H

theorem sum_rankOne_compact {ι : Type*} (s : Finset ι) (a : ι → E) (w : ι → F) :
    IsCompactOperator ⇑(∑ i ∈ s, ((innerSL ℝ (a i)).smulRight (w i) : E →L[ℝ] F)) := by
  have : (∑ i ∈ s, ((innerSL ℝ (a i)).smulRight (w i) : E →L[ℝ] F)) ∈
      compactOperator (RingHom.id ℝ) E F :=
    Submodule.sum_mem _ (fun i _ => rankOne_compact (a i) (w i))
  exact this

theorem trunc_bound {ι : Type*} [DecidableEq ι] (T : E →L[ℝ] F) (b : HilbertBasis ι ℝ E) {S : ℝ}
    (hS : HasSum (fun i => ‖T (b i)‖ ^ 2) S) (s : Finset ι) (v : E) :
    ‖T v - (∑ i ∈ s, ((innerSL ℝ (b i)).smulRight (T (b i)) : E →L[ℝ] F)) v‖ ≤
      Real.sqrt (S - ∑ i ∈ s, ‖T (b i)‖ ^ 2) * ‖v‖ := by
  have hsv : HasSum (fun i => ⟪b i, v⟫_ℝ • T (b i)) (T v) := by
    have := (b.hasSum_repr v).mapL T
    simpa [HilbertBasis.repr_apply_apply] using this
  have hTs : (∑ i ∈ s, ((innerSL ℝ (b i)).smulRight (T (b i)) : E →L[ℝ] F)) v =
      ∑ i ∈ s, ⟪b i, v⟫_ℝ • T (b i) := by
    simp [ContinuousLinearMap.sum_apply]
  rw [hTs]
  set f : ι → F := fun i => ⟪b i, v⟫_ℝ • T (b i) with hf
  set A : F := ∑ i ∈ s, f i with hA
  have hlim : Tendsto (fun t : Finset ι => ∑ i ∈ t, f i) atTop (𝓝 (T v)) := hsv
  have ht := (hlim.sub_const A).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop s] with t hst
  have hdiff : ∑ i ∈ t, f i - A = ∑ i ∈ t \ s, f i := by
    rw [← Finset.sum_sdiff hst, hA, add_sub_cancel_right]
  rw [hdiff]
  have hg : ∑ i ∈ t \ s, ‖T (b i)‖ ^ 2 ≤ S - ∑ i ∈ s, ‖T (b i)‖ ^ 2 := by
    have h1 := sum_le_hasSum t (fun i _ => sq_nonneg ‖T (b i)‖) hS
    have h2 := Finset.sum_sdiff hst (f := fun i => ‖T (b i)‖ ^ 2)
    linarith
  have hc : ∑ i ∈ t \ s, |⟪b i, v⟫_ℝ| ^ 2 ≤ ‖v‖ ^ 2 := by
    have := b.orthonormal.sum_inner_products_le (s := t \ s) v
    simpa [Real.norm_eq_abs] using this
  calc ‖∑ i ∈ t \ s, f i‖ ≤ ∑ i ∈ t \ s, ‖f i‖ := norm_sum_le _ _
    _ = ∑ i ∈ t \ s, |⟪b i, v⟫_ℝ| * ‖T (b i)‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [hf, norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ i ∈ t \ s, |⟪b i, v⟫_ℝ| ^ 2) * Real.sqrt (∑ i ∈ t \ s, ‖T (b i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ ‖v‖ * Real.sqrt (S - ∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
        refine mul_le_mul ?_ (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) (norm_nonneg _)
        exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hc⟩
    _ = Real.sqrt (S - ∑ i ∈ s, ‖T (b i)‖ ^ 2) * ‖v‖ := mul_comm _ _

theorem hs_isCompact (T : E →L[ℝ] F) (hT : IsHilbertSchmidt T) : IsCompactOperator T := by
  classical
  have hsum : Summable (fun i => ‖T (basis E i)‖ ^ 2) :=
    (isHilbertSchmidt_iff_summable T (basis E)).1 hT
  obtain ⟨S, hS⟩ := hsum
  have hnorm : ∀ s : Finset (basisIndex E),
      ‖(∑ i ∈ s, ((innerSL ℝ (basis E i)).smulRight (T (basis E i)) : E →L[ℝ] F)) - T‖ ≤
        Real.sqrt (S - ∑ i ∈ s, ‖T (basis E i)‖ ^ 2) := by
    intro s
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
    have := trunc_bound T (basis E) hS s v
    rw [ContinuousLinearMap.sub_apply, norm_sub_rev]
    exact this
  have hlim : Tendsto (fun s : Finset (basisIndex E) =>
      (∑ i ∈ s, ((innerSL ℝ (basis E i)).smulRight (T (basis E i)) : E →L[ℝ] F))) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun s : Finset (basisIndex E) => S - ∑ i ∈ s, ‖T (basis E i)‖ ^ 2) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := S)).sub hS
      simpa using this
    have h2 : Tendsto (fun s : Finset (basisIndex E) =>
        Real.sqrt (S - ∑ i ∈ s, ‖T (basis E i)‖ ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      exact this
    exact squeeze_zero (fun s => norm_nonneg _) hnorm h2
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s => sum_rankOne_compact s (fun i => basis E i) (fun i => T (basis E i))))

end G1092L3
end G1092L3Sec

section G1092Sec
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Schur
namespace G1092

theorem exp_npi_eq (n : ℤ) :
    Complex.exp (-(Complex.I * ((n : ℝ) * Real.pi : ℂ))) = Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ)) := by
  have h : Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ)) *
      Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have := Complex.exp_int_mul_two_pi_mul_I n
    rw [← this]; congr 1; push_cast; ring
  have h2 : Complex.exp (-(Complex.I * ((n : ℝ) * Real.pi : ℂ))) *
      Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hne : Complex.exp (Complex.I * ((n : ℝ) * Real.pi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hne (h2.trans h.symm)

theorem normingSpectral_free (n : ℤ) : normingSpectral38 0 ((n : ℝ) * Real.pi : ℂ) = 0 := by
  have hd : HasDerivAt (normingFactor 0) (-Complex.sin ((n : ℝ) * Real.pi : ℂ)) ((n : ℝ) * Real.pi : ℂ) := by
    have he : normingFactor 0 = Complex.cos := funext normingFactor_free38
    rw [he]; exact Complex.hasDerivAt_cos _
  have := (hasDerivAt_normingSpectral38 0 ((n : ℝ) * Real.pi : ℂ)).unique hd
  rw [this]
  have : Complex.sin ((n : ℝ) * Real.pi : ℂ) = 0 := by
    rw [Complex.ofReal_intCast]; exact Complex.sin_int_mul_pi n
  rw [this, neg_zero]

theorem free_kappaKernel (n : ℤ) (t : Time) :
    kappaKernel38 0 ((n : ℝ) * Real.pi : ℂ) t =
      ![Complex.I * Complex.exp (2 * Real.pi * Complex.I * n * (t : ℝ)),
        -Complex.I * Complex.exp (-(2 * Real.pi * Complex.I * n * (t : ℝ)))] := by
  set z : ℂ := ((n : ℝ) * Real.pi : ℂ) with hz
  set a : ℂ := Complex.exp (Complex.I * z) with ha
  have hab : Complex.exp (-(Complex.I * z)) = a := exp_npi_eq n
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have hmono : monodromyPair 0 z = !![a, 0; 0, a] := by
    rw [monodromyPair_zero_potential]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [freeE, hab, ha]
  have hc : normingFactor 0 z = a := by
    rw [normingFactor, hmono]; simp
  have hseed : terminalSeed 0 z = ![a, -a] := by
    ext i; fin_cases i <;> simp [terminalSeed, hmono]
  have hg : state 0 z ![1,1] t = ![Complex.exp (-Complex.I * z * (t : ℝ)), Complex.exp (Complex.I * z * (t : ℝ))] := by
    rw [probe_free_state]; simp
  have hh : state 0 z (terminalSeed 0 z) t =
      ![Complex.exp (-Complex.I * z * (t : ℝ)) * a, Complex.exp (Complex.I * z * (t : ℝ)) * (-a)] := by
    rw [hseed, probe_free_state]; simp
  have e1 : Complex.exp (Complex.I * z * (t : ℝ)) * Complex.exp (Complex.I * z * (t : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * n * (t : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; rw [hz]; push_cast; ring
  have e2 : Complex.exp (-Complex.I * z * (t : ℝ)) * Complex.exp (-Complex.I * z * (t : ℝ)) =
      Complex.exp (-(2 * Real.pi * Complex.I * n * (t : ℝ))) := by
    rw [← Complex.exp_add]; congr 1; rw [hz]; push_cast; ring
  have h2I : (2 * Complex.I) ≠ 0 := by simp
  change (2 / normingFactor 0 z) • (normingSpectral38 0 z • dirEigenKernel38 0 z + normingKernel38 0 z) t = _
  rw [normingSpectral_free n, hc]
  ext i
  fin_cases i
  · simp [normingKernel38, mixedSquare, starProd38, hg, hh]
    field_simp
    rw [pow_two, e1]; congr 1; ring
  · simp [normingKernel38, mixedSquare, starProd38, hg, hh]
    field_simp
    rw [pow_two, ← Complex.exp_add]; congr 1; rw [hz]; push_cast; ring


theorem Q_free_dirState (n : ℤ) : Q (dirState 0 n) = 2 := by
  have _hi := kernel_integrability (dirState 0 n)
  have he (s : ℝ) : pairKernelExt38 (dirState 0 n) s 0 *
      pairKernelExt38 (dirState 0 n) s 1 = 1 := by
    change dirState 0 n (projIcc 0 1 zero_le_one s) 0 *
      dirState 0 n (projIcc 0 1 zero_le_one s) 1 = 1
    rw [probe_free_dirichlet]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  simp [Q,he]

theorem free_dirEigenKernel (n : ℤ) (t : Time) :
    dirEigenKernel38 0 ((n : ℝ) * Real.pi : ℂ) t =
      ![(1/2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n * (t : ℝ)),
        (1/2 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * n * (t : ℝ)))] := by
  have hs : state 0 ((n : ℝ) * Real.pi : ℂ) ![1,1] = dirState 0 n := by
    unfold dirState
    rw [realSlice_zero, gkMu_free38]
    push_cast; rfl
  have hsq := (probe_free_dirichlet_gradient n).2.2.2 t
  unfold dirEigenKernel38
  rw [hs]
  change (Q (dirState 0 n))⁻¹ • square (dirState 0 n) t = _
  have e3 : (2 * Complex.I * (((n : ℝ) : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * n * (t : ℝ) := by push_cast; ring
  have e4 : (-2 * Complex.I * (((n : ℝ) : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ)) =
      -(2 * Real.pi * Complex.I * n * (t : ℝ)) := by push_cast; ring
  rw [Q_free_dirState, hsq, e3, e4]
  ext i
  fin_cases i <;> simp [div_eq_inv_mul]

theorem fourier_bridge (f : PhysicalL2) (n : ℤ) :
    ∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * n * s) * coverRep38 f s =
      physicalFourier f (-n) := by
  unfold physicalFourier
  rw [fourierCoeff_eq_intervalIntegral (f : AddCircle (1 : ℝ) → ℂ) (-n) 0]
  simp only [zero_add, div_one, one_smul, neg_neg, smul_eq_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys f] with s hs _
  rw [hs, fourier_coe_apply]
  push_cast
  simp

theorem pair_integral_exp (c0 c1 : ℂ) (g : PairKernelCont38) (n : ℤ)
    (hg : ∀ t : Time, g t = ![c0 * Complex.exp (2 * Real.pi * Complex.I * n * (t : ℝ)),
      c1 * Complex.exp (-(2 * Real.pi * Complex.I * n * (t : ℝ)))]) (v : PhysicalL2) :
    integralPairCLM38 g t1 (realSlice v) =
      c0 * physicalFourier v (-n) + c1 * star (physicalFourier v (-n)) := by
  change pairIntegral38 g t1 (realSlice v) = _
  unfold pairIntegral38
  have ht1 : ((t1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
  rw [ht1]
  have i0 : IntervalIntegrable (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * s) *
      coverRep38 v s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one v).continuousOn_mul (by fun_prop)
  have i1 : IntervalIntegrable (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * s) *
      coverRep38 (star v) s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one (star v)).continuousOn_mul (by fun_prop)
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      pairKernelExt38 g s 0 * potRepFst38 (realSlice v) s +
        pairKernelExt38 g s 1 * potRepSnd38 (realSlice v) s =
      c0 * (Complex.exp (2 * Real.pi * Complex.I * n * s) * coverRep38 v s) +
        c1 * (Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * s) * coverRep38 (star v) s) := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [pairKernelExt38_of_mem g hs, hg]
    have e : Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * s) =
        Complex.exp (-(2 * Real.pi * Complex.I * n * s)) := by
      congr 1; push_cast; ring
    rw [e]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, potRepFst38, potRepSnd38, realSlice_fst,
      realSlice_snd]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (i0.const_mul c0) (i1.const_mul c1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fourier_bridge v n, fourier_bridge (star v) (-n), neg_neg, NlsGge.Schur.physicalFourier_star38]

theorem realKappa_free_row (n : ℤ) (v : PhysicalL2) :
    realKappaCLM38 0 n v = -2 * (physicalFourier v (-n)).im := by
  have h := pair_integral_exp Complex.I (-Complex.I) (kappaKernel38 0 ((n : ℝ) * Real.pi : ℂ)) n
    (fun t => by rw [free_kappaKernel]) v
  unfold realKappaCLM38
  simp only [realSlice_zero, gkMu_free38, ContinuousLinearMap.comp_apply, kappaCLM38]
  push_cast at h ⊢
  show (integralPairCLM38 (kappaKernel38 0 _) t1 (realSlice v)).re = _
  rw [h]
  simp
  ring

theorem gkMu_free_row (n : ℤ) (v : PhysicalL2) :
    fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0 v = (physicalFourier v (-n)).re := by
  have hroot := gkMu_root38 0 n
  have hder := dirichlet_root_deriv_ne_zero38 0 (gkMu 0 n) hroot
  have h1 := actual_dirichlet_label_complex_gradient 0 n v
  rw [dirImplicitGradient_eq_kernel38 _ _ hroot hder] at h1
  have h2 := pair_integral_exp (1/2) (1/2) (dirEigenKernel38 (realSlice 0) (gkMu 0 n : ℂ)) n
    (fun t => by
      rw [realSlice_zero, gkMu_free38]
      have := free_dirEigenKernel n t
      push_cast at this ⊢
      exact this) v
  rw [h2] at h1
  apply Complex.ofReal_injective
  rw [h1]
  simp [Complex.star_def, Complex.ext_iff]
  ring


theorem earlyDerivative_zero_apply (v : PhysicalL2) (n : ℤ) :
    ((earlyDerivative 0 v : Lib.L2Z) : ℤ → ℂ) n =
      ((2 * (reflectedFourierL2 v n).im : ℝ) : ℂ) +
        Complex.I * ((-(reflectedFourierL2 v n).re : ℝ) : ℂ) := by
  rw [G1091S3.earlyDerivative_apply, realKappa_free_row, gkMu_free_row, reflectedFourierL2_apply]
  unfold reflectedFourier
  simp only [Complex.neg_re, Complex.neg_im, neg_neg]
  push_cast
  ring

theorem earlyDerivative_zero_injective : Function.Injective (earlyDerivative 0) := by
  intro v w h
  have hd : earlyDerivative 0 (v - w) = 0 := by rw [map_sub, h, sub_self]
  have hn : ∀ n, reflectedFourierL2 (v - w) n = 0 := by
    intro n
    have h1 := earlyDerivative_zero_apply (v - w) n
    rw [hd] at h1
    have h2 : (((0 : Lib.L2Z)) : ℤ → ℂ) n = 0 := rfl
    rw [h2] at h1
    generalize reflectedFourierL2 (v - w) n = x at h1 ⊢
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    refine Complex.ext ?_ ?_ <;> simp <;> linarith
  have : reflectedFourierL2 (v - w) = 0 := by
    ext n; exact hn n
  have := (map_eq_zero_iff reflectedFourierL2 reflectedFourierL2.injective).1 this
  exact sub_eq_zero.1 this

theorem earlyDerivative_zero_surjective : Function.Surjective (earlyDerivative 0) := by
  intro y
  let z : ℤ → ℂ := fun n => ((-(y n).im : ℝ) : ℂ) + Complex.I * (((y n).re / 2 : ℝ) : ℂ)
  have hz : Memℓp z 2 := by
    refine Memℓp.mono' (y.2) (fun n => ?_)
    have : ‖z n‖ ^ 2 ≤ ‖(y : ℤ → ℂ) n‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp [z]
      nlinarith [sq_nonneg (y n).re]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  refine ⟨reflectedFourierL2.symm ⟨z, hz⟩, ?_⟩
  ext n
  rw [earlyDerivative_zero_apply, LinearIsometryEquiv.apply_symm_apply]
  apply Complex.ext <;> simp [z] <;> ring

theorem earlyDerivative_zero_equiv :
    ∃ E₀ : PhysicalL2 ≃L[ℝ] Lib.L2Z, E₀.toContinuousLinearMap = earlyDerivative 0 :=
  ⟨ContinuousLinearEquiv.ofBijective (earlyDerivative 0)
    (LinearMap.ker_eq_bot.2 earlyDerivative_zero_injective)
    (LinearMap.range_eq_top.2 earlyDerivative_zero_surjective), rfl⟩

theorem continuous_earlyDerivative : Continuous earlyDerivative := by
  have h1 : ContDiff ℝ ⊤ normingDirichletMap :=
    contDiffOn_univ.1 (G1091S1.normingDirichletMap_analytic.contDiffOn uniqueDiffOn_univ)
  exact h1.continuous_fderiv (by simp)

theorem continuous_remainder : Continuous earlyDerivativeRemainder :=
  continuous_earlyDerivative.sub continuous_const

theorem compact_of_dense {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (Φ : PhysicalL2 → (G →L[ℝ] H)) (hΦ : Continuous Φ) (D : Set PhysicalL2) (hD : Dense D)
    (h : ∀ u ∈ D, IsCompactOperator (Φ u)) (u : PhysicalL2) : IsCompactOperator (Φ u) := by
  have hc : IsClosed {u : PhysicalL2 | IsCompactOperator (Φ u)} :=
    isClosed_setOfPred_isCompactOperator.preimage hΦ
  have hsub : D ⊆ {u : PhysicalL2 | IsCompactOperator (Φ u)} := fun u hu => h u hu
  have := hc.closure_subset_iff.2 hsub
  rw [hD.closure_eq] at this
  exact this (Set.mem_univ u)

theorem dense_sobolev : Dense {u : PhysicalL2 | physicalSobolev 1 u} := by
  classical
  intro u
  set y : lp (fun _ : ℤ => ℂ) 2 := reflectedFourierL2 u with hy
  have hsum := lp.hasSum_single (p := 2) (by norm_num) y
  have hlim : Filter.Tendsto (fun s : Finset ℤ => reflectedFourierL2.symm (∑ i ∈ s, lp.single 2 i (y i)))
      Filter.atTop (nhds u) := by
    have := (reflectedFourierL2.symm.continuous.tendsto y).comp hsum
    have e : reflectedFourierL2.symm y = u := by
      rw [hy]; exact LinearIsometryEquiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall (fun s => ?_))
  show physicalSobolev 1 _
  unfold physicalSobolev SobolevSquareSummable
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine summable_of_ne_finset_zero (s := s) (fun n hn => ?_)
  have : ((∑ i ∈ s, lp.single 2 i (y i) : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) n = 0 := by
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.single_apply]
    exact Finset.sum_eq_zero (fun i hi => by
      have : n ≠ i := fun h => hn (h ▸ hi)
      simp [this])
  rw [this]; simp


end G1092
end G1092Sec

theorem G1_092_compact_adjoint (u : PhysicalL2) (E₀inv : Lib.L2Z →L[ℝ] PhysicalL2) :
    IsCompactOperator ⇑((ContinuousLinearMap.adjoint (earlyDerivativeRemainder u)).comp
      (ContinuousLinearMap.adjoint E₀inv)) := by
  refine G1092.compact_of_dense (fun w => (ContinuousLinearMap.adjoint (earlyDerivativeRemainder w)).comp
      (ContinuousLinearMap.adjoint E₀inv)) ?_ {w : PhysicalL2 | physicalSobolev 1 w}
    G1092.dense_sobolev ?_ u
  · exact (ContinuousLinearMap.adjoint.continuous.comp G1092.continuous_remainder).clm_comp continuous_const
  · intro w hw
    have hHS := (G1_091_corrected w hw).2
    have hc : IsCompactOperator ⇑(ContinuousLinearMap.adjoint (earlyDerivativeRemainder w)) :=
      G1092L3.hs_isCompact _ hHS
    exact hc.comp_clm _

theorem G1_092_compact_remainder (u : PhysicalL2) :
    IsCompactOperator ⇑(earlyDerivativeRemainder u) := by
  refine G1092.compact_of_dense earlyDerivativeRemainder G1092.continuous_remainder
    {w : PhysicalL2 | physicalSobolev 1 w} G1092.dense_sobolev ?_ u
  intro w hw
  exact G1092L3.hs_isCompact _ (G1_091_corrected w hw).1

theorem G1_092_corrected (u : PhysicalL2) :
    IsCompactOperator (earlyDerivativeRemainder u) ∧
    ∃ E₀ : PhysicalL2 ≃L[ℝ] Lib.L2Z,
      E₀.toContinuousLinearMap = earlyDerivative 0 ∧
      IsCompactOperator
        ((ContinuousLinearMap.adjoint (earlyDerivative u)).comp
          (ContinuousLinearMap.adjoint E₀.symm.toContinuousLinearMap) -
          ContinuousLinearMap.id ℝ PhysicalL2) ∧
      (ContinuousLinearMap.adjoint (earlyDerivative u)).comp
          (ContinuousLinearMap.adjoint E₀.symm.toContinuousLinearMap) =
        ContinuousLinearMap.adjoint
          (E₀.symm.toContinuousLinearMap.comp (earlyDerivative u)) := by
  obtain ⟨E₀, hE₀⟩ := G1092.earlyDerivative_zero_equiv
  refine ⟨G1_092_compact_remainder u, E₀, hE₀, ?_, (ContinuousLinearMap.adjoint_comp _ _).symm⟩
  have hid : ContinuousLinearMap.id ℝ PhysicalL2 =
      (ContinuousLinearMap.adjoint (earlyDerivative 0)).comp
        (ContinuousLinearMap.adjoint E₀.symm.toContinuousLinearMap) := by
    rw [← ContinuousLinearMap.adjoint_comp, ← hE₀]
    have : E₀.symm.toContinuousLinearMap.comp E₀.toContinuousLinearMap = ContinuousLinearMap.id ℝ PhysicalL2 := by
      ext x; simp
    rw [this]
    have h1 := star_one (PhysicalL2 →L[ℝ] PhysicalL2)
    rw [ContinuousLinearMap.star_eq_adjoint] at h1
    exact h1.symm
  have key : (ContinuousLinearMap.adjoint (earlyDerivative u)).comp
          (ContinuousLinearMap.adjoint E₀.symm.toContinuousLinearMap) -
          ContinuousLinearMap.id ℝ PhysicalL2 =
      (ContinuousLinearMap.adjoint (earlyDerivativeRemainder u)).comp
        (ContinuousLinearMap.adjoint E₀.symm.toContinuousLinearMap) := by
    rw [hid]
    unfold earlyDerivativeRemainder
    rw [map_sub, ContinuousLinearMap.sub_comp]
  rw [key]
  exact G1_092_compact_adjoint u _


end
end NlsGge.GKDefinitionDesign
