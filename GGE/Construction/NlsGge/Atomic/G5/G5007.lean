import Mathlib
import NlsGge.Atomic.G5.G5003
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G4.G4013
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.ThirdConsultation.G5.G5005Support2
import NlsGge.GK38.GradEigenKernelProbe
import NlsGge.GK38.GradFundamentalFree
import NlsGge.GK38.GradFundamentalSpectralProbe
import NlsGge.GK38.Lib.EntireProductsParamProbe
import NlsGge.GK38.AbelianFreeSolutionFiber
import NlsGge.GK38.TauGammaFactorProbe
import NlsGge.GK38.PeriodicLabellingFreeLabels
import NlsGge.GK38.IsolatingTopology

                                                                                                                  
                                                                                                         
                                                
                                                                                                                            
                                                                                                                               
                                                                                                   
                                                                             
                                                                                                                        
                                                                                                                      
                                                                                           
                                                                                          
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation.G5005Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5007_zero_mem : (0 : PotPair) ∈ sourceBetaW := by
  have h : realSlice (0 : PhysicalL2) ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self 0)
  rwa [realSlice_zero] at h

theorem g5007_zero_gk : (0 : PotPair) ∈ gkW :=
  sourceFamily.W_gk (sourceFamily.V_W g5007_zero_mem)

theorem g5007_muSeq_zero (n : ℤ) : muSeq 0 n = (n : ℂ) * (Real.pi : ℂ) := by
  rw [muSeq_zero38]
  rfl

theorem g5007_sourceF_zero (n : ℤ) : sourceF n 0 = 0 := by
  obtain ⟨t, ht, -, hF⟩ := sourceFamily.F_real n 0
  rw [p5RealGapCube_free_unique38 n t ht] at hF
  simp only [map_zero] at hF
  exact hF

theorem g5007_cos (n : ℤ) : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
  have e : ((n : ℂ) * (Real.pi : ℂ)) = (((n : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cos, Real.cos_int_mul_pi, Complex.ofReal_zpow, Complex.ofReal_neg,
    Complex.ofReal_one]

theorem g5007_numerator_zero (n : ℤ) :
    p6PsiNumerator38 n (sourceF n) 0 (muSeq 0 n) = -2 * (-1 : ℂ) ^ n := by
  rw [g5007_muSeq_zero]
  unfold p6PsiNumerator38 p2Numerator38 p2FullNumerator38
  rw [g5007_sourceF_zero, map_zero, Lib.probe_omit_at_root, g5007_cos]

theorem g5007_zeta_zero (n : ℤ) : normalizedZeta n 0 (muSeq 0 n) = 1 := by
  obtain ⟨c, N, hg, hs⟩ := isolating_family38 (0 : PotPair) g5007_zero_gk
  have hmu : muSeq 0 n ∈ Metric.ball (discC (0 : PotPair) n) (discR (0 : PotPair) n) := (hs.1 n).2.1
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (muSeq 0 n) hmu
  have hlb : muSeq 0 n + ((ε / 2 : ℝ) : ℂ) ∈
      Metric.ball (discC (0 : PotPair) n) (discR (0 : PotPair) n) := by
    apply hεb
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hcut : muSeq 0 n + ((ε / 2 : ℝ) : ℂ) ∉ gapSegment 0 n := by
    unfold gapSegment
    rw [lamMinus_zero38, lamPlus_zero38, segment_same, Set.mem_singleton_iff, muSeq_zero38]
    intro h
    have h1 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination h
    have h2 : ε / 2 = 0 := by exact_mod_cast h1
    linarith
  exact (G4013 n 0 g5007_zero_mem _ hlb hcut).2.2.2.2 _ hmu

theorem g5007_radiusQuotient_zero (n : ℤ) :
    radiusQuotient n (0 : PotPair) = radiusQuotientLeading n := by
  unfold radiusQuotient radiusQuotientLeading
  rw [g5007_zeta_zero, g5007_numerator_zero]
  have hs : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_zpow]; norm_num
  have hne : ((-1 : ℂ) ^ n) ≠ 0 := zpow_ne_zero n (by norm_num)
  rw [div_eq_div_iff (mul_ne_zero (by norm_num) hne) (by norm_num)]
  linear_combination (-2 : ℂ) * hs

theorem g5007_gradDiscrimCont_zero (z : ℂ) : gradDiscrimCont38 0 z = 0 := by
  ext t k
  have h := scaled_gradDiscrim38_zero z t
  have h' : gradDiscrim38 0 z t = 0 := (smul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  show gradDiscrim38 0 z t k = 0
  rw [h']
  rfl

theorem g5007_class_zero : pairKernelL2Class38 (0 : PairKernelCont38) = 0 := by
  have h := map_zero pairKernelL2CLM38
  rwa [pairKernelL2CLM38_apply] at h

theorem g5007_pairGradient_tauN_zero (n : ℤ) : pairGradient (fun ψ => tauN ψ n) 0 = 0 := by
  rw [NlsGge.ThirdConsultation.G5005Support2.pairGradient_tauN 0 g5007_zero_gk n]
  have hk : gradTauCont38 (0 : PotPair) n = 0 := by
    unfold gradTauCont38
    have h : k4aQuotientKernelCont38 (0 : PotPair) = fun _ => 0 := by
      funext z
      unfold k4aQuotientKernelCont38
      rw [g5007_gradDiscrimCont_zero]
      first
      | exact smul_zero _
      | (ext t k; simp)
    rw [h]
    have h0 : circleIntegral (fun _ : ℂ => (0 : PairKernelCont38)) (discC (0 : PotPair) n) (discR (0 : PotPair) n) = 0 := by
      simp [circleIntegral]
    rw [h0]
    first
    | exact smul_zero _
    | (ext t k; simp)
  rw [hk, g5007_class_zero]

theorem g5007_Q_free (z : ℂ) :
    GradEigen38.Q (GradEigen38.state 0 z ![1, 1]) = 2 := by
  unfold GradEigen38.Q
  have hi : (∫ s in (0 : ℝ)..1, pairKernelExt38 (GradEigen38.state 0 z ![1, 1]) s 0 *
      pairKernelExt38 (GradEigen38.state 0 z ![1, 1]) s 1) = ∫ _ in (0 : ℝ)..1, (1 : ℂ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    simp only [pairKernelExt38_of_mem _ hs, GradEigen38.probe_free_state]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one]
    rw [← Complex.exp_add, neg_mul, neg_mul, neg_add_cancel, Complex.exp_zero]
  rw [hi, intervalIntegral.integral_const]
  norm_num

theorem g5007_dirEigenKernel_zero (n : ℤ) :
    PoissonDirichlet38.dirEigenKernel38 0 ((n : ℂ) * (Real.pi : ℂ)) = (1 / 2 : ℂ) • fkE n := by
  unfold PoissonDirichlet38.dirEigenKernel38
  rw [g5007_Q_free]
  ext t k
  have hsq : GradEigen38.square (GradEigen38.state 0 ((n : ℂ) * (Real.pi : ℂ)) ![1, 1]) t =
      starProd38 (GradEigen38.state 0 ((n : ℂ) * (Real.pi : ℂ)) ![1, 1] t)
        (GradEigen38.state 0 ((n : ℂ) * (Real.pi : ℂ)) ![1, 1] t) := rfl
  have hfk : fkE n t = ![Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I),
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I))] := rfl
  have e0 : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ) +
      Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I := by ring
  have e1 : -Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ) +
      -Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((t : ℝ) : ℂ) =
      -(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I) := by ring
  show ((2 : ℂ)⁻¹ • GradEigen38.square (GradEigen38.state 0 ((n : ℂ) * (Real.pi : ℂ)) ![1, 1]) t) k =
    ((1 / 2 : ℂ) • fkE n t) k
  rw [hsq, hfk, GradEigen38.probe_free_state]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul, starProd38,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one]
    rw [← Complex.exp_add, e0]
    norm_num
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul, starProd38,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one]
    rw [← Complex.exp_add, e1]
    norm_num

theorem g5007_gradAntiDiscrimCont_zero (n : ℤ) :
    gradAntiDiscrimCont38 0 ((n : ℂ) * (Real.pi : ℂ)) = (-Complex.I * (-1 : ℂ) ^ n) • fkD n := by
  have hpi : Complex.exp ((n : ℂ) * (-((Real.pi : ℂ) * Complex.I))) = (-1 : ℂ) ^ n := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  have hpi' : Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ n := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  ext t k
  have h := scaled_gradAntiDiscrim38_zero ((n : ℂ) * (Real.pi : ℂ)) t
  have hg : gradAntiDiscrim38 0 ((n : ℂ) * (Real.pi : ℂ)) t =
      (-Complex.I) • (Complex.I • gradAntiDiscrim38 0 ((n : ℂ) * (Real.pi : ℂ)) t) := by
    rw [smul_smul]
    simp
  rw [h] at hg
  have e0 : -Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (1 - 2 * ((t : ℝ) : ℂ)) =
      (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) +
        2 * (Real.pi : ℂ) * (n : ℂ) * ((t : ℝ) : ℂ) * Complex.I := by ring
  have e1 : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (1 - 2 * ((t : ℝ) : ℂ)) =
      (n : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        -(2 * (Real.pi : ℂ) * (n : ℂ) * ((t : ℝ) : ℂ) * Complex.I) := by ring
  rw [e0, e1, Complex.exp_add, Complex.exp_add, hpi, hpi'] at hg
  show gradAntiDiscrim38 0 ((n : ℂ) * (Real.pi : ℂ)) t k =
    ((-Complex.I * (-1 : ℂ) ^ n) • fkD n t) k
  have hfk : fkD n t = ![-Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I),
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) * (t.1 : ℂ) * Complex.I))] := rfl
  rw [hg, hfk]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    ring

theorem g5007_pairGradient_muSeq_zero (n : ℤ) :
    pairGradient (fun ψ => muSeq ψ n) 0 =
      (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n) := by
  rw [NlsGge.ThirdConsultation.G5005Support2.pairGradient_muSeq 0 g5007_zero_gk n,
    g5007_muSeq_zero, g5007_dirEigenKernel_zero, pairKernelL2Class38_smul, class_fkE]

theorem g5007_pairGradient_antiDiscrim_zero (n : ℤ) :
    pairGradient (fun ψ => antiDiscrim ψ (muSeq 0 n)) 0 =
      (-Complex.I * (-1 : ℂ) ^ n) • (fourierMode 1 n - fourierMode (-1) n) := by
  rw [NlsGge.ThirdConsultation.G5005Support2.pairGradient_antiDiscrim, g5007_muSeq_zero,
    g5007_gradAntiDiscrimCont_zero, pairKernelL2Class38_smul, class_fkD]

theorem G5007 (n a : ℤ) (ha : a = 1 ∨ a = -1) :
  radiusQuotient n (0 : PotPair) = radiusQuotientLeading n ∧
  antiDiscrim (0 : PotPair) (muSeq 0 n) = 0 ∧
  deriv (antiDiscrim (0 : PotPair)) (muSeq 0 n) = 0 ∧
  pairGradient (fun ψ => tauN ψ n) 0 = 0 ∧
  pairGradient (fun ψ => muSeq ψ n) 0 =
    (1 / 2 : ℂ) • (fourierMode 1 n + fourierMode (-1) n) ∧
  pairGradient (cartesianZExtended n a) 0 = (-2 : ℂ) • fourierMode a n := by
  have hq := g5007_radiusQuotient_zero n
  have hτ := g5007_pairGradient_tauN_zero n
  have hμ := g5007_pairGradient_muSeq_zero n
  refine ⟨hq, antiDiscrim_zero38 _, antiDiscrimDeriv_zero38 _, hτ, hμ, ?_⟩
  have hg : gamma2 (realSlice (0 : PhysicalL2)) n = 0 := by
    rw [realSlice_zero]
    exact (tauGamma_free_values38 discC discR (fun φ hφ => isolating_family38 φ hφ) n).2.1
  have hE := G5003 n a ha 0 hg
  simp only [realSlice_zero] at hE
  rw [hE, hτ, hμ, antiDiscrim_zero38, antiDiscrimDeriv_zero38, hq,
    g5007_pairGradient_antiDiscrim_zero n]
  unfold radiusQuotientLeading
  have hs2 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [sq, ← mul_zpow]; norm_num
  generalize (-1 : ℂ) ^ n = s at hs2 ⊢
  rcases ha with rfl | rfl
  · simp only [Int.cast_one]
    match_scalars <;> first
      | ring1
      | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf)
      | (ring_nf; simp only [Complex.I_sq, hs2])
      | (ring_nf; simp only [Complex.I_sq, hs2]; norm_num)
  · simp only [Int.cast_neg, Int.cast_one]
    match_scalars <;> first
      | ring1
      | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf)
      | (ring_nf; simp only [Complex.I_sq, hs2])
      | (ring_nf; simp only [Complex.I_sq, hs2]; norm_num)

end
end NlsGge.GKDefinitionDesign
