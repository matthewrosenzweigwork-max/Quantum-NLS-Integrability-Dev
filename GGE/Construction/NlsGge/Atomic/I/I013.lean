import NlsGge.Atomic.I.I010
import NlsGge.Atomic.I.I011
import NlsGge.Atomic.I.I012
import NlsGge.Herglotz38.PlemeljBoundaryE02_38
import NlsGge.Herglotz38.TruncatedSymmetrizationE02_38
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.ThirdConsultation.I.SymmetricKernel
import NlsGge.ThirdConsultation.I.I013L2

                                                                                                                    
                                                                                                                                                         
                                                                                                                            
                                                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I

theorem i013 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hc : ConvexOn ℝ Set.univ W) :
    let v := actualGapHeightE02_38 u
    let p := actualQuasimomentumRealPartE02_38 u
    let f := fun x : ℝ => W (2 * x)
    let H := fun (ε x : ℝ) => ∫ t in {t : ℝ | ε < |t - x|}, v t / (x - t)
    MemLp v 2 volume ∧ MemLp (fun x => deriv f (p x) * v x) 2 volume ∧
    MemLp (pvHilbert v) 2 volume ∧
    Integrable (fun x => deriv f (p x) * (x - p x) * v x) ∧
    Integrable (symmetricKernel f p v) ∧
    (∀ ε : ℝ, 0 < ε → MemLp (H ε) 2 volume) ∧
    Tendsto (fun ε : ℝ => eLpNorm (fun x => H ε x - pvHilbert v x) 2 volume)
      (𝓝[>] 0) (𝓝 0) ∧
    (∀ x : ℝ, x - p x = (1 / Real.pi) * pvHilbert v x) ∧
    Tendsto (fun ε : ℝ => ∫ x : ℝ, deriv f (p x) * v x * H ε x)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, deriv f (p x) * v x * pvHilbert v x)) ∧
    (2 / Real.pi) * (∫ x : ℝ, deriv f (p x) * (x - p x) * v x) =
      (1 / Real.pi ^ 2) * ∫ q : ℝ × ℝ, symmetricKernel f p v q := by
  intro v p f H
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hpc : Continuous p := continuous_actualQuasimomentumRealPartE02_38 u
  obtain ⟨-, A0, hA0⟩ := actualGapHeight_support_finiteGap_E02_38 u hfin
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |A0| + 1 := ⟨_, rfl⟩
  have hAnn : 0 ≤ A := by linarith [abs_nonneg A0]
  have hAA : |A0| < A := by linarith
  have hzero : ∀ x : ℝ, |A0| < |x| → v x = 0 :=
    fun x hx => hA0 x (lt_of_le_of_lt (le_abs_self _) hx)
  have hsuppA : ∀ t, t ∉ Icc (-A) A → v t = 0 := by
    intro t ht
    apply hzero t
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le (by linarith) (le_abs_self t)
  obtain ⟨H0, hH0⟩ := actualGapHeight_holder_E02_38 u A
  have hloc : ∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A, |v s - v t| ≤ |H0| * Real.sqrt |s - t| :=
    fun s hs t ht => (hH0 s hs t ht).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  have hhol : ∀ s t, |v s - v t| ≤ |H0| * Real.sqrt |s - t| :=
    holder_global_of_Icc_E02_38 v A |A0| |H0| (abs_nonneg _) (abs_nonneg _) hAA hzero hloc
  have hH : 0 ≤ |H0| := abs_nonneg _
  obtain ⟨B, hB0, hBv⟩ := NlsGge.ThirdConsultation.I.I013B.exists_abs_bound v hvc A hsuppA
  obtain ⟨M0, hM0⟩ := truncatedHilbert_bound_E02_38 hvc hH hAnn hsuppA hhol
  have hcsv : ∀ g : ℝ → ℝ, HasCompactSupport (fun x => g x * v x) := fun g =>
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) (fun x hx => by
      show g x * v x = 0
      rw [hsuppA x hx, mul_zero])
  -- the derivative of f and its continuity
  have hdf : deriv f = fun x => 2 * deriv W (2 * x) :=
    funext fun x => (NlsGge.Atomic.I010.hasDerivAt_scaled W hW x).deriv
  have hdfc : Continuous (deriv f) := by
    rw [hdf]
    exact continuous_const.mul ((hW.continuous_deriv (by norm_num)).comp
      (continuous_const.mul continuous_id))
  have hφc : Continuous (fun x => deriv f (p x)) := hdfc.comp hpc
  have hφv : Continuous (fun x => deriv f (p x) * v x) := hφc.mul hvc
  -- (1) and (2): integrability and L^2 membership of v and deriv f (p) v
  have hvL2 : MemLp v 2 volume := hvc.memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) (fun x hx => hsuppA x hx))
  have hφL2 : MemLp (fun x => deriv f (p x) * v x) 2 volume :=
    hφv.memLp_of_hasCompactSupport (hcsv _)
  have hg : Integrable (fun x => deriv f (p x) * v x) :=
    hφv.integrable_of_hasCompactSupport (hcsv _)
  -- (3) the PV transform: identity with p, continuity, and L^2
  have hid : ∀ x : ℝ, x - p x = (1 / Real.pi) * pvHilbert v x :=
    fun x => realPart_sub_eq_pvHilbert_E02_38 u hu |H0| A hH hAnn hsuppA hhol x
  have hpvc : Continuous (pvHilbert v) := by
    have e : pvHilbert v = fun x => Real.pi * (x - p x) := funext fun x => by
      rw [hid x, ← mul_assoc, mul_one_div_cancel Real.pi_ne_zero, one_mul]
    rw [e]
    exact continuous_const.mul (continuous_id.sub hpc)
  have hpvL2 : MemLp (pvHilbert v) 2 volume :=
    NlsGge.ThirdConsultation.I.I013C.pv_memLp v hvc |H0| M0 A B hH hAnn hB0 hsuppA hBv hhol hM0 hpvc
  -- (4) integrability of deriv f (p) (x - p) v
  have hint4 : Integrable (fun x => deriv f (p x) * (x - p x) * v x) :=
    ((hφc.mul (continuous_id.sub hpc)).mul hvc).integrable_of_hasCompactSupport
      (hcsv (fun x => deriv f (p x) * (x - p x)))
  -- (5) integrability of the symmetrized kernel, and the stabilization of I-012
  obtain ⟨hIK, -, δ0, hδ0, -, hstab⟩ := i012 u hu hfin W hW hc
  -- (6) truncations are in L^2
  have hH2 : ∀ ε : ℝ, 0 < ε → MemLp (H ε) 2 volume := fun ε hε =>
    NlsGge.ThirdConsultation.I.I013C.truncHilbert_memLp v hvc M0 A B hAnn hB0 hsuppA hBv hM0 ε hε
  -- (7) L^2 convergence of the truncations
  have hL2lim : Tendsto (fun ε : ℝ => eLpNorm (fun x => H ε x - pvHilbert v x) 2 volume)
      (𝓝[>] 0) (𝓝 0) :=
    NlsGge.ThirdConsultation.I.I013C.truncHilbert_sub_pv_tendsto v hvc |H0| M0 A B hH hAnn hB0
      hsuppA hBv hhol hM0 hpvc
  -- (9) the pairing limit
  have hpair : Tendsto (fun ε : ℝ => ∫ x : ℝ, deriv f (p x) * v x * H ε x)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, deriv f (p x) * v x * pvHilbert v x)) :=
    NlsGge.ThirdConsultation.I.I013C.truncHilbert_pairing_tendsto v hvc |H0| M0 A B hH hAnn
      hsuppA hhol hM0 (fun x => deriv f (p x) * v x) hg
  -- (10) the symmetrized identity
  have hpt : ∀ ε : ℝ, 0 < ε → ε < δ0 → ∀ q : ℝ × ℝ,
      (deriv f (p q.1) - deriv f (p q.2)) * truncKernelE02_38 v ε q = symmetricKernel f p v q := by
    intro ε hε hεδ q
    have hq := congrFun (hstab ε hε hεδ) q
    by_cases hc' : ε < |q.1 - q.2|
    · have hmem : q ∈ {q : ℝ × ℝ | ε < |q.2 - q.1|} := by
        show ε < |q.2 - q.1|
        rwa [abs_sub_comm]
      have hK : truncKernelE02_38 v ε q = v q.1 * v q.2 / (q.1 - q.2) := by
        unfold truncKernelE02_38
        rw [Set.indicator_of_mem hmem]
      rw [hK]
      unfold symmetricKernel
      ring
    · have hnmem : q ∉ {q : ℝ × ℝ | ε < |q.2 - q.1|} := by
        show ¬ (ε < |q.2 - q.1|)
        rwa [abs_sub_comm]
      have hK : truncKernelE02_38 v ε q = 0 := by
        unfold truncKernelE02_38
        rw [Set.indicator_of_notMem hnmem]
      have hS : symmetricKernel f p v q = 0 := by
        have hq' := hq
        rw [Set.indicator_of_notMem (show q ∉ {q : ℝ × ℝ | ε < |q.1 - q.2|} from hc')] at hq'
        exact hq'.symm
      rw [hK, hS, mul_zero]
  have hint_eq : ∀ ε : ℝ, 0 < ε → ε < δ0 →
      (∫ q : ℝ × ℝ, (deriv f (p q.1) - deriv f (p q.2)) * truncKernelE02_38 v ε q) =
        ∫ q : ℝ × ℝ, symmetricKernel f p v q :=
    fun ε hε hεδ => integral_congr_ae (Eventually.of_forall (hpt ε hε hεδ))
  have hsym : ∀ ε : ℝ, 0 < ε → ε < δ0 →
      2 * (∫ x : ℝ, deriv f (p x) * v x * H ε x) = ∫ q : ℝ × ℝ, symmetricKernel f p v q := by
    intro ε hε hεδ
    exact (NlsGge.Atomic.I011.truncatedHilbert_symmetrization u hu hfin W hW hc ε hε).2.2.trans
      (hint_eq ε hε hεδ)
  have hδpos : (0:ℝ) < δ0 := hδ0
  have hconst : Tendsto (fun ε : ℝ => ∫ x : ℝ, deriv f (p x) * v x * H ε x)
      (𝓝[>] 0) (𝓝 ((1 / 2) * ∫ q : ℝ × ℝ, symmetricKernel f p v q)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδpos] with ε hε
    have h := hsym ε hε.1 hε.2
    show (1 / 2) * (∫ q : ℝ × ℝ, symmetricKernel f p v q) = ∫ x : ℝ, deriv f (p x) * v x * H ε x
    linarith
  have hLim : (∫ x : ℝ, deriv f (p x) * v x * pvHilbert v x) =
      (1 / 2) * ∫ q : ℝ × ℝ, symmetricKernel f p v q :=
    tendsto_nhds_unique hpair hconst
  have hpt2 : ∀ x : ℝ, deriv f (p x) * (x - p x) * v x =
      (1 / Real.pi) * (deriv f (p x) * v x * pvHilbert v x) := fun x => by
    rw [hid x]; ring
  have hLHS : (∫ x : ℝ, deriv f (p x) * (x - p x) * v x) =
      (1 / Real.pi) * ∫ x : ℝ, deriv f (p x) * v x * pvHilbert v x := by
    rw [integral_congr_ae (Eventually.of_forall hpt2), integral_const_mul]
  refine ⟨hvL2, hφL2, hpvL2, hint4, hIK, hH2, hL2lim, hid, hpair, ?_⟩
  rw [hLHS, hLim]
  ring

end NlsGge.ThirdConsultation.I

end
