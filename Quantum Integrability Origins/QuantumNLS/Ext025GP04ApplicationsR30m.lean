import QuantumNLS.Local014ActualUseR29m
import QuantumNLS.Local014KernelFieldR29m
import QuantumNLS.ResetMoserAnalytic
import QuantumNLS.CompleteAnalyticFlowR107
import QuantumNLS.Ext025A4ProductDischarge
import QuantumNLS.Ext025A4D01Discharge
import QuantumNLS.Ext025GP04HartreeR30m

/-! GP-04 owner condition at the actual fields. LOCAL-014 and PROP-001 are
witnessed by their dedicated theorems. The four analytic fields below give
continuous state derivatives by the Fréchet derivative theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section
open Set Metric Filter Topology
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Ext025GP04ApplicationsR30m

open QuantumNLS.D01LocalPrimitive QuantumNLS.ResetMoser

/-- LOCAL-017. The state derivative of the Moser field is jointly continuous
on the time interval and smaller state ball used by the source. -/
theorem local017_continuous_state_derivative {S : ResetMoser.Hyp}
    (MD : MoserData S) :
    ContinuousOn (fun q : K × ℝ => fderiv ℝ (MD.Yf q.2) q.1)
      (ball 0 (MD.R0 / 4) ×ˢ Icc (0 : ℝ) 1) := by
  let Y : K × ℝ → K := fun q => MD.Yf q.2 q.1
  let U := ball (0 : K) (MD.R0 / 4) ×ˢ Icc (0 : ℝ) 1
  have hY : AnalyticOnNhd ℝ Y U := by
    intro q hq
    have hf := MD.Fc_analyticAt (mem_ball_zero_iff.mp hq.1) hq.2
    have h₁ : ∀ᶠ z : K × ℝ in 𝓝 q, z.1 ∈ ball (0 : K) (MD.R0 / 4) :=
      continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds hq.1)
    have h₂ : ∀ᶠ z : K × ℝ in 𝓝 q, z.2 ∈ Ioo (-1 / 4 : ℝ) (5 / 4) :=
      continuous_snd.continuousAt.eventually (Ioo_mem_nhds (by linarith [hq.2.1]) (by linarith [hq.2.2]))
    apply (analyticAt_fst.comp hf).congr
    filter_upwards [h₁,h₂] with z hz₁ hz₂
    change (MD.Fc z).1 = MD.Yf z.2 z.1
    rw [MD.Fc_eq_of_small (mem_ball_zero_iff.mp hz₁).le, MD.Ghat_apply,
      ResetMoserClamp.sig_eq ⟨hz₂.1.le,hz₂.2.le⟩]
  let i : K →L[ℝ] K × ℝ := ContinuousLinearMap.inl ℝ K ℝ
  have hc : ContinuousOn (fun q => (fderiv ℝ Y q).comp i) U :=
    hY.fderiv.continuousOn.clm_comp continuousOn_const
  apply hc.congr
  intro q hq
  have hi : HasFDerivAt (fun x : K => (x,q.2)) i q.1 := by
    have hh := i.hasFDerivAt (x := q.1) |>.add_const (0,q.2)
    simpa [i] using hh
  exact ((hY q hq).differentiableAt.hasFDerivAt.comp q.1 hi).fderiv

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.CompleteFlowPhysicalR107 (realNS_eq)

/-- R-7ED997C1 uses the physical indexed mass field. -/
theorem individual_period_continuous_state_derivative
    {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (n : ℤ) :
    Continuous (fderiv ℝ
      (SymplecticBracket.hamField (RootMassInvolutionR8.mass (L := L) hκ n))) := by
  have hf : AnalyticOnNhd ℝ
      (SymplecticBracket.hamField (RootMassInvolutionR8.mass (L := L) hκ n)) univ := by
    simpa +instances only [CompleteAnalyticFlowR107.realNormed, realNS_eq] using
      CompleteAnalyticFlowR107.analytic_field (L := L) hκ n
  exact continuousOn_univ.mp hf.fderiv.continuousOn

open _root_.HilbertL1Compact (L1)
open ProductTorusGenerator (Linf X)
open ProductTorusAnalytic (Lgen X_eq_Lgen)

/-- R-4C2E4AC7, for every bounded angle generator used in the product-torus construction. -/
theorem product_torus_continuous_state_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {I : E → L1 ℝ} (hI : AnalyticOnNhd ℝ I univ) (θ : Linf) :
    Continuous (fderiv ℝ (X (fderiv ℝ I) θ)) := by
  have he : X (fderiv ℝ I) θ = (fun u => Lgen θ (fderiv ℝ I u)) :=
    funext (X_eq_Lgen θ)
  rw [he]
  have ha : AnalyticOnNhd ℝ (fun u => Lgen θ (fderiv ℝ I u)) univ :=
    fun u hu => ((Lgen θ).analyticAt (fderiv ℝ I u)).comp (hI.fderiv u hu)
  exact continuousOn_univ.mp ha.fderiv.continuousOn

/-- R-B390B5E9, for the field from the original source reconstruction data. -/
theorem d01_continuous_state_derivative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : D01LocalPrimitive.Hyp H) : Continuous (fderiv ℝ S.Y) :=
  continuousOn_univ.mp ((show AnalyticOnNhd ℝ S.Y univ from
    fun u _ => (TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 u).fderiv.continuousOn)

end QuantumNLS.Ext025GP04ApplicationsR30m

#print axioms QuantumNLS.Local014ActualUseR29m.continuous_actual_field_derivative
#print axioms QuantumNLS.Local014KernelFieldR29m.continuousOn_kernel_field_derivative
#print axioms QuantumNLS.Ext025GP04HartreeR30m.source_continuous_derivative
#print axioms QuantumNLS.Ext025GP04ApplicationsR30m.local017_continuous_state_derivative
#print axioms QuantumNLS.Ext025GP04ApplicationsR30m.individual_period_continuous_state_derivative
#print axioms QuantumNLS.Ext025GP04ApplicationsR30m.product_torus_continuous_state_derivative
#print axioms QuantumNLS.Ext025GP04ApplicationsR30m.d01_continuous_state_derivative
