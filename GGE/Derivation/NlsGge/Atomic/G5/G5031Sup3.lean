import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031Sup1
import NlsGge.Atomic.G5.G5031Sup2
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.GK38.ContourAction
import NlsGge.GK38.GradFundamentalGradient
import NlsGge.Atomic.G2.G2029

/- G5-031 SUPPORT 3 `G5031Sup3` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5031Sup3.lean, namespace NlsGge.GKDefinitionDesign.G5031Sup3.
   `core31`: the Jacobi/actions argument of G5-031 (GK 18.6).  Landed inputs taken as parameters (instantiated by the final G5031):
     (h26)   G5026 at every real point with open angle gap:  {theta_j, I_i} = delta_ij              [landed G5026];
     (hprim) local analytic primitives of the angle differentials at real points                      [landed G5018M5a lift + betaSum analyticity].
   Concrete steps: the period equals -pi * {I_k, {theta_m, theta_n}} (G2_029 + evaluation commutes with the circle integral);
   Jacobi (local LIB081 version) reduces this to derivatives of the inner brackets {I_k,theta_m}, {theta_n,I_k}, which are locally
   constant along the real slice (h26), hence have zero complex derivative at the real point (G5031Sup2). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.ActionGradient
open NlsGge.Atomic.LIB

namespace NlsGge.GKDefinitionDesign
namespace G5031Sup3
noncomputable section

/-- The Hamiltonian map `J : (E →L ℂ) →L E` of the NLS pair bracket. -/
def Jmap : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair :=
  (((-Complex.I) • ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2).prod
    (Complex.I • ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2)).comp
    NlsGge.ThirdConsultation.G5017Support1.pairGradientL

theorem Jmap_apply (M : PotPair →L[ℂ] ℂ) :
    Jmap M = (-Complex.I • (pairGradientCLM M).2, Complex.I • (pairGradientCLM M).1) := rfl

theorem isSkew_Jmap : IsSkewDualMap Jmap := fun α β => by
  have h := pairPoissonCLM_antisymm α β
  exact h

theorem constantPoisson_eq_pairPoisson (f g : PotPair → ℂ) (φ : PotPair) :
    constantPoisson Jmap f g φ = pairPoisson f g φ := rfl

theorem differentiableAt_constantPoisson {f g : PotPair → ℂ} {x : PotPair}
    (hf : ContDiffAt ℂ 2 f x) (hg : ContDiffAt ℂ 2 g x) :
    DifferentiableAt ℂ (constantPoisson Jmap f g) x := by
  have hfd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℂ (fderiv ℂ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have : constantPoisson Jmap f g = fun y => (fderiv ℂ f y) (Jmap (fderiv ℂ g y)) := by
    funext y
    simp [constantPoisson_apply]
  rw [this]
  exact hfd.clm_apply (Jmap.differentiableAt.comp x hgd)

theorem eventually_gamma2_ne (u : PhysicalL2) (j : ℤ) (hj : gamma2 (realSlice u) j ≠ 0) :
    ∀ᶠ w in 𝓝 u, gamma2 (realSlice w) j ≠ 0 :=
  (((gamma2_analytic j).continuousOn.continuousAt
    (isOpen_gkW.mem_nhds (realSlice_mem_gkW u))).comp
    realSlice.continuous.continuousAt).eventually_ne hj

theorem core31 (u : PhysicalL2) (m n k : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (h26 : ∀ (w : PhysicalL2) (j i : ℤ), gamma2 (realSlice w) j ≠ 0 →
      pairPoissonCLM (angleDerivative j (realSlice w))
        (fderiv ℂ (fun φ => gkActionC38 φ i) (realSlice w)) = if i = j then 1 else 0)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ) :
    CircleIntegrable (fun lam => doubleAngleDiscriminantBracket m n (realSlice u) lam /
        canonRoot38 (realSlice u) lam) (discC (realSlice u) k) (discR (realSlice u) k) ∧
      abelianPeriod38 k (realSlice u) (doubleAngleDiscriminantBracket m n (realSlice u)) = 0 := by
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨hint, hfd, hdir⟩ := G2_029 (realSlice u) hφ k
  have hB : ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam =
      gradDiscrimCLM (realSlice u) lam (pairHamiltonianField (anglePoisson m n) (realSlice u)) := by
    intro lam
    show fderiv ℂ (fun ψ : PotPair => discrim ψ lam) (realSlice u) _ = _
    rw [(hasFDerivAt_gradDiscrimCLM (realSlice u) lam).fderiv]
  have hfun : (fun lam => doubleAngleDiscriminantBracket m n (realSlice u) lam /
      canonRoot38 (realSlice u) lam) = fun lam => gradDiscrimCLM (realSlice u) lam
        (pairHamiltonianField (anglePoisson m n) (realSlice u)) / canonRoot38 (realSlice u) lam :=
    funext fun lam => by rw [hB]
  -- (star): the Poisson bracket of the action with the double angle bracket vanishes
  have hstar : pairPoisson (fun ψ => gkActionC38 ψ k) (anglePoisson m n) (realSlice u) = 0 := by
    obtain ⟨Vm, θm, hVm, hxm, hanm, hdm⟩ := hprim u m hm
    obtain ⟨Vn, θn, hVn, hxn, hann, hdn⟩ := hprim u n hn
    have hVo : IsOpen (Vm ∩ Vn) := hVm.inter hVn
    have hxV : realSlice u ∈ Vm ∩ Vn := ⟨hxm, hxn⟩
    have hcm : ContDiffAt ℂ 2 θm (realSlice u) := (hanm _ hxm).contDiffAt
    have hcn : ContDiffAt ℂ 2 θn (realSlice u) := (hann _ hxn).contDiffAt
    have hcI : ContDiffAt ℂ 2 (fun ψ => gkActionC38 ψ k) (realSlice u) :=
      (action_analytic38 k _ hφ).contDiffAt
    have hPeq : anglePoisson m n =ᶠ[𝓝 (realSlice u)] constantPoisson Jmap θm θn := by
      filter_upwards [hVo.mem_nhds hxV] with ψ hψ
      simp only [anglePoisson, constantPoisson_apply, hdm ψ hψ.1, hdn ψ hψ.2]
      rfl
    have hevV : ∀ᶠ w in 𝓝 u, realSlice w ∈ Vm ∩ Vn :=
      realSlice.continuous.continuousAt.eventually (hVo.mem_nhds hxV)
    have hev2 := eventually_gamma2_ne u m hm
    have hev3 := eventually_gamma2_ne u n hn
    -- inner bracket {I_k, theta_m} is locally constant along the real slice
    have hd1 : fderiv ℂ (constantPoisson Jmap (fun ψ => gkActionC38 ψ k) θm) (realSlice u) = 0 := by
      refine G5031Sup2.fderiv_eq_zero_of_real_const _ u (-(if k = m then (1 : ℂ) else 0))
        (differentiableAt_constantPoisson hcI hcm) ?_
      filter_upwards [hevV, hev2] with w hw hw2
      have e1 : constantPoisson Jmap (fun ψ => gkActionC38 ψ k) θm (realSlice w) =
          pairPoissonCLM (fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice w))
            (angleDerivative m (realSlice w)) := by
        rw [constantPoisson_apply, hdm _ hw.1]
        rfl
      rw [e1, pairPoissonCLM_antisymm, h26 w m k hw2]
    have hd3 : fderiv ℂ (constantPoisson Jmap θn (fun ψ => gkActionC38 ψ k)) (realSlice u) = 0 := by
      refine G5031Sup2.fderiv_eq_zero_of_real_const _ u (if k = n then (1 : ℂ) else 0)
        (differentiableAt_constantPoisson hcn hcI) ?_
      filter_upwards [hevV, hev3] with w hw hw3
      have e1 : constantPoisson Jmap θn (fun ψ => gkActionC38 ψ k) (realSlice w) =
          pairPoissonCLM (angleDerivative n (realSlice w))
            (fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice w)) := by
        rw [constantPoisson_apply, hdn _ hw.2]
        rfl
      rw [e1, h26 w n k hw3]
    have hJac := G5031Sup1.constantPoisson_jacobi_at Jmap isSkew_Jmap
      (fun ψ => gkActionC38 ψ k) θm θn (realSlice u) hcI hcm hcn
    have T1 : constantPoisson Jmap (constantPoisson Jmap (fun ψ => gkActionC38 ψ k) θm) θn
        (realSlice u) = 0 := by
      rw [constantPoisson_apply, hd1]
      simp
    have T3 : constantPoisson Jmap (constantPoisson Jmap θn (fun ψ => gkActionC38 ψ k)) θm
        (realSlice u) = 0 := by
      rw [constantPoisson_apply, hd3]
      simp
    have T2 : constantPoisson Jmap (constantPoisson Jmap θm θn) (fun ψ => gkActionC38 ψ k)
        (realSlice u) = 0 := by
      rw [T1, T3] at hJac
      simpa using hJac
    have hskew := isSkew_Jmap (fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice u))
      (fderiv ℂ (anglePoisson m n) (realSlice u))
    have hfd2 : fderiv ℂ (anglePoisson m n) (realSlice u) =
        fderiv ℂ (constantPoisson Jmap θm θn) (realSlice u) := hPeq.fderiv_eq
    have hT2' : fderiv ℂ (constantPoisson Jmap θm θn) (realSlice u)
        (Jmap (fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice u))) = 0 := by
      rw [← constantPoisson_apply]
      exact T2
    show fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice u)
      (Jmap (fderiv ℂ (anglePoisson m n) (realSlice u))) = 0
    rw [hskew, hfd2, hT2', neg_zero]
  refine ⟨by rw [hfun]; exact hdir _, ?_⟩
  have hcomm := NlsGge.ThirdConsultation.G5017Support1.clm_circleIntegral_comm
    (ContinuousLinearMap.apply ℂ ℂ (pairHamiltonianField (anglePoisson m n) (realSlice u))) hint
  simp only [ContinuousLinearMap.apply_apply] at hcomm
  have hI : abelianPeriod38 k (realSlice u) (doubleAngleDiscriminantBracket m n (realSlice u)) =
      (circleIntegral (gradRootQuotient (realSlice u)) (discC (realSlice u) k)
        (discR (realSlice u) k)) (pairHamiltonianField (anglePoisson m n) (realSlice u)) := by
    rw [hcomm]
    unfold abelianPeriod38
    congr 1
    funext z
    simp only [hB, gradRootQuotient, ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hfd' := congrArg (fun L : PotPair →L[ℂ] ℂ => L (pairHamiltonianField (anglePoisson m n) (realSlice u)))
    hfd.fderiv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hfd'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hstar' : fderiv ℂ (fun ψ => gkActionC38 ψ k) (realSlice u)
      (pairHamiltonianField (anglePoisson m n) (realSlice u)) = 0 := hstar
  rw [hstar'] at hfd'
  rw [hI]
  have : -(1 / (Real.pi : ℂ)) * (circleIntegral (gradRootQuotient (realSlice u))
      (discC (realSlice u) k) (discR (realSlice u) k))
      (pairHamiltonianField (anglePoisson m n) (realSlice u)) = 0 := hfd'.symm
  rcases mul_eq_zero.mp this with h | h
  · exfalso
    have : (1 / (Real.pi : ℂ)) = 0 := by linear_combination -h
    exact one_div_ne_zero hπ this
  · exact h

end
end G5031Sup3
end NlsGge.GKDefinitionDesign
