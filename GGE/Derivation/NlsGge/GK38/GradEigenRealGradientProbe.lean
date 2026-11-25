import NlsGge.GK38.GradEigenRealNeumann
import NlsGge.GK38.GradEigenKernelProbe
import NlsGge.GK38.DirichletRealGapProbe
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem probe_free_dirichlet_gradient (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => gkMu v n) (realEnergyGradient (dirState 0 n)) 0 ∧
    dirState 0 n t0 = ![1,1] ∧ energy (dirState 0 n) = 2 ∧
    ∀ t : Time, square (dirState 0 n) t =
      ![Complex.exp (2*Complex.I*((n : ℝ)*Real.pi : ℂ)*(t : ℝ)),
        Complex.exp (-2*Complex.I*((n : ℝ)*Real.pi : ℂ)*(t : ℝ))] := by
  have hi := kernel_integrability (dirState 0 n)
  have he (s : ℝ) : pairKernelExt38 (dirState 0 n) s 0 *
      pairKernelExt38 (dirState 0 n) s 1 = 1 := by
    change dirState 0 n (projIcc 0 1 zero_le_one s) 0 *
      dirState 0 n (projIcc 0 1 zero_le_one s) 1 = 1
    rw [probe_free_dirichlet]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  have hQ : Q (dirState 0 n) = 2 := by simp [Q,he]
  have hE : energy (dirState 0 n) = 2 := by
    have hr := real_denominator (dirState 0 n) (dirState_real_symmetry 0 n)
    rw [hQ] at hr
    exact Complex.ofReal_injective hr.symm
  refine ⟨actual_dirichlet_label_hasFDerivAt 0 n,state_initial _ _ _,hE,?_⟩
  intro t
  ext i
  fin_cases i <;> simp only [square,ContinuousMap.coe_mk,starProd38,
    probe_free_dirichlet,Matrix.cons_val_zero,Matrix.cons_val_one,← Complex.exp_add] <;>
    congr 1 <;> ring

theorem probe_constant_dirichlet_state (t : Time) :
    dirState (constL2 1) 0 t = ![1,1] := by
  unfold dirState
  rw [dirichlet_real_constant_labels_probe38.1]
  norm_num only [Complex.ofReal_one]
  rw [state_eq_mulVec,fundPair_dirichlet_nilpotent38]
  ext i
  fin_cases i <;> simp [dirichletNilpotentFund38,zsCoefficientComplex,Matrix.mulVec,
    dotProduct,Fin.sum_univ_two,Complex.real_smul] <;> ring

theorem probe_constant_dirichlet_energy : energy (dirState (constL2 1) 0) = 2 := by
  have hi := kernel_integrability (dirState (constL2 1) 0)
  have he (s : ℝ) : pairKernelExt38 (dirState (constL2 1) 0) s = ![1,1] :=
    probe_constant_dirichlet_state (projIcc 0 1 zero_le_one s)
  norm_num [energy,he]

theorem probe_constant_dirichlet_pairing :
    integralPairCLM38 (square (dirState (constL2 1) 0)) t1 (realSlice (constL2 1)) = 2 := by
  have hi := intervalIntegrable_pairKernel38 (square (dirState (constL2 1) 0)) t1
    (realSlice (constL2 1))
  change pairIntegral38 (square (dirState (constL2 1) 0)) t1 (realSlice (constL2 1)) = 2
  rw [realSlice_constL2]
  simp only [star_one]
  unfold pairIntegral38
  have he (s : ℝ) : pairKernelExt38 (square (dirState (constL2 1) 0)) s = ![1,1] := by
    change square (dirState (constL2 1) 0) (projIcc 0 1 zero_le_one s) = ![1,1]
    simp [square,probe_constant_dirichlet_state,starProd38]
  have hae : (fun s => pairKernelExt38 (square (dirState (constL2 1) 0)) s 0 *
      potRepFst38 (constL2 1,constL2 1) s +
      pairKernelExt38 (square (dirState (constL2 1) 0)) s 1 *
      potRepSnd38 (constL2 1,constL2 1) s) =ᵐ[volume] fun _ => (2 : ℂ) := by
    filter_upwards [coverRep38_const_ae (1 : ℂ)] with s hs
    norm_num [he,potRepFst38,potRepSnd38,hs]
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  simp [t1]

theorem probe_constant_dirichlet_gradient :
    gkMu (constL2 1) 0 = 1 ∧
    HasFDerivAt (fun v : PhysicalL2 => gkMu v 0)
      (realEnergyGradient (dirState (constL2 1) 0)) (constL2 1) ∧
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v 0) (constL2 1)) (constL2 1) = 1 := by
  have hd := actual_dirichlet_label_hasFDerivAt (constL2 1) 0
  refine ⟨dirichlet_real_constant_labels_probe38.1,hd,?_⟩
  rw [hd.fderiv]
  change (energy (dirState (constL2 1) 0))⁻¹ *
    (integralPairCLM38 (square (dirState (constL2 1) 0)) t1 (realSlice (constL2 1))).re = 1
  rw [probe_constant_dirichlet_energy,probe_constant_dirichlet_pairing]
  norm_num

theorem probe_negative_constant_neumann_gradient :
    nu (-(constL2 1)) 0 = 1 ∧
    HasFDerivAt (fun v : PhysicalL2 => nu v 0)
      (realEnergyGradient (neuState (-(constL2 1)) 0)) (-(constL2 1)) ∧
    (fderiv ℝ (fun v : PhysicalL2 => nu v 0) (-(constL2 1))) (constL2 1) = -1 ∧
    ∀ t : Time, neuState (-(constL2 1)) 0 t = ![Complex.I,-Complex.I] := by
  have hd := actual_neumann_label_hasFDerivAt (-(constL2 1)) 0
  refine ⟨by simpa [nu] using dirichlet_real_constant_labels_probe38.1,hd,?_,?_⟩
  · rw [hd.fderiv,neuState_real_energy_gradient]
    simp only [neg_neg,ContinuousLinearMap.neg_apply]
    have hv := probe_constant_dirichlet_gradient.2.2
    rw [(actual_dirichlet_label_hasFDerivAt (constL2 1) 0).fderiv] at hv
    rw [hv]
  · intro t
    ext i
    fin_cases i <;> simp [neuState_gauge,gaugeSign38,probe_constant_dirichlet_state]

end
end NlsGge.GK38.GradEigen38
