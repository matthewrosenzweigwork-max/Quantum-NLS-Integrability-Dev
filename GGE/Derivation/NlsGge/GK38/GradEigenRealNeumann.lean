import NlsGge.GK38.GradEigenRealDirichlet
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem neuState_gauge (u : PhysicalL2) (n : ℤ) (t : Time) (i : Fin 2) :
    neuState u n t i = (Complex.I * gaugeSign38 i) * dirState (-u) n t i := by
  unfold neuState dirState nu
  rw [state_eq_mulVec,state_eq_mulVec,realSlice_neg,fundPair_neg_gauge38]
  fin_cases i <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,gaugeJ38_conj_apply,gaugeSign38] <;> ring

theorem neuState_square (u : PhysicalL2) (n : ℤ) :
    square (neuState u n) = (-1 : ℂ) • square (dirState (-u) n) := by
  ext t i
  fin_cases i <;> simp [square,starProd38,neuState_gauge,gaugeSign38] <;> ring_nf <;>
    simp [Complex.I_sq]

theorem neuState_energy (u : PhysicalL2) (n : ℤ) :
    energy (neuState u n) = energy (dirState (-u) n) := by
  unfold energy
  apply intervalIntegral.integral_congr
  intro s hs
  have hm : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  dsimp only
  rw [pairKernelExt38_of_mem _ hm,pairKernelExt38_of_mem _ hm]
  simp [neuState_gauge,gaugeSign38,norm_mul]

theorem neuState_real_energy_gradient (u : PhysicalL2) (n : ℤ) :
    realEnergyGradient (neuState u n) = -realEnergyGradient (dirState (-u) n) := by
  unfold realEnergyGradient
  rw [neuState_energy,neuState_square,integralPairCLM38_kernelSmul]
  apply ContinuousLinearMap.ext
  intro h
  simp [ContinuousLinearMap.comp_apply]

theorem actual_neumann_label_hasFDerivAt (u : PhysicalL2) (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => nu v n) (realEnergyGradient (neuState u n)) u := by
  have h := (actual_dirichlet_label_hasFDerivAt (-u) n).comp u
    (hasFDerivAt_id u).neg
  change HasFDerivAt (fun v : PhysicalL2 => nu v n)
    ((realEnergyGradient (dirState (-u) n)).comp (-ContinuousLinearMap.id ℝ PhysicalL2)) u at h
  have he : ((realEnergyGradient (dirState (-u) n)).comp (-ContinuousLinearMap.id ℝ PhysicalL2)) =
      realEnergyGradient (neuState u n) := by
    rw [neuState_real_energy_gradient]
    ext v
    simp
  rw [he] at h
  exact h

def RealNeumannGradientTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    realSymmetric (neuState u n) ∧ 0 < energy (neuState u n) ∧
    HasFDerivAt (fun v : PhysicalL2 => nu v n) (realEnergyGradient (neuState u n)) u

theorem real_neumann_gradient_target : RealNeumannGradientTarget := by
  intro u n
  exact ⟨neuState_real_symmetry u n,neuState_energy_positive u n,
    actual_neumann_label_hasFDerivAt u n⟩

end
end NlsGge.GK38.GradEigen38
