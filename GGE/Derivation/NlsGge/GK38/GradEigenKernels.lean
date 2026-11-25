import NlsGge.GK38.GradEigenDefs

/-! K2 continuous kernel integrability and source real denominator.
Private source anchor: GK I.7 Proposition 7.5. All identities refer to
independent interval kernels; they do not define a gradient by differentiation. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

def realSymmetric (w : PairKernelCont38) : Prop :=
  ∀ t : Time, w t 1 = star (w t 0)

theorem continuous_component (w : PairKernelCont38) (i : Fin 2) :
    Continuous (fun s => pairKernelExt38 w s i) :=
  (continuous_apply i).comp (continuous_pairKernelExt38 w)

theorem kernel_integrability (w : PairKernelCont38) :
    IntervalIntegrable (fun s => pairKernelExt38 w s 0 * pairKernelExt38 w s 1) volume 0 1 ∧
    IntervalIntegrable (fun s => ‖pairKernelExt38 w s 0‖ ^ 2 +
      ‖pairKernelExt38 w s 1‖ ^ 2) volume 0 1 ∧
    ∀ h : PotPair, IntervalIntegrable (fun s =>
      pairKernelExt38 (square w) s 0 * potRepFst38 h s +
      pairKernelExt38 (square w) s 1 * potRepSnd38 h s) volume 0 1 := by
  refine ⟨((continuous_component w 0).mul (continuous_component w 1)).intervalIntegrable 0 1,
    (((continuous_component w 0).norm.pow 2).add
      ((continuous_component w 1).norm.pow 2)).intervalIntegrable 0 1, ?_⟩
  intro h
  exact intervalIntegrable_pairKernel38 (square w) t1 h

theorem real_denominator (w : PairKernelCont38) (hw : realSymmetric w) :
    Q w = (energy w : ℂ) := by
  have _hQ := (kernel_integrability w).1
  have _hE := (kernel_integrability w).2.1
  rw [Q, energy, ← intervalIntegral.integral_ofReal,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hm : s ∈ Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hs
  change 2 * (pairKernelExt38 w s 0 * pairKernelExt38 w s 1) =
    ((‖pairKernelExt38 w s 0‖ ^ 2 + ‖pairKernelExt38 w s 1‖ ^ 2 : ℝ) : ℂ)
  rw [pairKernelExt38_of_mem w hm]
  rw [hw ⟨s, hm⟩]
  simp only [Complex.star_def, Complex.norm_conj, Complex.mul_conj',
    Complex.ofReal_add, Complex.ofReal_pow]
  ring

theorem Q_smul (c : ℂ) (w : PairKernelCont38) : Q (c • w) = c ^ 2 * Q w := by
  have _hi := (kernel_integrability w).1
  have he (s : ℝ) : pairKernelExt38 (c • w) s = c • pairKernelExt38 w s := by
    simp [pairKernelExt38, Set.IccExtend]
  unfold Q
  simp only [he, Pi.smul_apply, smul_eq_mul]
  calc 2 * (∫ s in (0 : ℝ)..1,
      (c * pairKernelExt38 w s 0) * (c * pairKernelExt38 w s 1)) =
      2 * (∫ s in (0 : ℝ)..1, c ^ 2 *
        (pairKernelExt38 w s 0 * pairKernelExt38 w s 1)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro s _
          ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

theorem square_smul (c : ℂ) (w : PairKernelCont38) :
    square (c • w) = c ^ 2 • square w := by
  ext t i
  fin_cases i <;> simp [square, starProd38, mul_mul_mul_comm, pow_two]

theorem state_eq_mulVec (φ : PotPair) (z : ℂ) (a : PairVec38) (t : Time) :
    state φ z a t = Matrix.mulVec (fundPair φ z t) a := by
  ext i
  simp only [state, ContinuousMap.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    fundColumn38, ext38_of_mem _ t.2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change a 0 * fundPair φ z t i 0 + a 1 * fundPair φ z t i 1 = _
  ring

theorem state_initial (φ : PotPair) (z : ℂ) (a : PairVec38) : state φ z a t0 = a := by
  rw [state_eq_mulVec]
  change Matrix.mulVec (fundPair φ z ⟨0, le_rfl, zero_le_one⟩) a = a
  rw [fundPair_zero, Matrix.one_mulVec]


theorem energy_pos_of_value (w : PairKernelCont38) (t : Time) (hw : w t ≠ 0) :
    0 < energy w := by
  have _hi := (kernel_integrability w).2.1
  unfold energy
  apply intervalIntegral.integral_pos
    (f := fun s => ‖pairKernelExt38 w s 0‖ ^ 2 + ‖pairKernelExt38 w s 1‖ ^ 2)
    zero_lt_one
    ((((continuous_component w 0).norm.pow 2).add
      ((continuous_component w 1).norm.pow 2)).continuousOn)
    (fun s _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨(t : ℝ), t.2, ?_⟩
  rw [pairKernelExt38_of_mem w t.2]
  change 0 < ‖w t 0‖ ^ 2 + ‖w t 1‖ ^ 2
  by_cases h0 : w t 0 = 0
  · have h1 : w t 1 ≠ 0 := by
      intro h1
      apply hw
      ext i
      fin_cases i <;> assumption
    have hn := norm_pos_iff.mpr h1
    positivity
  · have hn := norm_pos_iff.mpr h0
    positivity

theorem energy_pos_of_initial (w : PairKernelCont38) (hw : w t0 ≠ 0) :
    0 < energy w := energy_pos_of_value w t0 hw

theorem state_energy_positive (φ : PotPair) (z : ℂ) (a : PairVec38) (ha : a ≠ 0) :
    0 < energy (state φ z a) := by
  apply energy_pos_of_initial
  rw [state_initial]
  exact ha

end
end NlsGge.GK38.GradEigen38
