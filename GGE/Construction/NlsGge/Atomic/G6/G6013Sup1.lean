import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.X.X004
import NlsGge.Atomic.G5.G5012Sup4

                                                                                                                     
                                                                                                                
                                                                                                   
                                                                                                                       
                                                               
                                                                                                                             
                                                                                                                           
                                                                                                                               
                                                                                                                          
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem physicalBirkhoff_eq_cartesian (u : PhysicalL2) (n : ℤ) :
  physicalBirkhoff u n =
    (cartesianX n (realSlice u) - Complex.I * cartesianY n (realSlice u)) /
      (Real.sqrt 2 : ℂ) :=
  (NlsGge.Atomic.X004.samePhi_cartesian_normalization u n).2.2.1

theorem physicalBirkhoff_re_eq_realX (u : PhysicalL2) (n : ℤ) :
  (physicalBirkhoff u n).re = realX n u / Real.sqrt 2 := by
  have hY := (NlsGge.Atomic.X004.samePhi_cartesian_normalization u n).2.1
  rw [physicalBirkhoff_eq_cartesian, Complex.div_ofReal_re, realX]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, hY]
  ring

theorem physicalBirkhoff_im_eq_realY (u : PhysicalL2) (n : ℤ) :
  (physicalBirkhoff u n).im = -realY n u / Real.sqrt 2 := by
  have hX := (NlsGge.Atomic.X004.samePhi_cartesian_normalization u n).1
  rw [physicalBirkhoff_eq_cartesian, Complex.div_ofReal_im, realY]
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, hX]
  ring

namespace G6013Aux

theorem cart_norm_sq (x : CartesianReal) :
    ‖x‖ ^ 2 = ∑' n : ℤ, x (true, n) ^ 2 + ∑' n : ℤ, x (false, n) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  have hs : Summable (fun j : Bool × ℤ => x j ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using g5012_cart_sq_summable x
  have hb : ∀ b : Bool, Summable (fun n : ℤ => x (b, n) ^ 2) := fun b => by
    simpa [Real.norm_eq_abs, sq_abs] using g5012_slice_sq_summable x b
  rw [h, hs.tsum_prod' hb, tsum_fintype, Fintype.sum_bool]

theorem l2z_norm_sq (z : Lib.L2Z) : ‖z‖ ^ 2 = ∑' n : ℤ, ‖z n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) z
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem l2z_sq_summable (z : Lib.L2Z) : Summable (fun n : ℤ => ‖z n‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp z.2
  simpa using h

theorem re_sq_le (w : ℂ) : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg w.im]

theorem im_sq_le (w : ℂ) : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg w.re]

/-- The coordinate sequence of the physical-to-Cartesian conversion. -/
theorem seq_memℓp (z : Lib.L2Z) :
    Memℓp (fun j : Bool × ℤ =>
      if j.1 then Real.sqrt 2 * (z j.2).re else -Real.sqrt 2 * (z j.2).im) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hs := (l2z_sq_summable z).mul_left 2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2 ⟨fun b => ?_, Summable.of_finite⟩
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hs
  cases b
  · show (-Real.sqrt 2 * (z n).im) ^ 2 ≤ 2 * ‖z n‖ ^ 2
    rw [mul_pow, neg_sq, h2]
    nlinarith [im_sq_le (z n)]
  · show (Real.sqrt 2 * (z n).re) ^ 2 ≤ 2 * ‖z n‖ ^ 2
    rw [mul_pow, h2]
    nlinarith [re_sq_le (z n)]

theorem seq_norm_sq (z : Lib.L2Z) :
    ‖(⟨_, seq_memℓp z⟩ : CartesianReal)‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
  rw [cart_norm_sq, l2z_norm_sq]
  show ∑' n : ℤ, (Real.sqrt 2 * (z n).re) ^ 2 + ∑' n : ℤ, (-Real.sqrt 2 * (z n).im) ^ 2 =
    2 * ∑' n : ℤ, ‖z n‖ ^ 2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hre : Summable (fun n : ℤ => (z n).re ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => re_sq_le (z n)) (l2z_sq_summable z)
  have him : Summable (fun n : ℤ => (z n).im ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => im_sq_le (z n)) (l2z_sq_summable z)
  have e1 : (fun n : ℤ => (Real.sqrt 2 * (z n).re) ^ 2) = fun n => 2 * (z n).re ^ 2 := by
    funext n
    rw [mul_pow, h2]
  have e2 : (fun n : ℤ => (-Real.sqrt 2 * (z n).im) ^ 2) = fun n => 2 * (z n).im ^ 2 := by
    funext n
    rw [mul_pow, neg_sq, h2]
  have e3 : (fun n : ℤ => ‖z n‖ ^ 2) = fun n => (z n).re ^ 2 + (z n).im ^ 2 := by
    funext n
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [e1, e2, e3, tsum_mul_left, tsum_mul_left, hre.tsum_add him]
  ring

/-- The bounded real-linear conversion z |-> (sqrt2 Re z_n, -sqrt2 Im z_n), stated existentially (no new definition). -/
theorem seqCLM_exists : ∃ M : Lib.L2Z →L[ℝ] CartesianReal, ∀ (z : Lib.L2Z) (n : ℤ),
    M z (true, n) = Real.sqrt 2 * (z n).re ∧ M z (false, n) = -Real.sqrt 2 * (z n).im := by
  let Mlin : Lib.L2Z →ₗ[ℝ] CartesianReal :=
    { toFun := fun z => ⟨_, seq_memℓp z⟩
      map_add' := fun z w => by
        ext ⟨b, n⟩
        cases b
        · show -Real.sqrt 2 * ((z + w) n).im = -Real.sqrt 2 * (z n).im + -Real.sqrt 2 * (w n).im
          rw [lp.coeFn_add, Pi.add_apply, Complex.add_im]
          ring
        · show Real.sqrt 2 * ((z + w) n).re = Real.sqrt 2 * (z n).re + Real.sqrt 2 * (w n).re
          rw [lp.coeFn_add, Pi.add_apply, Complex.add_re]
          ring
      map_smul' := fun c z => by
        ext ⟨b, n⟩
        cases b
        · show -Real.sqrt 2 * ((c • z) n).im = c * (-Real.sqrt 2 * (z n).im)
          rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, Complex.im_ofReal_mul]
          ring
        · show Real.sqrt 2 * ((c • z) n).re = c * (Real.sqrt 2 * (z n).re)
          rw [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, Complex.re_ofReal_mul]
          ring }
  refine ⟨LinearMap.mkContinuous Mlin 2 (fun z => ?_), fun z n => ⟨rfl, rfl⟩⟩
  have h : ‖Mlin z‖ ^ 2 = 2 * ‖z‖ ^ 2 := seq_norm_sq z
  nlinarith [norm_nonneg (Mlin z), norm_nonneg z]

end G6013Aux

theorem exists_physicalCartesianEquiv :
  ∃ e : Lib.L2Z ≃L[ℝ] CartesianReal,
    (∀ (z : Lib.L2Z) (n : ℤ),
      e z (true, n) = Real.sqrt 2 * (z n).re ∧
      e z (false, n) = -Real.sqrt 2 * (z n).im) ∧
    ∀ u : PhysicalL2, realBirkhoffCartesian u = e (physicalBirkhoff u) := by
  obtain ⟨L, hL⟩ := g5012_L_exists
  obtain ⟨M, hM⟩ := G6013Aux.seqCLM_exists
  have h1 : Function.LeftInverse L M := fun z => by
    ext n
    rw [hL, (hM z n).1, (hM z n).2]
    conv_rhs => rw [← Complex.re_add_im (z n)]
    have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
    push_cast
    field_simp
    ring
  have h2 : Function.RightInverse L M := fun x => by
    have hs2r : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    ext ⟨b, n⟩
    cases b
    · rw [(hM (L x) n).2, hL]
      simp only [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re]
      field_simp
      ring
    · rw [(hM (L x) n).1, hL]
      simp only [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]
      field_simp
      ring
  refine ⟨ContinuousLinearEquiv.equivOfInverse M L h1 h2, fun z n => hM z n, fun u => ?_⟩
  have hs2r : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  ext ⟨b, n⟩
  rw [ContinuousLinearEquiv.equivOfInverse_apply]
  cases b
  · rw [realBirkhoffCartesian_false, (hM _ n).2, physicalBirkhoff_im_eq_realY]
    field_simp
  · rw [realBirkhoffCartesian_true, (hM _ n).1, physicalBirkhoff_re_eq_realX]
    field_simp
end
end NlsGge.GKDefinitionDesign
