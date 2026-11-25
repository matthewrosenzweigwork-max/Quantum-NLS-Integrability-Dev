import Mathlib
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.GK38.Lib.InterpolationHilbertOp

/- G5-012 SUPPORT4 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5012Sup4.lean.
   Supporting lemma (no new definition): the bounded real-linear map CartesianReal -> L2Z,
   x |-> ((x (true, n) - i x (false, n)) / sqrt 2)_n, stated existentially. Used to write the X-006 physical map Phi as
   this map composed with the real-analytic realBirkhoffCartesian (G4-042) in the G5-012 head. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5012_cart_sq_summable (x : CartesianReal) : Summable (fun j : Bool × ℤ => ‖x j‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp x.2
  simpa using h

theorem g5012_slice_sq_summable (x : CartesianReal) (b : Bool) :
    Summable (fun n : ℤ => ‖x (b, n)‖ ^ 2) :=
  (g5012_cart_sq_summable x).comp_injective (fun _ _ h => (Prod.mk.inj h).2)

theorem g5012_slice_tsum_le (x : CartesianReal) (b : Bool) :
    ∑' n : ℤ, ‖x (b, n)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  exact tsum_comp_le_tsum_of_inj (g5012_cart_sq_summable x) (fun _ => sq_nonneg _)
    (i := fun n : ℤ => (b, n)) (fun _ _ h => (Prod.mk.inj h).2)

theorem g5012_coord_bound (a b : ℝ) :
    ‖(((a : ℝ) : ℂ) - Complex.I * ((b : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ)‖ ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hn : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have h1 : ‖(((a : ℝ) : ℂ) - Complex.I * ((b : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ)‖ ≤ |a| + |b| := by
    rw [norm_div, hn]
    refine le_trans (div_le_self (norm_nonneg _) h2) ?_
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have h0 := norm_nonneg ((((a : ℝ) : ℂ) - Complex.I * ((b : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ))
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hsa : |a| ^ 2 = a ^ 2 := sq_abs a
  have hsb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (|a| - |b|)]

theorem g5012_L_exists : ∃ L : CartesianReal →L[ℝ] Lib.L2Z, ∀ (x : CartesianReal) (n : ℤ),
    L x n = (((x (true, n) : ℝ) : ℂ) - Complex.I * ((x (false, n) : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) := by
  have hmem : ∀ x : CartesianReal, Memℓp (fun n : ℤ =>
      (((x (true, n) : ℝ) : ℂ) - Complex.I * ((x (false, n) : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ)) 2 := by
    intro x
    refine (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => g5012_coord_bound _ _) ?_
    have h1 := g5012_slice_sq_summable x true
    have h2 := g5012_slice_sq_summable x false
    simp only [Real.norm_eq_abs, sq_abs] at h1 h2
    exact (h1.mul_left 2).add (h2.mul_left 2)
  let Lm : CartesianReal →ₗ[ℝ] Lib.L2Z :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_add' := fun x y => by
        ext n
        show (((((x + y) (true, n) : ℝ) : ℂ) - Complex.I * (((x + y) (false, n) : ℝ) : ℂ)) /
            (Real.sqrt 2 : ℂ)) = _
        rw [lp.coeFn_add]
        simp only [Pi.add_apply, Complex.ofReal_add]
        show _ = (((x (true, n) : ℝ) : ℂ) - Complex.I * ((x (false, n) : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) +
          (((y (true, n) : ℝ) : ℂ) - Complex.I * ((y (false, n) : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ)
        ring
      map_smul' := fun c x => by
        ext n
        show (((((c • x) (true, n) : ℝ) : ℂ) - Complex.I * (((c • x) (false, n) : ℝ) : ℂ)) /
            (Real.sqrt 2 : ℂ)) = _
        rw [lp.coeFn_smul]
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply]
        show _ = (c : ℂ) * ((((x (true, n) : ℝ) : ℂ) - Complex.I * ((x (false, n) : ℝ) : ℂ)) /
          (Real.sqrt 2 : ℂ))
        ring }
  have hbound : ∀ x : CartesianReal, ‖Lm x‖ ≤ 2 * ‖x‖ := by
    intro x
    refine lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal) (by positivity) ?_
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs1 := g5012_slice_sq_summable x true
    have hs2 := g5012_slice_sq_summable x false
    have t1 := g5012_slice_tsum_le x true
    have t2 := g5012_slice_tsum_le x false
    simp only [Real.norm_eq_abs, sq_abs] at hs1 hs2 t1 t2
    have hsum : Summable (fun n : ℤ => 2 * x (true, n) ^ 2 + 2 * x (false, n) ^ 2) :=
      (hs1.mul_left 2).add (hs2.mul_left 2)
    calc ∑' n : ℤ, ‖(Lm x : Lib.L2Z) n‖ ^ 2
        ≤ ∑' n : ℤ, (2 * x (true, n) ^ 2 + 2 * x (false, n) ^ 2) :=
          Summable.tsum_le_tsum (fun n => g5012_coord_bound _ _)
            (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => g5012_coord_bound _ _) hsum) hsum
      _ = 2 * ∑' n : ℤ, x (true, n) ^ 2 + 2 * ∑' n : ℤ, x (false, n) ^ 2 := by
          rw [(hs1.mul_left 2).tsum_add (hs2.mul_left 2), tsum_mul_left, tsum_mul_left]
      _ ≤ (2 * ‖x‖) ^ 2 := by nlinarith
  exact ⟨LinearMap.mkContinuous Lm 2 hbound, fun x n => rfl⟩

end
end NlsGge.GKDefinitionDesign
