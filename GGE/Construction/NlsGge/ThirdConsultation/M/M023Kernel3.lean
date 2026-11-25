import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M023Bridge
import NlsGge.ThirdConsultation.M.M023Kernel1
import NlsGge.ThirdConsultation.M.M023Kernel2
import NlsGge.ThirdConsultation.M.M021Real

   
                                                                        

                                                                                                                         
                                                                                                                            
                                                                                              
  

set_option autoImplicit false

open scoped ENNReal BigOperators BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode

theorem conv_summable (A z : ℤ → ℂ) (k : ℤ) (hA : Summable fun m => ‖A m‖ ^ 2)
    (hz : Summable fun l => ‖z l‖ ^ 2) : Summable fun l => A (k - l) * z l := by
  have hA' : Summable fun l : ℤ => ‖A (k - l)‖ ^ 2 :=
    hA.comp_injective (i := fun l : ℤ => k - l) (fun l l' h => by simpa using h)
  have h := (NlsGge.ThirdConsultation.MTwoMode.Real21.cs_sq (fun l => ‖A (k - l)‖) (fun l => ‖z l‖)
    (fun l => norm_nonneg _) (fun l => norm_nonneg _) hA' hz).1
  exact Summable.of_norm_bounded h (fun l => (norm_mul _ _).le)

theorem inner_summable (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (n : ℤ) (a : PotentialCode w)
    (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    Summable fun l : ℤ => potentialRaw w a j.1 (j.2 - l) *
      (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) := by
  have hWge : ∀ l : ℤ, 1 ≤ shiftWeight w n (!j.1) l := by
    intro l
    unfold shiftWeight
    split_ifs <;> exact hw1 _
  have hA : Summable fun m : ℤ => ‖potentialRaw w a j.1 m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_) (pr_facts w hw1 a j.1).1
    have h1 : (1 : ℝ) ≤ w m ^ 2 := by nlinarith [hw1 m]
    nlinarith [sq_nonneg ‖potentialRaw w a j.1 m‖]
  have hy : ∀ l : ℤ, ‖x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ)‖ ≤ ‖x (!j.1, l)‖ := by
    intro l
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one (hWge l))]
    exact div_le_self (norm_nonneg _) (hWge l)
  have hz : Summable fun l : ℤ => ‖Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
      ((lp_bool_summable x (!j.1)).mul_left (‖g‖ ^ 2))
    rw [norm_mul, mul_pow]
    have h1 : ‖Dm n g j.1 l‖ ^ 2 ≤ ‖g‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((Dm_facts n g j.1).1 l) 2
    have h2 : ‖x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ)‖ ^ 2 ≤ ‖x (!j.1, l)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hy l) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  exact conv_summable (potentialRaw w a j.1) _ j.2 hA hz

/-! ### Linearity of `kernFun` -/

theorem kernFun_add_x (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (n : ℤ) (a : PotentialCode w)
    (g : ℤ →ᵇ ℂ) (x y : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n a g (x + y) j = kernFun w n a g x j + kernFun w n a g y j := by
  unfold kernFun
  rw [← mul_add, ← (inner_summable w hw1 n a g x j).tsum_add (inner_summable w hw1 n a g y j)]
  congr 1
  refine tsum_congr fun l => ?_
  have e : (x + y) (!j.1, l) = x (!j.1, l) + y (!j.1, l) := rfl
  rw [e, add_div, mul_add, mul_add]

theorem kernFun_smul_x (w : ℤ → ℝ) (n : ℤ) (a : PotentialCode w)
    (g : ℤ →ᵇ ℂ) (c : ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n a g (c • x) j = c * kernFun w n a g x j := by
  unfold kernFun
  have h : ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
        (Dm n g j.1 l * ((c • x) (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) =
      c * ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
        (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    have e : (c • x) (!j.1, l) = c * x (!j.1, l) := rfl
    rw [e]
    ring
  rw [h]
  ring

theorem potentialRaw_add (w : ℤ → ℝ) (a a' : PotentialCode w) (b : Bool) (m : ℤ) :
    potentialRaw w (a + a') b m = potentialRaw w a b m + potentialRaw w a' b m := by
  unfold potentialRaw
  split_ifs
  · have e : (a + a') (b, m / 2) = a (b, m / 2) + a' (b, m / 2) := rfl
    rw [e, add_div]
  · simp

theorem potentialRaw_smul (w : ℤ → ℝ) (c : ℂ) (a : PotentialCode w) (b : Bool) (m : ℤ) :
    potentialRaw w (c • a) b m = c * potentialRaw w a b m := by
  unfold potentialRaw
  split_ifs
  · have e : (c • a) (b, m / 2) = c * a (b, m / 2) := rfl
    rw [e, mul_div_assoc]
  · simp

theorem kernFun_add_a (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (n : ℤ) (a a' : PotentialCode w)
    (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n (a + a') g x j = kernFun w n a g x j + kernFun w n a' g x j := by
  unfold kernFun
  rw [← mul_add, ← (inner_summable w hw1 n a g x j).tsum_add (inner_summable w hw1 n a' g x j)]
  congr 1
  refine tsum_congr fun l => ?_
  rw [potentialRaw_add, add_mul]

theorem kernFun_smul_a (w : ℤ → ℝ) (n : ℤ) (c : ℂ) (a : PotentialCode w)
    (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n (c • a) g x j = c * kernFun w n a g x j := by
  unfold kernFun
  have h : ∑' l : ℤ, potentialRaw w (c • a) j.1 (j.2 - l) *
        (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) =
      c * ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
        (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [potentialRaw_smul]
    ring
  rw [h]
  ring

theorem Dm_add (n : ℤ) (g g' : ℤ →ᵇ ℂ) (b : Bool) (l : ℤ) :
    Dm n (g + g') b l = Dm n g b l + Dm n g' b l := by
  unfold Dm
  split_ifs <;> simp [mul_add]

theorem Dm_smul (n : ℤ) (c : ℂ) (g : ℤ →ᵇ ℂ) (b : Bool) (l : ℤ) :
    Dm n (c • g) b l = c * Dm n g b l := by
  unfold Dm
  split_ifs <;> simp <;> ring

theorem kernFun_add_g (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (n : ℤ) (a : PotentialCode w)
    (g g' : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n a (g + g') x j = kernFun w n a g x j + kernFun w n a g' x j := by
  unfold kernFun
  rw [← mul_add, ← (inner_summable w hw1 n a g x j).tsum_add (inner_summable w hw1 n a g' x j)]
  congr 1
  refine tsum_congr fun l => ?_
  rw [Dm_add]
  ring

theorem kernFun_smul_g (w : ℤ → ℝ) (n : ℤ) (a : PotentialCode w) (c : ℂ)
    (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernFun w n a (c • g) x j = c * kernFun w n a g x j := by
  unfold kernFun
  have h : ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
        (Dm n (c • g) j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) =
      c * ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
        (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [Dm_smul]
    ring
  rw [h]
  ring

/-! ### The bilinear continuous operator -/

variable (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
  (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (n : ℤ)

/-- `kernFun` as a linear map of the source code. -/
def kernLin (a : PotentialCode w) (g : ℤ →ᵇ ℂ) : SourceCode w n →ₗ[ℂ] SourceCode w n where
  toFun x := ⟨kernFun w n a g x, kern_mem w hw hwmul n a g x⟩
  map_add' x y := by
    apply Subtype.ext
    funext j
    exact kernFun_add_x w (w_ge_one_of_oneDerivative w hw) n a g x y j
  map_smul' c x := by
    apply Subtype.ext
    funext j
    exact kernFun_smul_x w n a g c x j

def kernCLM (a : PotentialCode w) (g : ℤ →ᵇ ℂ) : SourceCode w n →L[ℂ] SourceCode w n :=
  LinearMap.mkContinuous (kernLin w hw hwmul n a g) (2 * ‖g‖ * w (2 * n) * ‖a‖)
    (fun x => kern_norm_le w hw hwmul n a g x)

theorem kernCLM_apply (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    kernCLM w hw hwmul n a g x j = kernFun w n a g x j := rfl

theorem kernCLM_add_a (a a' : PotentialCode w) (g : ℤ →ᵇ ℂ) :
    kernCLM w hw hwmul n (a + a') g = kernCLM w hw hwmul n a g + kernCLM w hw hwmul n a' g := by
  ext x j
  simp only [ContinuousLinearMap.add_apply]
  exact kernFun_add_a w (w_ge_one_of_oneDerivative w hw) n a a' g x j

theorem kernCLM_smul_a (c : ℂ) (a : PotentialCode w) (g : ℤ →ᵇ ℂ) :
    kernCLM w hw hwmul n (c • a) g = c • kernCLM w hw hwmul n a g := by
  ext x j
  simp only [ContinuousLinearMap.smul_apply]
  exact kernFun_smul_a w n c a g x j

theorem kernCLM_add_g (a : PotentialCode w) (g g' : ℤ →ᵇ ℂ) :
    kernCLM w hw hwmul n a (g + g') = kernCLM w hw hwmul n a g + kernCLM w hw hwmul n a g' := by
  ext x j
  simp only [ContinuousLinearMap.add_apply]
  exact kernFun_add_g w (w_ge_one_of_oneDerivative w hw) n a g g' x j

theorem kernCLM_smul_g (c : ℂ) (a : PotentialCode w) (g : ℤ →ᵇ ℂ) :
    kernCLM w hw hwmul n a (c • g) = c • kernCLM w hw hwmul n a g := by
  ext x j
  simp only [ContinuousLinearMap.smul_apply]
  exact kernFun_smul_g w n a c g x j

def kernBilin : PotentialCode w →ₗ[ℂ] (ℤ →ᵇ ℂ) →ₗ[ℂ] (SourceCode w n →L[ℂ] SourceCode w n) :=
  LinearMap.mk₂ ℂ (fun a g => kernCLM w hw hwmul n a g)
    (kernCLM_add_a w hw hwmul n) (kernCLM_smul_a w hw hwmul n)
    (kernCLM_add_g w hw hwmul n) (kernCLM_smul_g w hw hwmul n)

/-- The bilinear continuous kernel operator. -/
def Bop : PotentialCode w →L[ℂ] (ℤ →ᵇ ℂ) →L[ℂ] (SourceCode w n →L[ℂ] SourceCode w n) :=
  LinearMap.mkContinuous₂ (kernBilin w hw hwmul n) (2 * w (2 * n)) (fun a g => by
    have hw1 := w_ge_one_of_oneDerivative w hw
    have hw0 : 0 ≤ w (2 * n) := le_trans zero_le_one (hw1 _)
    have : ‖kernBilin w hw hwmul n a g‖ ≤ 2 * w (2 * n) * ‖a‖ * ‖g‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro x
      have h := kern_norm_le w hw hwmul n a g x
      calc ‖kernCLM w hw hwmul n a g x‖ ≤ 2 * ‖g‖ * w (2 * n) * ‖a‖ * ‖x‖ := h
        _ = 2 * w (2 * n) * ‖a‖ * ‖g‖ * ‖x‖ := by ring
    exact this)

theorem Bop_apply (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (j : Bool × ℤ) :
    Bop w hw hwmul n a g x j = kernFun w n a g x j := rfl

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
