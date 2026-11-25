import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M023Bridge
import NlsGge.ThirdConsultation.M.M023Kernel1
import NlsGge.Atomic.DM.DM046

   
                                                                         

                                                                                                  
                                                                                          
                                                                                                              
                                                                                          
  

set_option autoImplicit false

open scoped ENNReal BigOperators BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode

theorem w_neg_of_oneDerivative (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) : w (-k) = w k := by
  obtain ⟨v, _, hev, _, hwv⟩ := hw
  rw [hwv, hwv, hev]
  unfold NlsGge.Atomic.M.M054.indexWeight
  push_cast
  rw [abs_neg]

theorem comp_step (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (s : ℤ) (c0 : ℝ)
    (Win : ℤ → ℝ) (hWin1 : ∀ l, 1 ≤ Win l) (hWin : ∀ l, w (l + s) ≤ c0 * Win l)
    (A D z : ℤ → ℂ) (G : ℝ) (hG0 : 0 ≤ G)
    (hD1 : ∀ l, ‖D l‖ ≤ G) (hDs : Summable fun l => ‖D l‖ ^ 2)
    (hD4 : ∑' l, ‖D l‖ ^ 2 ≤ 4 * G ^ 2)
    (hA : Summable fun m => w m ^ 2 * ‖A m‖ ^ 2) (hz : Summable fun l => ‖z l‖ ^ 2) :
    ∑' k : ℤ, ENNReal.ofReal
        (w (k + s) ^ 2 * ‖∑' l, A (k - l) * (D l * (z l / (Win l : ℂ)))‖ ^ 2) ≤
      ENNReal.ofReal (4 * G ^ 2 * c0 ^ 2 * (∑' m, w m ^ 2 * ‖A m‖ ^ 2) * ∑' l, ‖z l‖ ^ 2) := by
  have hWpos : ∀ l, 0 < Win l := fun l => lt_of_lt_of_le one_pos (hWin1 l)
  have hc0 : 0 ≤ c0 := by
    by_contra h
    push_neg at h
    have h1 := hWin 0
    have h2 := hw1 (0 + s)
    have h3 := hWpos 0
    nlinarith
  have hy : ∀ l, w (l + s) ^ 2 * ‖z l / (Win l : ℂ)‖ ^ 2 ≤ c0 ^ 2 * ‖z l‖ ^ 2 := by
    intro l
    have hn : ‖z l / (Win l : ℂ)‖ = ‖z l‖ / Win l := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hWpos l)]
    have h1 : w (l + s) * ‖z l / (Win l : ℂ)‖ ≤ c0 * ‖z l‖ := by
      rw [hn, ← mul_div_assoc, div_le_iff₀ (hWpos l)]
      nlinarith [norm_nonneg (z l), hWin l]
    calc w (l + s) ^ 2 * ‖z l / (Win l : ℂ)‖ ^ 2 = (w (l + s) * ‖z l / (Win l : ℂ)‖) ^ 2 := by ring
      _ ≤ (c0 * ‖z l‖) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by linarith [hw1 (l + s)]) (norm_nonneg _)) h1 2
      _ = c0 ^ 2 * ‖z l‖ ^ 2 := by ring
  have hEx : ∑' l, ENNReal.ofReal (w (l + s) ^ 2 * ‖z l / (Win l : ℂ)‖ ^ 2) ≤
      ENNReal.ofReal (c0 ^ 2 * ∑' l, ‖z l‖ ^ 2) := by
    calc _ ≤ ∑' l, ENNReal.ofReal (c0 ^ 2 * ‖z l‖ ^ 2) :=
          ENNReal.tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal (hy l)
      _ = ENNReal.ofReal (∑' l, c0 ^ 2 * ‖z l‖ ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) (hz.mul_left _)).symm
      _ = _ := by rw [tsum_mul_left]
  have hPa : ∑' l, ENNReal.ofReal (w l ^ 2 * ‖A l‖ ^ 2) =
      ENNReal.ofReal (∑' m, w m ^ 2 * ‖A m‖ ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hA).symm
  have hZ0 : 0 ≤ ∑' l, ‖z l‖ ^ 2 := tsum_nonneg fun l => sq_nonneg _
  have hP0 : 0 ≤ ∑' m, w m ^ 2 * ‖A m‖ ^ 2 := tsum_nonneg fun m => by positivity
  have h := comp_gen w hw1 hwmul s A (fun l => z l / (Win l : ℂ)) D G hG0 hD1 hDs hD4
    (by rw [hPa]; exact ENNReal.ofReal_ne_top) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEx)
  calc _ ≤ _ := h
    _ ≤ ENNReal.ofReal (G ^ 2) * (4 * ENNReal.ofReal (∑' m, w m ^ 2 * ‖A m‖ ^ 2) *
          ENNReal.ofReal (c0 ^ 2 * ∑' l, ‖z l‖ ^ 2)) := by
        rw [hPa]
        gcongr
    _ = ENNReal.ofReal (4 * G ^ 2 * c0 ^ 2 * (∑' m, w m ^ 2 * ‖A m‖ ^ 2) * ∑' l, ‖z l‖ ^ 2) := by
        have e : 4 * G ^ 2 * c0 ^ 2 * (∑' m, w m ^ 2 * ‖A m‖ ^ 2) * ∑' l, ‖z l‖ ^ 2 =
            G ^ 2 * (4 * (∑' m, w m ^ 2 * ‖A m‖ ^ 2) * (c0 ^ 2 * ∑' l, ‖z l‖ ^ 2)) := by ring
        rw [e, ENNReal.ofReal_mul (sq_nonneg G),
          ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 4 * ∑' m, w m ^ 2 * ‖A m‖ ^ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_mul (sq_nonneg c0),
          ENNReal.ofReal_ofNat]

/-! ### Potential coefficients -/

theorem potentialRaw_odd (w : ℤ → ℝ) (a : PotentialCode w) (b : Bool) (m : ℤ) (h : ¬ Even m) :
    potentialRaw w a b m = 0 := by
  unfold potentialRaw
  simp [h]

theorem potentialRaw_two_mul (w : ℤ → ℝ) (a : PotentialCode w) (b : Bool) (j : ℤ) :
    potentialRaw w a b (2 * j) = a (b, j) / (w (2 * j) : ℂ) := by
  unfold potentialRaw
  have h : Even (2 * j) := even_two_mul j
  have h2 : (2 * j) / 2 = j := by omega
  rw [if_pos h, h2]

theorem pr_facts (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (a : PotentialCode w) (b : Bool) :
    Summable (fun m : ℤ => w m ^ 2 * ‖potentialRaw w a b m‖ ^ 2) ∧
      ∑' m : ℤ, w m ^ 2 * ‖potentialRaw w a b m‖ ^ 2 = ∑' j : ℤ, ‖a (b, j)‖ ^ 2 := by
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun x y h => by simpa using h
  have hf2 : ∀ j : ℤ, w (2 * j) ^ 2 * ‖potentialRaw w a b (2 * j)‖ ^ 2 = ‖a (b, j)‖ ^ 2 := by
    intro j
    rw [potentialRaw_two_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one (hw1 _))]
    have : w (2 * j) ≠ 0 := (lt_of_lt_of_le one_pos (hw1 _)).ne'
    field_simp
  have hsa : Summable fun j : ℤ => ‖a (b, j)‖ ^ 2 :=
    (lp_hasSum_sq a).summable.comp_injective (i := fun j : ℤ => (b, j))
      (fun j j' h => by simpa using h)
  have hzero : ∀ m : ℤ, m ∉ Set.range (fun j : ℤ => 2 * j) →
      w m ^ 2 * ‖potentialRaw w a b m‖ ^ 2 = 0 := by
    intro m hm
    have : ¬ Even m := by
      rintro ⟨r, hr⟩
      exact hm ⟨r, by simp only; omega⟩
    rw [potentialRaw_odd w a b m this]
    simp
  have hsupp : Function.support (fun m : ℤ => w m ^ 2 * ‖potentialRaw w a b m‖ ^ 2) ⊆
      Set.range (fun j : ℤ => 2 * j) := by
    intro m hm
    by_contra hmr
    exact hm (hzero m hmr)
  refine ⟨?_, ?_⟩
  · refine (hinj.summable_iff hzero).1 ?_
    exact hsa.congr fun j => (hf2 j).symm
  · calc ∑' m : ℤ, w m ^ 2 * ‖potentialRaw w a b m‖ ^ 2
        = ∑' j : ℤ, w (2 * j) ^ 2 * ‖potentialRaw w a b (2 * j)‖ ^ 2 :=
          (hinj.tsum_eq hsupp).symm
      _ = ∑' j : ℤ, ‖a (b, j)‖ ^ 2 := tsum_congr hf2

theorem lp_bool_summable (z : lp (fun _ : Bool × ℤ => ℂ) 2) (b : Bool) :
    Summable fun j : ℤ => ‖z (b, j)‖ ^ 2 :=
  (lp_hasSum_sq z).summable.comp_injective (i := fun j : ℤ => (b, j))
    (fun j j' h => by simpa using h)

theorem lp_bool_split (z : lp (fun _ : Bool × ℤ => ℂ) 2) :
    ‖z‖ ^ 2 = ∑' j : ℤ, ‖z (true, j)‖ ^ 2 + ∑' j : ℤ, ‖z (false, j)‖ ^ 2 := by
  have h1 : ENNReal.ofReal (‖z‖ ^ 2) =
      ENNReal.ofReal (∑' j : ℤ, ‖z (true, j)‖ ^ 2 + ∑' j : ℤ, ‖z (false, j)‖ ^ 2) := by
    rw [← lp_energy z, tsum_bool_prod,
      ENNReal.ofReal_add (tsum_nonneg fun j => sq_nonneg _) (tsum_nonneg fun j => sq_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (lp_bool_summable z true),
      ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (lp_bool_summable z false),
      ← ENNReal.tsum_add]
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (add_nonneg (tsum_nonneg fun j => sq_nonneg _) (tsum_nonneg fun j => sq_nonneg _))).1 h1

/-! ### The kernel function -/

def kernFun (w : ℤ → ℝ) (n : ℤ) (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n)
    (j : Bool × ℤ) : ℂ :=
  (shiftWeight w n j.1 j.2 : ℂ) *
    ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
      (Dm n g j.1 l * (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ)))

theorem comp_b (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (n : ℤ)
    (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) (b : Bool) (s : ℤ)
    (hs : ∀ k : ℤ, shiftWeight w n b k = w (k + s))
    (hWin : ∀ l : ℤ, w (l + s) ≤ w (2 * n) * shiftWeight w n (!b) l) :
    ∑' k : ℤ, ENNReal.ofReal (‖kernFun w n a g x (b, k)‖ ^ 2) ≤
      ENNReal.ofReal (4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * (∑' j : ℤ, ‖a (b, j)‖ ^ 2) *
        ∑' l : ℤ, ‖x (!b, l)‖ ^ 2) := by
  have hWin1 : ∀ l : ℤ, 1 ≤ shiftWeight w n (!b) l := by
    intro l
    unfold shiftWeight
    split_ifs <;> exact hw1 _
  obtain ⟨hD1, hDs, hD4⟩ := Dm_facts n g b
  have hz : Summable fun l : ℤ => ‖x (!b, l)‖ ^ 2 := lp_bool_summable x (!b)
  obtain ⟨hA, hAeq⟩ := pr_facts w hw1 a b
  have key := comp_step w hw1 hwmul s (w (2 * n)) (shiftWeight w n (!b)) hWin1 hWin
    (potentialRaw w a b) (Dm n g b) (fun l => x (!b, l)) ‖g‖ (norm_nonneg _) hD1 hDs hD4 hA hz
  rw [hAeq] at key
  have hterm : ∀ k : ℤ, ‖kernFun w n a g x (b, k)‖ ^ 2 =
      w (k + s) ^ 2 * ‖∑' l : ℤ, potentialRaw w a b (k - l) *
        (Dm n g b l * (x (!b, l) / (shiftWeight w n (!b) l : ℂ)))‖ ^ 2 := by
    intro k
    unfold kernFun
    simp only
    rw [norm_real_cast_sq, hs k]
  simp_rw [hterm]
  exact key

theorem kern_total (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (n : ℤ)
    (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) :
    ∑' p : Bool × ℤ, ENNReal.ofReal (‖kernFun w n a g x p‖ ^ 2) ≤
      ENNReal.ofReal (4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * ‖a‖ ^ 2 * ‖x‖ ^ 2) := by
  have hw1 := w_ge_one_of_oneDerivative w hw
  have hneg := w_neg_of_oneDerivative w hw
  have hT := comp_b w hw1 hwmul n a g x true (-n)
    (fun k => by simp [shiftWeight, sub_eq_add_neg])
    (fun l => by
      have h := hwmul (l + n) (-(2 * n))
      rw [hneg (2 * n), show l + n + -(2 * n) = l + -n by ring] at h
      simpa [shiftWeight, mul_comm] using h)
  have hF := comp_b w hw1 hwmul n a g x false n
    (fun k => by simp [shiftWeight])
    (fun l => by
      have h := hwmul (l - n) (2 * n)
      rw [show l - n + 2 * n = l + n by ring] at h
      simpa [shiftWeight, mul_comm] using h)
  rw [tsum_bool_prod, ENNReal.tsum_add]
  have ha := lp_bool_split a
  have hx := lp_bool_split x
  have hPt : 0 ≤ ∑' j : ℤ, ‖a (true, j)‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hPf : 0 ≤ ∑' j : ℤ, ‖a (false, j)‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hEt : 0 ≤ ∑' j : ℤ, ‖x (true, j)‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hEf : 0 ≤ ∑' j : ℤ, ‖x (false, j)‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hK : 0 ≤ 4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 := by positivity
  simp only [Bool.not_true, Bool.not_false] at hT hF
  calc _ ≤ ENNReal.ofReal (4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * (∑' j : ℤ, ‖a (true, j)‖ ^ 2) *
        ∑' l : ℤ, ‖x (false, l)‖ ^ 2) +
      ENNReal.ofReal (4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * (∑' j : ℤ, ‖a (false, j)‖ ^ 2) *
        ∑' l : ℤ, ‖x (true, l)‖ ^ 2) := add_le_add hT hF
    _ = ENNReal.ofReal (4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * (∑' j : ℤ, ‖a (true, j)‖ ^ 2) *
        ∑' l : ℤ, ‖x (false, l)‖ ^ 2 +
      4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * (∑' j : ℤ, ‖a (false, j)‖ ^ 2) *
        ∑' l : ℤ, ‖x (true, l)‖ ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [ha, hx]
        have e1 : 0 ≤ (∑' j : ℤ, ‖a (true, j)‖ ^ 2) * ∑' l : ℤ, ‖x (true, l)‖ ^ 2 := mul_nonneg hPt hEt
        have e2 : 0 ≤ (∑' j : ℤ, ‖a (false, j)‖ ^ 2) * ∑' l : ℤ, ‖x (false, l)‖ ^ 2 := mul_nonneg hPf hEf
        nlinarith [mul_nonneg hK e1, mul_nonneg hK e2]

theorem kern_mem (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (n : ℤ)
    (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) :
    Memℓp (kernFun w n a g x) 2 :=
  summable_of_energy_ne_top _
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (kern_total w hw hwmul n a g x))

theorem kern_norm_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w) (n : ℤ)
    (a : PotentialCode w) (g : ℤ →ᵇ ℂ) (x : SourceCode w n) :
    ‖(⟨kernFun w n a g x, kern_mem w hw hwmul n a g x⟩ : lp (fun _ : Bool × ℤ => ℂ) 2)‖ ≤
      2 * ‖g‖ * w (2 * n) * ‖a‖ * ‖x‖ := by
  have hw1 := w_ge_one_of_oneDerivative w hw
  have h := kern_total w hw hwmul n a g x
  set kl : lp (fun _ : Bool × ℤ => ℂ) 2 := ⟨kernFun w n a g x, kern_mem w hw hwmul n a g x⟩ with hkl
  have hE : ENNReal.ofReal (‖kl‖ ^ 2) = ∑' p : Bool × ℤ, ENNReal.ofReal (‖kernFun w n a g x p‖ ^ 2) :=
    (lp_energy kl).symm
  have hsq : ‖kl‖ ^ 2 ≤ 4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * ‖a‖ ^ 2 * ‖x‖ ^ 2 := by
    have := hE.le.trans h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  have hR : 4 * ‖g‖ ^ 2 * (w (2 * n)) ^ 2 * ‖a‖ ^ 2 * ‖x‖ ^ 2 =
      (2 * ‖g‖ * w (2 * n) * ‖a‖ * ‖x‖) ^ 2 := by ring
  rw [hR] at hsq
  have hw0 : 0 ≤ w (2 * n) := le_trans zero_le_one (hw1 _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
