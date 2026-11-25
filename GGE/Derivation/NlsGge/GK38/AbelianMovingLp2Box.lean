import NlsGge.GK38.AbelianLp2Clipping

/-! Uncompiled moving-order-box compactness from genuine strong endpoint
convergence. The original moving rows have NO assumed common lp2 envelope. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p5Lp2_norm_sq38 {ι : Type*} (t : lp (fun _ : ι => ℝ) 2) :
    ‖t‖^2 = ∑' i, ‖t i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) t

theorem p5Lp2_between_mem38 {ι : Type*} (a b : lp (fun _ : ι => ℝ) 2)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (a i) (b i)) : Memℓp x 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  have hsa := (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hsb := (lp.memℓp b).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs : Summable (fun i => 2*(‖a i‖^2+‖b i‖^2)) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (hsa.add hsb).mul_left 2
  have hxS : Summable (fun i => ‖x i‖^2) := by
    apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro i
    have h := mul_self_le_mul_self (norm_nonneg _) (p5Between_norm_le38 _ _ _ (hx i))
    nlinarith [sq_nonneg (‖a i‖-‖b i‖)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hxS

def p5LpClamp38 {ι : Type*} (a b x : lp (fun _ : ι => ℝ) 2)
    (hab : ∀ i, a i ≤ b i) : lp (fun _ : ι => ℝ) 2 :=
  ⟨fun i => p5Clamp38 (a i) (b i) (x i),p5Lp2_between_mem38 a b _
    (fun i => p5Clamp_mem_Icc38 _ _ _ (hab i))⟩

theorem p5LpClamp_mem38 {ι : Type*} (a b x : lp (fun _ : ι => ℝ) 2)
    (hab : ∀ i, a i ≤ b i) : ∀ i, p5LpClamp38 a b x hab i ∈ Icc (a i) (b i) :=
  fun i => p5Clamp_mem_Icc38 _ _ _ (hab i)

theorem p5LpClamp_error_norm_sq_le38 {ι : Type*}
    (a b a₀ b₀ x : lp (fun _ : ι => ℝ) 2) (h₀ : ∀ i, a₀ i ≤ b₀ i)
    (hx : ∀ i, x i ∈ Icc (a i) (b i)) :
    ‖x-p5LpClamp38 a₀ b₀ x h₀‖^2 ≤ 2*(‖a-a₀‖^2+‖b-b₀‖^2) := by
  have hs (t : lp (fun _ : ι => ℝ) 2) : Summable (fun i => ‖t i‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp t).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  calc
    _ = ∑' i, ‖(x-p5LpClamp38 a₀ b₀ x h₀) i‖^2 := p5Lp2_norm_sq38 _
    _ ≤ ∑' i, 2*(‖(a-a₀) i‖^2+‖(b-b₀) i‖^2) := by
      apply Summable.tsum_le_tsum _ (hs _) (((hs (a-a₀)).add (hs (b-b₀))).mul_left 2)
      intro i
      simpa only [lp.coeFn_sub,Pi.sub_apply,p5LpClamp38,Real.norm_eq_abs,sq_abs] using
        p5Clamp_error_sq_le38 (a i) (b i) (a₀ i) (b₀ i) (x i) (h₀ i) (hx i)
    _ = 2*(‖a-a₀‖^2+‖b-b₀‖^2) := by
      rw [tsum_mul_left,(hs (a-a₀)).tsum_add (hs (b-b₀)),
        ← p5Lp2_norm_sq38 (a-a₀),← p5Lp2_norm_sq38 (b-b₀)]

theorem p5MovingLp2OrderBox_subseq38 (ι : Type*)
    (a b : ℕ → lp (fun _ : ι => ℝ) 2) (a₀ b₀ : lp (fun _ : ι => ℝ) 2)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (h₀ : ∀ i, a₀ i ≤ b₀ i) (x : ℕ → lp (fun _ : ι => ℝ) 2)
    (hx : ∀ k i, x k i ∈ Icc (a k i) (b k i)) :
    ∃ x₀ : lp (fun _ : ι => ℝ) 2, (∀ i, x₀ i ∈ Icc (a₀ i) (b₀ i)) ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto (x ∘ s) atTop (𝓝 x₀) := by
  let y : ℕ → lp (fun _ : ι => ℝ) 2 := fun k => p5LpClamp38 a₀ b₀ (x k) h₀
  have hy (k : ℕ) : ∀ i, y k i ∈ Icc (a₀ i) (b₀ i) := p5LpClamp_mem38 _ _ _ h₀
  obtain ⟨x₀,hx₀,s,hs,hys⟩ := (p5Lp2_order_box_isCompact38 ι a₀ b₀).tendsto_subseq hy
  have ha' := (tendsto_iff_norm_sub_tendsto_zero.mp ha).pow 2
  have hb' := (tendsto_iff_norm_sub_tendsto_zero.mp hb).pow 2
  have hM : Tendsto (fun k => 2*(‖a k-a₀‖^2+‖b k-b₀‖^2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add,mul_zero] using
      (ha'.add hb').const_mul 2
  have hsq : Tendsto (fun k => ‖x k-y k‖^2) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun k => p5LpClamp_error_norm_sq_le38 (a k) (b k) a₀ b₀ (x k) h₀ (hx k)) hM
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  change Tendsto (fun k => Real.sqrt (‖x k-y k‖^2)) atTop (𝓝 (Real.sqrt 0)) at ht
  have he : (fun k => Real.sqrt (‖x k-y k‖^2))=(fun k => ‖x k-y k‖) :=
    funext (fun _ => Real.sqrt_sq (norm_nonneg _))
  rw [he,Real.sqrt_zero] at ht
  have herr : Tendsto (fun k => x k-y k) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ht
  refine ⟨x₀,hx₀,s,hs,?_⟩
  have hsum := (herr.comp hs.tendsto_atTop).add hys
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hsum

end
end NlsGge.GK38
