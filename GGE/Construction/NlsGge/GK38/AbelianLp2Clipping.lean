import NlsGge.GK38.AbelianCompactCoordinateBox

/-! Uncompiled scalar clipping and fixed lp2 order-box prerequisites for
moving-gap compactness. No varying-row summable envelope is assumed. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

def p5Clamp38 (a b x : ℝ) : ℝ := max a (min b x)

theorem p5Clamp_mem_Icc38 (a b x : ℝ) (hab : a ≤ b) :
    p5Clamp38 a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

theorem p5Between_norm_le38 (a b x : ℝ) (hx : x ∈ Icc a b) : ‖x‖ ≤ ‖a‖+‖b‖ := by
  rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le a,abs_nonneg b,hx.1]
  · linarith [le_abs_self b,abs_nonneg a,hx.2]

theorem p5Clamp_error_le38 (a b a₀ b₀ x : ℝ) (h₀ : a₀ ≤ b₀) (hx : x ∈ Icc a b) :
    |x-p5Clamp38 a₀ b₀ x| ≤ |a-a₀|+|b-b₀| := by
  by_cases hxa : x < a₀
  · have hxb : x ≤ b₀ := hxa.le.trans h₀
    rw [p5Clamp38,min_eq_right hxb,max_eq_left hxa.le,
      abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [neg_le_abs (a-a₀),abs_nonneg (b-b₀),hx.1]
  · have hax : a₀ ≤ x := le_of_not_gt hxa
    by_cases hxb : x ≤ b₀
    · rw [p5Clamp38,min_eq_right hxb,max_eq_right hax,sub_self,abs_zero]
      positivity
    · have hbx : b₀ ≤ x := (lt_of_not_ge hxb).le
      rw [p5Clamp38,min_eq_left hbx,max_eq_right h₀,
        abs_of_nonneg (sub_nonneg.mpr hbx)]
      linarith [le_abs_self (b-b₀),abs_nonneg (a-a₀),hx.2]

theorem p5Clamp_error_sq_le38 (a b a₀ b₀ x : ℝ) (h₀ : a₀ ≤ b₀) (hx : x ∈ Icc a b) :
    (x-p5Clamp38 a₀ b₀ x)^2 ≤ 2*((a-a₀)^2+(b-b₀)^2) := by
  have h := mul_self_le_mul_self (abs_nonneg (x-p5Clamp38 a₀ b₀ x))
    (p5Clamp_error_le38 a b a₀ b₀ x h₀ hx)
  nlinarith [sq_abs (x-p5Clamp38 a₀ b₀ x),sq_abs (a-a₀),sq_abs (b-b₀),
    sq_nonneg (|a-a₀|-|b-b₀|)]

theorem p5Lp2_order_box_isCompact38 (ι : Type*)
    (a b : lp (fun _ : ι => ℝ) 2) :
    IsCompact {t : lp (fun _ : ι => ℝ) 2 | ∀ i, t i ∈ Icc (a i) (b i)} := by
  have ha := (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hb := (lp.memℓp b).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs : Summable (fun i => (‖a i‖+‖b i‖)^2) := by
    have hs' : Summable (fun i => 2*(‖a i‖^2+‖b i‖^2)) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (ha.add hb).mul_left 2
    apply hs'.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro i
    nlinarith [sq_nonneg (‖a i‖-‖b i‖)]
  have hc := p5Lp_coordinate_box_isCompact38 ι (fun i => ‖a i‖+‖b i‖)
    (fun i => add_nonneg (norm_nonneg _) (norm_nonneg _)) hs
  have hclosed : IsClosed {t : lp (fun _ : ι => ℝ) 2 | ∀ i, t i ∈ Icc (a i) (b i)} := by
    have hi (i : ι) : IsClosed {t : lp (fun _ : ι => ℝ) 2 | t i ∈ Icc (a i) (b i)} :=
      isClosed_Icc.preimage (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).continuous
    simpa only [ofPred_forall] using isClosed_iInter hi
  apply hc.of_isClosed_subset hclosed
  exact fun t ht i => p5Between_norm_le38 (a i) (b i) (t i) (ht i)

end
end NlsGge.GK38
