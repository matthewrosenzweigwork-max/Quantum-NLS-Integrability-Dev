import QuantumNLS.Q07WindowDifferentiationR16

/-! The actual source window Hamiltonian has full real first and second
Frechet differentials, with the printed uniform polynomial Hessian bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric
namespace QuantumNLS.Q07WindowHessiansR16
open PhysicalTensor (L2T)
open Q07IntegratedHessiansR16 (windowContour)
variable {L κ : ℝ} [Fact (0 < L)]

theorem uniform_window_hessians (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) (r : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l : ℕ, l0 ≤ l → 1 ≤ PROP017UniformN.cutSeq L l ∧
        ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
          ∀ v : L2T L, ‖v-u‖ < δ →
            DifferentiableAt ℝ (windowContour hκ r (PROP017UniformN.cutSeq L l) h) v ∧
            DifferentiableAt ℝ (fderiv ℝ (windowContour hκ r (PROP017UniformN.cutSeq L l) h)) v ∧
            ∀ w q : L2T L,
              |((fderiv ℝ (fderiv ℝ (windowContour hκ r (PROP017UniformN.cutSeq L l) h)) v) w) q| ≤
                C*(PROP017UniformN.cutSeq L l)^(r+1)*‖w‖*‖q‖ := by
  obtain ⟨η,hη,l0,A1,A2,h1,h2,hops⟩ := Q07ContourApplicationR16.uniform_field_operators (L := L) hκ hs B hh
  obtain ⟨n,hn⟩ := exists_nat_gt L
  let K := 1/(2*Real.pi*κ)
  let C := K*4*(1+h)^(r+1)*A2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨η/2,half_pos hη,max l0 n,C,hC,?_⟩
  intro l hl
  have hll := (le_max_left l0 n).trans hl
  have hnl := (le_max_right l0 n).trans hl
  let a := PROP017UniformN.cutSeq L l
  have ha : 1 ≤ a := by
    dsimp [a, PROP017UniformN.cutSeq]
    apply (le_div_iff₀ (Fact.out : 0 < L)).mpr
    have hnL : L < (l : ℝ) := hn.trans_le (by exact_mod_cast hnl)
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hlp : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    nlinarith
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  refine ⟨ha,?_⟩
  intro u hu v hv
  let U := ball v (η/2)
  have hnear : ∀ x ∈ U, ‖x-u‖ < η := by
    intro x hx
    have hXV : ‖x-v‖ < η/2 := by simpa only [U,mem_ball,dist_eq_norm] using hx
    have hn : ‖x-u‖ ≤ ‖x-v‖+‖v-u‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x-v) (v-u)
    linarith
  have hpoint := fun x hx z hz => hops l hll u hu x (hnear x hx) z hz
  obtain ⟨hd1,hd2,hess⟩ := Q07WindowDifferentiationR16.window_second hκ r ha0 hh
    (U := U) isOpen_ball h2
    (fun x hx z hz => (hpoint x hx z hz).1)
    (fun x hx z hz => (hpoint x hx z hz).2.1)
    (fun x hx z hz => (hpoint x hx z hz).2.2)
    (mem_ball_self (half_pos hη))
  refine ⟨hd1,hd2,?_⟩
  intro w q
  refine (hess w q).trans ?_
  change K*(4*(a+h)*((a+h)^r*A2))*‖w‖*‖q‖ ≤ C*a^(r+1)*‖w‖*‖q‖
  have hlen : a+h ≤ (1+h)*a := by nlinarith
  calc
    _ ≤ K*(4*((1+h)*a)*(((1+h)*a)^r*A2))*‖w‖*‖q‖ := by gcongr
    _ = C*a^(r+1)*‖w‖*‖q‖ := by
      dsimp [C]
      rw [mul_pow,pow_succ,pow_succ]
      ring

end QuantumNLS.Q07WindowHessiansR16
