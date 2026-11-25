import NlsGge.GK38.XiSqActualC3

/-! Genuine common square-mass of the actual P2 row envelope.
UNCOMPILED prospective source. This is not yet a bound on the Abelian coordinates. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

def p2RowEnvelope38 (φ : PotPair) (s : Lib.L2Seq) (m : ℤ) : ℝ :=
  ‖s m‖+‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖+‖lamPlus φ m-lamMinus φ m‖/2

 theorem p2RowEnvelope_nonneg38 (φ : PotPair) (s : Lib.L2Seq) (m : ℤ) :
    0 ≤ p2RowEnvelope38 φ s m := by
  unfold p2RowEnvelope38
  positivity

/-- Common U,V,B before EVERY input and row; all three sums are genuinely summable. -/
theorem p2RowEnvelope_common_l2_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, Summable (fun m : ℤ => p2RowEnvelope38 φ s m^2) ∧
        (∑' m : ℤ, p2RowEnvelope38 φ s m^2) ≤ B := by
  obtain ⟨U,hU,hUW,Bt,hBt,ht⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  let Bs : ℝ := (‖s₀‖+1)^2
  refine ⟨U,hU,hUW,ball s₀ 1,ball_mem_nhds _ (by norm_num),3*(Bs+Bt+Bt/4),?_,?_⟩
  · dsimp [Bs]
    positivity
  · intro φ hφ s hs
    have hinput := (Lib.hasSum_sq_l2 s).summable
    have htau : Summable (fun m : ℤ => ‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖^2) := (ht φ hφ).1
    have hgap := (ht φ hφ).2.1
    have hnorm : ‖s‖ ≤ ‖s₀‖+1 := by
      have he := norm_le_norm_sub_add s s₀
      have hd : ‖s-s₀‖<1 := mem_ball_iff_norm.mp hs
      linarith
    have hinputB : (∑' m : ℤ, ‖s m‖^2) ≤ Bs := by
      rw [Lib.tsum_sq_l2]
      dsimp [Bs]
      nlinarith [norm_nonneg s,norm_nonneg s₀]
    have htauB := (ht φ hφ).2.2.2.1
    have hgapB := (ht φ hφ).2.2.2.2.1
    let d : ℤ → ℝ := fun m => 3*(‖s m‖^2+
      ‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖^2+‖lamPlus φ m-lamMinus φ m‖^2/4)
    have hd : Summable d := ((hinput.add htau).add (hgap.div_const 4)).mul_left 3
    have hpoint : ∀ m : ℤ, p2RowEnvelope38 φ s m^2 ≤ d m := by
      intro m
      dsimp [p2RowEnvelope38,d]
      nlinarith [sq_nonneg (‖s m‖-‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖),
        sq_nonneg (‖s m‖-‖lamPlus φ m-lamMinus φ m‖/2),
        sq_nonneg (‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖-‖lamPlus φ m-lamMinus φ m‖/2)]
    have he := hd.of_nonneg_of_le (fun m => sq_nonneg _) hpoint
    refine ⟨he,(he.tsum_le_tsum hpoint hd).trans ?_⟩
    change (∑' m : ℤ, 3*(‖s m‖^2+
      ‖tauN φ m-(m:ℂ)*(Real.pi:ℂ)‖^2+‖lamPlus φ m-lamMinus φ m‖^2/4)) ≤ _
    rw [tsum_mul_left]
    rw [((hinput.add htau).tsum_add (hgap.div_const 4)),hinput.tsum_add htau,tsum_div_const]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hinputB htauB) (div_le_div_of_nonneg_right hgapB (by norm_num)))
      (by norm_num)

#print axioms p2RowEnvelope_nonneg38
#print axioms p2RowEnvelope_common_l2_bound38
end
end NlsGge.GK38
