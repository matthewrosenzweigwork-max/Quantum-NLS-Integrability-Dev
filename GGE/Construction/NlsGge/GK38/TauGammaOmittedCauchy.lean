import NlsGge.GK38.TauGammaOmittedValues
import Mathlib.Analysis.Complex.Liouville

/-! Inner circles fit strictly inside the quarter discs, so Cauchy gives the derivative L2 bound. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem sincAt_entire38 (n : ℤ) : AnalyticOnNhd ℂ (Lib.sincAt n) univ := by
  intro z _
  have h := Lib.analyticAt_omitProd_line n 0 z
  simpa only [Lib.omitProd_zero_eq_sincAt] using h

theorem paired_omit_inner_bound38 (n : ℤ) (sp sm : Lib.L2Seq) (b : ℝ)
    (hb : ∀ w ∈ Lib.Dn n, ‖Lib.omitProd n sp w * Lib.omitProd n sm w - (Lib.sincAt n w) ^ 2‖ ≤ b)
    (z : ℂ) (hz : z ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8)) :
    ‖Lib.omitProd n sp z * Lib.omitProd n sm z - (Lib.sincAt n z) ^ 2‖ ≤ b ∧
    ‖deriv (fun w => Lib.omitProd n sp w * Lib.omitProd n sm w) z -
      deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ b / (Real.pi / 8) := by
  let f : ℂ → ℂ := fun w => Lib.omitProd n sp w * Lib.omitProd n sm w
  let g : ℂ → ℂ := fun w => (Lib.sincAt n w) ^ 2
  have hf : AnalyticOnNhd ℂ f univ := fun w _ =>
    (Lib.analyticAt_omitProd_line n sp w).mul (Lib.analyticAt_omitProd_line n sm w)
  have hg : AnalyticOnNhd ℂ g univ := (sincAt_entire38 n).pow 2
  have he : AnalyticOnNhd ℂ (fun w => f w - g w) univ := hf.sub hg
  have hdiff : Differentiable ℂ (fun w => f w - g w) :=
    fun w => (he w (mem_univ _)).differentiableAt
  have hderiv : deriv (fun w => f w - g w) z = deriv f z - deriv g z := by
    exact deriv_fun_sub (hf z (mem_univ _)).differentiableAt (hg z (mem_univ _)).differentiableAt
  have hcircle (w : ℂ) (hw : w ∈ sphere z (Real.pi / 8)) : w ∈ Lib.Dn n := by
    have ht := dist_triangle w z ((n : ℂ) * (Real.pi : ℂ))
    have hrad := mem_sphere.mp hw
    have hinner := mem_ball.mp hz
    change dist w ((n : ℂ) * (Real.pi : ℂ)) < Real.pi / 4
    linarith
  have hzOuter : z ∈ Lib.Dn n := by
    change dist z ((n : ℂ) * (Real.pi : ℂ)) < Real.pi / 4
    linarith [mem_ball.mp hz, Real.pi_pos]
  refine ⟨hb z hzOuter, ?_⟩
  change ‖deriv f z - deriv g z‖ ≤ _
  rw [← hderiv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdiff.diffContOnCl
    (fun w hw => hb w (hcircle w hw))

theorem paired_omit_cauchy38 (K : ℝ) (hK : 0 ≤ K) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ sp sm : Lib.L2Seq, ‖sp‖ ≤ K → ‖sm‖ ≤ K → ∃ b : ℤ → ℝ,
      (∀ n : ℤ, 0 ≤ b n ∧ ∀ z ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8),
        ‖Lib.omitProd n sp z * Lib.omitProd n sm z - (Lib.sincAt n z) ^ 2‖ ≤ b n ∧
        ‖deriv (fun w => Lib.omitProd n sp w * Lib.omitProd n sm w) z -
          deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ b n) ∧
      Summable (fun n => b n ^ 2) ∧ (∑' n : ℤ, b n ^ 2) ≤ B := by
  obtain ⟨C, hC, h⟩ := paired_omit_value_majorant38 K hK
  let L := 1 + 8 / Real.pi
  have hL : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (by positivity : 0 ≤ 8 / Real.pi)
  refine ⟨L ^ 2 * C, mul_nonneg (sq_nonneg L) hC, fun sp sm hsp hsm => ?_⟩
  obtain ⟨a, ha, has, hab⟩ := h sp sm hsp hsm
  let b : ℤ → ℝ := fun n => L * a n
  have hs : Summable (fun n => b n ^ 2) := by
    simpa only [b, mul_pow] using has.mul_left (L ^ 2)
  refine ⟨b, fun n => ⟨mul_nonneg (by linarith) (ha n).1, fun z hz => ?_⟩, hs, ?_⟩
  · have hn := paired_omit_inner_bound38 n sp sm (a n) (ha n).2 z hz
    have hlarge : a n ≤ b n := by dsimp [b]; nlinarith [(ha n).1]
    refine ⟨hn.1.trans hlarge, hn.2.trans ?_⟩
    have heq : a n / (Real.pi / 8) = (8 / Real.pi) * a n := by field_simp <;> ring
    rw [heq]
    dsimp [b, L]
    nlinarith [(ha n).1]
  · simp only [b, mul_pow, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hab (sq_nonneg L)

end
end NlsGge.GK38
