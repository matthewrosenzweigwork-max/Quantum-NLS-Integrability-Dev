import Mathlib
import NlsGge.ThirdConsultation.G2.ActionSeries036A
import NlsGge.ThirdConsultation.G2.ActionSeries036B
import NlsGge.ThirdConsultation.G2.ActionSeries036C
import NlsGge.Atomic.G4.G4011

/- G2-036 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G2/G2036.lean, namespace NlsGge.GKDefinitionDesign.
   Head verbatim from followup4 STATEMENTS/G2.md G2-036 (no repair). Uses local-uniform l1 Lipschitz estimate (Schwarz lemma, ActionSeries036A/B),
   local l1 bound (ActionSeries036C), and G4011 along the finsets Icc (-N) N. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38
noncomputable section

namespace NlsGge.GKDefinitionDesign

theorem G2_036 :
    (∀ φ ∈ gkW, Summable (fun n : ℤ => ‖gkActionC38 φ n‖)) ∧
    HasSumLocallyUniformlyOn (fun n : ℤ => fun φ : PotPair => ‖gkActionC38 φ n‖)
      (fun φ => ∑' n : ℤ, ‖gkActionC38 φ n‖) gkW ∧
    HasSumLocallyUniformlyOn (fun n : ℤ => fun φ : PotPair => gkActionC38 φ n)
      (fun φ => ∑' n : ℤ, gkActionC38 φ n) gkW ∧
    AnalyticOnNhd ℂ (fun φ : PotPair => ∑' n : ℤ, gkActionC38 φ n) gkW := by
  have hlip : ∀ x₀ ∈ gkW, ∃ V ∈ 𝓝 x₀, ∃ L : ℝ,
      Summable (fun n : ℤ => ‖gkActionC38 x₀ n‖) ∧
      ∀ y ∈ V, Summable (fun n : ℤ => ‖gkActionC38 y n‖) ∧
        ∑' n : ℤ, ‖gkActionC38 y n - gkActionC38 x₀ n‖ ≤ L * ‖y - x₀‖ := by
    intro x₀ hx₀
    obtain ⟨r, hr, hsub, B, hB⟩ := gk_action_local_l1 x₀ hx₀
    refine ⟨ball x₀ r, ball_mem_nhds _ hr, (2 * B + 1) / r, (hB x₀ (mem_ball_self hr)).1,
      fun y hy => ⟨(hB y hy).1, ?_⟩⟩
    have hd : ∀ n : ℤ, DifferentiableOn ℂ (fun φ : PotPair => gkActionC38 φ n) (ball x₀ r) :=
      fun n => ((action_analytic38 n).differentiableOn).mono hsub
    exact (schwarz_l1_sum (fun n φ => gkActionC38 φ n) hr hd hB hy).2
  obtain ⟨hn, hc⟩ := hasSumLocUnif_of_l1_lip gkW (fun n φ => gkActionC38 φ n) hlip
  refine ⟨fun φ hφ => ?_, hn, hc, ?_⟩
  · obtain ⟨r, hr, -, B, hB⟩ := gk_action_local_l1 φ hφ
    exact (hB φ (mem_ball_self hr)).1
  · -- analytic limit along the finsets Icc (-N) N
    let f : ℕ → PotPair → ℂ := fun N φ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gkActionC38 φ n
    have hf : ∀ N, AnalyticOnNhd ℂ (f N) gkW := by
      intro N
      have : f N = fun φ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), gkActionC38 φ n := rfl
      rw [this]
      have h := Finset.analyticOnNhd_sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
        (fun n _ => action_analytic38 n)
      convert h using 1
      funext φ
      simp [Finset.sum_apply]
    have hseq : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro F
      refine eventually_atTop.2 ⟨F.sup Int.natAbs, fun N hN => ?_⟩
      intro n hn
      have h1 : n.natAbs ≤ F.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hn
      rw [Finset.mem_Icc]
      omega
    have hlim : TendstoLocallyUniformlyOn f (fun φ => ∑' n : ℤ, gkActionC38 φ n) atTop gkW := by
      rw [HasSumLocallyUniformlyOn, Metric.tendstoLocallyUniformlyOn_iff] at hc
      rw [Metric.tendstoLocallyUniformlyOn_iff]
      intro ε hε x hx
      obtain ⟨t, ht, hev⟩ := hc ε hε x hx
      exact ⟨t, ht, hseq.eventually hev⟩
    exact NlsGge.Atomic.G4.analyticOnNhd_of_locally_uniform_limit isOpen_gkW hf hlim

end NlsGge.GKDefinitionDesign
end
