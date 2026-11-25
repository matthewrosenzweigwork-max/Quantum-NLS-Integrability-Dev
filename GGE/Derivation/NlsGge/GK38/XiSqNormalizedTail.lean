import NlsGge.GK38.XiSqKernelMajorant
import NlsGge.GK38.XiSqCircleError
import NlsGge.GK38.ActionRadialTail

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Actual radial comparison transports the already earned through-collapse candidate identity. -/
theorem a5Candidate_smallcircle38 (n : ℤ) (g : PotPair → ℂ) (hg : XiSqSpec38 n g)
    (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ : PotPair) (hφ : φ ∈ V)
    (hC : C n = (n:ℂ)*(Real.pi:ℂ)) (hR : R n = Real.pi/4)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball ((n:ℂ)*(Real.pi:ℂ)) (Real.pi/16)) :
    CircleIntegrable (fun z => a5CenteredKernel38 n (φ,z)) ((n:ℂ)*(Real.pi:ℂ)) (Real.pi/8) ∧
      g φ = (4/(Real.pi:ℂ))*circleIntegral (fun z => a5CenteredKernel38 n (φ,z))
        ((n:ℂ)*(Real.pi:ℂ)) (Real.pi/8) := by
  have ha : AnalyticOnNhd ℂ (fun z => a5CenteredKernel38 n (φ,z)) (actionCutDomain38 φ) := by
    intro z hz
    exact AnalyticAt.comp (g := a5CenteredKernel38 n) (f := fun w : ℂ => (φ,w))
      (a5CenteredKernel_analytic38 n (φ,z) ⟨hVW hφ,hz⟩) (analyticAt_const.prod analyticAt_id)
  have hrad := NlsGge.GK38.ActionRadial.fixed_tail_contour_realization φ (hVW hφ) C R
    (hf φ hφ) n hC hR hown _ ha
  refine ⟨hrad.2.1,?_⟩
  have hcandidate := a5CenteredLocalXi_eq_candidate38 n g hg V hVo hVW C R hf φ hφ
  rw [← hcandidate]
  unfold a5CenteredLocalXi38
  rw [hC,hR,hrad.2.2]

/-- ACTUAL normalized action errors have a common full square-summable far-label majorant. -/
theorem a5XiSqError_tail_l2_majorant38 (g : ℤ → PotPair → ℂ)
    (hspec : ∀ n, XiSqSpec38 n (g n)) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ φ ∈ U, ∃ b : ℤ → ℝ, (∀ n, 0 ≤ b n) ∧
        Summable (fun n : ℤ => b n^2) ∧ (∑' n : ℤ, b n^2) ≤ M ∧
        ∀ n : ℤ, (N:ℤ) < |n| → ‖g n φ-1‖ ≤ b n := by
  obtain ⟨Uk,hUk,hUkW,Nk,Bk,hBk,hkernel⟩ := a5CenteredKernel_circle_l2_majorant38 φ₀ hφ₀
  obtain ⟨Uo,hUo,_hUoW,No,hown⟩ := a5OwnCut_uniform_ball38 φ₀ hφ₀ (Real.pi/16) (by positivity)
  obtain ⟨V,hV,hVW,hVo,_hVc,C,R,c,Nv,hgeom,hspectral⟩ := local_isolatingFamily_common38 φ₀ hφ₀
  let U := Uk ∩ (Uo ∩ V)
  let N := max Nk (max No Nv)
  let L : ℝ := 8*(Real.pi/8)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hf : ∀ φ ∈ V, IsolatingFamily38 φ C R := fun φ hφ => ⟨c,Nv,hgeom,hspectral φ hφ⟩
  refine ⟨U,inter_mem hUk (inter_mem hUo hV),fun φ hφ => hUkW hφ.1,
    N,L^2*Bk,mul_nonneg (sq_nonneg _) hBk,?_⟩
  intro φ hφ
  obtain ⟨b,hb0,hbs,hbB,hb⟩ := hkernel φ hφ.1
  have hs : Summable (fun n => (L*b n)^2) := by
    simpa only [mul_pow] using hbs.mul_left (L^2)
  refine ⟨fun n => L*b n,fun n => mul_nonneg hL (hb0 n),hs,?_,?_⟩
  · simp only [mul_pow,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hbB (sq_nonneg _)
  · intro n hn
    have hnk : (Nk:ℤ) < |n| := by have h := le_max_left Nk (max No Nv); omega
    have hno : (No:ℤ) < |n| := by have h := (le_max_left No Nv).trans (le_max_right Nk _); omega
    have hnv : (Nv:ℤ) < |n| := by have h := (le_max_right No Nv).trans (le_max_right Nk _); omega
    have ht := hgeom.2.2.2.2 n hnv
    have hCn : C n=(n:ℂ)*(Real.pi:ℂ) := ht.1
    have hRn : R n=Real.pi/4 := ht.2.1
    have ho := hown φ hφ.2.1 n hno
    have hsmall := a5Candidate_smallcircle38 n (g n) (hspec n) V hVo hVW C R hf
      φ hφ.2.2 hCn hRn ho
    rw [hsmall.2]
    apply a5NormalizedCircle_error38 _ _ _ _ (by positivity) hsmall.1
    intro z hz
    apply hb n hnk z hz
    refine ⟨hVW hφ.2.2,?_⟩
    have hzC : z ∈ sphere (C n) (Real.pi/8) := by rw [hCn]; exact hz
    have hownC : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) (Real.pi/16) := by
      rw [hCn]
      exact ho
    have hrR : Real.pi/8 ≤ R n := by rw [hRn]; linarith [Real.pi_pos]
    exact NlsGge.GK38.ActionRadial.radial_sphere_subset φ C R (hf φ hφ.2.2) n
      (Real.pi/16) (Real.pi/8) (by linarith [Real.pi_pos]) hrR hownC hzC

end
end NlsGge.GK38
