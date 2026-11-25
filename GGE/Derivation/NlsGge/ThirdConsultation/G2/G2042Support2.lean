import Mathlib
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.TauGamma
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.XiSqChiMajorant
import NlsGge.Atomic.G2.G2046

/- G2-042 SUPPORT2 (proof development, AUTHOR; not self-reviewed; no packet acceptance claimed).
   Supporting prerequisite MS-D of G2-042 (proof development/G2042_STOP.md), statement exactly as there:
   a uniform bound on a5Chi38 over the rescaled critical segment, uniform in n and locally uniform in φ.
   Route: for |n| large, the geometry of the isolating family gives ball (C n) (R n) = Lib.Dn n and
   the public a5Chi_Dn_l2_majorant38 bounds a5Chi38 - 1 by a summable majorant b n with b n ≤ 1 + B;
   for the finitely many remaining n, compactness of the closed isolating disc gives a bound
   by continuity of a5Chi38 on the open omitted domain (a5Chi_analytic38). `gap` comes from
   NlsGge.Atomic.G2.G2046 (the rescaled segment is segment (lamMinus) (lamPlus)). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G2042S2
noncomputable section

/-- MS-D: uniform bound on the rescaled critical product `a5Chi38` over the segment `t ∈ [-1,1]`. -/
theorem a5Chi_rescaled_bound :
    ∀ φ₀ ∈ gkW, ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ C : ℝ, ∀ φ ∈ V, ∀ n : ℤ, ∀ t : ℝ,
      t ∈ Set.Icc (-1:ℝ) 1 → ‖a5Chi38 n (φ, tauN φ n + (t:ℂ) * gap φ n / 2)‖ ≤ C := by
  intro φ₀ hφ₀
  obtain ⟨V, hV, hVW, _hVo, _hVc, C, R, c, Ng, hgeom, hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  obtain ⟨U, hU, _hUW, Nc, B, hB, hmaj⟩ := a5Chi_Dn_l2_majorant38 φ₀ hφ₀
  obtain ⟨Nt, hNg_le, hNc_le⟩ : ∃ Nt : ℕ, Ng ≤ Nt ∧ Nc ≤ Nt :=
    ⟨max Ng Nc, le_max_left _ _, le_max_right _ _⟩
  -- The rescaled point lies on the own gap segment, hence in the isolating disc.
  have hpt : ∀ ψ ∈ V, ∀ m : ℤ, ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 →
      tauN ψ m + (t:ℂ) * gap ψ m / 2 ∈ ball (C m) (R m) := by
    intro ψ hψ m t ht
    have hs : segment ℝ (lamMinus ψ m) (lamPlus ψ m) ⊆ ball (C m) (R m) := by
      have h := hspec ψ hψ
      unfold IsolatingSpectral38 at h
      exact (h.1 m).1
    apply hs
    have hτ : tauN ψ m = (lamPlus ψ m + lamMinus ψ m) / 2 := tauN_value38 ψ (hVW hψ) m
    refine ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, ?_⟩
    simp only [Complex.real_smul, gap]
    push_cast
    rw [hτ]
    ring
  -- Finitely many indices: a uniform bound on the closed isolating disc, locally in φ.
  have hfin : ∀ n : ℤ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ ψ in 𝓝 φ₀,
      ∀ z ∈ closedBall (C n) (R n), ‖a5Chi38 n (ψ, z)‖ ≤ M := by
    intro n
    have hdom : ∀ z ∈ closedBall (C n) (R n), (φ₀, z) ∈ a5OmittedRootDomain38 n := fun z hz =>
      a5OwnClosedBall_omittedDomain38 φ₀ hφ₀ C R
        ⟨c, Ng, hgeom, hspec φ₀ (mem_of_mem_nhds hV)⟩ n z hz
    have hcont : ContinuousOn (fun z : ℂ => a5Chi38 n (φ₀, z)) (closedBall (C n) (R n)) :=
      fun z hz => (AnalyticAt.comp (g := a5Chi38 n) (f := fun w : ℂ => (φ₀, w))
        (a5Chi_analytic38 n _ (hdom z hz)) (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall (C n) (R n)).exists_bound_of_continuousOn hcont
    have hlt : ∀ z ∈ closedBall (C n) (R n), ∀ᶠ q : PotPair × ℂ in 𝓝 (φ₀, z),
        ‖a5Chi38 n q‖ < max M 0 + 1 := by
      intro z hz
      have hc : ContinuousAt (fun q : PotPair × ℂ => ‖a5Chi38 n q‖) (φ₀, z) :=
        ((a5Chi_analytic38 n _ (hdom z hz)).continuousAt).norm
      have hlt0 : ‖a5Chi38 n (φ₀, z)‖ < max M 0 + 1 := by
        have := hM z hz
        linarith [le_max_left M 0]
      exact hc.tendsto.eventually (gt_mem_nhds hlt0)
    have hall := (isCompact_closedBall (C n) (R n)).eventually_forall_of_forall_eventually
      (x₀ := φ₀) (P := fun ψ z => ‖a5Chi38 n (ψ, z)‖ < max M 0 + 1) hlt
    refine ⟨max M 0 + 1, by linarith [le_max_right M 0], hall.mono fun ψ hψ z hz => (hψ z hz).le⟩
  choose Mf hMf0 hMf using hfin
  let S : Finset ℤ := Finset.Icc (-(Nt : ℤ)) (Nt : ℤ)
  have hE : ∀ᶠ ψ in 𝓝 φ₀, ∀ n ∈ S, ∀ z ∈ closedBall (C n) (R n),
      ‖a5Chi38 n (ψ, z)‖ ≤ Mf n :=
    (Filter.eventually_all_finset S).2 (fun n _ => hMf n)
  refine ⟨V ∩ (U ∩ {ψ | ∀ n ∈ S, ∀ z ∈ closedBall (C n) (R n), ‖a5Chi38 n (ψ, z)‖ ≤ Mf n}),
    inter_mem hV (inter_mem hU hE), fun ψ hψ => hVW hψ.1,
    (B + 2) + ∑ n ∈ S, Mf n, ?_⟩
  intro ψ hψ n t ht
  have hψV : ψ ∈ V := hψ.1
  have hψU : ψ ∈ U := hψ.2.1
  have hψE : ∀ m ∈ S, ∀ z ∈ closedBall (C m) (R m), ‖a5Chi38 m (ψ, z)‖ ≤ Mf m := hψ.2.2
  have hz := hpt ψ hψV n t ht
  have hsum0 : 0 ≤ ∑ m ∈ S, Mf m := Finset.sum_nonneg (fun m _ => hMf0 m)
  by_cases hnS : n ∈ S
  · have h1 := hψE n hnS _ (ball_subset_closedBall hz)
    have h2 : Mf n ≤ ∑ m ∈ S, Mf m := Finset.single_le_sum (fun m _ => hMf0 m) hnS
    linarith
  · have hn : (Nt : ℤ) < |n| := by
      by_contra h
      apply hnS
      rw [Finset.mem_Icc]
      exact abs_le.mp (not_lt.mp h)
    have hNc : (Nc : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast hNc_le) hn
    have hNg : (Ng : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast hNg_le) hn
    have hball : ball (C n) (R n) = ball (countingCenter38 n) (Real.pi / 4) :=
      (hgeom.2.2.2.2 n hNg).2.2
    have hzD : tauN ψ n + (t:ℂ) * gap ψ n / 2 ∈ NlsGge.GK38.Lib.Dn n := by
      rw [hball] at hz
      exact hz
    obtain ⟨b, hb0, hbs, hbB, hb⟩ := hmaj ψ hψU
    have hbn := hb n hNc _ hzD
    have hsq : b n ^ 2 ≤ ∑' m : ℤ, b m ^ 2 := by
      simpa only [Finset.sum_singleton] using hbs.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hbsq : b n ^ 2 ≤ B := hsq.trans hbB
    have hb1 : b n ≤ 1 + B := by nlinarith [sq_nonneg (b n - 1 / 2)]
    have key : ‖a5Chi38 n (ψ, tauN ψ n + (t:ℂ) * gap ψ n / 2)‖ ≤
        ‖a5Chi38 n (ψ, tauN ψ n + (t:ℂ) * gap ψ n / 2) - 1‖ + 1 := by
      have h := norm_add_le (a5Chi38 n (ψ, tauN ψ n + (t:ℂ) * gap ψ n / 2) - 1) (1:ℂ)
      rwa [sub_add_cancel, norm_one] at h
    linarith

end
end G2042S2
end NlsGge.GKDefinitionDesign
