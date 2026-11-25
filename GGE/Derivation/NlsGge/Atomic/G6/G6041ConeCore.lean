import Mathlib
import NlsGge.Atomic.G6.G6041ToolCore
import NlsGge.Atomic.G6.G6040Host
import NlsGge.Atomic.G6.G6040Sup1
import NlsGge.Atomic.G6.G6039Sup4
import NlsGge.Atomic.LIB.LIB100
import NlsGge.Atomic.LIB.LIB089
import NlsGge.GK38.Lib.InterpolationLemma

/- G6041 CONE CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6041ConeCore.lean, namespace NlsGge.ThirdConsultation.G6041S.  SUPPORT (no packet
   increment): cone_of = the G6-041 head body `AnalyticAtCone actionHamiltonian I` for every I, from hypotheses with
   the EXACT types of (hFa) G6041S.diagonalHamiltonian_analytic (G6041Diag glue), (hflip) G6036S.diagH_flip applied
   to G6033.2, and (heq) h782's diagonalHamiltonian_eq_actionHamiltonian.
   Route = Pro r16 §Q3 common-neighbourhood order (L987-998), unchanged:
   1. complexify the actual diagonal Hamiltonian ONCE at the full positive root x = rootR I (exists_local_complexification
      with the concrete diagC); 2. shrink ONCE to a ball of radius r with one bound M;
   3. only then choose the finite nonzero head A (window N) with ‖x - x_F‖ < r/8;
   4. tail evenness of the complexification on ball(c(x_F,0), r/2) by LIB-100 (real-slice flip invariance);
   5. f(p, y) = G(complexHeadLift A p + complexTailProjection A y) on UP ×ˢ ball(0, r/4); parametric_even_tail_descent;
   6. LIB-089 positive square-root charts on the active coordinates, the real tail action map, Re: an ambient real
      analytic g on an open U ∋ I with g = actionHamiltonian on the cone (heq; the tail action norm is ‖x - x_F‖² <
      (r/8)² < (r/4)²).  The empty head and finite support (G6-040) are included.
   Own imports: Mathlib, G6041ToolCore, G6040Host, G6040Sup1, G6039Sup4, LIB100, LIB089, GK38.Lib.InterpolationLemma. -/
set_option autoImplicit false

open Set Filter Topology Metric
open scoped ENNReal
open NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

/-! ### Real window sums -/

theorem coe_finsum_single_real (T : Finset ℤ) (c : ℤ → ℝ) (m : ℤ) :
    ((∑ n ∈ T, lp.single 2 n (c n) : RealDiagonalSpace) : ℤ → ℝ) m = if m ∈ T then c m else 0 := by
  have h := map_sum (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 m) (fun k => lp.single 2 k (c k)) T
  have e : ∀ x : RealDiagonalSpace, lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 m x = (x : ℤ → ℝ) m := fun x => rfl
  rw [e] at h
  rw [h]
  simp only [e, lp.single_apply]
  split_ifs with hm
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h'; exact absurd hm h'
  · refine Finset.sum_eq_zero (fun k hk => ?_)
    have : m ≠ k := fun h => hm (h ▸ hk)
    simp [Pi.single_apply, this]

theorem tendsto_window_real (z : RealDiagonalSpace) :
    Tendsto (fun N : ℕ => ∑ n ∈ Lib.win N, lp.single 2 n (z n)) atTop (𝓝 z) := by
  have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) z
  have hw : Tendsto (fun N : ℕ => Lib.win N) atTop atTop :=
    tendsto_atTop_finset_of_monotone (fun a b h => Lib.win_mono h)
      (fun n => ⟨n.natAbs, Lib.mem_win_of_natAbs_le le_rfl⟩)
  exact hs.comp hw

/-! ### Step 4: tail evenness of the complexification (LIB-100) -/

theorem tail_even (G : ComplexDiagonalSpace → ℂ) (c0 : ComplexDiagonalSpace) (r₀ : ℝ)
    (hGa : AnalyticOnNhd ℂ G (ball c0 r₀))
    (hGeq : ∀ y : RealDiagonalSpace, diagC (y, 0) ∈ ball c0 r₀ → G (diagC (y, 0)) = (diagonalHamiltonian y : ℂ))
    (hflip : ∀ (n : ℤ) (x : RealDiagonalSpace),
      diagonalHamiltonian (NlsGge.ThirdConsultation.G6036S.flipR n x) = diagonalHamiltonian x)
    (xF : RealDiagonalSpace) (s : ℝ) (hs : 0 < s) (hsub : ball (diagC (xF, 0)) s ⊆ ball c0 r₀)
    (n : ℤ) (hn : xF n = 0) :
    ∀ z ∈ ball (diagC (xF, 0)) s, G (flipComplexCoordinate n z) = G z := by
  have hcF : (diagC (xF, 0)) n = 0 := by rw [diagC_real_apply, hn, Complex.ofReal_zero]
  have hmapsU : ∀ z ∈ ball (diagC (xF, 0)) s, flipComplexCoordinate n z ∈ ball (diagC (xF, 0)) s := by
    intro z hz
    rw [mem_ball, ← flipC_fix n _ hcF, dist_flipC]; exact hz
  have hreal : (fun y : RealDiagonalSpace => diagC (y, 0)) '' ball xF s ⊆ ball (diagC (xF, 0)) s := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_ball, dist_diagC_real]; exact hy
  have hf : AnalyticOnNhd ℂ (fun z => G (flipCLM n z)) (ball (diagC (xF, 0)) s) := fun z hz =>
    (hGa _ (hsub (hmapsU z hz))).comp ((flipCLM n).analyticAt z)
  have hg : AnalyticOnNhd ℂ G (ball (diagC (xF, 0)) s) := fun z hz => hGa z (hsub hz)
  have heqR : ∀ y ∈ ball xF s, (fun z => G (flipCLM n z)) (diagC (y, 0)) = G (diagC (y, 0)) := by
    intro y hy
    have hy1 : diagC (NlsGge.ThirdConsultation.G6036S.flipR n y, 0) ∈ ball c0 r₀ := by
      apply hsub
      rw [mem_ball, dist_diagC_real, ← flipR_fix n xF hn, dist_flipR]; exact hy
    have hy2 : diagC (y, 0) ∈ ball c0 r₀ := hsub (hreal ⟨y, hy, rfl⟩)
    show G (flipCLM n (diagC (y, 0))) = G (diagC (y, 0))
    rw [flipCLM_apply, flipC_diagC, hGeq _ hy1, hGeq _ hy2, hflip]
  have H := NlsGge.Atomic.LIB100.analytic_eq_of_realSlice diagC diagC_hc xF s hs
    (ball (diagC (xF, 0)) s) isOpen_ball hreal (fun z => G (flipCLM n z)) G hf hg heqR
  intro z hz
  exact H.2 (convex_ball _ _).isPreconnected hz

/-! ### Step 6: positive branches -/

theorem sn_eq_sqrt (s : ℂ → ℂ) (U : Set ℂ)
    (hsq : ∀ z ∈ U, s z ^ 2 = z)
    (hpos : ∀ x : ℝ, (x : ℂ) ∈ U → 0 < x → ∃ r : ℝ, 0 < r ∧ s (x : ℂ) = (r : ℂ))
    (x : ℝ) (hxU : (x : ℂ) ∈ U) (hx : 0 < x) : s (x : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
  obtain ⟨ρ, hρ, hsρ⟩ := hpos x hxU hx
  have h2 : ((ρ : ℂ)) ^ 2 = (x : ℂ) := by rw [← hsρ]; exact hsq _ hxU
  have h3 : ρ ^ 2 = x := by exact_mod_cast h2
  rw [hsρ, ← h3, Real.sqrt_sq hρ.le]

/-! ### The assembly -/

theorem cone_of
    (hFa : AnalyticOnNhd ℝ diagonalHamiltonian Set.univ)
    (hflip : ∀ (n : ℤ) (x : RealDiagonalSpace),
      diagonalHamiltonian (NlsGge.ThirdConsultation.G6036S.flipR n x) = diagonalHamiltonian x)
    (heq : ∀ (I : PositiveActionSpace) (x : RealDiagonalSpace),
      (∀ n : ℤ, (x n)^2 = I.val n) → diagonalHamiltonian x = actionHamiltonian I)
    (I : PositiveActionSpace) : AnalyticAtCone actionHamiltonian I := by
  classical
  -- Step 1: complexify at the full positive root
  set xr : RealDiagonalSpace := rootR I with hxr
  obtain ⟨r₀, G, hr₀, hGa, hGeq⟩ :=
    exists_local_complexification diagC diagC_hc diagonalHamiltonian xr (hFa xr (Set.mem_univ _))
  set c0 : ComplexDiagonalSpace := diagC (xr, 0) with hc0
  -- Step 2: one bounded ball
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 (hGa c0 (mem_ball_self hr₀)).continuousAt 1 one_pos
  set r : ℝ := min (r₀ / 2) δ with hrdef
  have hr : 0 < r := lt_min (by linarith) hδ
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hball_sub : ball c0 r ⊆ ball c0 r₀ := ball_subset_ball hrr₀.le
  set M : ℝ := ‖G c0‖ + 1 with hMdef
  have hM : ∀ z ∈ ball c0 r, ‖G z‖ ≤ M := by
    intro z hz
    have h1 := hδG (lt_of_lt_of_le hz (min_le_right _ _))
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (G z) (G c0)
    linarith
  -- Step 3: the finite head, chosen after the ball
  obtain ⟨N, hN⟩ := ((tendsto_window_real xr).eventually (ball_mem_nhds xr (by linarith : 0 < r / 8))).exists
  set A : Finset ℤ := (Lib.win N).filter (fun n => xr n ≠ 0) with hA
  set xF : RealDiagonalSpace := ∑ n ∈ A, lp.single 2 n (xr n) with hxF
  have hxF_apply : ∀ m, xF m = if m ∈ A then xr m else 0 := fun m => coe_finsum_single_real A _ m
  have hxFN : xF = ∑ n ∈ Lib.win N, lp.single 2 n (xr n) := by
    apply lp.ext; funext m
    rw [hxF_apply, coe_finsum_single_real]
    by_cases hm : m ∈ Lib.win N
    · by_cases hz : xr m = 0
      · rw [if_neg (by simp [hA, hz]), if_pos hm, hz]
      · rw [if_pos (by simp [hA, hm, hz]), if_pos hm]
    · rw [if_neg (by simp [hA, hm]), if_neg hm]
  have hdist : dist xF xr < r / 8 := by rw [hxFN]; exact hN
  set cF : ComplexDiagonalSpace := diagC (xF, 0) with hcF
  have hcFc0 : dist cF c0 < r / 8 := by rw [hcF, hc0, dist_diagC_real]; exact hdist
  have hBsub : ball cF (r / 2) ⊆ ball c0 r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z c0 ≤ dist z cF + dist cF c0 := dist_triangle _ _ _
      _ < r / 2 + r / 8 := add_lt_add hz hcFc0
      _ < r := by linarith
  have hBsub₀ : ball cF (r / 2) ⊆ ball c0 r₀ := hBsub.trans hball_sub
  -- Step 4: tail evenness
  have heven4 : ∀ n : ℤ, n ∉ A → ∀ z ∈ ball cF (r / 2), G (flipComplexCoordinate n z) = G z := by
    intro n hn
    exact tail_even G c0 r₀ hGa hGeq hflip xF (r / 2) (by linarith) hBsub₀ n
      (by rw [hxF_apply, if_neg hn])
  -- Step 5: the parametric descent
  let L : (A → ℂ) × ComplexDiagonalSpace →L[ℂ] ComplexDiagonalSpace :=
    (headCLM A).comp (ContinuousLinearMap.fst ℂ (A → ℂ) ComplexDiagonalSpace) +
      (tailCLM A).comp (ContinuousLinearMap.snd ℂ (A → ℂ) ComplexDiagonalSpace)
  have hL : ∀ q, L q = complexHeadLift A q.1 + complexTailProjection A q.2 := fun q => rfl
  let f : (A → ℂ) × ComplexDiagonalSpace → ℂ := fun q => G (L q)
  set UP : Set (A → ℂ) := {p | dist (complexHeadLift A p) cF < r / 8} with hUPdef
  have hUP : IsOpen UP := isOpen_lt ((headCLM A).continuous.dist continuous_const) continuous_const
  have hLmem : ∀ p ∈ UP, ∀ y ∈ ball (0 : ComplexDiagonalSpace) (r / 4), L (p, y) ∈ ball cF (r / 2) := by
    intro p hp y hy
    rw [mem_ball, hL, dist_eq_norm]
    have hp' : ‖complexHeadLift A p - cF‖ < r / 8 := by rw [← dist_eq_norm]; exact hp
    have hy' : ‖y‖ < r / 4 := by rwa [mem_ball, dist_zero_right] at hy
    calc ‖complexHeadLift A (p, y).1 + complexTailProjection A (p, y).2 - cF‖
        = ‖(complexHeadLift A p - cF) + complexTailProjection A y‖ := by congr 1; abel
      _ ≤ ‖complexHeadLift A p - cF‖ + ‖complexTailProjection A y‖ := norm_add_le _ _
      _ < r / 8 + r / 4 := add_lt_add_of_lt_of_le hp' ((norm_tail_le A y).trans hy'.le)
      _ < r / 2 := by linarith
  have hf : AnalyticOnNhd ℂ f (UP ×ˢ ball (0 : ComplexDiagonalSpace) (r / 4)) := fun q hq =>
    (hGa _ (hBsub₀ (hLmem q.1 hq.1 q.2 hq.2))).comp (L.analyticAt q)
  have heven : ∀ p : A → ℂ, p ∈ UP →
      CoordinatewiseEvenOn (fun y : ComplexDiagonalSpace => f (p, y)) Set.univ
        (ball (0 : ComplexDiagonalSpace) (r / 4)) := by
    intro p hp y hy n _
    show G (L (p, flipComplexCoordinate n y)) = G (L (p, y))
    by_cases hn : n ∈ A
    · have ht : complexTailProjection A (flipComplexCoordinate n y) = complexTailProjection A y := by
        apply lp.ext; funext m
        rw [tail_apply, tail_apply, flipC_apply]
        split_ifs with h1 h2
        · rfl
        · exact absurd (h2 ▸ hn) h1
        · rfl
      rw [hL, hL, ht]
    · have hfl : L (p, flipComplexCoordinate n y) = flipComplexCoordinate n (L (p, y)) := by
        apply lp.ext; funext m
        rw [hL, hL, lp.coeFn_add, Pi.add_apply, flipC_apply, lp.coeFn_add, Pi.add_apply, tail_apply,
          tail_apply, head_apply, flipC_apply]
        by_cases hm : m = n
        · subst hm; simp [hn]
        · simp [hm]
      rw [hfl, heven4 n hn _ (hLmem p hp y hy)]
  have hbd : ∃ M' : ℝ, ∀ (p : A → ℂ) (y : ComplexDiagonalSpace),
      p ∈ UP → y ∈ ball (0 : ComplexDiagonalSpace) (r / 4) → ‖f (p, y)‖ ≤ M' :=
    ⟨M, fun p y hp hy => hM _ (hBsub (hLmem p hp y hy))⟩
  obtain ⟨hΦa, hΦid⟩ := parametric_even_tail_descent UP hUP f (r / 4) (by linarith) hf heven hbd
  -- Step 6: real chart
  have hIpos : ∀ n : A, 0 < I.val n := by
    intro n
    have hn := (Finset.mem_filter.1 n.2).2
    have hx : xr n = Real.sqrt (I.val n) := rootR_apply I n
    rw [hx] at hn
    exact Real.sqrt_pos.1 (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hn))
  have h89 := fun n : A => NlsGge.Atomic.LIB089.lib089_statement (I.val n) (hIpos n)
  choose Un sn hUo hIn hsa hs0 hsq hsR hpos using h89
  let pJ : WeightedActionSpace → (A → ℂ) := fun J n => sn n (evalR n J)
  let V0 : Set WeightedActionSpace := ⋂ n : A, ({J | evalR n J ∈ Un n} ∩ {J | I.val n / 2 < J n})
  have hV0 : IsOpen V0 := isOpen_iInter_of_finite fun n =>
    ((hUo n).preimage (evalR n).continuous).inter
      (isOpen_lt continuous_const ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 (n : ℤ)).continuous))
  have hV0mem : ∀ J ∈ V0, ∀ n : A, evalR n J ∈ Un n ∧ I.val n / 2 < J n := fun J hJ n =>
    Set.mem_iInter.1 hJ n
  have hpJc : ContinuousOn pJ V0 := by
    refine continuousOn_pi.2 fun n => ?_
    refine (hsa n).continuousOn.comp (evalR n).continuous.continuousOn ?_
    intro J hJ; exact (hV0mem J hJ n).1
  let Q : WeightedActionSpace → (A → ℂ) × ComplexActionSpace := fun J => (pJ J, tailAct A J)
  have hQc : ContinuousOn Q V0 := hpJc.prodMk (tailAct A).continuous.continuousOn
  let U : Set WeightedActionSpace := V0 ∩ Q ⁻¹' (UP ×ˢ ball (0 : ComplexActionSpace) ((r / 4) ^ 2))
  have hUo' : IsOpen U := hQc.isOpen_inter_preimage hV0 (hUP.prod isOpen_ball)
  let g : WeightedActionSpace → ℝ := fun J => Complex.reCLM (parametricActionDescent f (Q J))
  -- the center
  have hpJI : pJ I.val = fun n : A => ((xr n : ℝ) : ℂ) := by
    funext n
    show sn n (evalR n I.val) = _
    rw [evalR_apply, hs0 n, rootR_apply]
  have htailI : ‖tailAct A I.val‖ = ‖xF - xr‖ ^ 2 := by
    have h1 := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) (tailAct A I.val)
    simp only [ENNReal.toReal_one, Real.rpow_one] at h1
    have h2 := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (xF - xr)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
    have he : (fun m => ‖(tailAct A I.val : ℤ → ℂ) m‖) = fun m => ‖((xF - xr : RealDiagonalSpace) : ℤ → ℝ) m‖ ^ 2 := by
      funext m
      rw [tailAct_apply, lp.coeFn_sub, Pi.sub_apply, hxF_apply]
      split_ifs
      · simp
      · rw [Complex.norm_real, zero_sub, norm_neg, Real.norm_of_nonneg (I.2 m), Real.norm_eq_abs, sq_abs]
        exact (rootR_sq I m).symm
    rw [he] at h1
    exact h1.unique h2
  have hIU : I.val ∈ U := by
    refine ⟨Set.mem_iInter.2 fun n => ⟨?_, ?_⟩, ?_, ?_⟩
    · show evalR n I.val ∈ Un n
      rw [evalR_apply]; exact hIn n
    · show I.val n / 2 < I.val n
      linarith [hIpos n]
    · show dist (complexHeadLift A (pJ I.val)) cF < r / 8
      have : complexHeadLift A (pJ I.val) = cF := by
        rw [hpJI]
        apply lp.ext; funext m
        rw [head_apply, hcF, diagC_real_apply, hxF_apply]
        by_cases hm : m ∈ A
        · simp [hm]
        · simp [hm]
      rw [this, dist_self]; linarith
    · show tailAct A I.val ∈ ball (0 : ComplexActionSpace) ((r / 4) ^ 2)
      rw [mem_ball, dist_zero_right, htailI, ← dist_eq_norm]
      have h0 : 0 ≤ dist xF xr := dist_nonneg
      nlinarith
  refine ⟨U, g, hUo', hIU, ?_, ?_⟩
  · -- analyticity
    intro J hJ
    have hJ0 := hV0mem J hJ.1
    have hpJa : AnalyticAt ℝ pJ J := by
      refine AnalyticAt.pi fun n => ?_
      exact ((hsa n _ (hJ0 n).1).restrictScalars (𝕜 := ℝ)).comp ((evalR n).analyticAt J)
    have hQa : AnalyticAt ℝ Q J := hpJa.prod ((tailAct A).analyticAt J)
    have hΦJ := (hΦa (Q J) hJ.2).restrictScalars (𝕜 := ℝ)
    exact (Complex.reCLM.analyticAt _).comp (hΦJ.comp hQa)
  · -- agreement on the cone
    intro J hJ
    have hJ0 := hV0mem J.val hJ.1
    set zJ : RealDiagonalSpace := rootR J with hzJ
    set yJ : ComplexDiagonalSpace := complexTailProjection A (diagC (zJ, 0)) with hyJ
    have hyJsq : ∀ m : ℤ, (yJ m) ^ 2 = tailAct A J.val m := by
      intro m
      rw [hyJ, tail_apply, tailAct_apply, diagC_real_apply]
      split_ifs
      · ring
      · rw [← Complex.ofReal_pow, rootR_sq]
    have hyJb : yJ ∈ ball (0 : ComplexDiagonalSpace) (r / 4) := by
      have h1 := NlsGge.ThirdConsultation.G6039S.norm_sq_of_sq (tailAct A J.val) yJ hyJsq
      have h2 := hJ.2.2
      rw [mem_ball, dist_zero_right] at h2 ⊢
      exact lt_of_pow_lt_pow_left₀ 2 (by linarith) (by rw [h1]; exact h2)
    have hid := hΦid (pJ J.val) (tailAct A J.val) yJ hJ.2.1 hJ.2.2 hyJsq
    have hLz : L (pJ J.val, yJ) = diagC (zJ, 0) := by
      apply lp.ext; funext m
      rw [hL, lp.coeFn_add, Pi.add_apply, head_apply, hyJ, tail_apply, tail_apply, diagC_real_apply]
      by_cases hm : m ∈ A
      · rw [dif_pos hm, if_pos hm, add_zero]
        have hpos' : 0 < J.val m := by linarith [(hJ0 ⟨m, hm⟩).2, hIpos ⟨m, hm⟩]
        show sn ⟨m, hm⟩ (evalR m J.val) = _
        rw [evalR_apply, sn_eq_sqrt (sn ⟨m, hm⟩) (Un ⟨m, hm⟩) (hsq ⟨m, hm⟩) (hpos ⟨m, hm⟩) _
          (by rw [← evalR_apply]; exact (hJ0 ⟨m, hm⟩).1) hpos', hzJ, rootR_apply]
      · rw [dif_neg hm, if_neg hm, if_neg hm, zero_add]
    have hzin : diagC (zJ, 0) ∈ ball c0 r₀ := by
      rw [← hLz]; exact hBsub₀ (hLmem _ hJ.2.1 _ hyJb)
    have hval : parametricActionDescent f (Q J.val) = (actionHamiltonian J : ℂ) := by
      show parametricActionDescent f (pJ J.val, tailAct A J.val) = _
      rw [← hid]
      show G (L (pJ J.val, yJ)) = _
      have h1 : G (L (pJ J.val, yJ)) = G (diagC (zJ, 0)) := congrArg G hLz
      have h2 : G (diagC (zJ, 0)) = (diagonalHamiltonian zJ : ℂ) := hGeq zJ hzin
      have h3 : diagonalHamiltonian zJ = actionHamiltonian J := heq J zJ (rootR_sq J)
      exact h1.trans (h2.trans (congrArg (fun t : ℝ => (t : ℂ)) h3))
    show Complex.reCLM (parametricActionDescent f (Q J.val)) = actionHamiltonian J
    rw [hval, Complex.reCLM_apply, Complex.ofReal_re]

end
end NlsGge.ThirdConsultation.G6041S
