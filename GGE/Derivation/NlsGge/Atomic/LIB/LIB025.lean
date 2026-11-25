import NlsGge.Atomic.LIB.LIB024
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! LIB-025 private proof candidate 01 (step 3). Statement = LIB-025_COMMAND02:
`NlsGge.Atomic.LIB.extend_solution_of_compact_range`, with [CompleteSpace E] per the Banach
carrier of the LIB-024 prerequisite (WORK_PACKETS/LIB/LIB-025.md, "## Prerequisites").
Route: uniform Picard flow from a cluster point s0 of x at T⁻ (Mathlib, via FunSpace range),
uniqueness on (T-h, T) (LIB-024), and gluing at s0. -/

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped NNReal

namespace NlsGge.Atomic.LIB

namespace LIB025Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Picard flow with range: the proof of `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`
plus membership of the flow in the outer closed ball (`FunSpace.compProj_mem_closedBall`). -/
lemma picard_flow_mem [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ closedBall x₀ a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht => ⟨?_, α.compProj_mem_closedBall hf.mul_max_le⟩⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ ht' => α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- Uniform-in-start-time Picard flow for a time-independent field on a closed ball. -/
lemma uniform_flow [CompleteSpace E] {V : E → E} {p x : E} {a r L K : ℝ≥0}
    {tmin tmax s0 : ℝ} (hs : s0 ∈ Icc tmin tmax) (hb : ∀ u ∈ closedBall p (a : ℝ), ‖V u‖ ≤ (L : ℝ))
    (hl : LipschitzOnWith K V (closedBall p (a : ℝ)))
    (hm : (L : ℝ) * max (tmax - s0) (s0 - tmin) ≤ (a : ℝ) - (r : ℝ))
    (hx : x ∈ closedBall p (r : ℝ)) :
    ∃ w : ℝ → E, w s0 = x ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt w (V (w t)) (Icc tmin tmax) t ∧ w t ∈ closedBall p (a : ℝ) := by
  have hf := IsPicardLindelof.of_time_independent (t₀ := ⟨s0, hs⟩) hb hl hm
  obtain ⟨w, hw0, hw⟩ := picard_flow_mem hf hx
  exact ⟨w, hw0, hw⟩

/-- A compact set trapping `x` on `[0,T)` has a point `p` that is a cluster point of `x` at `T⁻`. -/
lemma exists_near_cluster {K : Set E} (hK : IsCompact K) {x : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hx : ∀ t ∈ Ico 0 T, x t ∈ K) :
    ∃ p ∈ K, ∀ δ > 0, ∀ ρ > 0, ∃ s, max 0 (T - δ) < s ∧ s < T ∧ dist (x s) p < ρ := by
  have hle : map x (𝓝[<] T) ≤ 𝓟 K := by
    rw [le_principal_iff]
    apply mem_map.2
    exact Filter.mem_of_superset (Ioo_mem_nhdsLT hT) (fun t ht => hx t ⟨ht.1.le, ht.2⟩)
  obtain ⟨p, hpK, hcl⟩ := hK.exists_clusterPt hle
  refine ⟨p, hpK, fun δ hδ ρ hρ => ?_⟩
  have hfreq : ∃ᶠ t in 𝓝[<] T, x t ∈ ball p ρ :=
    (mapClusterPt_iff_frequently (x := p) (F := 𝓝[<] T) (u := x)).1 hcl (ball p ρ)
      (ball_mem_nhds p hρ)
  have hmax : max 0 (T - δ) < T := max_lt hT (by linarith)
  have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo (max 0 (T - δ)) T := Ioo_mem_nhdsLT hmax
  obtain ⟨s, hs1, hs2⟩ := (hfreq.and_eventually hev).exists
  exact ⟨s, hs2.1, hs2.2, mem_ball.1 hs1⟩

end LIB025Aux

open LIB025Aux

/-- LIB-025 (candidate): a solution of a locally Lipschitz field on an open set, with range in a
compact subset of the domain on `[0,T)`, extends past `T`. -/
theorem extend_solution_of_compact_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set E} {V : E → E} (hU : IsOpen U) (hV : LocallyLipschitzOn U V)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {T : ℝ} (hT : 0 < T) (x : ℝ → E)
    (hsol : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (V (x t)) (Set.Ico 0 T) t)
    (hrange : ∀ t ∈ Set.Ico 0 T, x t ∈ K) :
    ∃ ε > (0 : ℝ), ∃ y : ℝ → E,
      (∀ t ∈ Set.Ico 0 (T + ε), HasDerivWithinAt y (V (y t)) (Set.Ico 0 (T + ε)) t) ∧
      Set.EqOn y x (Set.Ico 0 T) ∧
      ∀ t ∈ Set.Ico 0 (T + ε), y t ∈ U := by
  -- Step 0: bounds on V over K and a Lipschitz bound on x near T
  have hVc : ContinuousOn V U := hV.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hVc.mono hKU)
  set C0 : ℝ := max C 0 with hC0def
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hbd : ∀ t ∈ Ico 0 T, ‖V (x t)‖ ≤ C0 := fun t ht => (hC _ (hrange t ht)).trans (le_max_left _ _)
  have hxlip : ∀ s ∈ Ico 0 T, ∀ t ∈ Ico 0 T, ‖x t - x s‖ ≤ C0 * ‖t - s‖ := by
    intro s hs t ht
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hsol hbd (convex_Ico 0 T) hs ht
  -- Step 1: cluster point p of x at T⁻, and a Lipschitz ball around p
  obtain ⟨p, hpK, hnear⟩ := exists_near_cluster hK hT hrange
  have hpU : p ∈ U := hKU hpK
  obtain ⟨L0, t0, ht0, hLip0⟩ := hV hpU
  obtain ⟨u1, hu1, hu1t⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ht0
  obtain ⟨ε1, hε1, hball1⟩ := Metric.mem_nhds_iff.1 hu1
  obtain ⟨ε2, hε2, hball2⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hpU)
  set ρ : ℝ := min ε1 ε2 with hρdef
  have hρ : 0 < ρ := lt_min hε1 hε2
  have hballρ : ball p ρ ⊆ t0 := fun y hy =>
    hu1t ⟨hball1 (ball_subset_ball (min_le_left _ _) hy),
      hball2 (ball_subset_ball (min_le_right _ _) hy)⟩
  -- Step 2: radii and constants
  set aN : ℝ≥0 := Real.toNNReal (ρ / 2) with haN_def
  have haN : (aN : ℝ) = ρ / 2 := Real.coe_toNNReal _ (by linarith)
  set rN : ℝ≥0 := Real.toNNReal (ρ / 4) with hrN_def
  have hrN : (rN : ℝ) = ρ / 4 := Real.coe_toNNReal _ (by linarith)
  set Bd : ℝ := ‖V p‖ + (L0 : ℝ) * (ρ / 2) with hBd_def
  have hBd0 : 0 ≤ Bd :=
    add_nonneg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (by linarith))
  set LN : ℝ≥0 := Real.toNNReal Bd with hLN_def
  have hLN : (LN : ℝ) = Bd := Real.coe_toNNReal _ hBd0
  have hsubball : closedBall p (aN : ℝ) ⊆ ball p ρ :=
    closedBall_subset_ball (by rw [haN]; linarith)
  have hl : LipschitzOnWith L0 V (closedBall p (aN : ℝ)) := hLip0.mono (hsubball.trans hballρ)
  have hb : ∀ u ∈ closedBall p (aN : ℝ), ‖V u‖ ≤ (LN : ℝ) := by
    intro u hu
    have hu' : dist u p ≤ ρ / 2 := by
      have := mem_closedBall.1 hu
      rw [haN] at this
      exact this
    have hVu : dist (V u) (V p) ≤ (L0 : ℝ) * dist u p :=
      hl.dist_le_mul u hu p (mem_closedBall_self (by positivity))
    have htri : ‖V u‖ ≤ ‖V p‖ + ‖V u - V p‖ := by
      linarith [norm_sub_norm_le (V u) (V p)]
    rw [← dist_eq_norm] at htri
    have hLmul : (L0 : ℝ) * dist u p ≤ (L0 : ℝ) * (ρ / 2) :=
      mul_le_mul_of_nonneg_left hu' (by positivity)
    rw [hLN, hBd_def]
    linarith
  -- Step 3: time length h
  set h : ℝ := min T (min (ρ / (8 * (C0 + 1))) (ρ / (8 * (Bd + 1)))) with hh_def
  have hh0 : 0 < h := lt_min hT (lt_min (div_pos hρ (by linarith)) (div_pos hρ (by linarith)))
  have hhT : h ≤ T := min_le_left _ _
  have hhA : h ≤ ρ / (8 * (C0 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hhB : h ≤ ρ / (8 * (Bd + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hh1 : h * (8 * (C0 + 1)) ≤ ρ := (le_div_iff₀ (by linarith)).1 hhA
  have hh2 : h * (8 * (Bd + 1)) ≤ ρ := (le_div_iff₀ (by linarith)).1 hhB
  have hC0h : C0 * h ≤ ρ / 4 := by nlinarith
  have hBh : 2 * Bd * h ≤ ρ / 4 := by nlinarith
  -- Step 4: a start time s0 close to p, uniform Picard flow from x s0
  obtain ⟨s0, hs0a, hs0b, hs0d⟩ := hnear h hh0 (ρ / 4) (by linarith)
  have hs0pos : 0 < s0 := lt_of_le_of_lt (le_max_left _ _) hs0a
  have hTh : T - h < s0 := lt_of_le_of_lt (le_max_right _ _) hs0a
  have hs : s0 ∈ Icc (T - 2 * h) (T + h) := ⟨by linarith, by linarith⟩
  have hm : (LN : ℝ) * max ((T + h) - s0) (s0 - (T - 2 * h)) ≤ (aN : ℝ) - (rN : ℝ) := by
    rw [hLN, haN, hrN]
    have hmax : max ((T + h) - s0) (s0 - (T - 2 * h)) ≤ 2 * h :=
      max_le (by linarith) (by linarith)
    have hmul : Bd * max ((T + h) - s0) (s0 - (T - 2 * h)) ≤ Bd * (2 * h) :=
      mul_le_mul_of_nonneg_left hmax hBd0
    nlinarith
  have hxs0 : x s0 ∈ closedBall p (rN : ℝ) := by
    rw [hrN]
    exact mem_closedBall.2 hs0d.le
  obtain ⟨w, hw0, hw⟩ := uniform_flow (V := V) (p := p) (x := x s0) (a := aN) (r := rN)
    (L := LN) (K := L0) hs hb hl hm hxs0
  -- Step 5: x and w agree on (T-h, T) by LIB-024 uniqueness
  have hsolx : ∀ t ∈ Ioo (T - h) T, HasDerivAt x (V (x t)) t ∧ x t ∈ closedBall p (aN : ℝ) := by
    intro t ht
    have ht0' : 0 < t := by linarith [ht.1]
    have hd : HasDerivAt x (V (x t)) t :=
      (hsol t ⟨ht0'.le, ht.2⟩).hasDerivAt (Ico_mem_nhds ht0' ht.2)
    refine ⟨hd, ?_⟩
    have hdiff : ‖t - s0‖ ≤ h := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hlip := hxlip s0 ⟨hs0pos.le, hs0b⟩ t ⟨ht0'.le, ht.2⟩
    have hstep : ‖x t - x s0‖ ≤ ρ / 4 :=
      hlip.trans ((mul_le_mul_of_nonneg_left hdiff hC0).trans hC0h)
    rw [mem_closedBall, haN]
    have htri := dist_triangle (x t) (x s0) p
    have hd2 : dist (x t) (x s0) = ‖x t - x s0‖ := dist_eq_norm _ _
    linarith [hs0d, hstep, htri, hd2]
  have hsolw : ∀ t ∈ Ioo (T - h) T, HasDerivAt w (V (w t)) t ∧ w t ∈ closedBall p (aN : ℝ) := by
    intro t ht
    have hI : t ∈ Icc (T - 2 * h) (T + h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hd, hmem⟩ := hw t hI
    refine ⟨?_, hmem⟩
    exact hd.hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  have hs0I : s0 ∈ Ioo (T - h) T := ⟨hTh, hs0b⟩
  have huniq : Set.EqOn x w (Ioo (T - h) T) :=
    NlsGge.Atomic.LIB024.solution_unique_in_lipschitz_region hl hs0I hsolx hsolw hw0.symm
  have hρU : ball p ρ ⊆ U := (ball_subset_ball (min_le_right ε1 ε2)).trans hball2
  have hcballU : closedBall p (aN : ℝ) ⊆ U := hsubball.trans hρU
  -- Step 6: glue at s0
  obtain ⟨y, hy⟩ : ∃ y : ℝ → E, y = fun t => if t < s0 then x t else w t := ⟨_, rfl⟩
  refine ⟨h, hh0, y, ?_, ?_, ?_⟩
  · intro t hmem
    rcases lt_trichotomy t s0 with hts | hts | hts
    · -- before s0: y = x locally
      have htT : t < T := by linarith
      have hx' : HasDerivWithinAt x (V (x t)) (Ico 0 (T + h)) t := by
        apply (hsol t ⟨hmem.1, htT⟩).mono_of_mem_nhdsWithin
        exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ico 0 (T + h)) (Iio_mem_nhds htT))
          (fun u hu => ⟨hu.1.1, hu.2⟩)
      have hev : y =ᶠ[𝓝[Ico 0 (T + h)] t] x :=
        eventually_nhdsWithin_of_eventually_nhds
          ((eventually_lt_nhds hts).mono fun u hu => by simp [hy, hu])
      have hyt : y t = x t := by simp [hy, hts]
      rw [hyt]
      exact hx'.congr_of_eventuallyEq hev hyt
    · -- at s0: two-sided union of the left (x) and right (w) pieces
      rw [hts]
      have hxd : HasDerivAt x (V (x s0)) s0 :=
        (hsol s0 ⟨hs0pos.le, hs0b⟩).hasDerivAt (Ico_mem_nhds hs0pos hs0b)
      have hleft : HasDerivWithinAt y (V (x s0)) (Iic s0) s0 := by
        refine (hxd.hasDerivWithinAt).congr (fun u hu => ?_) ?_
        · rcases lt_or_eq_of_le (Set.mem_Iic.1 hu) with h' | h'
          · simp [hy, h']
          · simp [hy, h', hw0]
        · simp [hy, hw0]
      have hright : HasDerivWithinAt y (V (x s0)) (Ici s0) s0 := by
        have h1 : HasDerivAt w (V (w s0)) s0 :=
          (hw s0 hs).1.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))
        have h3 : HasDerivWithinAt y (V (w s0)) (Ici s0) s0 :=
          (h1.hasDerivWithinAt).congr (fun u hu => by simp [hy, not_lt.2 (Set.mem_Ici.1 hu)])
            (by simp [hy])
        rw [hw0] at h3
        exact h3
      have hU2 : HasDerivWithinAt y (V (x s0)) (Iic s0 ∪ Ici s0) s0 := hleft.union hright
      have hsub : Ico 0 (T + h) ⊆ Iic s0 ∪ Ici s0 := fun u _ => by
        rcases le_total u s0 with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      have hyv : y s0 = x s0 := by simp [hy, hw0]
      rw [hyv]
      exact hU2.mono hsub
    · -- after s0: y = w locally
      have htT : t < T + h := hmem.2
      have hd : HasDerivAt w (V (w t)) t :=
        (hw t ⟨by linarith, htT.le⟩).1.hasDerivAt (Icc_mem_nhds (by linarith) htT)
      have hev : y =ᶠ[𝓝 t] w :=
        (eventually_gt_nhds hts).mono fun u hu => by simp [hy, not_lt.2 hu.le]
      have hyt : y t = w t := by simp [hy, not_lt.2 hts.le]
      rw [hyt]
      exact (hd.congr_of_eventuallyEq hev).hasDerivWithinAt
  · intro u hu
    by_cases hus : u < s0
    · simp [hy, hus]
    · push_neg at hus
      have hwu : w u = x u := by
        rcases eq_or_lt_of_le hus with h' | h'
        · rw [← h']
          exact hw0
        · exact (huniq ⟨lt_trans hTh h', hu.2⟩).symm
      simp [hy, not_lt.2 hus, hwu]
  · intro t hmem
    by_cases hts : t < s0
    · have hxK : x t ∈ K := hrange t ⟨hmem.1, by linarith⟩
      have hyt : y t = x t := by simp [hy, hts]
      rw [hyt]
      exact hKU hxK
    · have hyt : y t = w t := by simp [hy, hts]
      rw [hyt]
      exact hcballU ((hw t ⟨by linarith, hmem.2.le⟩).2)

end NlsGge.Atomic.LIB
