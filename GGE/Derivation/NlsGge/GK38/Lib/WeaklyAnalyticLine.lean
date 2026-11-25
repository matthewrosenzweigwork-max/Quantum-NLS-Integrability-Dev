import Mathlib

/-!
# One-variable inputs for weak analyticity (library piece L3a of campaign E01, part 1)

Local re-proof from Mathlib (E01-D8).  Two facts about maps `g : ℂ → G` into a complex Banach space:

* `norm_sub_sub_deriv_le`: the second order Cauchy bound
  `‖g (z₀ + s) - g z₀ - s • g' z₀‖ ≤ 8 M ‖s‖² / δ²` for `g` differentiable and bounded by `M` on
  `closedBall z₀ δ`;
* `differentiableAt_of_forall_dual` (the Dunford step): if `L ∘ g` is differentiable for every
  continuous linear functional `L` and `g` is bounded near `z₀`, then `g` is differentiable at `z₀`.
-/

set_option autoImplicit false

open Metric Set Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

section SecondOrder

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Cauchy bound for the derivative: if `g` is differentiable on `closedBall c R` and bounded by `M`
there, then `‖g' c‖ ≤ M / R`. -/
theorem norm_deriv_le_of_closedBall {g : ℂ → G} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hd : ∀ w, ‖w - c‖ ≤ R → DifferentiableAt ℂ g w) (hb : ∀ w, ‖w - c‖ ≤ R → ‖g w‖ ≤ M) :
    ‖deriv g c‖ ≤ M / R := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR ?_ ?_
  · refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro w hw
    exact (hd w (by simpa [dist_eq_norm] using hw)).differentiableWithinAt
  · intro w hw
    exact hb w (by simp [mem_sphere_iff_norm.mp hw])

/-- Second order Cauchy bound. -/
theorem norm_sub_sub_deriv_le {g : ℂ → G} {c : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hd : ∀ w, ‖w - c‖ ≤ δ → DifferentiableAt ℂ g w) (hb : ∀ w, ‖w - c‖ ≤ δ → ‖g w‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ δ / 4) :
    ‖g (c + s) - g c - s • deriv g c‖ ≤ 8 * M * ‖s‖ ^ 2 / δ ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb c (by simp [hδ.le]))
  -- first derivative bound on `closedBall c (δ/2)`
  have h1 : ∀ y, ‖y - c‖ ≤ δ / 2 → ‖deriv g y‖ ≤ M / (δ / 2) := by
    intro y hy
    refine norm_deriv_le_of_closedBall (by positivity) ?_ ?_
    · intro w hw
      exact hd w (by
        calc ‖w - c‖ = ‖(w - y) + (y - c)‖ := by congr 1; ring
          _ ≤ ‖w - y‖ + ‖y - c‖ := norm_add_le _ _
          _ ≤ δ := by linarith)
    · intro w hw
      exact hb w (by
        calc ‖w - c‖ = ‖(w - y) + (y - c)‖ := by congr 1; ring
          _ ≤ ‖w - y‖ + ‖y - c‖ := norm_add_le _ _
          _ ≤ δ := by linarith)
  -- differentiability of `deriv g` on the open ball
  have hdo : DifferentiableOn ℂ g (ball c δ) := fun w hw =>
    (hd w (mem_ball_iff_norm.mp hw).le).differentiableWithinAt
  have han : AnalyticOnNhd ℂ g (ball c δ) := hdo.analyticOnNhd isOpen_ball
  have hdd : ∀ y, ‖y - c‖ < δ → DifferentiableAt ℂ (deriv g) y := fun y hy =>
    (han y (by simpa [dist_eq_norm] using hy)).deriv.differentiableAt
  -- second derivative bound
  have h2 : ∀ w, ‖w - c‖ ≤ δ / 4 → ‖deriv (deriv g) w‖ ≤ (M / (δ / 2)) / (δ / 4) := by
    intro w hw
    refine norm_deriv_le_of_closedBall (by positivity) ?_ ?_
    · intro y hy
      exact hdd y (by
        calc ‖y - c‖ = ‖(y - w) + (w - c)‖ := by congr 1; ring
          _ ≤ ‖y - w‖ + ‖w - c‖ := norm_add_le _ _
          _ < δ := by linarith)
    · intro y hy
      refine h1 y ?_
      calc ‖y - c‖ = ‖(y - w) + (w - c)‖ := by congr 1; ring
          _ ≤ ‖y - w‖ + ‖w - c‖ := norm_add_le _ _
          _ ≤ δ / 2 := by linarith
  set K : ℝ := (M / (δ / 2)) / (δ / 4) with hK
  have hKnn : 0 ≤ K := by positivity
  -- Taylor remainder via two applications of the mean value inequality
  have hball : Convex ℝ (closedBall c ‖s‖) := convex_closedBall c ‖s‖
  have hsub : closedBall c ‖s‖ ⊆ closedBall c (δ / 4) := closedBall_subset_closedBall hs
  have key : ∀ y ∈ closedBall c ‖s‖,
      ‖deriv g y - deriv g c‖ ≤ K * ‖s‖ := by
    intro y hy
    have hyc : ‖y - c‖ ≤ ‖s‖ := by simpa [dist_eq_norm] using hy
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv g) (s := closedBall c ‖s‖)
      (C := K)
      (fun z hz => hdd z (by
        have : ‖z - c‖ ≤ ‖s‖ := by simpa [dist_eq_norm] using hz
        linarith))
      (fun z hz => h2 z (by
        have : ‖z - c‖ ≤ ‖s‖ := by simpa [dist_eq_norm] using hz
        linarith)) hball (mem_closedBall_self (norm_nonneg s)) hy
    calc ‖deriv g y - deriv g c‖ ≤ K * ‖y - c‖ := by simpa using this
      _ ≤ K * ‖s‖ := by gcongr
  have hψ : ∀ z ∈ closedBall c ‖s‖, HasDerivAt (fun y => g y - y • deriv g c)
      (deriv g z - deriv g c) z := by
    intro z hz
    have hz' : ‖z - c‖ ≤ ‖s‖ := by simpa [dist_eq_norm] using hz
    have hg := (hd z (by linarith [hs, hδ])).hasDerivAt
    have : HasDerivAt (fun y : ℂ => y • deriv g c) (deriv g c) z := by
      simpa using (hasDerivAt_id z).smul_const (deriv g c)
    exact hg.sub this
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => g y - y • deriv g c) (f' := fun z => deriv g z - deriv g c)
    (s := closedBall c ‖s‖) (C := K * ‖s‖)
    (fun z hz => (hψ z hz).hasDerivWithinAt) (fun z hz => key z hz) hball
    (mem_closedBall_self (norm_nonneg s)) (y := c + s) (by simp)
  have e : g (c + s) - (c + s) • deriv g c - (g c - c • deriv g c)
      = g (c + s) - g c - s • deriv g c := by
    rw [add_smul]; abel
  simp only [e, add_sub_cancel_left] at this
  calc _ ≤ K * ‖s‖ * ‖s‖ := this
    _ = 8 * M * ‖s‖ ^ 2 / δ ^ 2 := by rw [hK]; field_simp; ring

end SecondOrder

section Dunford

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Dunford step.**  A bounded map `g : ℂ → F` all of whose scalarizations `L ∘ g`,
`L ∈ F →L[ℂ] ℂ`, are differentiable near `z₀` is differentiable at `z₀`. -/
theorem differentiableAt_of_forall_dual {g : ℂ → F} {z₀ : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hd : ∀ L : F →L[ℂ] ℂ, ∀ w, ‖w - z₀‖ < δ → DifferentiableAt ℂ (fun t => L (g t)) w)
    (hb : ∀ w, ‖w - z₀‖ < δ → ‖g w‖ ≤ M) : DifferentiableAt ℂ g z₀ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb z₀ (by simpa using hδ))
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  -- scalar second order bound
  have hsc : ∀ (L : F →L[ℂ] ℂ) (s : ℂ), ‖s‖ ≤ δ' / 4 →
      ‖L (g (z₀ + s)) - L (g z₀) - s * deriv (fun t => L (g t)) z₀‖
        ≤ 8 * (M * ‖L‖) * ‖s‖ ^ 2 / δ' ^ 2 := by
    intro L s hs
    have := norm_sub_sub_deriv_le (g := fun t => L (g t)) (c := z₀) (δ := δ') (M := M * ‖L‖)
      hδ'0 (fun w hw => hd L w (by linarith [hw, hδ'])) (fun w hw => by
        calc ‖L (g w)‖ ≤ ‖L‖ * ‖g w‖ := L.le_opNorm _
          _ ≤ ‖L‖ * M := by gcongr; exact hb w (by linarith [hw, hδ'])
          _ = M * ‖L‖ := mul_comm _ _) hs
    simpa [smul_eq_mul] using this
  set C : ℝ := 8 * M / δ' ^ 2 with hC
  have hCnn : 0 ≤ C := by positivity
  -- difference quotients
  set q : ℂ → F := fun s => s⁻¹ • (g (z₀ + s) - g z₀) with hq
  have hqq : ∀ s t : ℂ, s ≠ 0 → t ≠ 0 → ‖s‖ ≤ δ' / 4 → ‖t‖ ≤ δ' / 4 →
      ‖q s - q t‖ ≤ C * (‖s‖ + ‖t‖) := by
    intro s t hs0 ht0 hs ht
    by_cases hz : q s - q t = 0
    · rw [hz, norm_zero]; positivity
    obtain ⟨L, hL1, hLx⟩ := exists_dual_vector ℂ (q s - q t) (norm_ne_zero_iff.mpr hz)
    set a := deriv (fun t => L (g t)) z₀
    have hLq : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ δ' / 4 → ‖L (q u) - a‖ ≤ C * ‖u‖ := by
      intro u hu0 hu
      have h := hsc L u hu
      have e : L (q u) - a = u⁻¹ * (L (g (z₀ + u)) - L (g z₀) - u * a) := by
        simp only [hq, map_smul, map_sub, smul_eq_mul]; field_simp
      rw [e, norm_mul, norm_inv]
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      calc ‖u‖⁻¹ * ‖L (g (z₀ + u)) - L (g z₀) - u * a‖
          ≤ ‖u‖⁻¹ * (8 * (M * ‖L‖) * ‖u‖ ^ 2 / δ' ^ 2) := by gcongr
        _ = C * ‖L‖ * ‖u‖ := by rw [hC]; field_simp
        _ ≤ C * ‖u‖ := by rw [hL1]; simp
    have : (‖q s - q t‖ : ℂ) = L (q s - q t) := hLx.symm
    have h2 : ‖q s - q t‖ = ‖L (q s) - L (q t)‖ := by
      rw [← map_sub]
      have := congrArg (‖·‖) hLx
      simpa using this.symm
    rw [h2]
    calc ‖L (q s) - L (q t)‖ = ‖(L (q s) - a) - (L (q t) - a)‖ := by congr 1; ring
      _ ≤ ‖L (q s) - a‖ + ‖L (q t) - a‖ := norm_sub_le _ _
      _ ≤ C * ‖s‖ + C * ‖t‖ := add_le_add (hLq s hs0 hs) (hLq t ht0 ht)
      _ = C * (‖s‖ + ‖t‖) := by ring
  -- limit along a sequence
  set sq : ℕ → ℂ := fun n => ((δ' / 4) / ((n : ℝ) + 1) : ℝ) with hsq
  have hsq0 : ∀ n, sq n ≠ 0 := fun n => by
    simp only [hsq]; norm_cast; positivity
  have hsqn : ∀ n, ‖sq n‖ = (δ' / 4) / ((n : ℝ) + 1) := fun n => by
    simp only [hsq, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (by positivity)
  have hsqle : ∀ n, ‖sq n‖ ≤ δ' / 4 := fun n => by
    rw [hsqn]; apply div_le_self (by positivity); linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hcau : CauchySeq (fun n => q (sq n)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 * C * (δ' / 4) + 1) / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine (hqq _ _ (hsq0 n) (hsq0 N) (hsqle n) (hsqle N)).trans_lt ?_
    have hN1 : (0:ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : ‖sq n‖ ≤ ‖sq N‖ := by
      rw [hsqn, hsqn]
      apply div_le_div_of_nonneg_left (by positivity) hN1
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have : C * (‖sq n‖ + ‖sq N‖) ≤ 2 * C * ‖sq N‖ := by nlinarith
    refine this.trans_lt ?_
    rw [hsqn]
    have hε' : (2 * C * (δ' / 4) + 1) / ε < N := hN
    rw [div_lt_iff₀ hε] at hε'
    calc 2 * C * ((δ' / 4) / ((N : ℝ) + 1)) = (2 * C * (δ' / 4)) / ((N : ℝ) + 1) := by ring
      _ < ε := by rw [div_lt_iff₀ hN1]; nlinarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau
  -- bound `‖q s - a‖ ≤ C ‖s‖`
  have hqa : ∀ s : ℂ, s ≠ 0 → ‖s‖ ≤ δ' / 4 → ‖q s - a‖ ≤ C * ‖s‖ := by
    intro s hs0 hs
    have hlim : Tendsto (fun n => ‖q s - q (sq n)‖) atTop (𝓝 ‖q s - a‖) :=
      (tendsto_const_nhds.sub ha).norm
    have hb' : ∀ n, ‖q s - q (sq n)‖ ≤ C * (‖s‖ + ‖sq n‖) := fun n =>
      hqq _ _ hs0 (hsq0 n) hs (hsqle n)
    have hlim2 : Tendsto (fun n => C * (‖s‖ + ‖sq n‖)) atTop (𝓝 (C * (‖s‖ + 0))) := by
      refine tendsto_const_nhds.mul (tendsto_const_nhds.add ?_)
      have : Tendsto (fun n : ℕ => (δ' / 4) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (δ' / 4) |>.comp tendsto_id |> fun h => by
          simpa using (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add
            tendsto_const_nhds : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop))
      simpa [hsqn] using this
    have := le_of_tendsto_of_tendsto hlim hlim2 (Eventually.of_forall hb')
    simpa using this
  -- conclude `HasDerivAt`
  refine (HasDerivAt.differentiableAt (f' := a) ?_)
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hpos : 0 < min (δ' / 4) (ε / (C + 1)) := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with s hs
  rw [mem_ball_zero_iff] at hs
  by_cases hs0 : s = 0
  · subst hs0; simp
  have hs1 : ‖s‖ ≤ δ' / 4 := (lt_of_lt_of_le hs (min_le_left _ _)).le
  have hs2 : ‖s‖ < ε / (C + 1) := lt_of_lt_of_le hs (min_le_right _ _)
  have e : g (z₀ + s) - g z₀ - s • a = s • (q s - a) := by
    simp only [hq, smul_sub, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  rw [e, norm_smul]
  have := hqa s hs0 hs1
  calc ‖s‖ * ‖q s - a‖ ≤ ‖s‖ * (C * ‖s‖) := by gcongr
    _ = (C * ‖s‖) * ‖s‖ := by ring
    _ ≤ ε * ‖s‖ := by
      gcongr
      have hC1 : (0:ℝ) < C + 1 := by positivity
      have : ‖s‖ * (C + 1) < ε := by rwa [lt_div_iff₀ hC1] at hs2
      nlinarith [norm_nonneg s]

end Dunford

end

end NlsGge.GK38.Lib
