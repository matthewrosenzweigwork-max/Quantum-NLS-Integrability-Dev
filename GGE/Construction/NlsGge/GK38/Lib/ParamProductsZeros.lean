import NlsGge.GK38.Lib.ParamProductsCore

/-!
# L4c, part 2a (zeros): zero set and order of a symmetric product of analytic factors

For a single sequence `f : ℤ → ℂ` with `Σ ‖pairDev f m‖ < ∞`:
* `{n | f n = 0}` is finite and `∏'[symmetricIcc ℤ] f = 0 ↔ ∃ n, f n = 0`;
* for a family `G : ℤ → ℂ → ℂ` of analytic factors on an open `V ⊆ ℂ` with a locally summable
  majorant of the paired deviations: the product is analytic on `V` and its order at `w ∈ V` is
  `∑ᶠ m, analyticOrderAt (G m) w` (finitely many nonzero terms), i.e. zeros counted with the
  multiplicity of the factors.  For `G m z = (σ_m - z)/π_m` this is `analyticOrderAt_entProd`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### One sequence -/

theorem exists_pairDev_lt_one {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ‖pairDev f m‖ < 1 :=
  eventually_atTop.mp (h.tendsto_atTop_zero.eventually (gt_mem_nhds one_pos))

/-- If the paired deviations are `< 1` from `M` on, no factor with `|n| > M` vanishes. -/
theorem ne_zero_of_pairDev_lt_one {f : ℤ → ℂ} {M : ℕ} (hM : ∀ m : ℕ, M ≤ m → ‖pairDev f m‖ < 1)
    {n : ℤ} (hn : (M : ℤ) < n.natAbs) : f n ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n.natAbs = k + 1 := ⟨n.natAbs - 1, by omega⟩
  have hkM : M ≤ k := by omega
  have hq := hM k hkM
  have hn' : n = (k : ℤ) + 1 ∨ n = -((k : ℤ) + 1) := by omega
  have hpd : pairDev f k = -1 := by
    unfold pairDev
    rcases hn' with rfl | rfl
    · rw [h0]; ring
    · rw [h0]; ring
  rw [hpd] at hq
  simp at hq

theorem finite_zeros_of_summable_pairDev {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) :
    {n : ℤ | f n = 0}.Finite := by
  obtain ⟨M, hM⟩ := exists_pairDev_lt_one h
  refine (Finset.Icc (-(M : ℤ)) M).finite_toSet.subset fun n hn => ?_
  by_contra hnot
  have : (M : ℤ) < n.natAbs := by
    simp only [Finset.coe_Icc, Set.mem_Icc] at hnot
    omega
  exact ne_zero_of_pairDev_lt_one hM this hn

theorem tprod_tail_ne_zero {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) {M : ℕ}
    (hM : ∀ m : ℕ, M ≤ m → ‖pairDev f m‖ < 1) :
    ∏' m : ℕ, (1 + pairDev f (m + M)) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun m : ℕ => pairDev f (m + M)) (fun i => ?_)
    ((summable_nat_add_iff M).mpr h)
  intro h0
  have h1 : pairDev f (i + M) = -1 := by linear_combination h0
  have := hM (i + M) (by omega)
  rw [h1] at this
  simp at this

/-- **Zero criterion.**  The symmetric product vanishes iff a factor vanishes. -/
theorem tprod_symm_eq_zero_iff {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) :
    ∏'[symmetricIcc ℤ] m, f m = 0 ↔ ∃ n, f n = 0 := by
  constructor
  · intro h0
    by_contra hne
    push Not at hne
    rw [tprod_symm_eq_mul_tprod_pairDev h] at h0
    refine mul_ne_zero (hne 0) ?_ h0
    refine tprod_one_add_ne_zero_of_summable (f := pairDev f) (fun i => ?_) h
    rw [one_add_pairDev]
    exact mul_ne_zero (hne _) (hne _)
  · rintro ⟨n, hn⟩
    rw [tprod_symm_eq_prod_mul_tail h n.natAbs]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := n) ?_ hn) _
    simp only [Finset.mem_Icc]
    omega

/-! ### Orders -/

theorem analyticOrderAt_finset_prod_general {G : ℤ → ℂ → ℂ} {w : ℂ}
    (hG : ∀ n, AnalyticAt ℂ (G n) w) (S : Finset ℤ) :
    analyticOrderAt (fun z => ∏ n ∈ S, G n z) w = ∑ n ∈ S, analyticOrderAt (G n) w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [analyticOrderAt_eq_zero]
    right
    simp
  | insert a S ha ih =>
    have e : (fun z => ∏ n ∈ insert a S, G n z) = (G a) * (fun z => ∏ n ∈ S, G n z) := by
      funext z
      simp [Finset.prod_insert ha]
    have hS : AnalyticAt ℂ (fun z => ∏ n ∈ S, G n z) w :=
      Finset.analyticAt_fun_prod S fun n _ => hG n
    rw [e, analyticOrderAt_mul (hG a) hS, ih, Finset.sum_insert ha]

/-- **Zero set and order of a symmetric product (one complex variable).**  Let `G m` be analytic on
an open `V ⊆ ℂ` and the paired deviations have a locally (in `V`) summable majorant.  Then for
`w ∈ V`: the product is analytic at `w`; only finitely many factors vanish at `w`; and
`analyticOrderAt (∏) w = ∑ᶠ m, analyticOrderAt (G m) w`. -/
theorem analyticOrderAt_symm_tprod {V : Set ℂ} (hV : IsOpen V) {G : ℤ → ℂ → ℂ}
    (hG : ∀ m, AnalyticOnNhd ℂ (G m) V)
    (hloc : ∀ w ∈ V, ∃ ρ > 0, ∃ u : ℕ → ℝ, Summable u ∧ ∀ z ∈ ball w ρ, z ∈ V →
      ∀ m, ‖pairDev (fun n => G n z) m‖ ≤ u m)
    {w : ℂ} (hw : w ∈ V) :
    AnalyticAt ℂ (fun z => ∏'[symmetricIcc ℤ] m : ℤ, G m z) w ∧ {m : ℤ | G m w = 0}.Finite ∧
      analyticOrderAt (fun z => ∏'[symmetricIcc ℤ] m : ℤ, G m z) w
        = ∑ᶠ m : ℤ, analyticOrderAt (G m) w := by
  obtain ⟨ρ, hρ, u, hu, hb⟩ := hloc w hw
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hV w hw
  set r : ℝ := min ρ ρ' with hr
  have hrpos : 0 < r := lt_min hρ hρ'
  have hKV : ball w r ⊆ V := (ball_subset_ball (min_le_right _ _)).trans hball
  have hGd : ∀ m, DifferentiableOn ℂ (G m) (ball w r) := fun m z hz =>
    ((hG m) z (hKV hz)).differentiableAt.differentiableWithinAt
  have hbK : ∀ z ∈ ball w r, ∀ m, ‖pairDev (fun n => G n z) m‖ ≤ u m := fun z hz m =>
    hb z (ball_subset_ball (min_le_left _ _) hz) (hKV hz) m
  have hKn : ball w r ∈ 𝓝 w := ball_mem_nhds w hrpos
  have hsum : ∀ z ∈ ball w r, Summable fun m : ℕ => ‖pairDev (fun n => G n z) m‖ := fun z hz =>
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (hbK z hz)
  have hPan : AnalyticAt ℂ (fun z => ∏'[symmetricIcc ℤ] m : ℤ, G m z) w :=
    (differentiableOn_symm_tprod hGd hu hbK).analyticAt hKn
  obtain ⟨M, hM⟩ := exists_pairDev_lt_one (hsum w (mem_ball_self hrpos))
  refine ⟨hPan, finite_zeros_of_summable_pairDev (hsum w (mem_ball_self hrpos)), ?_⟩
  have hTan : AnalyticAt ℂ (fun z => ∏' m : ℕ, (1 + pairDev (fun n => G n z) (m + M))) w :=
    (differentiableOn_pairTail hGd hu hbK M).analyticAt hKn
  have hTne := tprod_tail_ne_zero (hsum w (mem_ball_self hrpos)) hM
  have hFan : AnalyticAt ℂ (fun z => ∏ n ∈ Finset.Icc (-(M : ℤ)) M, G n z) w :=
    Finset.analyticAt_fun_prod _ fun n _ => (hG n) w hw
  have hev : (fun z => ∏'[symmetricIcc ℤ] m : ℤ, G m z)
      =ᶠ[𝓝 w] (fun z => ∏ n ∈ Finset.Icc (-(M : ℤ)) M, G n z)
        * (fun z => ∏' m : ℕ, (1 + pairDev (fun n => G n z) (m + M))) := by
    filter_upwards [hKn] with z hz
    exact tprod_symm_eq_prod_mul_tail (hsum z hz) M
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hFan hTan,
    hTan.analyticOrderAt_eq_zero.mpr hTne, add_zero,
    analyticOrderAt_finset_prod_general (fun n => (hG n) w hw)]
  symm
  refine finsum_eq_sum_of_support_subset _ ?_
  intro n hn
  by_contra hnot
  have hlt : (M : ℤ) < n.natAbs := by
    simp only [Finset.coe_Icc, Set.mem_Icc] at hnot
    omega
  have hne := ne_zero_of_pairDev_lt_one hM hlt
  exact hn (((hG n) w hw).analyticOrderAt_eq_zero.mpr hne)

/-- Zero set (one complex variable): `∏ G m z = 0` iff some `G m z = 0`, for `z ∈ V`. -/
theorem symm_tprod_eq_zero_iff {V : Set ℂ} {G : ℤ → ℂ → ℂ}
    (hloc : ∀ w ∈ V, ∃ ρ > 0, ∃ u : ℕ → ℝ, Summable u ∧ ∀ z ∈ ball w ρ, z ∈ V →
      ∀ m, ‖pairDev (fun n => G n z) m‖ ≤ u m)
    {w : ℂ} (hw : w ∈ V) :
    ∏'[symmetricIcc ℤ] m : ℤ, G m w = 0 ↔ ∃ m, G m w = 0 := by
  obtain ⟨ρ, hρ, u, hu, hb⟩ := hloc w hw
  exact tprod_symm_eq_zero_iff (hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (hb w (mem_ball_self hρ) hw))

end

end NlsGge.GK38.Lib
