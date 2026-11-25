import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB14Cont
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB16LocAn

/-! # Track B: approved contracts 18 `l2Flow_analytic` and 19 `l2Flow_contDiff`

Statements copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056). Real Banach structures,
sup norm on `C([-T,T], L²)`.
* `l2Flow_time_analytic`: every time-`s` map is real-analytic on `L²` (local map `LF` of
  PdeB16LocAn on `[0,δ]`, iteration by the group law (contract 15) with mass conservation
  (contract 16), negative times by `l2Flow_neg` and the real-linear conjugation `cjL 2`);
* `pieceSum`: on `‖a‖ < M` the trajectory on `[-T,T]` is the telescoping sum
  `P₀ + Σₖ (Pₖ₊₁ - Qₖ₊₁)` of the clamped local trajectories `Pₖ a = LF (l2Flow cₖ a) ∘ proj_{[cₖ,cₖ+δ]}`
  and the constants `Qₖ a = l2Flow cₖ a`, `cₖ = -T + kδ`; each term is analytic in `a`;
* contract 18: `F u₀ = (t ↦ l2Flow t u₀)` agrees with the telescoping sum near every datum;
* contract 19: `AnalyticOnNhd.contDiff`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

open Filter Topology

theorem conjL2_eq_cjL (v : PhysicalL2) : conjL2 v = (cjL (μ := spatialMeasure) 2) v := rfl

namespace LocData

variable {M δ R Kd Cf : ℝ}

theorem time_analytic_local (D : LocData M δ R Kd Cf) {s : ℝ} (hs : s ∈ Set.Icc 0 δ) :
    AnalyticOnNhd ℝ (l2Flow s) (Metric.ball 0 M) := by
  intro a ha
  rw [mem_ball_zero_iff] at ha
  set ev : C(Set.Icc (0 : ℝ) δ, PhysicalL2) →L[ℝ] PhysicalL2 := LinearMap.mkContinuous
    { toFun := fun f => f ⟨s, hs⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by rw [one_mul]; exact ContinuousMap.norm_coe_le_norm f _) with hev
  have h : AnalyticAt ℝ (fun b => ev (D.LF b)) a :=
    AnalyticAt.comp (g := ev) (f := D.LF) (ev.analyticAt _) (D.LF_analytic ha)
  refine h.congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 ha)] with b hb
  rw [mem_ball_zero_iff] at hb
  exact D.LF_apply hb.le ⟨s, hs⟩

theorem time_analytic_nonneg (D : LocData M δ R Kd Cf) :
    ∀ n : ℕ, ∀ s ∈ Set.Icc 0 (n * δ), AnalyticOnNhd ℝ (l2Flow s) (Metric.ball 0 M) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    refine D.time_analytic_local ⟨hs.1, ?_⟩
    have := hs.2; simp only [Nat.cast_zero, zero_mul] at this; linarith [D.hδ]
  | succ n ih =>
    intro s hs
    rcases le_total s (n * δ) with h | h
    · exact ih s ⟨hs.1, h⟩
    · have hs' : s - n * δ ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith, by
        have := hs.2; push_cast at this; linarith⟩
      have hn : (n : ℝ) * δ ∈ Set.Icc 0 (n * δ) := ⟨by have := D.hδ.le; positivity, le_rfl⟩
      have hmaps : Set.MapsTo (l2Flow (n * δ)) (Metric.ball 0 M) (Metric.ball 0 M) := by
        intro a ha
        rw [mem_ball_zero_iff, l2Flow_norm]
        exact mem_ball_zero_iff.1 ha
      have hc := (D.time_analytic_local hs').comp (ih _ hn) hmaps
      have e : l2Flow (s - n * δ) ∘ l2Flow (n * δ) = l2Flow s := by
        funext a
        rw [Function.comp_apply, ← l2Flow_add, sub_add_cancel]
      rwa [e] at hc

theorem time_analytic_ball (D : LocData M δ R Kd Cf) (s : ℝ) :
    AnalyticOnNhd ℝ (l2Flow s) (Metric.ball 0 M) := by
  have pos : ∀ s : ℝ, 0 ≤ s → AnalyticOnNhd ℝ (l2Flow s) (Metric.ball 0 M) := by
    intro s hs
    obtain ⟨n, hn⟩ := exists_nat_ge (s / δ)
    rw [div_le_iff₀ D.hδ] at hn
    exact D.time_analytic_nonneg n s ⟨hs, hn⟩
  rcases le_total 0 s with h | h
  · exact pos s h
  · set cj : PhysicalL2 →L[ℝ] PhysicalL2 := cjL (μ := spatialMeasure) 2 with hcj
    have hmaps : Set.MapsTo cj (Metric.ball 0 M) (Metric.ball 0 M) := by
      intro a ha
      rw [mem_ball_zero_iff, hcj, ← conjL2_eq_cjL, norm_conjL2]
      exact mem_ball_zero_iff.1 ha
    have h1 := (pos (-s) (by linarith)).comp (cj.analyticOnNhd _) hmaps
    have h2 := (cj.analyticOnNhd Set.univ).comp h1 (Set.mapsTo_univ _ _)
    have e : cj ∘ (l2Flow (-s) ∘ cj) = l2Flow s := by
      funext a
      simp only [Function.comp_apply, hcj, ← conjL2_eq_cjL]
      rw [← l2Flow_neg, neg_neg]
    rwa [e] at h2

/-- The clamp `t ↦ proj_{[0,δ]}(t - c)` on `[-T,T]`. -/
def clampC (D : LocData M δ R Kd Cf) (T c : ℝ) : C(Set.Icc (-T) T, Set.Icc (0 : ℝ) δ) :=
  ⟨fun t => Set.projIcc 0 δ D.hδ.le ((t : ℝ) - c),
    continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)⟩

/-- Precomposition with the clamp, as a real continuous linear map. -/
def RC (D : LocData M δ R Kd Cf) (T c : ℝ) :
    C(Set.Icc (0 : ℝ) δ, PhysicalL2) →L[ℝ] C(Set.Icc (-T) T, PhysicalL2) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp (D.clampC T c)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun t => ContinuousMap.norm_coe_le_norm f _)

end LocData

theorem l2Flow_time_analytic (s : ℝ) : AnalyticOnNhd ℝ (l2Flow s) Set.univ := by
  intro a₀ _
  obtain ⟨δ, R, Kd, Cf, D⟩ := locData_exists (‖a₀‖ + 1)
  exact D.time_analytic_ball s a₀ (mem_ball_zero_iff.2 (by linarith))

/-- Constant trajectories, as a real continuous linear map. -/
def CC (T : ℝ) : PhysicalL2 →L[ℝ] C(Set.Icc (-T) T, PhysicalL2) :=
  LinearMap.mkContinuous
    { toFun := fun v => ContinuousMap.const _ v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun v => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg v)).2 fun _ => le_rfl)

/-! ### Telescoping -/

/-- Grid points `cₖ = -T + kδ`. -/
def cpt (T δ : ℝ) (k : ℕ) : ℝ := -T + k * δ

/-- `max(cₖ, min(t, cₖ + δ))`. -/
def phiK (T δ : ℝ) (k : ℕ) (t : ℝ) : ℝ := max 0 (min δ (t - cpt T δ k)) + cpt T δ k

/-- `max(c₀, min(t, c₀ + (m+1)δ))`. -/
def psiM (T δ : ℝ) (m : ℕ) (t : ℝ) : ℝ := max 0 (min ((m + 1) * δ) (t - cpt T δ 0)) + cpt T δ 0

theorem tele (T δ : ℝ) (hδ : 0 < δ) (a : PhysicalL2) (t : ℝ) (m : ℕ) :
    l2Flow (phiK T δ 0 t) a + ∑ k ∈ Finset.range m,
      (l2Flow (phiK T δ (k + 1) t) a - l2Flow (cpt T δ (k + 1)) a) = l2Flow (psiM T δ m t) a := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, phiK, psiM, Nat.cast_zero,
      zero_add, one_mul]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have hc : cpt T δ (m + 1) = cpt T δ 0 + (m + 1) * δ := by
      simp only [cpt]; push_cast; ring
    have hc2 : cpt T δ 0 = -T := by simp [cpt]
    rcases le_total (t - cpt T δ 0) ((m + 1) * δ) with h | h
    · have e1 : psiM T δ (m + 1) t = psiM T δ m t := by
        simp only [psiM]
        push_cast
        rw [min_eq_right h, min_eq_right (by nlinarith)]
      have e2 : phiK T δ (m + 1) t = cpt T δ (m + 1) := by
        simp only [phiK]
        rw [min_eq_right (by rw [hc]; linarith), max_eq_left (by rw [hc]; linarith), zero_add]
      rw [e1, e2, sub_self, add_zero]
    · have e1 : psiM T δ m t = cpt T δ (m + 1) := by
        simp only [psiM]
        rw [min_eq_left h, max_eq_right (by positivity), hc]
        ring
      have e2 : phiK T δ (m + 1) t = psiM T δ (m + 1) t := by
        simp only [phiK, psiM]
        rw [hc]
        push_cast
        have hmδ : 0 ≤ ((m : ℝ) + 1) * δ := by positivity
        rcases le_total (t - cpt T δ 0) ((m + 1 + 1) * δ) with h2 | h2
        · rw [min_eq_right (by linarith), min_eq_right h2, max_eq_right (by linarith),
            max_eq_right (by linarith)]
          ring
        · rw [min_eq_left (by linarith), min_eq_left h2, max_eq_right hδ.le,
            max_eq_right (by positivity)]
          ring
      rw [e1, e2]
      abel

theorem psiM_eq_self {T δ : ℝ} {m : ℕ} (hm : 2 * T ≤ (m + 1) * δ) {t : ℝ}
    (ht : t ∈ Set.Icc (-T) T) : psiM T δ m t = t := by
  have hc : cpt T δ 0 = -T := by simp [cpt]
  simp only [psiM, hc]
  rw [min_eq_right (by linarith [ht.1, ht.2]), max_eq_right (by linarith [ht.1])]
  ring

namespace LocData

variable {M δ R Kd Cf : ℝ}

/-- The telescoping sum of clamped local trajectories. -/
def pieceSum (D : LocData M δ R Kd Cf) (T : ℝ) (m : ℕ) (a : PhysicalL2) :
    C(Set.Icc (-T) T, PhysicalL2) :=
  D.RC T (cpt T δ 0) (D.LF (l2Flow (cpt T δ 0) a)) + ∑ k ∈ Finset.range m,
    (D.RC T (cpt T δ (k + 1)) (D.LF (l2Flow (cpt T δ (k + 1)) a)) - CC T (l2Flow (cpt T δ (k + 1)) a))

theorem piece_apply (D : LocData M δ R Kd Cf) (T : ℝ) (k : ℕ) {a : PhysicalL2} (ha : ‖a‖ ≤ M)
    (t : Set.Icc (-T) T) :
    D.RC T (cpt T δ k) (D.LF (l2Flow (cpt T δ k) a)) t = l2Flow (phiK T δ k t) a := by
  have hb : ‖l2Flow (cpt T δ k) a‖ ≤ M := by rw [l2Flow_norm]; exact ha
  change D.LF (l2Flow (cpt T δ k) a) (D.clampC T (cpt T δ k) t) = _
  rw [D.LF_apply hb, ← l2Flow_add]
  congr 1

theorem pieceSum_apply (D : LocData M δ R Kd Cf) (T : ℝ) (m : ℕ) {a : PhysicalL2}
    (ha : ‖a‖ ≤ M) (t : Set.Icc (-T) T) : D.pieceSum T m a t = l2Flow (psiM T δ m t) a := by
  rw [← tele T δ D.hδ a t m, pieceSum, ContinuousMap.add_apply, ContinuousMap.sum_apply,
    D.piece_apply T 0 ha t]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousMap.sub_apply, D.piece_apply T (k + 1) ha t]
  rfl

theorem pieceSum_analytic (D : LocData M δ R Kd Cf) (T : ℝ) (m : ℕ) {a₀ : PhysicalL2}
    (ha₀ : ‖a₀‖ < M) : AnalyticAt ℝ (D.pieceSum T m) a₀ := by
  have hP : ∀ k : ℕ, AnalyticAt ℝ (fun a => D.RC T (cpt T δ k) (D.LF (l2Flow (cpt T δ k) a))) a₀ := by
    intro k
    have h1 := l2Flow_time_analytic (cpt T δ k) a₀ (Set.mem_univ _)
    have h2 : AnalyticAt ℝ D.LF (l2Flow (cpt T δ k) a₀) :=
      D.LF_analytic (by rw [l2Flow_norm]; exact ha₀)
    have h3 := AnalyticAt.comp (g := D.LF) (f := l2Flow (cpt T δ k)) h2 h1
    exact AnalyticAt.comp (g := D.RC T (cpt T δ k)) (f := D.LF ∘ l2Flow (cpt T δ k))
      ((D.RC T _).analyticAt _) h3
  have hQ : ∀ k : ℕ, AnalyticAt ℝ (fun a => CC T (l2Flow (cpt T δ k) a)) a₀ := fun k =>
    AnalyticAt.comp (g := CC T) (f := l2Flow (cpt T δ k)) ((CC T).analyticAt _)
      (l2Flow_time_analytic (cpt T δ k) a₀ (Set.mem_univ _))
  have hS := Finset.analyticAt_sum (Finset.range m)
    (f := fun k a => D.RC T (cpt T δ (k + 1)) (D.LF (l2Flow (cpt T δ (k + 1)) a)) -
      CC T (l2Flow (cpt T δ (k + 1)) a)) (fun k _ => (hP (k + 1)).sub (hQ (k + 1)))
  have e : D.pieceSum T m = fun a => D.RC T (cpt T δ 0) (D.LF (l2Flow (cpt T δ 0) a)) +
      (∑ k ∈ Finset.range m, fun a => D.RC T (cpt T δ (k + 1)) (D.LF (l2Flow (cpt T δ (k + 1)) a)) -
        CC T (l2Flow (cpt T δ (k + 1)) a)) a := by
    funext a
    rw [pieceSum, Finset.sum_apply]
  rw [e]
  exact (hP 0).add hS

end LocData

/-! ### Approved contract 18 -/

theorem l2Flow_analytic (T : ℝ) :
    ∃ F : PhysicalL2 → C(Set.Icc (-T) T, PhysicalL2),
      AnalyticOnNhd ℝ F Set.univ ∧ ∀ u₀ (t : Set.Icc (-T) T), F u₀ t = l2Flow t u₀ := by
  refine ⟨fun u₀ => ⟨fun t => l2Flow t u₀, ((l2Flow_solution u₀).1.1).comp continuous_subtype_val⟩,
    ?_, fun u₀ t => rfl⟩
  intro a₀ _
  obtain ⟨δ, R, Kd, Cf, D⟩ := locData_exists (‖a₀‖ + 1)
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * T / δ)
  rw [div_le_iff₀ D.hδ] at hm
  have hm' : 2 * T ≤ (m + 1) * δ := by linarith [D.hδ]
  have ha₀ : ‖a₀‖ < ‖a₀‖ + 1 := by linarith
  refine (D.pieceSum_analytic T m ha₀).congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 ha₀)] with a ha
  ext1 t
  rw [D.pieceSum_apply T m (mem_ball_zero_iff.1 ha).le t, psiM_eq_self hm' t.2]
  rfl

/-! ### Approved contract 19 -/

theorem l2Flow_contDiff (T : ℝ) :
    ∃ F : PhysicalL2 → C(Set.Icc (-T) T, PhysicalL2),
      ContDiff ℝ 1 F ∧ ∀ u₀ (t : Set.Icc (-T) T), F u₀ t = l2Flow t u₀ := by
  obtain ⟨F, hF, hFeq⟩ := l2Flow_analytic T
  exact ⟨F, hF.contDiff, hFeq⟩

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
