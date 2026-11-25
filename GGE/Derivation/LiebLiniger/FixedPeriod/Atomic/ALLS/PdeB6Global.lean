import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Glue

/-! # Track B, package 3: global existence and uniqueness of `L⁴` Duhamel solutions

`IsDuhSol u` is the approved `IsL2NLSSolution u` without its `IsDistributionalNLS` component:
continuity, an `L⁴_loc` spacetime representative and the approved `H⁻¹` Duhamel identity
(`IsHm1Duhamel`). Proved here:
* `isDuhSol_of_massHyp` / `massHyp_of_isDuhSol`: global ↔ interval solutions on all `[-mδ, mδ]`;
* `isDuhSol_rev`: time reversal;
* `duh_exists`: every `L²` datum has a global `IsDuhSol` trajectory, with conserved `L²` norm
  (stepping with the uniform lifespan `δ(‖u₀‖)` of `local_massHyp_exists`, mass conservation,
  gluing; recursive extension and consistent limit);
* `duh_unique`: two `IsDuhSol` trajectories with the same datum coincide (forward argument of
  `PdeB5Forward`, backward by time reversal).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section

theorem ite_t {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_f {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- `IsL2NLSSolution` without the distributional component. -/
def IsDuhSol (u : ℝ → PhysicalL2) : Prop :=
  Continuous u ∧ ∃ U, IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsHm1Duhamel u U

theorem intervalIntegrable_intG_loc {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) (n : ℤ)
    (s t : ℝ) : IntervalIntegrable (intG U n) volume s t := by
  have hs : s ∈ Set.Icc (-(|s| + |t|)) (|s| + |t|) :=
    ⟨by linarith [neg_abs_le s, abs_nonneg t], by linarith [le_abs_self s, abs_nonneg t]⟩
  have ht : t ∈ Set.Icc (-(|s| + |t|)) (|s| + |t|) :=
    ⟨by linarith [neg_abs_le t, abs_nonneg s], by linarith [le_abs_self t, abs_nonneg s]⟩
  exact intervalIntegrable_intG (memLp_slabM_of_isL4Loc h4 _ _) n hs ht

theorem massHyp_of_isDuhSol {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ}
    (hc : Continuous u) (hrep : IsSpacetimeRep u U) (h4 : IsL4Loc U) (hD : IsHm1Duhamel u U)
    (a b : ℝ) : MassHyp u U a b where
  cont := hc.continuousOn
  memLp := memLp_slabM_of_isL4Loc h4 a b
  slice := ae_restrict_of_ae hrep.slice
  coeff := by
    intro n s _ t _
    have h := (isHm1Duhamel_iff_intA h4).1 hD n
    rw [h t, h s, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_intG_loc h4 n 0 t)
        (intervalIntegrable_intG_loc h4 n 0 s)]

theorem exists_nat_mul_gt {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : ∃ m : ℕ, |t| < m * δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (|t| / δ)
  exact ⟨m, by rwa [div_lt_iff₀ hδ] at hm⟩

theorem isDuhSol_of_massHyp {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (H : ∀ m : ℕ, MassHyp u U (-(m * δ)) (m * δ)) :
    Continuous u ∧ IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsHm1Duhamel u U := by
  have hcover : ∀ t : ℝ, ∃ m : ℕ, t ∈ Set.Ioo (-(m * δ)) (m * δ) := fun t => by
    obtain ⟨m, hm⟩ := exists_nat_mul_gt hδ t
    exact ⟨m, by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h4 : IsL4Loc U := by
    intro T
    obtain ⟨m, hm⟩ := hcover T
    refine (H m).memLp.mono_measure (Measure.restrict_mono (Set.prod_mono ?_ le_rfl) le_rfl)
    intro r hr
    constructor <;> linarith [hr.1, hr.2, hm.1, hm.2]
  refine ⟨?_, ⟨?_, ?_⟩, h4, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨m, hm⟩ := hcover t
    exact (H m).cont.continuousAt (Icc_mem_nhds hm.1 hm.2)
  · have hU : Set.univ = ⋃ m : ℕ, Set.Icc (-(m * δ)) (m * δ) ×ˢ (Set.univ : Set PhysicalCircle) := by
      ext p
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_prod, and_true, true_iff]
      obtain ⟨m, hm⟩ := hcover p.1
      exact ⟨m, hm.1.le, hm.2.le⟩
    rw [← Measure.restrict_univ (μ := spacetimeMeasure), hU, aestronglyMeasurable_iUnion_iff]
    exact fun m => (H m).memLp.aestronglyMeasurable
  · have hall := ae_all_iff.2 fun m : ℕ =>
      (ae_restrict_iff' (measurableSet_Icc (a := -(m * δ)) (b := m * δ))).1 (H m).slice
    filter_upwards [hall] with t ht
    obtain ⟨m, hm⟩ := hcover t
    exact ht m ⟨hm.1.le, hm.2.le⟩
  · refine (isHm1Duhamel_iff_intA h4).2 fun n t => ?_
    obtain ⟨m, hm⟩ := hcover t
    have h0 : (0 : ℝ) ∈ Set.Icc (-(m * δ)) (m * δ) := ⟨by
      have : (0 : ℝ) ≤ m * δ := by positivity
      linarith, by positivity⟩
    rw [← (H m).coeff n 0 h0 t ⟨hm.1.le, hm.2.le⟩]
    ring

/-- Time reversal of global Duhamel solutions. -/
theorem isDuhSol_rev {u : ℝ → PhysicalL2} (hu : IsDuhSol u) : IsDuhSol (revL2 u) := by
  obtain ⟨hc, U, hrep, h4, hD⟩ := hu
  have H : ∀ m : ℕ, MassHyp (revL2 u) (revU U) (-(m * (1 : ℝ))) (m * 1) := fun m => by
    have h := (massHyp_of_isDuhSol hc hrep h4 hD (-(m * (1 : ℝ))) (m * 1)).rev
    rw [neg_neg] at h
    exact h
  obtain ⟨h1, h2, h3, h5⟩ := isDuhSol_of_massHyp one_pos H
  exact ⟨h1, revU U, h2, h3, h5⟩

/-! ### Existence -/

/-- One extension step of a symmetric interval solution. -/
theorem extend_step {δ : ℝ} (hδ : 0 < δ) (u0 : PhysicalL2)
    (hloc : ∀ a0 : PhysicalL2, ‖a0‖ ≤ ‖u0‖ →
      (∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ), MassHyp v W 0 δ ∧ v 0 = a0) ∧
      (∃ (v : ℝ → PhysicalL2) (W : ℝ × PhysicalCircle → ℂ), MassHyp v W (-δ) 0 ∧ v 0 = a0))
    (k : ℕ) (p : (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ))
    (hp : MassHyp p.1 p.2 (-(k * δ)) (k * δ) ∧ p.1 0 = u0) :
    ∃ q : (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ),
      (MassHyp q.1 q.2 (-((k + 1 : ℕ) * δ)) ((k + 1 : ℕ) * δ) ∧ q.1 0 = u0) ∧
      (∀ t ∈ Set.Icc (-(k * δ)) (k * δ), q.1 t = p.1 t) ∧
      (∀ x : ℝ × PhysicalCircle, x.1 ∈ Set.Ioo (-(k * δ)) (k * δ) → q.2 x = p.2 x) := by
  obtain ⟨u, U⟩ := p
  obtain ⟨H, hu0⟩ := hp
  simp only at H hu0
  set L : ℝ := k * δ with hL
  have hL0 : 0 ≤ L := by positivity
  have h0 : (0 : ℝ) ∈ Set.Icc (-L) L := ⟨by linarith, hL0⟩
  have hmR : ‖u L‖ ≤ ‖u0‖ := by
    rw [← hu0, H.norm_eq h0 ⟨by linarith, le_rfl⟩ hL0]
  have hmL : ‖u (-L)‖ ≤ ‖u0‖ := by
    rw [← hu0, ← H.norm_eq ⟨le_rfl, by linarith⟩ h0 (by linarith)]
  obtain ⟨vp, Wp, Hp, hvp⟩ := (hloc (u L) hmR).1
  obtain ⟨vm, Wm, Hm, hvm⟩ := (hloc (u (-L)) hmL).2
  have Hp' := Hp.shift (-L)
  have Hm' := Hm.shift L
  simp only [sub_neg_eq_add, zero_add, zero_sub] at Hp' Hm'
  set u' : ℝ → PhysicalL2 := fun t =>
    if t < -L then vm (t + L) else if t ≤ L then u t else vp (t + -L) with hu'
  set U' : ℝ × PhysicalCircle → ℂ :=
    glueU (-L) (fun p => Wm (p.1 + L, p.2)) (glueU L U (fun p => Wp (p.1 + -L, p.2))) with hU'
  have e1 : (k + 1 : ℕ) * δ = L + δ := by rw [hL]; push_cast; ring
  have P1 : MassHyp u' (fun p => Wm (p.1 + L, p.2)) (-L + -δ) (-L) := by
    have h := Hm'
    rw [show -δ - L = -L + -δ by ring] at h
    refine h.congr (fun t ht => ?_) (fun _ _ _ => rfl)
    simp only [hu']
    rcases ht.2.lt_or_eq with hlt | heq
    · rw [ite_t hlt]
    · rw [ite_f (not_lt.2 heq.ge), ite_t (by rw [heq]; linarith), heq, neg_add_cancel, hvm]
  have P2 : MassHyp u' U (-L) L :=
    H.congr (fun t ht => by
      simp only [hu', ite_f (not_lt.2 ht.1), ite_t ht.2]) (fun _ _ _ => rfl)
  have P3 : MassHyp u' (fun p => Wp (p.1 + -L, p.2)) L (L + δ) := by
    have h := Hp'
    rw [add_comm δ L] at h
    refine h.congr (fun t ht => ?_) (fun _ _ _ => rfl)
    simp only [hu', ite_f (not_lt.2 (by linarith [ht.1] : -L ≤ t))]
    rcases ht.1.lt_or_eq with hlt | heq
    · rw [ite_f (not_le.2 hlt)]
    · rw [ite_t heq.ge, ← heq, add_neg_cancel, hvp]
  have G := P1.glue (P2.glue P3 (by linarith) (by linarith)) (by linarith) (by linarith)
  refine ⟨(u', U'), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e1, show -(L + δ) = -L + -δ by ring]
    exact G
  · simp only [hu', ite_f (not_lt.2 (by linarith : -L ≤ (0 : ℝ))), ite_t hL0, hu0]
  · intro t ht
    simp only [hu', ite_f (not_lt.2 ht.1), ite_t ht.2]
  · intro x hx
    simp only [hU', glueU, ite_f (not_le.2 hx.1), ite_t hx.2.le]

/-- **Global existence** of `L⁴` Duhamel solutions with conserved mass. -/
theorem duh_exists (u0 : PhysicalL2) :
    ∃ u : ℝ → PhysicalL2, IsDuhSol u ∧ u 0 = u0 ∧ ∀ t, ‖u t‖ = ‖u0‖ := by
  obtain ⟨δ, hδ, hloc⟩ := local_massHyp_exists ‖u0‖
  have step := extend_step hδ u0 hloc
  choose F hF using step
  let Good : ℕ → (ℝ → PhysicalL2) × (ℝ × PhysicalCircle → ℂ) → Prop := fun k p =>
    MassHyp p.1 p.2 (-(k * δ)) (k * δ) ∧ p.1 0 = u0
  have base : Good 0 (fun _ => u0, fun _ => 0) := by
    refine ⟨?_, rfl⟩
    simp only [Nat.cast_zero, zero_mul, neg_zero]
    exact massHyp_point u0
  let seq : (k : ℕ) → {p // Good k p} := fun k =>
    Nat.rec ⟨(fun _ => u0, fun _ => 0), base⟩ (fun k s => ⟨F k s.1 s.2, (hF k s.1 s.2).1⟩) k
  have hsucc : ∀ k, (seq (k + 1)).1 = F k (seq k).1 (seq k).2 := fun k => rfl
  have cons_u : ∀ k m : ℕ, k ≤ m → ∀ t ∈ Set.Icc (-(k * δ)) (k * δ),
      (seq m).1.1 t = (seq k).1.1 t := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hkm ih =>
      intro t ht
      have hmono : (k : ℝ) * δ ≤ m * δ := by
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm
        nlinarith
      rw [hsucc, (hF m (seq m).1 (seq m).2).2.1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ih t ht]
  have cons_U : ∀ k m : ℕ, k ≤ m → ∀ x : ℝ × PhysicalCircle, x.1 ∈ Set.Ioo (-(k * δ)) (k * δ) →
      (seq m).1.2 x = (seq k).1.2 x := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ m hkm ih =>
      intro x hx
      have hmono : (k : ℝ) * δ ≤ m * δ := by
        have : (k : ℝ) ≤ m := by exact_mod_cast hkm
        nlinarith
      rw [hsucc, (hF m (seq m).1 (seq m).2).2.2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩, ih x hx]
  set Nt : ℝ → ℕ := fun t => Nat.ceil (|t| / δ) with hNt
  have hNt_ge : ∀ t, |t| ≤ Nt t * δ := fun t => by
    have h := Nat.le_ceil (|t| / δ)
    rwa [div_le_iff₀ hδ] at h
  set u : ℝ → PhysicalL2 := fun t => (seq (Nt t)).1.1 t with hu
  set U : ℝ × PhysicalCircle → ℂ := fun x => (seq (Nt x.1 + 1)).1.2 x with hU
  have hu_eq : ∀ m : ℕ, ∀ t ∈ Set.Icc (-(m * δ)) (m * δ), u t = (seq m).1.1 t := by
    intro m t ht
    have h1 : t ∈ Set.Icc (-(Nt t * δ)) (Nt t * δ) :=
      ⟨by linarith [neg_abs_le t, hNt_ge t], by linarith [le_abs_self t, hNt_ge t]⟩
    simp only [hu]
    rw [← cons_u (Nt t) (max (Nt t) m) (le_max_left _ _) t h1,
      cons_u m (max (Nt t) m) (le_max_right _ _) t ht]
  have hU_eq : ∀ m : ℕ, ∀ x : ℝ × PhysicalCircle, x.1 ∈ Set.Ioo (-(m * δ)) (m * δ) →
      U x = (seq m).1.2 x := by
    intro m x hx
    have h1 : x.1 ∈ Set.Ioo (-((Nt x.1 + 1 : ℕ) * δ)) ((Nt x.1 + 1 : ℕ) * δ) := by
      have := hNt_ge x.1
      push_cast
      constructor <;> nlinarith [neg_abs_le x.1, le_abs_self x.1]
    simp only [hU]
    rw [← cons_U (Nt x.1 + 1) (max (Nt x.1 + 1) m) (le_max_left _ _) x h1,
      cons_U m (max (Nt x.1 + 1) m) (le_max_right _ _) x hx]
  have H : ∀ m : ℕ, MassHyp u U (-(m * δ)) (m * δ) := fun m =>
    (seq m).2.1.congr (fun t ht => (hu_eq m t ht).symm)
      (fun t ht x => (hU_eq m (t, x) ht).symm)
  obtain ⟨hc, hrep, h4, hD⟩ := isDuhSol_of_massHyp hδ H
  have hu0 : u 0 = u0 := by
    rw [hu_eq 0 0 (by simp)]
    exact (seq 0).2.2
  refine ⟨u, ⟨hc, U, hrep, h4, hD⟩, hu0, fun t => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_mul_gt hδ t
  have h0 : (0 : ℝ) ∈ Set.Icc (-(m * δ)) (m * δ) := ⟨by
    have : (0 : ℝ) ≤ m * δ := by positivity
    linarith, by positivity⟩
  have htm : t ∈ Set.Icc (-(m * δ)) (m * δ) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  rw [← hu0]
  rcases le_total 0 t with h | h
  · exact (H m).norm_eq h0 htm h
  · exact ((H m).norm_eq htm h0 h).symm

/-! ### Uniqueness -/

theorem forward_unique_duh {u u' : ℝ → PhysicalL2} (hu : IsDuhSol u) (hu' : IsDuhSol u')
    (h0 : u 0 = u' 0) : ∀ t, 0 ≤ t → u t = u' t := by
  obtain ⟨hc, U, hrep, h4, hD⟩ := hu
  obtain ⟨hc', U', hrep', h4', hD'⟩ := hu'
  have step : ∀ τ, u τ = u' τ → ∃ ε > 0, ∀ t ∈ Set.Icc 0 ε, u (t + τ) = u' (t + τ) := by
    intro τ hτ
    obtain ⟨ε, hε, -, h⟩ := duhamel_unique_short one_pos le_rfl
      (memLp_slab_one_of_isL4Loc (isL4Loc_shift h4 τ))
      (memLp_slab_one_of_isL4Loc (isL4Loc_shift h4' τ))
      (ae_restrict_of_ae (isSpacetimeRep_shift hrep τ).slice)
      (ae_restrict_of_ae (isSpacetimeRep_shift hrep' τ).slice)
      (by simpa using hτ) (fun t _ => ((isHm1Duhamel_shift h4 hD τ) t).2)
      (fun t _ => ((isHm1Duhamel_shift h4' hD' τ) t).2)
    exact ⟨ε, hε, h⟩
  by_contra hne
  push Not at hne
  set D : Set ℝ := {t : ℝ | 0 ≤ t ∧ u t ≠ u' t} with hDdef
  have hDne : D.Nonempty := by
    obtain ⟨t, ht, h⟩ := hne
    exact ⟨t, ht, h⟩
  have hDbdd : BddBelow D := ⟨0, fun t ht => ht.1⟩
  set τ := sInf D with hτdef
  have hτ0 : 0 ≤ τ := le_csInf hDne fun t ht => ht.1
  have hbelow : ∀ t, 0 ≤ t → t < τ → u t = u' t := fun t ht htτ => by
    by_contra h
    exact absurd (csInf_le hDbdd ⟨ht, h⟩) (not_le.2 htτ)
  have hclosed : IsClosed {t | u t = u' t} := isClosed_eq hc hc'
  have hτeq : u τ = u' τ := by
    rcases hτ0.eq_or_lt with h | h
    · rw [← h]; exact h0
    · have hmem : τ ∈ closure (Set.Ico 0 τ) := by
        rw [closure_Ico h.ne]; exact ⟨hτ0, le_rfl⟩
      exact (hclosed.closure_subset_iff.2 (fun t ht => hbelow t ht.1 ht.2)) hmem
  obtain ⟨ε, hε, hstep⟩ := step τ hτeq
  have hlb : τ + ε ≤ τ := by
    refine le_csInf hDne fun t ht => ?_
    by_contra hlt
    push Not at hlt
    have htτ : τ ≤ t := csInf_le hDbdd ht
    have h := hstep (t - τ) ⟨by linarith, by linarith⟩
    rw [sub_add_cancel] at h
    exact ht.2 h
  linarith

/-- **Uniqueness** of `L⁴` Duhamel solutions (both time directions). -/
theorem duh_unique {u u' : ℝ → PhysicalL2} (hu : IsDuhSol u) (hu' : IsDuhSol u')
    (h0 : u 0 = u' 0) : u = u' := by
  funext t
  rcases le_total 0 t with h | h
  · exact forward_unique_duh hu hu' h0 t h
  · have hr := forward_unique_duh (isDuhSol_rev hu) (isDuhSol_rev hu')
      (by simp only [revL2, neg_zero, h0]) (-t) (by linarith)
    simp only [revL2, neg_neg] at hr
    rw [← conjL2_conjL2 (u t), hr, conjL2_conjL2]

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
