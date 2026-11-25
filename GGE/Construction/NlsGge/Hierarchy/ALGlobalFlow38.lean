import NlsGge.Hierarchy.ALPoissonLiouville38
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Batch 38, E07-6c (targets 1 and 2): local existence/uniqueness and global existence of the
integral curves of `alX38 H` on the open polydisk `alDisk38 L`
(paper/v2.tex l.1976-1977: "The mass integral controls distance from the disk boundary along any
orbit, so the finite-dimensional flow is global on each such mass sublevel").

Phase space `E = ZMod L → ℂ` as a real normed space; `H : E → ℝ` is `C²` on the open polydisk.
Mass conservation enters only through the explicit hypothesis `{M_d, H} = 0` on the disk
(`alBracket38 (alMass38 L) H α = 0`), so that nothing here depends on the worker 6b. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Set Metric Filter Topology
open scoped NNReal

variable {L : ℕ} [NeZero L]

/-- The Hamiltonian vector field of a `C²` function is `C¹` at every point of the polydisk. -/
theorem alX38_contDiffAt38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {α : ZMod L → ℂ} (hα : IsALField38 α) : ContDiffAt ℝ 1 (alX38 H) α := by
  have hU : alDisk38 L ∈ nhds α := isOpen_alDisk38.mem_nhds hα
  have hH2 : ContDiffAt ℝ 2 H α := hH.contDiffAt hU
  have hD : ContDiffAt ℝ 1 (fderiv ℝ H) α := hH2.fderiv_right (m := 1) (by norm_num)
  have hv : ∀ v : ZMod L → ℂ, ContDiffAt ℝ 1 (fun β => ((fderiv ℝ H β v : ℝ) : ℂ)) α :=
    fun v => (Complex.ofRealCLM.contDiff.contDiffAt).comp α
      ((ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp α hD)
  rw [contDiffAt_pi]
  intro j
  have hp : ContDiffAt ℝ 1 (fun β : ZMod L → ℂ => ‖β j‖ ^ 2) α :=
    (contDiff_norm_sq ℝ (E := ℂ)).contDiffAt.comp α
      ((contDiff_apply ℝ ℂ j).contDiffAt (x := α))
  have hn : ContDiffAt ℝ 1 (fun β : ZMod L → ℂ => ((1 - ‖β j‖ ^ 2 : ℝ) : ℂ)) α :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp α (contDiffAt_const.sub hp)
  simp only [alX38, alWdb38]
  exact (contDiffAt_const.mul hn).mul
    (contDiffAt_const.mul ((hv _).add (contDiffAt_const.mul (hv _))))

/-- Local uniqueness of integral curves at a point of the polydisk. -/
theorem alFlow_unique_local38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {γ δ : ℝ → ZMod L → ℂ} {t : ℝ}
    (hγ : ∀ᶠ s in nhds t, IsALField38 (γ s) ∧ HasDerivAt γ (alX38 H (γ s)) s)
    (hδ : ∀ᶠ s in nhds t, IsALField38 (δ s) ∧ HasDerivAt δ (alX38 H (δ s)) s)
    (heq : γ t = δ t) : γ =ᶠ[nhds t] δ := by
  have ht := hγ.self_of_nhds
  obtain ⟨K, u, hu, hK⟩ := (alX38_contDiffAt38 hH ht.1).exists_lipschitzOnWith
  have hγc : ContinuousAt γ t := ht.2.continuousAt
  have hδc : ContinuousAt δ t := hδ.self_of_nhds.2.continuousAt
  have h1 : ∀ᶠ s in nhds t, γ s ∈ u := hγc.eventually hu
  have h2 : ∀ᶠ s in nhds t, δ s ∈ u := by
    have : u ∈ nhds (δ t) := heq ▸ hu
    exact hδc.eventually this
  refine ODE_solution_unique_of_eventually (v := fun _ => alX38 H) (s := fun _ => u) (K := K)
    (Eventually.of_forall fun _ => hK) ?_ ?_ heq
  · filter_upwards [hγ, h1] with s hs h1s using ⟨hs.2, h1s⟩
  · filter_upwards [hδ, h2] with s hs h2s using ⟨hs.2, h2s⟩

/-- Uniqueness of integral curves of `X_H` in the polydisk on an open interval-like set. -/
theorem alFlow_unique38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {γ δ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ I, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 H (γ t)) t)
    (hδ : ∀ t ∈ I, IsALField38 (δ t) ∧ HasDerivAt δ (alX38 H (δ t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (heq : γ t₀ = δ t₀) : EqOn γ δ I := by
  let u : Set ℝ := {t | γ =ᶠ[nhds t] δ}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hγ' : ∀ t ∈ I, ∀ᶠ s in nhds t, IsALField38 (γ s) ∧ HasDerivAt γ (alX38 H (γ s)) s :=
    fun t ht => Filter.eventually_of_mem (hI.mem_nhds ht) hγ
  have hδ' : ∀ t ∈ I, ∀ᶠ s in nhds t, IsALField38 (δ s) ∧ HasDerivAt δ (alX38 H (δ s)) s :=
    fun t ht => Filter.eventually_of_mem (hI.mem_nhds ht) hδ
  have hsub : I ⊆ u := by
    refine hIc.subset_of_closure_inter_subset hu ⟨t₀, ht₀, ?_⟩ ?_
    · exact alFlow_unique_local38 hH (hγ' t₀ ht₀) (hδ' t₀ ht₀) heq
    · rintro t ⟨htc, htI⟩
      have hg : ContinuousAt (fun s => γ s - δ s) t :=
        ((hγ t htI).2.continuousAt).sub ((hδ t htI).2.continuousAt)
      have hz : γ t = δ t := by
        by_contra hne
        have hne' : γ t - δ t ≠ 0 := sub_ne_zero.mpr hne
        have hev : ∀ᶠ s in nhds t, γ s - δ s ≠ 0 := hg.eventually_ne hne'
        have hfr : ∃ᶠ s in nhds t, s ∈ u := mem_closure_iff_frequently.mp htc
        obtain ⟨s, hs1, hs2⟩ := (hfr.and_eventually hev).exists
        exact hs2 (sub_eq_zero.mpr hs1.self_of_nhds)
      exact alFlow_unique_local38 hH (hγ' t htI) (hδ' t htI) hz
  intro t ht
  exact (hsub ht).self_of_nhds


/-- Target 1: local existence of an integral curve of `X_H` through every point of the polydisk,
staying in the polydisk. -/
theorem alFlow_local_exist38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {α₀ : ZMod L → ℂ} (h₀ : IsALField38 α₀) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → ZMod L → ℂ, γ 0 = α₀ ∧
      ∀ t ∈ Ioo (-ε) ε, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 H (γ t)) t := by
  obtain ⟨γ, h0, ε, hε, hd⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (alX38_contDiffAt38 hH h₀) 0
  have hc : ContinuousAt γ 0 := (hd 0 (by simp [hε])).continuousAt
  have hev1 : ∀ᶠ s in nhds (0 : ℝ), IsALField38 (γ s) := by
    have : alDisk38 L ∈ nhds (γ 0) := isOpen_alDisk38.mem_nhds (h0 ▸ h₀)
    exact hc.eventually this
  have hev2 : ∀ᶠ s in nhds (0 : ℝ), s ∈ Ioo (0 - ε) (0 + ε) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff_ball.mp (hev1.and hev2)
  refine ⟨η, hη, γ, h0, fun t ht => ?_⟩
  have := hηs t (by rw [Real.ball_eq_Ioo]; simpa using ht)
  exact ⟨this.1, hd t this.2⟩

/-- `M_d` is differentiable on the polydisk. -/
theorem alMass_differentiableAt38 {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableAt ℝ (alMass38 L) α := by
  have hj : ∀ j : ZMod L, DifferentiableAt ℝ (fun β : ZMod L → ℂ => Real.log (1 - ‖β j‖ ^ 2)) α :=
    fun j => by
      have hp : DifferentiableAt ℝ (fun β : ZMod L → ℂ => ‖β j‖ ^ 2) α :=
        ((contDiff_norm_sq ℝ (E := ℂ)).differentiable one_ne_zero _).comp α
          ((contDiff_apply ℝ ℂ j).differentiable one_ne_zero _)
      have h1 := hα j
      have : 0 < 1 - ‖α j‖ ^ 2 := by nlinarith [norm_nonneg (α j)]
      exact (differentiableAt_const _ |>.sub hp).log this.ne'
  have := DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
  exact this.neg

/-- `M_d` is continuous on the polydisk (as a function on the whole space, at points of it). -/
theorem alMass_continuousAt38 {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ContinuousAt (alMass38 L) α := (alMass_differentiableAt38 hα).continuousAt

/-- The mass controls the distance to the boundary: `r_j ≤ 1 - e^{-M_d}`. -/
theorem alNormSq_le_mass38 {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ZMod L) :
    ‖α j‖ ^ 2 ≤ 1 - Real.exp (-alMass38 L α) := by
  have hpos : ∀ k : ZMod L, 0 < 1 - ‖α k‖ ^ 2 := fun k => by
    have := hα k; nlinarith [norm_nonneg (α k)]
  have hnn : ∀ k ∈ (Finset.univ : Finset (ZMod L)), 0 ≤ -Real.log (1 - ‖α k‖ ^ 2) := fun k _ => by
    have : Real.log (1 - ‖α k‖ ^ 2) ≤ 0 :=
      Real.log_nonpos (hpos k).le (by nlinarith [sq_nonneg ‖α k‖])
    linarith
  have h1 : -Real.log (1 - ‖α j‖ ^ 2) ≤ ∑ k : ZMod L, -Real.log (1 - ‖α k‖ ^ 2) :=
    Finset.single_le_sum hnn (Finset.mem_univ j)
  have h2 : ∑ k : ZMod L, -Real.log (1 - ‖α k‖ ^ 2) = alMass38 L α := by
    simp [alMass38]
  have h3 : -alMass38 L α ≤ Real.log (1 - ‖α j‖ ^ 2) := by linarith
  have h4 := Real.exp_le_exp.mpr h3
  rw [Real.exp_log (hpos j)] at h4
  linarith

/-- If `{M_d, H} = 0` on the polydisk, `M_d` is locally constant along integral curves staying
in the polydisk on an open interval. -/
theorem alMass_const_Ioo38 {H : (ZMod L → ℂ) → ℝ}
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {γ : ℝ → ZMod L → ℂ} {a b : ℝ}
    (hγ : ∀ t ∈ Ioo a b, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 H (γ t)) t)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    alMass38 L (γ s) = alMass38 L (γ t) := by
  have hd : ∀ u ∈ Ioo a b, HasDerivAt (fun r => alMass38 L (γ r)) 0 u := fun u hu => by
    have := alBracket_deriv38 (F := alMass38 L) (H := H) (alMass_differentiableAt38 (hγ u hu).1)
      (hγ u hu).2
    rwa [hcons _ (hγ u hu).1] at this
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hd u hu).deriv) hs ht


/-- Global existence for a globally Lipschitz, bounded autonomous vector field on a Banach space
(Picard-Lindelöf on `[-n-1, n+1]` for every `n`, glued by uniqueness). -/
theorem ode_global_of_lipschitz38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {K : ℝ≥0} (hK : LipschitzWith K f) {B : ℝ}
    (hB : ∀ x, ‖f x‖ ≤ B) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivWithinAt α (f (α t))
        (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := fun n => by
    have hT : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h0 : (0 : ℝ) ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨by linarith, by linarith⟩
    have hpl : IsPicardLindelof (fun _ : ℝ => f) (tmin := -((n : ℝ) + 1)) (tmax := (n : ℝ) + 1)
        (⟨0, h0⟩ : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) x₀ (B.toNNReal * (n + 1)) 0 B.toNNReal K := by
      refine IsPicardLindelof.of_time_independent (fun x _ => ?_) hK.lipschitzOnWith ?_
      · exact (hB x).trans (Real.le_coe_toNNReal B)
      · simp only [NNReal.coe_zero, sub_zero, zero_sub, neg_neg, sub_zero]
        rw [max_self]
        push_cast
        exact le_of_eq (by ring)
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, hα0, hα⟩
  choose α hα0 hα using hloc
  have hint : ∀ n : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt (α n) (f (α n t)) t :=
    fun n t ht => (hα n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n t ht => (hα n t ht).continuousWithinAt
  have hagree : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), α n t = α m t := by
    intro n m hnm
    have hle : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have := ODE_solution_unique_of_mem_Icc (v := fun _ => f) (s := fun _ => Set.univ) (K := K)
      (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1) (t₀ := 0) (f := α n) (g := α m)
      (fun _ _ => hK.lipschitzOnWith) ⟨by linarith, by linarith⟩ (hcont n)
      (hint n) (fun _ _ => trivial)
      ((hcont m).mono (Icc_subset_Icc (by linarith) (by linarith)))
      (fun t ht => (hint m t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
      (fun _ _ => trivial) (by rw [hα0, hα0])
    exact this
  have hagree' : ∀ n m : ℕ, ∀ t : ℝ, |t| ≤ ((min n m : ℕ) : ℝ) + 1 → α n t = α m t := by
    intro n m t ht
    rcases le_total n m with h | h
    · refine hagree n m h t ?_
      have : (min n m : ℕ) = n := min_eq_left h
      rw [this] at ht
      exact abs_le.mp ht
    · refine (hagree m n h t ?_).symm
      have : (min n m : ℕ) = m := min_eq_right h
      rw [this] at ht
      exact abs_le.mp ht
  refine ⟨fun t => α ⌈|t|⌉₊ t, by simpa using hα0 0, fun t => ?_⟩
  set N := ⌈|t|⌉₊ with hN
  have htN : |t| ≤ N := Nat.le_ceil _
  have hnb : Ioo (-((N : ℝ) + 1)) ((N : ℝ) + 1) ∈ nhds t :=
    Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
  have heq : (fun s => α ⌈|s|⌉₊ s) =ᶠ[nhds t] α N := by
    filter_upwards [hnb] with s hs
    refine hagree' _ _ s ?_
    have h1 : |s| < N + 1 := abs_lt.mpr hs
    have h2 : |s| ≤ ⌈|s|⌉₊ := Nat.le_ceil _
    rcases le_total ⌈|s|⌉₊ N with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hd := hint N t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact hd.congr_of_eventuallyEq heq


omit [NeZero L] in
/-- The compact box `{‖α_j‖ ≤ c}` in the phase space. -/
lemma isCompact_box38 (c : ℝ) : IsCompact {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c} := by
  have : {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c} = Set.pi univ fun _ => closedBall (0 : ℂ) c := by
    ext α; simp [Set.pi, mem_closedBall, dist_zero_right]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

/-- Cut-off vector field: for `0 ≤ c₁ < c₂ < 1` there is a globally Lipschitz bounded `C¹` field
agreeing with `X_H` on the box `{‖α_j‖ ≤ c₁}`, and in fact on `{‖α_j‖ < c₁}` (indeed on the box). -/
theorem alCutoff38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {c₁ c₂ : ℝ} (h12 : c₁ < c₂) (h2 : c₂ < 1) :
    ∃ (W : (ZMod L → ℂ) → ZMod L → ℂ) (K : ℝ≥0) (B : ℝ), LipschitzWith K W ∧ (∀ x, ‖W x‖ ≤ B) ∧
      ∀ α : ZMod L → ℂ, (∀ j, ‖α j‖ ≤ c₁) → W α = alX38 H α := by
  have hs : IsOpen {α : ZMod L → ℂ | ∀ j, ‖α j‖ < c₂} := by
    have : {α : ZMod L → ℂ | ∀ j, ‖α j‖ < c₂} = ⋂ j : ZMod L, {α | ‖α j‖ < c₂} := by
      ext α; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const
  have ht : IsClosed {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₁} := by
    have : {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₁} = ⋂ j : ZMod L, {α | ‖α j‖ ≤ c₁} := by
      ext α; simp
    rw [this]
    exact isClosed_iInter fun j =>
      isClosed_le (continuous_norm.comp (continuous_apply j)) continuous_const
  have hts : {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₁} ⊆ {α | ∀ j, ‖α j‖ < c₂} :=
    fun α hα j => lt_of_le_of_lt (hα j) h12
  obtain ⟨χ, hχ, -, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1) hs ht hts
  have hχ0 : ∀ α, α ∉ {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₂} → χ α = 0 := by
    intro α hα
    by_contra hne
    have : α ∈ Function.support χ := hne
    rw [hsupp] at this
    exact hα fun j => (this j).le
  have hcpt := isCompact_box38 (L := L) c₂
  have hclosed : IsClosed {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₂} := hcpt.isClosed
  have hcd : ContDiff ℝ 1 (fun α => χ α • alX38 H α) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : IsALField38 x
    · exact (hχ.contDiffAt).smul (alX38_contDiffAt38 hH hx)
    · have hxK : x ∈ ({α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c₂})ᶜ := by
        intro hK
        apply hx
        intro j
        exact lt_of_le_of_lt (hK j) h2
      have hev : (fun α => χ α • alX38 H α) =ᶠ[nhds x] fun _ => (0 : ZMod L → ℂ) := by
        filter_upwards [hclosed.isOpen_compl.mem_nhds hxK] with y hy
        simp [hχ0 y hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hcs : HasCompactSupport (fun α => χ α • alX38 H α) := by
    refine HasCompactSupport.intro hcpt fun x hx => ?_
    simp [hχ0 x hx]
  obtain ⟨K, hK⟩ := hcd.lipschitzWith_of_hasCompactSupport hcs one_ne_zero
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hcd.continuous
  refine ⟨_, K, B, hK, hB, fun α hα => ?_⟩
  have := (hone α).mp hα
  simp [this]


/-- Target 2: global existence.  If `H` is `C²` on the polydisk and `{M_d, H} = 0` there (mass is
conserved), then through every `α₀` in the polydisk there is an integral curve of `X_H` defined for
all `t ∈ ℝ`; it stays in the polydisk, `M_d` is constant along it, and every coordinate satisfies
`r_j = |α_j|² ≤ 1 - exp(-M_d(α₀))`. -/
theorem alFlow_global_exist38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α₀ : ZMod L → ℂ} (h₀ : IsALField38 α₀) :
    ∃ γ : ℝ → ZMod L → ℂ, γ 0 = α₀ ∧ ∀ t, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 H (γ t)) t ∧ alMass38 L (γ t) = alMass38 L α₀ ∧
      ∀ j, ‖γ t j‖ ^ 2 ≤ 1 - Real.exp (-alMass38 L α₀) := by
  set m := alMass38 L α₀ with hm
  set q : ℝ := 1 - Real.exp (-m) with hq
  set c : ℝ := Real.sqrt q with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c < 1 := by
    rw [hc, Real.sqrt_lt' one_pos]
    have := Real.exp_pos (-m)
    rw [hq]; nlinarith
  set c₁ : ℝ := c + (1 - c) / 3 with hc₁
  set c₂ : ℝ := c + 2 * (1 - c) / 3 with hc₂
  have h12 : c₁ < c₂ := by rw [hc₁, hc₂]; linarith
  have h2 : c₂ < 1 := by rw [hc₂]; linarith
  have hcc₁ : c < c₁ := by rw [hc₁]; linarith
  have hc₁1 : c₁ < 1 := h12.trans h2
  obtain ⟨W, K, B, hK, hB, hW⟩ := alCutoff38 hH h12 h2
  obtain ⟨γ, hγ0, hγd⟩ := ode_global_of_lipschitz38 hK hB α₀
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγd t).continuousAt
  -- bound from the mass
  have hbd : ∀ α : ZMod L → ℂ, IsALField38 α → alMass38 L α = m → ∀ j, ‖α j‖ ≤ c := by
    intro α hα hαm j
    have h := alNormSq_le_mass38 hα j
    rw [hαm] at h
    have := Real.abs_le_sqrt h
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  let S : Set ℝ := {t | (∀ j, ‖γ t j‖ < c₁) ∧ alMass38 L (γ t) = m}
  have hdisk : ∀ t, (∀ j, ‖γ t j‖ < c₁) → IsALField38 (γ t) := fun t ht j =>
    (ht j).trans hc₁1
  have hode : ∀ t, (∀ j, ‖γ t j‖ ≤ c₁) → HasDerivAt γ (alX38 H (γ t)) t := fun t ht => by
    have := hγd t
    rwa [hW _ ht] at this
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hPo : IsOpen {s : ℝ | ∀ j, ‖γ s j‖ < c₁} := by
      have : {s : ℝ | ∀ j, ‖γ s j‖ < c₁} = ⋂ j : ZMod L, {s | ‖γ s j‖ < c₁} := by
        ext s; simp
      rw [this]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (continuous_norm.comp ((continuous_apply j).comp hγc)) continuous_const
    obtain ⟨ε, hε, hεP⟩ := Metric.isOpen_iff.mp hPo t ht.1
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hε) fun s hs => ?_
    have hI : ∀ u ∈ Ioo (t - ε) (t + ε), IsALField38 (γ u) ∧
        HasDerivAt γ (alX38 H (γ u)) u := fun u hu => by
      have hu' : u ∈ {s : ℝ | ∀ j, ‖γ s j‖ < c₁} :=
        hεP (by rw [Real.ball_eq_Ioo]; exact hu)
      exact ⟨hdisk u hu', hode u fun j => (hu' j).le⟩
    have hs' : s ∈ Ioo (t - ε) (t + ε) := by rw [← Real.ball_eq_Ioo]; exact hs
    have ht' : t ∈ Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
    refine ⟨(hεP hs), ?_⟩
    rw [alMass_const_Ioo38 hcons hI hs' ht']
    exact ht.2
  have hSclosed : IsClosed S := by
    have hCc : IsClosed {s : ℝ | ∀ j, ‖γ s j‖ ≤ c} := by
      have : {s : ℝ | ∀ j, ‖γ s j‖ ≤ c} = ⋂ j : ZMod L, {s | ‖γ s j‖ ≤ c} := by
        ext s; simp
      rw [this]
      exact isClosed_iInter fun j =>
        isClosed_le (continuous_norm.comp ((continuous_apply j).comp hγc)) continuous_const
    have hSC : S ⊆ {s : ℝ | ∀ j, ‖γ s j‖ ≤ c} := fun s hs =>
      hbd (γ s) (hdisk s hs.1) hs.2
    refine isClosed_of_closure_subset fun t htc => ?_
    have htC : ∀ j, ‖γ t j‖ ≤ c := closure_minimal hSC hCc htc
    have hlt : ∀ j, ‖γ t j‖ < c₁ := fun j => lt_of_le_of_lt (htC j) hcc₁
    refine ⟨hlt, ?_⟩
    by_contra hne
    have hcont : ContinuousAt (fun s => alMass38 L (γ s)) t :=
      (alMass_continuousAt38 (hdisk t hlt)).comp (hγd t).continuousAt
    have hev : ∀ᶠ s in nhds t, alMass38 L (γ s) ≠ m := hcont.eventually_ne hne
    have hfr : ∃ᶠ s in nhds t, s ∈ S := mem_closure_iff_frequently.mp htc
    obtain ⟨s, hs1, hs2⟩ := (hfr.and_eventually hev).exists
    exact hs2 hs1.2
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨fun j => ?_, by simp [hγ0, hm]⟩
    rw [hγ0]
    exact lt_of_le_of_lt (hbd α₀ h₀ rfl j) hcc₁
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨0, h0S⟩
  refine ⟨γ, hγ0, fun t => ?_⟩
  have ht : t ∈ S := hSuniv ▸ mem_univ t
  have hd := hdisk t ht.1
  refine ⟨hd, hode t fun j => (ht.1 j).le, ht.2, fun j => ?_⟩
  have := alNormSq_le_mass38 hd j
  rwa [ht.2] at this


/-- Global uniqueness of integral curves in the polydisk. -/
theorem alFlow_unique_global38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {γ δ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 H (γ t)) t)
    (hδ : ∀ t, IsALField38 (δ t) ∧ HasDerivAt δ (alX38 H (δ t)) t)
    (h0 : γ 0 = δ 0) : γ = δ := by
  funext t
  exact alFlow_unique38 hH isOpen_univ isPreconnected_univ (fun t _ => hγ t) (fun t _ => hδ t)
    (mem_univ 0) h0 (mem_univ t)

/-- A global integral curve of `X_H` inside the polydisk with initial value `α`. -/
def IsAlGlobalCurve38 (H : (ZMod L → ℂ) → ℝ) (γ : ℝ → ZMod L → ℂ) : Prop :=
  ∀ t, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 H (γ t)) t

/-- The AL flow map `φ_t` of `H` (defined by choice; meaningful when the global curve exists, see
`alFlow_spec38`; it is the identity at points without a global curve). -/
def alFlow38 (H : (ZMod L → ℂ) → ℝ) (t : ℝ) (α : ZMod L → ℂ) : ZMod L → ℂ := by
  classical
  exact if h : ∃ γ : ℝ → ZMod L → ℂ, γ 0 = α ∧ IsAlGlobalCurve38 H γ then h.choose t else α

/-- Specification of the flow map under the hypotheses of `alFlow_global_exist38`. -/
theorem alFlow_spec38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alFlow38 H 0 α = α ∧ IsAlGlobalCurve38 H (fun t => alFlow38 H t α) := by
  classical
  obtain ⟨γ, h0, hγ⟩ := alFlow_global_exist38 hH hcons hα
  have hex : ∃ γ : ℝ → ZMod L → ℂ, γ 0 = α ∧ IsAlGlobalCurve38 H γ :=
    ⟨γ, h0, fun t => ⟨(hγ t).1, (hγ t).2.1⟩⟩
  have hfun : (fun t => alFlow38 H t α) = hex.choose := by
    funext t
    simp only [alFlow38, hex, dite_true]
  have h0' : alFlow38 H 0 α = hex.choose 0 := congrFun hfun 0
  rw [hfun]
  exact ⟨h0'.trans hex.choose_spec.1, hex.choose_spec.2⟩

/-- Flow property `φ_{s+t} = φ_s ∘ φ_t` on the polydisk. -/
theorem alFlow_add38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α : ZMod L → ℂ} (hα : IsALField38 α) (s t : ℝ) :
    alFlow38 H (s + t) α = alFlow38 H s (alFlow38 H t α) := by
  have hα' := alFlow_spec38 hH hcons hα
  have hβ : IsALField38 (alFlow38 H t α) := (hα'.2 t).1
  have hβ' := alFlow_spec38 hH hcons hβ
  have hshift : IsAlGlobalCurve38 H (fun u => alFlow38 H (u + t) α) := fun u => by
    refine ⟨(hα'.2 (u + t)).1, ?_⟩
    exact (hα'.2 (u + t)).2.comp_add_const u t
  have := alFlow_unique_global38 hH hshift hβ'.2 (by simp [hβ'.1])
  exact congrFun this s

#check @alX38_contDiffAt38
#check @alFlow_unique_local38
#check @alFlow_unique38
#check @alFlow_local_exist38
#check @alMass_differentiableAt38
#check @alNormSq_le_mass38
#check @alMass_const_Ioo38
#check @ode_global_of_lipschitz38
#check @alCutoff38
#check @alFlow_global_exist38
#check @alFlow_unique_global38
#check @alFlow_spec38
#check @alFlow_add38
#print axioms alX38_contDiffAt38
#print axioms alFlow_unique_local38
#print axioms alFlow_unique38
#print axioms alFlow_local_exist38
#print axioms alMass_differentiableAt38
#print axioms alNormSq_le_mass38
#print axioms alMass_const_Ioo38
#print axioms ode_global_of_lipschitz38
#print axioms alCutoff38
#print axioms alFlow_global_exist38
#print axioms alFlow_unique_global38
#print axioms alFlow_spec38
#print axioms alFlow_add38

end NlsGge.AblowitzLadik
end
