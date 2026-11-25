import Mathlib

/-!
# Argument principle on circles (library piece L1 of campaign E01)

Local re-proof from Mathlib (E01-D8: no external code).  Statements:

* `zeroMultiset f D`: the zeros of `f` in `D`, with multiplicity (analytic order), as a `Multiset`;
  defined from `MeromorphicOn.divisor`.
* `circleIntegral_logDeriv`: `∮ logDeriv f = 2πi · #zeros` for `f` analytic on a closed disc and
  zero-free on the boundary circle.
* `circleIntegral_mul_logDeriv`: the weighted version `∮ g · logDeriv f = 2πi Σ g(zero)`.

Method: induction on the number of zeros, peeling one zero `a` off by `dslope f a`
(`f = (· - a) * dslope f a`), the Cauchy integral formula for `g/(z-a)` and Cauchy's theorem for
the zero-free remainder.

Author conventions: Mathlib pin `d13f23b`; namespace `NlsGge.GK38.Lib`.
-/

set_option autoImplicit false

open Complex Metric Set Filter Topology
open scoped Real

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### Zero multiset -/

/-- Multiplicity of `z` as a zero of `f` inside `D` (`0` outside `D`, at non-zeros, at poles and
for functions that are not meromorphic on `D`), read off from `MeromorphicOn.divisor`. -/
def zeroMult (f : ℂ → ℂ) (D : Set ℂ) (z : ℂ) : ℕ := (MeromorphicOn.divisor f D z).toNat

open Classical in
/-- The zeros of `f` in `D`, each repeated according to its multiplicity.  The junk value `0` is
returned when the multiplicity function has infinite support (never the case for the analytic
functions on compact sets used below, see `zeroMult_support_finite`). -/
def zeroMultiset (f : ℂ → ℂ) (D : Set ℂ) : Multiset ℂ :=
  if h : (Function.support (zeroMult f D)).Finite then
    Multiset.toFinsupp.symm (Finsupp.ofSupportFinite (zeroMult f D) h)
  else 0

theorem zeroMult_support_finite {f : ℂ → ℂ} {K D : Set ℂ} (hf : MeromorphicOn f K)
    (hK : IsCompact K) (hD : D ⊆ K) : (Function.support (zeroMult f D)).Finite := by
  refine (hf.divisor_support_finite_of_subset hK hD).subset ?_
  intro z hz hz0
  apply hz
  simp [zeroMult, hz0]

theorem count_zeroMultiset {f : ℂ → ℂ} {D : Set ℂ} [DecidableEq ℂ]
    (hfin : (Function.support (zeroMult f D)).Finite) (z : ℂ) :
    (zeroMultiset f D).count z = zeroMult f D z := by
  classical
  unfold zeroMultiset
  simp only [hfin, dite_true]
  rw [← Multiset.toFinsupp_apply]
  simp

theorem zeroMult_of_notMem {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ} (hz : z ∉ D) : zeroMult f D z = 0 := by
  simp [zeroMult, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

theorem zeroMult_eq {f : ℂ → ℂ} {D : Set ℂ} (hf : AnalyticOnNhd ℂ f D) {z : ℂ} (hz : z ∈ D) :
    zeroMult f D z = analyticOrderNatAt f z := by
  unfold zeroMult analyticOrderNatAt
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  generalize analyticOrderAt f z = n
  induction n using ENat.recTopCoe <;> simp

open Classical in
/-- Multiplicities of the zeros of `f` in a subset `D` of a compact set `K` on which `f` is
analytic. -/
theorem count_zeroMultiset_of_subset {f : ℂ → ℂ} {K D : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (hD : D ⊆ K) (z : ℂ) :
    (zeroMultiset f D).count z = if z ∈ D then analyticOrderNatAt f z else 0 := by
  rw [count_zeroMultiset (zeroMult_support_finite hf.meromorphicOn hK hD)]
  by_cases hz : z ∈ D
  · rw [ite_eq_left hz, zeroMult_eq (hf.mono hD) hz]
  · rw [ite_eq_right hz, zeroMult_of_notMem hz]

open Classical in
/-- Multiplicities of zeros of `f` in the open disc `ball c R`, for `f` analytic on the closed
disc. -/
theorem count_zeroMultiset_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (z : ℂ) :
    (zeroMultiset f (ball c R)).count z =
      if z ∈ ball c R then analyticOrderNatAt f z else 0 :=
  count_zeroMultiset_of_subset hf (isCompact_closedBall c R) ball_subset_closedBall z

/-- Membership in the zero multiset. -/
theorem mem_zeroMultiset {f : ℂ → ℂ} {K D : Set ℂ} (hf : AnalyticOnNhd ℂ f K)
    (hK : IsCompact K) (hD : D ⊆ K) {z : ℂ} :
    z ∈ zeroMultiset f D ↔ z ∈ D ∧ analyticOrderNatAt f z ≠ 0 := by
  classical
  rw [← Multiset.count_ne_zero, count_zeroMultiset_of_subset hf hK hD]
  split_ifs with h <;> simp [h]

/-- Membership in the zero multiset of an analytic function on a disc. -/
theorem mem_zeroMultiset_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) {z : ℂ} :
    z ∈ zeroMultiset f (ball c R) ↔ z ∈ ball c R ∧ analyticOrderNatAt f z ≠ 0 :=
  mem_zeroMultiset hf (isCompact_closedBall c R) ball_subset_closedBall

/-- The zero multiset of a not-identically-zero analytic function consists exactly of its zeros:
`z ∈ zeroMultiset f D ↔ z ∈ D ∧ f z = 0`, provided `f` is analytic on the closed disc
`closedBall c R ⊇ D` and does not vanish at some point of that disc. -/
theorem mem_zeroMultiset_iff_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {D : Set ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hD : D ⊆ closedBall c R)
    (hw : ∃ w ∈ closedBall c R, f w ≠ 0) {z : ℂ} :
    z ∈ zeroMultiset f D ↔ z ∈ D ∧ f z = 0 := by
  rw [mem_zeroMultiset hf (isCompact_closedBall c R) hD]
  refine and_congr_right fun hzD => ?_
  obtain ⟨w, hwB, hw0⟩ := hw
  have hz := hD hzD
  have hnt : analyticOrderAt f z ≠ ⊤ := by
    refine hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      hwB hz ?_
    rw [(hf w hwB).analyticOrderAt_eq_zero.2 hw0]
    exact ENat.zero_ne_top
  constructor
  · intro hne
    by_contra hz0
    apply hne
    have : analyticOrderAt f z = 0 := (hf z hz).analyticOrderAt_eq_zero.2 hz0
    simp [analyticOrderNatAt, this]
  · intro hz0 hord
    have : analyticOrderAt f z = 0 := by
      rw [← ENat.natCast_toNat hnt]
      exact_mod_cast hord
    exact (hf z hz).analyticOrderAt_eq_zero.1 this hz0

/-- Additivity over disjoint subsets of a compact set of analyticity. -/
theorem zeroMultiset_union_of_disjoint {f : ℂ → ℂ} {K D₁ D₂ : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (h₁ : D₁ ⊆ K) (h₂ : D₂ ⊆ K)
    (hd : Disjoint D₁ D₂) :
    zeroMultiset f (D₁ ∪ D₂) = zeroMultiset f D₁ + zeroMultiset f D₂ := by
  classical
  refine Multiset.ext' fun z => ?_
  rw [Multiset.count_add, count_zeroMultiset_of_subset hf hK (union_subset h₁ h₂),
    count_zeroMultiset_of_subset hf hK h₁, count_zeroMultiset_of_subset hf hK h₂]
  by_cases hz1 : z ∈ D₁
  · have hz2 : z ∉ D₂ := fun h => (Set.disjoint_left.1 hd hz1) h
    simp [hz1, hz2]
  · by_cases hz2 : z ∈ D₂ <;> simp [hz1, hz2]

/-- Total count over a finite family of pairwise disjoint subsets. -/
theorem card_zeroMultiset_biUnion {ι : Type*} [DecidableEq ι] {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hK : IsCompact K) (s : Finset ι) (D : ι → Set ℂ)
    (hD : ∀ i ∈ s, D i ⊆ K) (hd : (s : Set ι).PairwiseDisjoint D) :
    Multiset.card (zeroMultiset f (⋃ i ∈ s, D i)) =
      ∑ i ∈ s, Multiset.card (zeroMultiset f (D i)) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : zeroMultiset f (∅ : Set ℂ) = 0 := by
      classical
      refine Multiset.ext' fun z => ?_
      rw [count_zeroMultiset_of_subset hf hK (empty_subset K)]
      simp
    simp [h0]
  | insert i s hi ih =>
    have hsub : (⋃ j ∈ s, D j) ⊆ K := iUnion₂_subset fun j hj => hD j (Finset.mem_insert_of_mem hj)
    have hdisj : Disjoint (D i) (⋃ j ∈ s, D j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact hd (Finset.mem_coe.2 (Finset.mem_insert_self i s))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hj)) (fun e => hi (e ▸ hj))
    rw [Finset.set_biUnion_insert, zeroMultiset_union_of_disjoint hf hK
      (hD i (Finset.mem_insert_self i s)) hsub hdisj, Multiset.card_add, Finset.sum_insert hi,
      ih (fun j hj => hD j (Finset.mem_insert_of_mem hj))
        (hd.subset (by intro x hx; simp only [Finset.coe_insert, Set.mem_insert_iff]; exact Or.inr hx))]

/-! ### Auxiliary analytic lemmas -/

section Aux

variable {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}

theorem analyticAt_dslope' {a z : ℂ} (ha : AnalyticAt ℂ f a) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f a) z := by
  by_cases h : z = a
  · subst h
    obtain ⟨p, hp⟩ := ha
    exact (hp.has_fpower_series_dslope_fslope).analyticAt
  · have h1 : dslope f a =ᶠ[𝓝 z] fun w => (w - a)⁻¹ * (f w - f a) := by
      filter_upwards [isOpen_ne.mem_nhds h] with w hw
      simp [dslope_of_ne _ hw, slope_def_field, div_eq_inv_mul]
    refine AnalyticAt.congr ?_ h1.symm
    exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h)).mul
      (hz.sub analyticAt_const)

theorem analyticOrderAt_ne_top_of_sphere (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) {z : ℂ} (hz : z ∈ closedBall c R) :
    analyticOrderAt f z ≠ ⊤ := by
  have hx : c + (R : ℂ) ∈ sphere c R := by
    simp [abs_of_pos hR]
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
    (sphere_subset_closedBall hx) hz ?_
  rw [(hf _ (sphere_subset_closedBall hx)).analyticOrderAt_eq_zero.2 (hne _ hx)]
  exact ENat.zero_ne_top

theorem continuousAt_logDeriv' {h : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ h z) (h0 : h z ≠ 0) :
    ContinuousAt (logDeriv h) z := by
  have : logDeriv h = fun x => deriv h x / h x := funext (logDeriv_apply h)
  rw [this]
  exact hz.deriv.continuousAt.div hz.continuousAt h0

theorem differentiableAt_logDeriv' {h : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ h z) (h0 : h z ≠ 0) :
    DifferentiableAt ℂ (logDeriv h) z := by
  have : logDeriv h = fun x => deriv h x / h x := funext (logDeriv_apply h)
  rw [this]
  exact hz.deriv.differentiableAt.div hz.differentiableAt h0

theorem diffContOnCl_mul' {s : Set ℂ} {g k : ℂ → ℂ} (hg : DiffContOnCl ℂ g s)
    (hk : DiffContOnCl ℂ k s) : DiffContOnCl ℂ (fun z => g z * k z) s :=
  ⟨hg.1.mul hk.1, hg.2.mul hk.2⟩

theorem continuousOn_sphere_of_diffContOnCl (hR : 0 < R) (hg : DiffContOnCl ℂ g (ball c R)) :
    ContinuousOn g (sphere c R) := by
  have := hg.2
  rw [closure_ball c hR.ne'] at this
  exact this.mono sphere_subset_closedBall

/-- `logDeriv` of an analytic, zero-free-on-the-closed-disc function is `DiffContOnCl`. -/
theorem diffContOnCl_logDeriv (hR : 0 < R) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall c R)) (h0 : ∀ z ∈ closedBall c R, h z ≠ 0) :
    DiffContOnCl ℂ (logDeriv h) (ball c R) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball c hR.ne']
  exact fun z hz => (differentiableAt_logDeriv' (hh z hz) (h0 z hz)).differentiableWithinAt

end Aux

/-! ### The argument principle -/

section ArgPrinciple

variable {c : ℂ} {R : ℝ}

private theorem argPrinciple_aux (hR : 0 < R) :
    ∀ (N : ℕ) (f g : ℂ → ℂ), AnalyticOnNhd ℂ f (closedBall c R) →
      (∀ z ∈ sphere c R, f z ≠ 0) → DiffContOnCl ℂ g (ball c R) →
      Multiset.card (zeroMultiset f (ball c R)) = N →
      (∮ z in C(c, R), g z * logDeriv f z) =
        2 * π * I * ((zeroMultiset f (ball c R)).map g).sum := by
  classical
  intro N
  induction N with
  | zero =>
    intro f g hf hne hg hN
    have h0 : zeroMultiset f (ball c R) = 0 := Multiset.card_eq_zero.1 hN
    have hz0 : ∀ z ∈ closedBall c R, f z ≠ 0 := by
      intro z hz
      rcases (mem_closedBall.1 hz).lt_or_eq with hlt | heq
      · have hc := count_zeroMultiset_ball hf z
        rw [h0, Multiset.count_zero, ite_eq_left (mem_ball.2 hlt)] at hc
        have hnt := analyticOrderAt_ne_top_of_sphere hR hf hne hz
        have : analyticOrderAt f z = 0 := by
          rw [← ENat.natCast_toNat hnt]
          exact_mod_cast hc.symm
        exact (hf z hz).analyticOrderAt_eq_zero.1 this
      · exact hne z (mem_sphere.2 heq)
    rw [h0, Multiset.map_zero, Multiset.sum_zero, mul_zero]
    refine DiffContOnCl.circleIntegral_eq_zero hR.le ?_
    exact diffContOnCl_mul' hg (diffContOnCl_logDeriv hR hf hz0)
  | succ N ih =>
    intro f g hf hne hg hN
    have hpos : 0 < Multiset.card (zeroMultiset f (ball c R)) := by omega
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
    rw [mem_zeroMultiset_ball hf] at ha
    obtain ⟨haB, haN⟩ := ha
    have haCB : a ∈ closedBall c R := ball_subset_closedBall haB
    have hfa : f a = 0 := by
      by_contra hne'
      apply haN
      have : analyticOrderAt f a = 0 := (hf a haCB).analyticOrderAt_eq_zero.2 hne'
      simp [analyticOrderNatAt, this]
    set h : ℂ → ℂ := dslope f a with hh
    have hfac : ∀ w, f w = (w - a) * h w := by
      intro w
      have := sub_smul_dslope f a w
      simp only [hfa, sub_zero, smul_eq_mul] at this
      exact this.symm
    have hfeq : f = (fun w => w - a) * h := funext hfac
    have hhan : AnalyticOnNhd ℂ h (closedBall c R) := fun z hz =>
      analyticAt_dslope' (hf a haCB) (hf z hz)
    have hhne : ∀ z ∈ sphere c R, h z ≠ 0 := by
      intro z hz hz0
      apply hne z hz
      rw [hfac z, hz0, mul_zero]
    -- the multiplicity relation
    have hord : ∀ z ∈ closedBall c R,
        analyticOrderNatAt f z = (if z = a then 1 else 0) + analyticOrderNatAt h z := by
      intro z hz
      have hm : analyticOrderAt f z = analyticOrderAt (fun w => w - a) z + analyticOrderAt h z := by
        rw [hfeq]
        exact analyticOrderAt_mul (analyticAt_id.sub analyticAt_const) (hhan z hz)
      have hnt := analyticOrderAt_ne_top_of_sphere hR hhan hhne hz
      unfold analyticOrderNatAt
      rw [hm]
      by_cases hza : z = a
      · subst hza
        rw [ite_eq_left rfl, analyticOrderAt_id_sub_const_self,
          ENat.toNat_add (by simp) hnt]
        simp
      · rw [ite_eq_right hza, analyticOrderAt_id_sub_const_of_ne hza, zero_add, zero_add]
    -- zeros of `h`
    have hmult : zeroMultiset h (ball c R) = (zeroMultiset f (ball c R)).erase a := by
      refine Multiset.ext' fun z => ?_
      rw [count_zeroMultiset_ball hhan]
      by_cases hz : z ∈ ball c R
      · have hzc := hord z (ball_subset_closedBall hz)
        have hcf := count_zeroMultiset_ball hf z
        rw [ite_eq_left hz] at hcf ⊢
        by_cases hza : z = a
        · subst hza
          rw [Multiset.count_erase_self, hcf, hzc]
          simp
        · rw [Multiset.count_erase_of_ne hza, hcf, hzc]
          simp [hza]
      · have hza : z ≠ a := fun e => hz (e ▸ haB)
        rw [ite_eq_right hz, Multiset.count_erase_of_ne hza, count_zeroMultiset_ball hf, ite_eq_right hz]
    have hmem : a ∈ zeroMultiset f (ball c R) := (mem_zeroMultiset_ball hf).2 ⟨haB, haN⟩
    have hcard : Multiset.card (zeroMultiset h (ball c R)) = N := by
      rw [hmult, Multiset.card_erase_of_mem hmem, Nat.pred_eq_sub_one]
      omega
    have hIH := ih h g hhan hhne hg hcard
    -- integrand decomposition on the circle
    have hdec : ∀ z ∈ sphere c R,
        g z * logDeriv f z = (z - a)⁻¹ • g z + g z * logDeriv h z := by
      intro z hz
      have hza : z - a ≠ 0 := by
        intro e
        have : z = a := sub_eq_zero.1 e
        rw [this] at hz
        exact (mem_ball.1 haB).ne (mem_sphere.1 hz)
      have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
      have hl : logDeriv f z = (z - a)⁻¹ + logDeriv h z := by
        rw [hfeq]
        rw [logDeriv_mul z hza (hhne z hz) (by fun_prop) (hhan z hzc).differentiableAt]
        congr 1
        simp [logDeriv_apply]
      rw [hl, smul_eq_mul]
      ring
    have hgc := continuousOn_sphere_of_diffContOnCl hR hg
    have hint1 : CircleIntegrable (fun z => (z - a)⁻¹ • g z) c R := by
      refine ContinuousOn.circleIntegrable hR.le ?_
      have hinv : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (sphere c R) := by
        refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz => ?_
        intro e
        have : z = a := sub_eq_zero.1 e
        rw [this] at hz
        exact (mem_ball.1 haB).ne (mem_sphere.1 hz)
      exact hinv.smul hgc
    have hint2 : CircleIntegrable (fun z => g z * logDeriv h z) c R := by
      refine ContinuousOn.circleIntegrable hR.le ?_
      refine hgc.mul ?_
      intro z hz
      exact (continuousAt_logDeriv' (hhan z (sphere_subset_closedBall hz))
        (hhne z hz)).continuousWithinAt
    rw [circleIntegral.integral_congr hR.le hdec, circleIntegral.integral_add hint1 hint2,
      hg.circleIntegral_sub_inv_smul haB, hIH, hmult]
    conv_rhs => rw [← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.sum_cons]
    ring

/-- **Argument principle on a circle, weighted form.**  If `f` is analytic on the closed disc and
zero-free on its boundary circle, and `g` is continuous on the closed disc and holomorphic inside,
then `∮ g · f'/f = 2πi Σ_{zeros a of f in the disc} g(a)` (zeros counted with multiplicity). -/
theorem circleIntegral_mul_logDeriv {f g : ℂ → ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : ∀ z ∈ sphere c R, f z ≠ 0)
    (hg : DiffContOnCl ℂ g (ball c R)) :
    (∮ z in C(c, R), g z * logDeriv f z) =
      2 * π * I * ((zeroMultiset f (ball c R)).map g).sum :=
  argPrinciple_aux hR _ f g hf hne hg rfl

/-- **Argument principle on a circle.**  `∮ f'/f = 2πi · #(zeros of f in the disc)`. -/
theorem circleIntegral_logDeriv {f : ℂ → ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) =
      2 * π * I * (Multiset.card (zeroMultiset f (ball c R)) : ℂ) := by
  have := circleIntegral_mul_logDeriv (g := fun _ => (1 : ℂ)) hR hf hne diffContOnCl_const
  simpa using this

end ArgPrinciple

end

end NlsGge.GK38.Lib
