import Mathlib

/-! # EXT-025 GP-17 (Riesz-rank convention): scalar argument principle on a circle

Scalar part of the repaired contract FIN-EXT025-GP-17 (text in
`implementation/ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md`, sha256 7af85990...).
The repaired text says: "Scalar part: unchanged (argument principle and Rouché for
holomorphic functions with no boundary zeros)."

Statement proved here (circle form, exact correspondence to the scalar part):
* `f` holomorphic on an open disc `ball c R'` with `0 < R < R'`;
* no zero of `f` on the boundary circle `sphere c R`;
* then there is a finite set `Z` of points of `ball c R` that is exactly the zero set of
  `f` in the open disc, and `(2πi)⁻¹ ∮_{|z-c|=R} f'/f dz = ∑_{a∈Z} (multiplicity of a)`.

Multiplicity convention (scalar): the multiplicity of a zero `a` of `f` is the analytic
order `analyticOrderNatAt f a`, i.e. the `n` with `f = (z-a)^n g` near `a`, `g(a) ≠ 0`.
This is the scalar zero order used by the consumers LOCAL-007, LOCAL-009 and R-EC25334D.
It is NOT the operator algebraic multiplicity; that is handled, under the Riesz-rank
convention, in `Ext025HGP17Riesz`.

Ambiguity recorded (not resolved here): the source does not define operator algebraic
multiplicity in general (review record r81). Nothing in this module claims source intent
for any operator convention. The scalar statement does not depend on that question.

Mathlib has no argument principle; the proof is built here from Mathlib's Cauchy theorem
for Banach-valued functions off a countable set (`Complex.circleIntegral_eq_zero_of_...`),
the circle integral `∮ (z-w)⁻¹ = 2πi` for `w` inside, and analytic-order factorization
(`AnalyticAt.analyticOrderAt_eq_natCast`).

Proof structure: induction on a finite set `Z` of prescribed zeros. Removing one zero `a`
of order `m` replaces `f` by `f1 = f/(z-a)^m` (removable at `a`). On the circle,
`f'/f = m/(z-a) + f1'/f1`. Base case: no zero in the closed disc, so Cauchy gives zero.

Author: haiku_inventory (EXT-025 GP-17 packaging round, 2026-11-17). Frozen modules untouched.
No `sorry`, no axioms beyond the standard three. -/

noncomputable section
set_option autoImplicit false

open Complex Metric Set Filter Topology Real
open scoped Interval

namespace QuantumNLS.Ext025HGP17Argument

/-- Algebra of the logarithmic-derivative step: `(m w^(m-1) u + w^m u') / (w^m u) = m/w + u'/u`. -/
theorem log_identity (m : ℕ) (w u u' : ℂ) (hw : w ≠ 0) (hu : u ≠ 0) :
    ((m : ℂ) * w ^ (m - 1) * u + w ^ m * u') / (w ^ m * u) = (m : ℂ) * w⁻¹ + u' / u := by
  cases m with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel, Nat.cast_succ]
    rw [pow_succ]
    field_simp

/-- A function not identically zero near a point of a disc where it is holomorphic and
zero-free on the boundary circle: its germ at any interior point is not eventually zero. -/
theorem not_eventually_zero {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball c R')) (hs : ∀ z ∈ sphere c R, f z ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R') : ¬ ∀ᶠ w in 𝓝 z, f w = 0 := by
  intro h
  have hA : AnalyticOnNhd ℂ f (ball c R') := hd.analyticOnNhd isOpen_ball
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball c R').isPreconnected hz h
  have hsph : c + (R : ℂ) ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm]
    simp [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hball : c + (R : ℂ) ∈ ball c R' := by
    rw [mem_ball, dist_eq_norm]
    simp [Complex.norm_real, Real.norm_of_nonneg hR.le, hRR]
  exact hs _ hsph (by simpa using hEq hball)

/-- Zero-free closed disc from a zero-free sphere and a zero-free open disc. -/
theorem ne_zero_of_closedBall {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hs : ∀ z ∈ sphere c R, f z ≠ 0)
    (hb : ∀ z ∈ ball c R, f z ≠ 0) : ∀ z ∈ closedBall c R, f z ≠ 0 := by
  intro z hz
  by_cases h : z ∈ sphere c R
  · exact hs z h
  · exact hb z (mem_ball.2 (lt_of_le_of_ne (mem_closedBall.1 hz) (fun e => h (mem_sphere.2 e))))

/-- Factorization of a function that is not eventually zero at an analytic point. -/
theorem ord_factor {f : ℂ → ℂ} {a : ℂ} (hA : AnalyticAt ℂ f a)
    (hne : ¬ ∀ᶠ z in 𝓝 a, f z = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, f z = (z - a) ^ (analyticOrderNatAt f a) * g z := by
  have htop : analyticOrderAt f a ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.1 h)
  have hn : analyticOrderAt f a = ((analyticOrderNatAt f a : ℕ) : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨g, hg, hg0, hfg⟩ := (hA.analyticOrderAt_eq_natCast).1 hn
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz, smul_eq_mul]

/-- The zeros of `f` in the open disc are finite (compactness plus isolated zeros). -/
theorem zeros_finite {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball c R')) (hs : ∀ z ∈ sphere c R, f z ≠ 0) :
    {z | z ∈ ball c R ∧ f z = 0}.Finite := by
  by_contra hinf
  have hsub : {z | z ∈ ball c R ∧ f z = 0} ⊆ closedBall c R :=
    fun z hz => ball_subset_closedBall hz.1
  obtain ⟨x, hxK, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall c R) hsub
  have hxR : x ∈ ball c R' := closedBall_subset_ball hRR hxK
  have hA : AnalyticAt ℂ f x := hd.analyticOnNhd isOpen_ball x hxR
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact not_eventually_zero hR hRR hd hs hxR h
  · haveI : (𝓝[≠] x ⊓ 𝓟 {z | z ∈ ball c R ∧ f z = 0}).NeBot := hacc
    have h1 : ∀ᶠ z in 𝓝[≠] x ⊓ 𝓟 {z | z ∈ ball c R ∧ f z = 0}, f z ≠ 0 :=
      Filter.Eventually.filter_mono inf_le_left h
    have h2 : ∀ᶠ z in 𝓝[≠] x ⊓ 𝓟 {z | z ∈ ball c R ∧ f z = 0}, f z = 0 :=
      Filter.eventually_inf_principal.2 (Eventually.of_forall fun z hz => hz.2)
    obtain ⟨z, hz1, hz2⟩ := (h1.and h2).exists
    exact hz1 hz2

/-- Induction on a finite set of prescribed zeros: the circle integral of `f'/f` equals
`2πi` times the sum of the analytic orders over `Z`, when `Z` contains all zeros in the disc
and lies in the disc. -/
theorem count_lemma (c : ℂ) {R R' : ℝ} (hR : 0 < R) (hRR : R < R') (Z : Finset ℂ) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball c R') → (∀ z ∈ sphere c R, f z ≠ 0) →
      (∀ a ∈ Z, a ∈ ball c R) → (∀ z ∈ ball c R, f z = 0 → z ∈ Z) →
      circleIntegral (fun z => deriv f z / f z) c R =
        (2 * π * I) * ∑ a ∈ Z, (analyticOrderNatAt f a : ℂ) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    intro f hd hs _ hz
    have hb : ∀ z ∈ ball c R, f z ≠ 0 := fun z hzb hfz => by simpa using hz z hzb hfz
    have hnz := ne_zero_of_closedBall hs hb
    have hcont : ContinuousOn (fun z => deriv f z / f z) (closedBall c R) := by
      have h1 : ContinuousOn (deriv f) (closedBall c R) :=
        ((hd.deriv isOpen_ball).continuousOn).mono (closedBall_subset_ball hRR)
      have h2 : ContinuousOn f (closedBall c R) :=
        hd.continuousOn.mono (closedBall_subset_ball hRR)
      exact h1.div h2 hnz
    have hdiff : ∀ z ∈ ball c R \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun z => deriv f z / f z) z := by
      intro z hz
      have hzR : z ∈ ball c R' := ball_subset_ball hRR.le hz.1
      have hdf : DifferentiableAt ℂ (deriv f) z :=
        (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hzR)
      have hf : DifferentiableAt ℂ f z := hd.differentiableAt (isOpen_ball.mem_nhds hzR)
      exact hdf.div hf (hnz z (ball_subset_closedBall hz.1))
    have hcauchy := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty hcont hdiff
    simpa using hcauchy
  | @insert a Z0 haZ ih =>
    intro f hd hs hmem hz
    have haB : a ∈ ball c R := hmem a (Finset.mem_insert_self a Z0)
    have hZ0B : ∀ b ∈ Z0, b ∈ ball c R := fun b hb => hmem b (Finset.mem_insert_of_mem hb)
    have haR' : a ∈ ball c R' := ball_subset_ball hRR.le haB
    have hfa : AnalyticAt ℂ f a := hd.analyticOnNhd isOpen_ball a haR'
    have hnev : ¬ ∀ᶠ z in 𝓝 a, f z = 0 := not_eventually_zero hR hRR hd hs haR'
    obtain ⟨g, hg, hg0, hfg⟩ := ord_factor hfa hnev
    obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderNatAt f a = m := ⟨_, rfl⟩
    rw [hm] at hfg
    obtain ⟨f1, hf1⟩ : ∃ f1 : ℂ → ℂ, ∀ z, f1 z = if z = a then g a else f z / (z - a) ^ m :=
      ⟨_, fun z => rfl⟩
    have hF1ne : ∀ z, z ≠ a → f1 z = f z / (z - a) ^ m := fun z hz' => by
      rw [hf1, if_neg hz']
    have hF1a : f1 a = g a := by rw [hf1, if_pos rfl]
    have hfz : ∀ z, z ≠ a → f z = (z - a) ^ m * f1 z := by
      intro z hz'
      have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz')
      rw [hF1ne z hz']
      field_simp
    have hF1g : f1 =ᶠ[𝓝 a] g := by
      filter_upwards [hfg] with z hz'
      by_cases hza : z = a
      · rw [hza, hF1a]
      · have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hza)
        rw [hF1ne z hza, hz']
        field_simp
    have hf1diff : DifferentiableOn ℂ f1 (ball c R') := by
      intro z hz'
      by_cases hza : z = a
      · rw [hza]
        exact ((hg.differentiableAt).congr_of_eventuallyEq hF1g).differentiableWithinAt
      · have hzf : DifferentiableAt ℂ f z := hd.differentiableAt (isOpen_ball.mem_nhds hz')
        have hq : DifferentiableAt ℂ (fun w => f w / (w - a) ^ m) z :=
          hzf.div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hza))
        have hfe : f1 =ᶠ[𝓝 z] (fun w => f w / (w - a) ^ m) := by
          filter_upwards [eventually_ne_nhds hza] with w hw
          exact hF1ne w hw
        exact (hq.congr_of_eventuallyEq hfe).differentiableWithinAt
    have hf1nz : ∀ z ∈ sphere c R, f1 z ≠ 0 := by
      intro z hz'
      have hza : z ≠ a := by
        intro e
        have h1 := mem_sphere.1 hz'
        have h2 := mem_ball.1 haB
        rw [e] at h1
        linarith
      rw [hF1ne z hza]
      exact div_ne_zero (hs z hz') (pow_ne_zero _ (sub_ne_zero.2 hza))
    have hzeros1 : ∀ z ∈ ball c R, f1 z = 0 → z ∈ Z0 := by
      intro z hzB hz1
      by_cases hza : z = a
      · rw [hza, hF1a] at hz1
        exact absurd hz1 hg0
      · rw [hF1ne z hza] at hz1
        have hfz0 : f z = 0 :=
          (div_eq_zero_iff.1 hz1).resolve_right (pow_ne_zero _ (sub_ne_zero.2 hza))
        rcases Finset.mem_insert.1 (hz z hzB hfz0) with h1 | h1
        · exact absurd h1 hza
        · exact h1
    have hF7 : ∀ b ∈ Z0, analyticOrderNatAt f b = analyticOrderNatAt f1 b := by
      intro b hb
      have hba : b ≠ a := fun e => haZ (e ▸ hb)
      have hbR' : b ∈ ball c R' := ball_subset_ball hRR.le (hZ0B b hb)
      have hpowA : AnalyticAt ℂ (fun w : ℂ => (w - a) ^ m) b :=
        (analyticAt_id.sub analyticAt_const).pow m
      have hf1A : AnalyticAt ℂ f1 b := hf1diff.analyticOnNhd isOpen_ball b hbR'
      have hev : f =ᶠ[𝓝 b] (fun w : ℂ => (w - a) ^ m) * f1 := by
        filter_upwards [eventually_ne_nhds hba] with w hw
        simp only [Pi.mul_apply]
        exact hfz w hw
      have hpow0 : analyticOrderAt (fun w : ℂ => (w - a) ^ m) b = 0 := by
        apply analyticOrderAt_eq_zero.2
        right
        show (b - a) ^ m ≠ 0
        exact pow_ne_zero _ (sub_ne_zero.2 hba)
      have hord : analyticOrderAt f b = analyticOrderAt ((fun w : ℂ => (w - a) ^ m) * f1) b :=
        analyticOrderAt_congr hev
      have hmul := analyticOrderAt_mul hpowA hf1A
      unfold analyticOrderNatAt
      rw [hord, hmul, hpow0, zero_add]
    have hid : ∀ z ∈ sphere c R, deriv f z / f z = (m : ℂ) * (z - a)⁻¹ + deriv f1 z / f1 z := by
      intro z hz'
      have hza : z ≠ a := by
        intro e
        have h1 := mem_sphere.1 hz'
        have h2 := mem_ball.1 haB
        rw [e] at h1
        linarith
      have hzR : z ∈ ball c R' := closedBall_subset_ball hRR (sphere_subset_closedBall hz')
      have hfe : f =ᶠ[𝓝 z] fun w => (w - a) ^ m * f1 w := by
        filter_upwards [eventually_ne_nhds hza] with w hw
        exact hfz w hw
      have hd1 : deriv f z = deriv (fun w => (w - a) ^ m * f1 w) z := hfe.deriv_eq
      have hp : HasDerivAt (fun w : ℂ => (w - a) ^ m) ((m : ℂ) * (z - a) ^ (m - 1)) z := by
        exact (hasDerivAt_pow m (z - a)).comp_sub_const z a
      have hf1d : HasDerivAt f1 (deriv f1 z) z :=
        (hf1diff.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
      have hprod : HasDerivAt (fun w => (w - a) ^ m * f1 w)
          ((m : ℂ) * (z - a) ^ (m - 1) * f1 z + (z - a) ^ m * deriv f1 z) z :=
        hp.mul hf1d
      rw [hd1, hprod.deriv, hfz z hza]
      exact log_identity m (z - a) (f1 z) (deriv f1 z) (sub_ne_zero.2 hza) (hf1nz z hz')
    have hcont1 : ContinuousOn (fun z => deriv f1 z / f1 z) (sphere c R) := by
      have hsub : sphere c R ⊆ ball c R' := fun z hz' =>
        mem_ball.2 (by rw [mem_sphere.1 hz']; exact hRR)
      have hc1 : ContinuousOn (deriv f1) (sphere c R) :=
        (hf1diff.deriv isOpen_ball).continuousOn.mono hsub
      have hc2 : ContinuousOn f1 (sphere c R) := hf1diff.continuousOn.mono hsub
      exact hc1.div hc2 hf1nz
    have hnot : a ∉ sphere c |R| := by
      rw [abs_of_pos hR]
      intro h
      have h1 := mem_sphere.1 h
      have h2 := mem_ball.1 haB
      linarith
    have hint1 : CircleIntegrable (fun z => deriv f1 z / f1 z) c R :=
      ContinuousOn.circleIntegrable hR.le hcont1
    have hint0 : CircleIntegrable (fun z => (z - a)⁻¹) c R :=
      circleIntegrable_sub_inv_iff.2 (Or.inr hnot)
    have hlin : circleIntegral (fun z => deriv f z / f z) c R =
        circleIntegral (fun z => (m : ℂ) * (z - a)⁻¹ + deriv f1 z / f1 z) c R :=
      circleIntegral.integral_congr hR.le (fun z hz' => hid z hz')
    have hsplit : circleIntegral (fun z => (m : ℂ) * (z - a)⁻¹ + deriv f1 z / f1 z) c R =
        circleIntegral (fun z => (m : ℂ) * (z - a)⁻¹) c R +
          circleIntegral (fun z => deriv f1 z / f1 z) c R :=
      circleIntegral.integral_add (hint0.const_mul _) hint1
    have hc : circleIntegral (fun z => (m : ℂ) * (z - a)⁻¹) c R =
        (m : ℂ) * circleIntegral (fun z => (z - a)⁻¹) c R :=
      circleIntegral.integral_const_mul (m : ℂ) (fun z => (z - a)⁻¹) c R
    have hI : circleIntegral (fun z => (z - a)⁻¹) c R = 2 * π * I :=
      circleIntegral.integral_sub_inv_of_mem_ball haB
    have hsum : ∑ b ∈ Z0, (analyticOrderNatAt f b : ℂ) =
        ∑ b ∈ Z0, (analyticOrderNatAt f1 b : ℂ) :=
      Finset.sum_congr rfl (fun b hb => by rw [hF7 b hb])
    rw [hlin, hsplit, hc, hI, ih f1 hf1diff hf1nz hZ0B hzeros1, Finset.sum_insert haZ, hm, hsum]
    ring

/-- SCALAR ARGUMENT PRINCIPLE (circle form, repaired GP-17 scalar part).
For `f` holomorphic on `ball c R'` with no zero on `sphere c R` (`0 < R < R'`), there is a
finite set `Z` of zeros, exactly the zero set of `f` in `ball c R`, such that the circle
integral of `f'/f` equals `2πi` times the number of zeros with multiplicity. -/
theorem argument_principle {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R') {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball c R')) (hs : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ a ∈ Z, a ∈ ball c R) ∧ (∀ z ∈ ball c R, (f z = 0 ↔ z ∈ Z)) ∧
      circleIntegral (fun z => deriv f z / f z) c R =
        (2 * π * I) * ∑ a ∈ Z, (analyticOrderNatAt f a : ℂ) := by
  classical
  have hfin := zeros_finite hR hRR hd hs
  refine ⟨hfin.toFinset, fun a ha => (hfin.mem_toFinset.1 ha).1, fun z hz => ?_, ?_⟩
  · constructor
    · intro hfz
      exact hfin.mem_toFinset.2 ⟨hz, hfz⟩
    · intro hzZ
      exact (hfin.mem_toFinset.1 hzZ).2
  · exact count_lemma c hR hRR hfin.toFinset f hd hs
      (fun a ha => (hfin.mem_toFinset.1 ha).1)
      (fun z hz hfz => hfin.mem_toFinset.2 ⟨hz, hfz⟩)

end QuantumNLS.Ext025HGP17Argument

#print axioms QuantumNLS.Ext025HGP17Argument.argument_principle
#print axioms QuantumNLS.Ext025HGP17Argument.count_lemma
#print axioms QuantumNLS.Ext025HGP17Argument.zeros_finite
#print axioms QuantumNLS.Ext025HGP17Argument.log_identity
