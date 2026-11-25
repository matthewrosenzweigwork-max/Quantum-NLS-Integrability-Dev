import Mathlib
import QuantumNLS.Ext025HGP17Argument

/-! # EXT-025 GP-17 (Riesz-rank convention): Rouché for the scalar part

Scalar part of the repaired contract FIN-EXT025-GP-17 (`OWNER_CONTRACT_REPAIRS_2026-11-16.md`,
sha256 7af85990...): "argument principle and Rouché for holomorphic functions with no
boundary zeros".

Statement proved here (circle form):
* `f`, `g` holomorphic on `ball c R'`, `0 < R < R'`;
* strict domination on the circle: `‖g z - f z‖ < ‖f z‖` for `z ∈ sphere c R`;
* the zero sets of `f` and `g` in `ball c R` are the finite sets `Zf`, `Zg` (exact
  characterization, both contained in the open disc);
* conclusion: the numbers of zeros with multiplicity agree,
  `∑_{a∈Zf} analyticOrderNatAt f a = ∑_{b∈Zg} analyticOrderNatAt g b`.

Proof. The homotopy `V_t = f + t (g - f)`, `t ∈ [0,1]`, is zero-free on the circle. The
argument principle (module `Ext025HGP17Argument`) gives for each `t` a natural number `n_t`
with `∮ V_t'/V_t = 2πi n_t`. The map `t ↦ ∮ V_t'/V_t` is continuous on `[0,1]`, by dominated
convergence on the compact set `[0,1] × circle`. A continuous ℕ-valued map on `[0,1]`
is constant (ℕ is discrete, `[0,1]` connected), so `n_0 = n_1`. Since `V_0 = f` and `V_1 = g`,
the counts agree.

Multiplicity convention: scalar analytic order (see `Ext025HGP17Argument`). The operator
algebraic multiplicity under the Riesz-rank convention is not involved in this module.

Author: haiku_inventory (EXT-025 GP-17 packaging round, 2026-11-17). No `sorry`, no axioms
beyond the standard three. -/

noncomputable section
set_option autoImplicit false

open Complex Metric Set Filter Topology Real MeasureTheory
open scoped Interval

namespace QuantumNLS.Ext025HGP17Rouche
open QuantumNLS.Ext025HGP17Argument

/-- The homotopy `f + t (g - f)`. -/
def Vt (f g : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ := f z + (t : ℂ) * (g z - f z)

/-- Its derivative `f' + t (g' - f')`. -/
def Dt (f g : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ := deriv f z + (t : ℂ) * (deriv g z - deriv f z)

/-- The argument-principle integral along the homotopy. -/
def phi (f g : ℂ → ℂ) (c : ℂ) (R : ℝ) (t : ℝ) : ℂ :=
  circleIntegral (fun z => Dt f g t z / Vt f g t z) c R

theorem sphere_mem_ball {c : ℂ} {R R' : ℝ} (hRR : R < R') {z : ℂ} (hz : z ∈ sphere c R) :
    z ∈ ball c R' :=
  mem_ball.2 (by rw [mem_sphere.1 hz]; exact hRR)

/-- Argument principle for any finite set with the zero characterization. -/
theorem ap_any {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R') {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball c R')) (hs : ∀ z ∈ sphere c R, f z ≠ 0)
    {Z : Finset ℂ} (hZ : ∀ a ∈ Z, a ∈ ball c R) (hZz : ∀ z ∈ ball c R, (f z = 0 ↔ z ∈ Z)) :
    circleIntegral (fun z => deriv f z / f z) c R =
      (2 * π * I) * ∑ a ∈ Z, (analyticOrderNatAt f a : ℂ) := by
  obtain ⟨Z', hZ'1, hZ'2, hZ'3⟩ := argument_principle hR hRR hd hs
  have hEq : Z' = Z := by
    ext a
    constructor
    · intro ha
      exact (hZz a (hZ'1 a ha)).1 ((hZ'2 a (hZ'1 a ha)).2 ha)
    · intro ha
      exact (hZ'2 a (hZ a ha)).1 ((hZz a (hZ a ha)).2 ha)
  rw [hZ'3, hEq]

theorem Vt_diff {f g : ℂ → ℂ} {c : ℂ} {R' : ℝ} (hf : DifferentiableOn ℂ f (ball c R'))
    (hg : DifferentiableOn ℂ g (ball c R')) (t : ℝ) :
    DifferentiableOn ℂ (Vt f g t) (ball c R') :=
  hf.add ((hg.sub hf).const_mul (t : ℂ))

theorem deriv_Vt {f g : ℂ → ℂ} {c : ℂ} {R' : ℝ} (hf : DifferentiableOn ℂ f (ball c R'))
    (hg : DifferentiableOn ℂ g (ball c R')) (t : ℝ) {z : ℂ} (hz : z ∈ ball c R') :
    deriv (Vt f g t) z = Dt f g t z := by
  have hfz : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgz : HasDerivAt g (deriv g z) z :=
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have h := hfz.add ((hgz.sub hfz).const_mul (t : ℂ))
  unfold Vt Dt
  exact h.deriv

/-- Zero-freeness on the circle along the homotopy, from the strict domination. -/
theorem Vt_ne {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hlt : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ z ∈ sphere c R, Vt f g t z ≠ 0 := by
  intro z hz h0
  have key : f z = -((t : ℂ) * (g z - f z)) := by
    unfold Vt at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h1 : ‖f z‖ = t * ‖g z - f z‖ := by
    have hn := congrArg norm key
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1] at hn
    exact hn
  have h2 : t * ‖g z - f z‖ ≤ ‖g z - f z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
  linarith [hlt z hz]

/-- Continuity of the argument-principle integral along the homotopy, within `[0,1]`. -/
theorem phi_continuousWithinAt {f g : ℂ → ℂ} {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    (hf : DifferentiableOn ℂ f (ball c R')) (hg : DifferentiableOn ℂ g (ball c R'))
    (hlt : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) {t0 : ℝ} (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (phi f g c R) (Icc (0 : ℝ) 1) t0 := by
  have hsub : sphere c R ⊆ ball c R' := fun z hz => sphere_mem_ball hRR hz
  have hdfc : ContinuousOn (deriv f) (sphere c R) :=
    (hf.deriv isOpen_ball).continuousOn.mono hsub
  have hdgc : ContinuousOn (deriv g) (sphere c R) :=
    (hg.deriv isOpen_ball).continuousOn.mono hsub
  have hfc : ContinuousOn f (sphere c R) := hf.continuousOn.mono hsub
  have hgc : ContinuousOn g (sphere c R) := hg.continuousOn.mono hsub
  have hdf' : ContinuousOn (fun p : ℝ × ℂ => deriv f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hdfc.comp continuousOn_snd (fun p hp => hp.2)
  have hdg' : ContinuousOn (fun p : ℝ × ℂ => deriv g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hdgc.comp continuousOn_snd (fun p hp => hp.2)
  have hf' : ContinuousOn (fun p : ℝ × ℂ => f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hfc.comp continuousOn_snd (fun p hp => hp.2)
  have hg' : ContinuousOn (fun p : ℝ × ℂ => g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hgc.comp continuousOn_snd (fun p hp => hp.2)
  have hpt : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ)) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn
  have hDc : ContinuousOn (fun p : ℝ × ℂ => Dt f g p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hdf'.add (hpt.mul (hdg'.sub hdf'))
  have hVc : ContinuousOn (fun p : ℝ × ℂ => Vt f g p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hf'.add (hpt.mul (hg'.sub hf'))
  have hVne : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ sphere c R, Vt f g p.1 p.2 ≠ 0 := fun p hp =>
    Vt_ne hlt hp.1 p.2 hp.2
  have hKc : ContinuousOn (fun p : ℝ × ℂ => Dt f g p.1 p.2 / Vt f g p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere c R) :=
    hDc.div hVc hVne
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_sphere c R)).exists_bound_of_continuousOn hKc
  have hnorm_deriv : ∀ θ : ℝ, ‖deriv (circleMap c R) θ‖ = R := by
    intro θ
    rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
      abs_of_pos hR]
  have hmemS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ : ℝ, (t, circleMap c R θ) ∈ Icc (0 : ℝ) 1 ×ˢ sphere c R :=
    fun t ht θ => ⟨ht, circleMap_mem_sphere c hR.le θ⟩
  let F : ℝ → ℝ → ℂ := fun t θ => deriv (circleMap c R) θ •
    (Dt f g t (circleMap c R θ) / Vt f g t (circleMap c R θ))
  show ContinuousWithinAt (fun t => ∫ θ in (0 : ℝ)..2 * π, F t θ) (Icc (0 : ℝ) 1) t0
  have hFcont : ∀ t ∈ Icc (0 : ℝ) 1, Continuous (F t) := by
    intro t ht
    have hKt : ContinuousOn (fun z => Dt f g t z / Vt f g t z) (sphere c R) :=
      hKc.comp (f := fun z : ℂ => (t, z)) (continuous_const.prodMk continuous_id).continuousOn
        (fun z hz => ⟨ht, hz⟩)
    have hK : Continuous (fun θ => Dt f g t (circleMap c R θ) / Vt f g t (circleMap c R θ)) :=
      hKt.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR.le θ)
    have hdc : Continuous (fun θ => deriv (circleMap c R) θ) := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact hdc.smul hK
  have hmeas : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] t0,
      AEStronglyMeasurable (F t) (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hFcont t ht).aestronglyMeasurable
  have hbound : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] t0, ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Ι 0 (2 * π) → ‖F t θ‖ ≤ R * B := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine ae_of_all _ (fun θ _ => ?_)
    have hk := hB (t, circleMap c R θ) (hmemS t ht θ)
    simp only at hk
    show ‖deriv (circleMap c R) θ • (Dt f g t (circleMap c R θ) / Vt f g t (circleMap c R θ))‖ ≤ R * B
    rw [norm_smul, hnorm_deriv θ]
    exact mul_le_mul_of_nonneg_left hk hR.le
  have hcontt : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι 0 (2 * π) →
      ContinuousWithinAt (fun t => F t θ) (Icc (0 : ℝ) 1) t0 := by
    refine ae_of_all _ (fun θ _ => ?_)
    have hz : circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le θ
    have hV0 : Vt f g t0 (circleMap c R θ) ≠ 0 := Vt_ne hlt ht0 _ hz
    have hDcont : Continuous (fun t : ℝ => Dt f g t (circleMap c R θ)) := by
      unfold Dt; fun_prop
    have hVcont : Continuous (fun t : ℝ => Vt f g t (circleMap c R θ)) := by
      unfold Vt; fun_prop
    have hK : ContinuousAt (fun t : ℝ => Dt f g t (circleMap c R θ) / Vt f g t (circleMap c R θ)) t0 :=
      hDcont.continuousAt.div hVcont.continuousAt hV0
    have hc0 : ContinuousAt (fun _ : ℝ => deriv (circleMap c R) θ) t0 := continuousAt_const
    exact (hc0.smul hK).continuousWithinAt
  exact intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => R * B)
    hmeas hbound intervalIntegrable_const hcontt

/-- Two natural numbers whose images under `2πi·` are within distance `1` are equal. -/
theorem nat_eq_of_norm_lt (a b : ℕ) (h : ‖(2 * π * I : ℂ) * ((a : ℂ) - (b : ℂ))‖ < 1) :
    a = b := by
  have hpi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hpi] at h
  have h1 : ‖(a : ℂ) - (b : ℂ)‖ < 1 := by
    nlinarith [norm_nonneg ((a : ℂ) - (b : ℂ)), Real.pi_gt_three]
  have hc : ((a : ℂ) - (b : ℂ)) = (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) := by simp
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h1
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h2 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (show a + 1 ≤ b from hlt)
    linarith [(abs_lt.1 h1).1]
  · have h2 : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast (show b + 1 ≤ a from hlt)
    linarith [(abs_lt.1 h1).2]

/-- ROUCHÉ (circle form, repaired GP-17 scalar part). If `‖g - f‖ < ‖f‖` on the circle, and the
zero sets of `f`, `g` in the open disc are the finite sets `Zf`, `Zg`, then the numbers of zeros
with multiplicity coincide. -/
theorem rouche {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R') {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball c R')) (hg : DifferentiableOn ℂ g (ball c R'))
    (hlt : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖)
    {Zf Zg : Finset ℂ} (hZf : ∀ a ∈ Zf, a ∈ ball c R)
    (hZf' : ∀ z ∈ ball c R, (f z = 0 ↔ z ∈ Zf))
    (hZg : ∀ a ∈ Zg, a ∈ ball c R) (hZg' : ∀ z ∈ ball c R, (g z = 0 ↔ z ∈ Zg)) :
    ∑ a ∈ Zf, analyticOrderNatAt f a = ∑ b ∈ Zg, analyticOrderNatAt g b := by
  have hfs : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz h
    have h1 := hlt z hz
    rw [h, sub_zero, norm_zero] at h1
    exact absurd h1 (not_lt.2 (norm_nonneg _))
  have hgs : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz h
    have h1 := hlt z hz
    rw [h, zero_sub, norm_neg] at h1
    exact lt_irrefl _ h1
  have hex : ∀ t ∈ Icc (0 : ℝ) 1, ∃ n : ℕ, phi f g c R t = 2 * π * I * n := by
    intro t ht
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ :=
      argument_principle hR hRR (Vt_diff hf hg t) (Vt_ne hlt ht)
    refine ⟨∑ a ∈ Z, analyticOrderNatAt (Vt f g t) a, ?_⟩
    have hcongr : phi f g c R t =
        circleIntegral (fun z => deriv (Vt f g t) z / Vt f g t z) c R := by
      unfold phi
      apply circleIntegral.integral_congr hR.le
      intro z hz
      simp only [deriv_Vt hf hg t (sphere_mem_ball hRR hz)]
    rw [hcongr, hZ3, Nat.cast_sum]
  choose! ν hν using hex
  have hνc : ContinuousOn ν (Icc (0 : ℝ) 1) := by
    intro t0 ht0
    rw [ContinuousWithinAt, nhds_discrete ℕ, tendsto_pure]
    filter_upwards [(phi_continuousWithinAt hR hRR hf hg hlt ht0) (Metric.ball_mem_nhds
        (phi f g c R t0) one_pos), self_mem_nhdsWithin] with s hs hsI
    have hs' : dist (phi f g c R s) (phi f g c R t0) < 1 := hs
    rw [hν s hsI, hν t0 ht0, dist_eq_norm, ← mul_sub] at hs'
    exact nat_eq_of_norm_lt (ν s) (ν t0) hs'
  have hconst : ν 0 = ν 1 :=
    IsPreconnected.constant isPreconnected_Icc hνc
      (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hphi0 : phi f g c R 0 = circleIntegral (fun z => deriv f z / f z) c R := by
    unfold phi Dt Vt
    simp
  have hphi1 : phi f g c R 1 = circleIntegral (fun z => deriv g z / g z) c R := by
    unfold phi Dt Vt
    simp
  have hf0 := ap_any hR hRR hf hfs hZf hZf'
  have hg0 := ap_any hR hRR hg hgs hZg hZg'
  have h0 : ν 0 = ∑ a ∈ Zf, analyticOrderNatAt f a := by
    have e1 : (2 * π * I : ℂ) * (ν 0 : ℂ) =
        (2 * π * I : ℂ) * ((∑ a ∈ Zf, analyticOrderNatAt f a : ℕ) : ℂ) := by
      rw [← hν 0 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1), hphi0, hf0, Nat.cast_sum]
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero e1
  have h1 : ν 1 = ∑ b ∈ Zg, analyticOrderNatAt g b := by
    have e1 : (2 * π * I : ℂ) * (ν 1 : ℂ) =
        (2 * π * I : ℂ) * ((∑ b ∈ Zg, analyticOrderNatAt g b : ℕ) : ℂ) := by
      rw [← hν 1 (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1), hphi1, hg0, Nat.cast_sum]
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero e1
  rw [← h0, ← h1]
  exact hconst

end QuantumNLS.Ext025HGP17Rouche

#print axioms QuantumNLS.Ext025HGP17Rouche.rouche
#print axioms QuantumNLS.Ext025HGP17Rouche.ap_any
#print axioms QuantumNLS.Ext025HGP17Rouche.phi_continuousWithinAt
#print axioms QuantumNLS.Ext025HGP17Rouche.nat_eq_of_norm_lt
