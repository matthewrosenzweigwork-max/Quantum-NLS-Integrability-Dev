import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK2
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepM1
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCGenActionBound

/-! # Trunk C PREPARATORY lemma K2 in the K5 interface form (NOT approved/admitted/rooted)

Author: Claude Opus 5.5 (preparatory author P1, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; non-approved prefix `prep_`.
Inputs: my K2 core `prep_K2_rate` (K1 + K0 + `rate_close_of_uniform_close`), P2's K0
(`prep_action_invariant`) and P2's M1 (`prep_phase_equivariant`, `prep_phase_equivariant_coord`),
Track B `l2Flow_add`, `l2Flow_solution`, `continuous_l2Flow`, Track A `actual_birkhoff_bindings`.
No hypothesis is added: `prep_K2` has NO premises.

Notation: `Φ = physicalBirkhoff`, `Ψ = physicalInverseBirkhoff`, `R_t y = Φ (l2Flow t (Ψ y))`.

Binders and conclusions (one line each):
* `prep_liftAmp p`: the `ℓ²` vector with coordinates `(p k : ℂ)` if that sequence is in `ℓ²`, else `0`.
* `prep_exists_phase a b (h : ‖a‖ = ‖b‖)`: some real `θ` has `exp(θ i) a = b`.
* `prep_coord_phase_invariant n t y z (hn : y_n = z_n) (hk : ∀ k, ‖y_k‖ = ‖z_k‖)`: the `n`-th
  coordinate of `R_t` agrees at `y` and `z` (phases of the coordinates `k ≠ n` do not matter).
* `prep_K2 (n : ℤ)`: there is `rate : (ℤ → ℝ) → ℝ` with (a) ε–δ continuity on the nonnegative
  `ℓ²` cone for `Σ (p − q)²`; (b) for EVERY `u : PhysicalL2` and EVERY real `t`,
  `Φ_n(l2Flow t u) = exp(−(t · rate(k ↦ ‖Φ_k u‖)) i) · Φ_n u`; (c) for every `J ≥ 0` vanishing
  off a finite set with `0 < J n`, `rate (k ↦ √(J k)) = actualOmega n J`.
  The statement is verbatim the per-mode body of the hypothesis `hK2` of P3's
  `prep_allS_birkhoff_conjugacy_of_K2` (workers/llfp-AllSD 61c3cced1).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

open Classical in
/-- Real amplitudes as an `ℓ²` vector (junk `0` if not square-summable). -/
def prep_liftAmp (p : ℤ → ℝ) : Lib.L2Z :=
  if h : Memℓp (fun k => ((p k : ℝ) : ℂ)) 2 then ⟨fun k => ((p k : ℝ) : ℂ), h⟩ else 0

theorem prep_memℓp_amp (p : ℤ → ℝ) (hp : Summable fun k => p k ^ 2) :
    Memℓp (fun k => ((p k : ℝ) : ℂ)) 2 := by
  refine memℓp_gen ?_
  refine hp.congr (fun k => ?_)
  rw [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem prep_liftAmp_apply (p : ℤ → ℝ) (hp : Summable fun k => p k ^ 2) (k : ℤ) :
    (prep_liftAmp p : ℤ → ℂ) k = ((p k : ℝ) : ℂ) := by
  unfold prep_liftAmp
  split_ifs with h
  · rfl
  · exact absurd (prep_memℓp_amp p hp) h

theorem prep_summable_amp (x : Lib.L2Z) : Summable fun k => ‖(x : ℤ → ℂ) k‖ ^ 2 := by
  have h := (lp.hasSum_norm (p := 2) (by norm_num) x).summable
  refine h.congr (fun k => ?_)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

theorem prep_exists_phase (a b : ℂ) (h : ‖a‖ = ‖b‖) :
    ∃ θ : ℝ, Complex.exp (θ * Complex.I) * a = b := by
  have ha := Complex.norm_mul_exp_arg_mul_I a
  have hb := Complex.norm_mul_exp_arg_mul_I b
  refine ⟨b.arg - a.arg, ?_⟩
  calc Complex.exp (((b.arg - a.arg : ℝ) : ℂ) * Complex.I) * a
      = Complex.exp (((b.arg - a.arg : ℝ) : ℂ) * Complex.I) *
          ((‖a‖ : ℂ) * Complex.exp ((a.arg : ℂ) * Complex.I)) := by rw [ha]
    _ = (‖a‖ : ℂ) * (Complex.exp (((b.arg - a.arg : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((a.arg : ℂ) * Complex.I)) := by ring
    _ = (‖a‖ : ℂ) * Complex.exp ((b.arg : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 2; push_cast; ring
    _ = b := by rw [h, hb]

/-- Rotating a coordinate `k ≠ n` does not change the `n`-th coordinate of `R_t`. -/
theorem prep_coord_rot_other (n k : ℤ) (hkn : k ≠ n) (t θ : ℝ) (w : Lib.L2Z) :
    (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff
      (w + lp.single (E := fun _ : ℤ => ℂ) 2 k
        ((Complex.exp (θ * Complex.I) - 1) * (w : ℤ → ℂ) k)))) : ℤ → ℂ) n =
    (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff w)) : ℤ → ℂ) n := by
  rw [prep_phase_equivariant w t θ k, lp.coeFn_add, Pi.add_apply,
    lp.single_apply_ne 2 k _ (Ne.symm hkn), add_zero]

/-- Phases of the coordinates `k ≠ n` do not affect the `n`-th coordinate of `R_t`. -/
theorem prep_coord_phase_invariant (n : ℤ) (t : ℝ) (y z : Lib.L2Z)
    (hn : (y : ℤ → ℂ) n = (z : ℤ → ℂ) n) (hk : ∀ k, ‖(y : ℤ → ℂ) k‖ = ‖(z : ℤ → ℂ) k‖) :
    (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff y)) : ℤ → ℂ) n =
      (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff z)) : ℤ → ℂ) n := by
  obtain ⟨-, -, hA, hAinv, -⟩ := actual_birkhoff_bindings
  have hΦ : Continuous physicalBirkhoff := continuousOn_univ.mp hA.continuousOn
  have hΨ : Continuous physicalInverseBirkhoff := continuousOn_univ.mp hAinv.continuousOn
  set f : Lib.L2Z → ℂ := fun w =>
    (physicalBirkhoff (l2Flow t (physicalInverseBirkhoff w)) : ℤ → ℂ) n with hf
  have hfc : Continuous f :=
    (prep_continuous_coord n).comp (hΦ.comp
      ((continuous_l2Flow.comp (continuous_const.prodMk continuous_id)).comp hΨ))
  let d : Lib.L2Z := z - y
  let q : Finset ℤ → Lib.L2Z := fun S =>
    ∑ i ∈ S, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i ((d : ℤ → ℂ) i)
  have hpartial : Tendsto q atTop (𝓝 d) :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top d
  have hcoord (S : Finset ℤ) (j : ℤ) :
      (q S : ℤ → ℂ) j = if j ∈ S then (d : ℤ → ℂ) j else 0 := by
    simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  let mix : Finset ℤ → Lib.L2Z := fun S => y + q S
  have hmix (S : Finset ℤ) (j : ℤ) :
      (mix S : ℤ → ℂ) j = if j ∈ S then (z : ℤ → ℂ) j else (y : ℤ → ℂ) j := by
    simp only [mix, lp.coeFn_add, Pi.add_apply, hcoord, d, lp.coeFn_sub, Pi.sub_apply]
    split_ifs <;> ring
  have hlim : Tendsto mix atTop (𝓝 z) := by
    have h := (tendsto_const_nhds (x := y)).add hpartial
    simp only [d, add_sub_cancel] at h
    exact h
  have hconst : ∀ S : Finset ℤ, f (mix S) = f y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : mix ∅ = y := by simp [mix, q]
      rw [this]
    | insert k S hkS ih =>
      by_cases hkn : k = n
      · have : mix (insert k S) = mix S := by
          ext j
          rw [hmix, hmix]
          by_cases hj : j = k
          · subst hj
            simp only [Finset.mem_insert_self, hkS, ↓reduceIte]
            rw [hkn]; exact hn.symm
          · simp only [Finset.mem_insert, hj, false_or]
        rw [this, ih]
      · obtain ⟨θ, hθ⟩ := prep_exists_phase ((y : ℤ → ℂ) k) ((z : ℤ → ℂ) k) (hk k)
        have hyk : (mix S : ℤ → ℂ) k = (y : ℤ → ℂ) k := by rw [hmix]; simp only [hkS, ↓reduceIte]
        have : mix (insert k S) = mix S + lp.single (E := fun _ : ℤ => ℂ) 2 k
            ((Complex.exp (θ * Complex.I) - 1) * (mix S : ℤ → ℂ) k) := by
          ext j
          rw [prep_phase_apply, hmix, hyk]
          by_cases hj : j = k
          · subst hj
            simp only [Finset.mem_insert_self, ↓reduceIte]
            exact hθ.symm
          · rw [hmix]
            simp only [Finset.mem_insert, hj, false_or, ↓reduceIte]
        rw [this]
        simp only [hf]
        rw [prep_coord_rot_other n k hkn t θ (mix S)]
        exact ih
  have h1 : Tendsto (fun S => f (mix S)) atTop (𝓝 (f z)) := (hfc.tendsto z).comp hlim
  have h2 : Tendsto (fun S => f (mix S)) atTop (𝓝 (f y)) := by
    simp only [hconst]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h2 h1

/-- Exponential factor algebra. -/
theorem prep_exp_add_rate (s t r : ℝ) :
    Complex.exp (-(((s + t) * r : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((s * r : ℝ) : ℂ) * Complex.I) * Complex.exp (-((t * r : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- **K2** (interface form consumed by P3's K5). -/
theorem prep_K2 (n : ℤ) :
    ∃ rate : (ℤ → ℝ) → ℝ,
      (∀ q : ℤ → ℝ, ((∀ k, 0 ≤ q k) ∧ Summable (fun k => q k ^ 2)) →
        ∀ ε > 0, ∃ δ > 0, ∀ p : ℤ → ℝ, ((∀ k, 0 ≤ p k) ∧ Summable (fun k => p k ^ 2)) →
          ∑' k, (p k - q k) ^ 2 < δ → |rate p - rate q| < ε) ∧
      (∀ (u : PhysicalL2) (t : ℝ),
        (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
          Complex.exp (-(((t * rate (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖)) : ℝ) : ℂ) *
            Complex.I) * (physicalBirkhoff u : ℤ → ℂ) n) ∧
      (∀ J : ℤ → ℝ, (∀ k, 0 ≤ J k) → (∃ s : Finset ℤ, ∀ k ∉ s, J k = 0) → 0 < J n →
        rate (fun k => Real.sqrt (J k)) = actualOmega n J) := by
  obtain ⟨hL, hR, -⟩ := actual_birkhoff_bindings
  obtain ⟨ω, hωc, hωid, hωD⟩ := prep_K2_rate n
  refine ⟨fun p => ω (prep_liftAmp p), ?_, ?_, ?_⟩
  -- (a) continuity on the nonnegative ℓ² cone
  · rintro q ⟨hq0, hq⟩ ε hε
    have hqC : (prep_liftAmp q : ℤ → ℂ) n =
        ((‖(prep_liftAmp q : ℤ → ℂ) n‖ : ℝ) : ℂ) := by
      rw [prep_liftAmp_apply q hq, Complex.norm_real, Real.norm_of_nonneg (hq0 n)]
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousOn_iff.mp hωc (prep_liftAmp q) hqC ε hε
    refine ⟨δ ^ 2, by positivity, ?_⟩
    rintro p ⟨hp0, hp⟩ hpq
    have hpC : (prep_liftAmp p : ℤ → ℂ) n =
        ((‖(prep_liftAmp p : ℤ → ℂ) n‖ : ℝ) : ℂ) := by
      rw [prep_liftAmp_apply p hp, Complex.norm_real, Real.norm_of_nonneg (hp0 n)]
    have hdist : dist (prep_liftAmp p) (prep_liftAmp q) < δ := by
      rw [dist_eq_norm, prep_lp_two_norm_eq_sqrt]
      have hterm : ∀ k, ‖((prep_liftAmp p - prep_liftAmp q : Lib.L2Z) : ℤ → ℂ) k‖ ^ 2 =
          (p k - q k) ^ 2 := by
        intro k
        rw [lp.coeFn_sub, Pi.sub_apply, prep_liftAmp_apply p hp, prep_liftAmp_apply q hq,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp only [hterm]
      calc Real.sqrt (∑' k, (p k - q k) ^ 2) < Real.sqrt (δ ^ 2) :=
            Real.sqrt_lt_sqrt (tsum_nonneg fun k => sq_nonneg _) hpq
        _ = δ := Real.sqrt_sq hδ.le
    have := hball (prep_liftAmp p) hpC hdist
    rwa [Real.dist_eq] at this
  -- (b) conjugacy for every datum and every time
  · -- amplitudes and their lift
    have hamp : ∀ u : PhysicalL2, ∀ s : ℝ,
        (fun k => ‖(physicalBirkhoff (l2Flow s u) : ℤ → ℂ) k‖) =
          fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖ :=
      fun u s => funext fun k => prep_action_invariant u s k
    let r : PhysicalL2 → ℝ := fun u =>
      ω (prep_liftAmp (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖))
    have hr : ∀ u s, r (l2Flow s u) = r u := fun u s => by simp only [r, hamp u s]
    let P : ℝ → Prop := fun t => ∀ u : PhysicalL2,
      (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
        Complex.exp (-((t * r u : ℝ) : ℂ) * Complex.I) * (physicalBirkhoff u : ℤ → ℂ) n
    -- the unit interval
    have hP01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t := by
      intro t ht u
      set x : Lib.L2Z := physicalBirkhoff u with hx
      have hxs := prep_summable_amp x
      set W : Lib.L2Z := prep_liftAmp (fun k => ‖(x : ℤ → ℂ) k‖) with hW
      have hWk : ∀ k, (W : ℤ → ℂ) k = ((‖(x : ℤ → ℂ) k‖ : ℝ) : ℂ) := fun k =>
        prep_liftAmp_apply _ (by simpa using hxs) k
      have hWC : (W : ℤ → ℂ) n = ((‖(W : ℤ → ℂ) n‖ : ℝ) : ℂ) := by
        rw [hWk, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      set V : Lib.L2Z := W + lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Complex.exp (((x : ℤ → ℂ) n).arg * Complex.I) - 1) * (W : ℤ → ℂ) n) with hV
      have hxn : Complex.exp (((x : ℤ → ℂ) n).arg * Complex.I) * (W : ℤ → ℂ) n =
          (x : ℤ → ℂ) n := by
        rw [hWk, mul_comm]; exact Complex.norm_mul_exp_arg_mul_I _
      have hVn : (V : ℤ → ℂ) n = (x : ℤ → ℂ) n := by
        rw [hV, prep_phase_apply]; simp only [↓reduceIte]; exact hxn
      have hVk : ∀ k, ‖(x : ℤ → ℂ) k‖ = ‖(V : ℤ → ℂ) k‖ := by
        intro k
        by_cases hk : k = n
        · subst hk; rw [hVn]
        · rw [hV, prep_phase_apply]
          simp only [hk, ↓reduceIte]
          rw [hWk, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      have h1 := prep_coord_phase_invariant n t x V hVn.symm hVk
      have h2 := prep_phase_equivariant_coord W t (((x : ℤ → ℂ) n).arg) n
      have h3 := hωid W hWC t ht
      rw [hL u] at h1
      rw [h1, hV, h2, h3]
      have e : Complex.exp (-((t * r u : ℝ) : ℂ) * Complex.I) * (x : ℤ → ℂ) n =
          Complex.exp (-((t * ω W : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((x : ℤ → ℂ) n).arg * Complex.I) * (W : ℤ → ℂ) n) := by
        rw [hxn]
      rw [e]; ring
    -- group law
    have hadd : ∀ s t, P s → P t → P (s + t) := by
      intro s t hs ht u
      rw [l2Flow_add, hs, hr, ht, prep_exp_add_rate]
      ring
    have hzero : ∀ u : PhysicalL2, l2Flow 0 u = u := fun u => (l2Flow_solution u).2
    have hneg : ∀ t, P t → P (-t) := by
      intro t ht u
      have hv : l2Flow t (l2Flow (-t) u) = u := by
        rw [← l2Flow_add, add_neg_cancel, hzero]
      have h := ht (l2Flow (-t) u)
      rw [hv, hr] at h
      rw [h, ← mul_assoc, ← prep_exp_add_rate, neg_add_cancel, zero_mul]
      simp
    have hnonneg : ∀ N : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (N + 1), P t := by
      intro N
      induction N with
      | zero => intro t ht; exact hP01 t (by simpa using ht)
      | succ N ih =>
        intro t ht
        by_cases htN : t ≤ (N : ℝ) + 1
        · exact ih t ⟨ht.1, htN⟩
        · have h1 : P 1 := hP01 1 ⟨zero_le_one, le_rfl⟩
          have h2 : P (t - 1) := ih (t - 1) ⟨by linarith, by
            push_cast at ht; linarith [ht.2]⟩
          have := hadd 1 (t - 1) h1 h2
          rwa [add_sub_cancel] at this
    have hall : ∀ t, P t := by
      intro t
      obtain ⟨N, hN⟩ := exists_nat_ge |t|
      rcases le_or_gt 0 t with h0 | h0
      · exact hnonneg N t ⟨h0, by linarith [le_abs_self t]⟩
      · have := hneg (-t) (hnonneg N (-t) ⟨by linarith, by linarith [neg_abs_le t]⟩)
        rwa [neg_neg] at this
    intro u t
    exact hall t u
  -- (c) agreement with actualOmega on finitely supported nonnegative data
  · rintro J hJ0 ⟨s, hs⟩ hJn
    have hsq : ∀ k, Real.sqrt (J k) ^ 2 = J k := fun k => Real.sq_sqrt (hJ0 k)
    have hsum : Summable fun k => Real.sqrt (J k) ^ 2 := by
      refine summable_of_ne_finset_zero (s := s) (fun k hk => ?_)
      rw [hsq, hs k hk]
    have hap := prep_liftAmp_apply (fun k => Real.sqrt (J k)) hsum
    have hC : (prep_liftAmp (fun k => Real.sqrt (J k)) : ℤ → ℂ) n =
        ((‖(prep_liftAmp (fun k => Real.sqrt (J k)) : ℤ → ℂ) n‖ : ℝ) : ℂ) := by
      rw [hap, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hfin : FiniteSupportSequence (prep_liftAmp (fun k => Real.sqrt (J k))) := by
      refine s.finite_toSet.subset fun k hk => ?_
      by_contra hks
      apply hk
      rw [hap, hs k hks, Real.sqrt_zero, Complex.ofReal_zero]
    have hne : (prep_liftAmp (fun k => Real.sqrt (J k)) : ℤ → ℂ) n ≠ 0 := by
      rw [hap]; exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hJn).ne'
    show ω (prep_liftAmp fun k => Real.sqrt (J k)) = actualOmega n J
    rw [hωD _ hC hfin hne]
    congr 1
    funext k
    rw [actions, hap, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hsq]

end NlsGge.ALLS.TransCPrep
