import NlsGge.NLS38.CutoffField38
import NlsGge.NLS38.SolutionNotion38
import NlsGge.NLS38.Functionals38a

/-! # GWP piece A5b: global cutoff solutions, uniqueness, interval-local uniqueness of true solutions

Plan: `campaign/GWP_PLAN.md` §5.1 items 3 and 7, §7 Part A, piece A5b (revised after G1, note N1).

* `ode_global_nonauto38`: global existence for a globally Lipschitz, bounded, jointly continuous
  time-dependent field on a Banach space (Picard-Lindelöf on `[-n-1, n+1]`, glued by uniqueness).
* `dist_le_two_sided38`: two-sided Gronwall (Lipschitz dependence on data, both time directions).
* `exists_cutSol`, `cutSol_unique`: the cutoff equation (`IsCutSol R`) has exactly one solution through
  every `h¹` datum, global in time.
* `nls_unique_on` (note N1): uniqueness of TRUE solutions on `[-T, T]`, assuming only that both are
  bounded by `R` in `h¹` on that interval (which continuity always provides); no global bound.
* `cutSol_lipschitz`, `cutFlow`: Lipschitz dependence and the choice-defined cutoff flow.
* Probes: the plane wave is the cutoff solution through `δ_k a` once `R ≥ ⟨k⟩‖a‖`.

Cast convention (§6.0): every Sobolev index `1` is `((1 : ℕ) : ℝ)`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal

/-! ## Generic ODE layer -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global existence for a globally Lipschitz, bounded, jointly continuous non-autonomous field. -/
theorem ode_global_nonauto38 [CompleteSpace E] {f : ℝ → E → E} {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (f t)) {B : ℝ}
    (hB : ∀ t x, ‖f t x‖ ≤ B) (hc : Continuous fun p : ℝ × E => f p.1 p.2) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f t (γ t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivWithinAt α (f t (α t))
        (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := fun n => by
    have h0 : (0 : ℝ) ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨by linarith, by linarith⟩
    have hpl : IsPicardLindelof f (tmin := -((n : ℝ) + 1)) (tmax := (n : ℝ) + 1)
        (⟨0, h0⟩ : Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) x₀ (B.toNNReal * (n + 1)) 0 B.toNNReal K :=
      { lipschitzOnWith := fun t _ => (hK t).lipschitzOnWith
        continuousOn := fun x _ => (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
        norm_le := fun t _ x _ => (hB t x).trans (Real.le_coe_toNNReal B)
        mul_max_le := by
          simp only [NNReal.coe_zero, sub_zero, zero_sub, neg_neg]
          rw [max_self]
          push_cast
          exact le_of_eq (by ring) }
    exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hloc
  have hint : ∀ n : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt (α n) (f t (α n t)) t :=
    fun n t ht => (hα n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n t ht => (hα n t ht).continuousWithinAt
  have hagree : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), α n t = α m t := by
    intro n m hnm
    have hle : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ODE_solution_unique_of_mem_Icc (v := f) (s := fun _ => Set.univ) (K := K)
      (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1) (t₀ := 0) (f := α n) (g := α m)
      (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, by linarith⟩ (hcont n)
      (hint n) (fun _ _ => trivial)
      ((hcont m).mono (Icc_subset_Icc (by linarith) (by linarith)))
      (fun t ht => (hint m t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
      (fun _ _ => trivial) (by rw [hα0, hα0])
  have hagree' : ∀ n m : ℕ, ∀ t : ℝ, |t| ≤ ((min n m : ℕ) : ℝ) + 1 → α n t = α m t := by
    intro n m t ht
    rcases le_total n m with h | h
    · refine hagree n m h t ?_
      rw [min_eq_left h] at ht
      exact abs_le.mp ht
    · refine (hagree m n h t ?_).symm
      rw [min_eq_right h] at ht
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
  exact (hint N t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).congr_of_eventuallyEq heq

/-- Gronwall for `t ≥ 0`. -/
theorem dist_le_nonneg38 {f : ℝ → E → E} {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (f t)) {g h : ℝ → E}
    (hg : ∀ t, HasDerivAt g (f t (g t)) t) (hh : ∀ t, HasDerivAt h (f t (h t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    dist (g t) (h t) ≤ dist (g 0) (h 0) * Real.exp (K * t) := by
  have := dist_le_of_trajectories_ODE (v := f) (K := K) (a := 0) (b := t) hK
    (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => (hg s).hasDerivWithinAt)
    (fun s _ => (hh s).continuousAt.continuousWithinAt) (fun s _ => (hh s).hasDerivWithinAt)
    (le_refl _) t ⟨ht, le_rfl⟩
  simpa using this

/-- Two-sided Gronwall: Lipschitz dependence on the datum, in both time directions. -/
theorem dist_le_two_sided38 {f : ℝ → E → E} {K : ℝ≥0} (hK : ∀ t, LipschitzWith K (f t))
    {g h : ℝ → E} (hg : ∀ t, HasDerivAt g (f t (g t)) t) (hh : ∀ t, HasDerivAt h (f t (h t)) t)
    (t : ℝ) : dist (g t) (h t) ≤ dist (g 0) (h 0) * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact dist_le_nonneg38 hK hg hh ht
  · rw [abs_of_nonpos ht]
    have hK' : ∀ s, LipschitzWith K (fun x => -f (-s) x) := fun s =>
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_neg_neg]; exact (hK (-s)).dist_le_mul x y
    have key : ∀ k : ℝ → E, (∀ t, HasDerivAt k (f t (k t)) t) →
        ∀ s, HasDerivAt (fun r => k (-r)) ((fun s x => -f (-s) x) s (k (-s))) s := fun k hk s => by
      have := (hk (-s)).scomp s (hasDerivAt_neg s)
      exact this.congr_deriv (by simp)
    have := dist_le_nonneg38 hK' (key g hg) (key h hh) (neg_nonneg.2 ht)
    simpa using this

end Generic

/-! ## Carrier-level existence and uniqueness -/

/-- Notation: the `h¹` carrier. -/
abbrev H1Carrier38 := SobolevCarrier38 ((1 : ℕ) : ℝ)

/-- From the interaction variable back to the solution. -/
theorem eq_phase_of_interaction38 {u : ℝ → ℤ → ℂ} {v : ℝ → H1Carrier38}
    (hc : ∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (v t) = phase (-t) (u t)) (t : ℝ) :
    u t = phase t (carrierCoe38 ((1 : ℕ) : ℝ) (v t)) := by
  rw [hc t, phase_phase_neg_apply]

/-- Global existence for the cutoff equation: `IsCutSol R` through every `h¹` datum. -/
theorem exists_cutSol (R : ℝ) (hR : 0 < R) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    ∃ u, IsCutSol R u ∧ u 0 = x := by
  obtain ⟨⟨K, hK⟩, B, hB⟩ := Gc_lipschitz R hR
  obtain ⟨γ, hγ0, hγ⟩ := ode_global_nonauto38 (f := Gc 1 le_rfl R) hK hB
    (continuous_Gc_uncurry 1 le_rfl R) (carrierMk38 ((1 : ℕ) : ℝ) x hx)
  refine ⟨fun t => phase t (carrierCoe38 ((1 : ℕ) : ℝ) (γ t)), ?_, ?_⟩
  · refine (isCutSolM_iff 1 le_rfl R _).2 ⟨fun t => carrierCoe38_mem _ (phaseC _ t (γ t)), γ,
      fun t => (phase_neg_phase_apply t _).symm, hγ⟩
  · simp [hγ0, phase_zero_apply]

/-- The interaction variable of a cutoff solution. -/
theorem cutSol_interaction38 {R : ℝ} {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) :
    ∃ v : ℝ → H1Carrier38, (∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (v t) = phase (-t) (u t)) ∧
      ∀ t, HasDerivAt v (Gc 1 le_rfl R t (v t)) t := by
  obtain ⟨_, v, hc, hd⟩ := (isCutSolM_iff 1 le_rfl R u).1 hu
  exact ⟨v, hc, hd⟩

/-- Global uniqueness among CUTOFF solutions. -/
theorem cutSol_unique (R : ℝ) (hR : 0 < R) {u w : ℝ → ℤ → ℂ} (hu : IsCutSol R u)
    (hw : IsCutSol R w) (h0 : u 0 = w 0) : u = w := by
  obtain ⟨⟨K, hK⟩, -⟩ := Gc_lipschitz R hR
  obtain ⟨vu, hcu, hdu⟩ := cutSol_interaction38 hu
  obtain ⟨vw, hcw, hdw⟩ := cutSol_interaction38 hw
  have hv0 : vu 0 = vw 0 := carrierExt38 (by rw [hcu 0, hcw 0, h0])
  have hv : vu = vw := ODE_solution_unique_univ (v := Gc 1 le_rfl R) (s := fun _ => Set.univ)
    (K := K) (t₀ := 0) (fun t => (hK t).lipschitzOnWith) (fun t => ⟨hdu t, trivial⟩)
    (fun t => ⟨hdw t, trivial⟩) hv0
  funext t
  rw [eq_phase_of_interaction38 hcu t, eq_phase_of_interaction38 hcw t, hv]

/-- INTERVAL-LOCAL uniqueness of true solutions (review note N1): no global bound on `u`, `w`. -/
theorem nls_unique_on (R T : ℝ) (hR : 0 < R) (hT : 0 < T) {u w : ℝ → ℤ → ℂ} (hu : IsNLSSol u)
    (hw : IsNLSSol w) (h0 : u 0 = w 0)
    (hbu : ∀ t ∈ Set.Icc (-T) T, hn 1 (u t) ≤ R) (hbw : ∀ t ∈ Set.Icc (-T) T, hn 1 (w t) ≤ R) :
    ∀ t ∈ Set.Icc (-T) T, u t = w t := by
  obtain ⟨⟨K, hK⟩, -⟩ := Gc_lipschitz R hR
  obtain ⟨vu, hcu, hcontu, hdu⟩ := nlsSol_cutOn R T hu hbu
  obtain ⟨vw, hcw, hcontw, hdw⟩ := nlsSol_cutOn R T hw hbw
  have hv0 : vu 0 = vw 0 := carrierExt38 (by rw [hcu 0, hcw 0, h0])
  have h0T : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hv := ODE_solution_unique_of_mem_Icc (v := Gc 1 le_rfl R) (s := fun _ => Set.univ)
    (K := K) (a := -T) (b := T) (t₀ := 0) (f := vu) (g := vw)
    (fun t _ => (hK t).lipschitzOnWith) h0T hcontu
    (fun t ht => hdu t (Ioo_subset_Icc_self ht)) (fun _ _ => trivial) hcontw
    (fun t ht => hdw t (Ioo_subset_Icc_self ht)) (fun _ _ => trivial) hv0
  intro t ht
  rw [eq_phase_of_interaction38 hcu t, eq_phase_of_interaction38 hcw t, hv ht]

/-- Lipschitz dependence of cutoff solutions on the datum, in the `h¹` norm. -/
theorem cutSol_lipschitz (R : ℝ) (hR : 0 < R) : ∃ L : ℝ≥0, ∀ u w, IsCutSol R u → IsCutSol R w →
    ∀ t, hn 1 (fun n => u t n - w t n) ≤
      Real.exp (L * |t|) * hn 1 (fun n => u 0 n - w 0 n) := by
  obtain ⟨⟨K, hK⟩, -⟩ := Gc_lipschitz R hR
  refine ⟨K, fun u w hu hw t => ?_⟩
  obtain ⟨vu, hcu, hdu⟩ := cutSol_interaction38 hu
  obtain ⟨vw, hcw, hdw⟩ := cutSol_interaction38 hw
  have hdiff : ∀ s, hn 1 (fun n => u s n - w s n) = ‖vu s - vw s‖ := fun s => by
    have e : (fun n => u s n - w s n) =
        carrierCoe38 ((1 : ℕ) : ℝ) (phaseC ((1 : ℕ) : ℝ) s (vu s - vw s)) := by
      funext n
      rw [eq_phase_of_interaction38 hcu s, eq_phase_of_interaction38 hcw s]
      simp [carrierCoe38_phaseC_apply, phase, carrierCoe38_sub']
    rw [e, hn_coe38, norm_phaseC]
  rw [hdiff, hdiff, mul_comm, ← dist_eq_norm, ← dist_eq_norm]
  exact dist_le_two_sided38 hK hdu hdw t

open Classical in
/-- The cutoff flow: the (unique, by `cutSol_unique`) cutoff solution through `x` at time `t`;
the identity off `h¹` (junk). -/
def cutFlow (R : ℝ) (t : ℝ) (x : ℤ → ℂ) : ℤ → ℂ :=
  if h : ∃ u, IsCutSol R u ∧ u 0 = x then (Classical.choose h) t else x

theorem cutFlow_spec (R : ℝ) (hR : 0 < R) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    IsCutSol R (fun t => cutFlow R t x) ∧ cutFlow R 0 x = x := by
  have h := exists_cutSol R hR x hx
  have hs := Classical.choose_spec h
  have e : (fun t => cutFlow R t x) = Classical.choose h := by
    funext t; simp only [cutFlow, h, dite_true]
  have e0 : cutFlow R 0 x = Classical.choose h 0 := congrFun e 0
  rw [e, e0]
  exact ⟨hs.1, hs.2⟩

theorem cutFlow_eq (R : ℝ) (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) (t : ℝ) :
    cutFlow R t (u 0) = u t := by
  have hx : u 0 ∈ seqSobolev38 ((1 : ℕ) : ℝ) := hu.mem 0
  have := cutSol_unique R hR (cutFlow_spec R hR (u 0) hx).1 hu (cutFlow_spec R hR (u 0) hx).2
  exact congrFun this t

/-! ## Regression probe: the plane wave -/

/-- `‖planeWave(t)‖_{h¹} = ⟨k⟩‖a‖` for all `t`. -/
theorem hn_planeWave_le38 (R : ℝ) (k : ℤ) (a : ℂ)
    (hRa : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R) (t : ℝ) :
    hn 1 (Pi.single k (planeWaveAmp38 k a t)) ≤ R := by
  have h := hn_one_sq_single k (planeWaveAmp38 k a t)
  have hn0 : 0 ≤ hn 1 (Pi.single k (planeWaveAmp38 k a t)) := Real.sqrt_nonneg _
  have hnorm : ‖planeWaveAmp38 k a t‖ = ‖a‖ := by
    unfold planeWaveAmp38
    rw [norm_mul, norm_phaseFactor, one_mul]
  rw [hnorm] at h
  rw [← Real.sqrt_sq hn0, h]
  exact hRa

/-- The plane wave is a cutoff solution as soon as `⟨k⟩‖a‖ ≤ R`. -/
theorem isCutSol_planeWave (R : ℝ) (k : ℤ) (a : ℂ)
    (hRa : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R) :
    IsCutSol R (fun t => Pi.single k (planeWaveAmp38 k a t)) :=
  isCutSol_of_nlsSol (isNLSSol_planeWave k a) (hn_planeWave_le38 R k a hRa)

/-- End-to-end probe: through `δ_k a` with `⟨k⟩‖a‖ ≤ R`, the cutoff flow IS the explicit plane wave
(existence by `exists_cutSol`, identification by `cutSol_unique`). -/
theorem cutFlow_planeWave (R : ℝ) (hR : 0 < R) (k : ℤ) (a : ℂ)
    (hRa : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R) (t : ℝ) :
    cutFlow R t (Pi.single k a) = Pi.single k (planeWaveAmp38 k a t) := by
  have h0 : planeWaveAmp38 k a 0 = a := by simp [planeWaveAmp38]
  have := cutFlow_eq R hR (isCutSol_planeWave R k a hRa) t
  simp only [h0] at this
  exact this

/-- Interval-local uniqueness probe: a true solution through `δ_k a`, bounded by `R` on `[-T, T]`,
is the plane wave there. -/
theorem nlsSol_eq_planeWave_on (R T : ℝ) (hR : 0 < R) (hT : 0 < T) (k : ℤ) (a : ℂ)
    {w : ℝ → ℤ → ℂ} (hw : IsNLSSol w) (h0 : w 0 = Pi.single k a)
    (hRa : Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R)
    (hbw : ∀ t ∈ Set.Icc (-T) T, hn 1 (w t) ≤ R) :
    ∀ t ∈ Set.Icc (-T) T, w t = Pi.single k (planeWaveAmp38 k a t) := by
  intro t ht
  have hu := isNLSSol_planeWave k a
  have h00 : planeWaveAmp38 k a 0 = a := by simp [planeWaveAmp38]
  have hbu : ∀ t ∈ Set.Icc (-T) T, hn 1 (Pi.single k (planeWaveAmp38 k a t)) ≤ R := fun s _ =>
    (hn_planeWave_le38 R k a hRa s)
  exact (nls_unique_on R T hR hT hu hw (by rw [h0]; simp only [h00]) hbu hbw t ht).symm

end NlsGge.NLS38
