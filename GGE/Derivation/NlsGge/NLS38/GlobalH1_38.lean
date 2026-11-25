import NlsGge.NLS38.Conservation38
import NlsGge.Birkhoff.F01Determinant38

/-! # GWP piece A8: global `h¹` well-posedness (existence, uniqueness, conservation)

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A8 (with review note N1).

* `Bx x = √(mass x + ham x / (4π²))`: since `quart ≥ 0`, `hn 1 x ≤ Bx x` (`hn_le_Bx38`).
* `cutSol_inactive`: for `R ≥ Bx x + 2` a cutoff solution never leaves the ball of radius `Bx x`
  and conserves mass and energy.  `h³` data: `no_exit` applied to `φ t = hn 1 (u t)²` with
  `conserved_inside` (`inactive_h3_38`).  `h¹` data: Fourier truncations `x_N → x`, the cutoff-`R'`
  solutions `u_N` through `x_N` conserve mass/energy, `u_N t → u t` in `h¹` by `cutSol_lipschitz`,
  and `mass`, `ham` are continuous (`conserved_limit38`); then the cutoff is inactive for every
  `R ≥ Bx x + 2` by `cutSol_unique`.
* `nls_unique` is interval-local (note N1): `nls_unique_on` on `[-T, T]` with `R` a bound of
  `hn 1 (u ·)`, `hn 1 (w ·)` on the compact interval.  `isNLSSol_iff_cutSol` is used only for existence.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set Filter Topology
open scoped ComplexConjugate NNReal

/-- The a priori `h¹` bound from mass and energy. -/
def Bx (x : ℤ → ℂ) : ℝ := Real.sqrt (mass x + ham x / (4 * Real.pi ^ 2))

theorem Bx_nonneg38 (x : ℤ → ℂ) : 0 ≤ Bx x := Real.sqrt_nonneg _

theorem Bx_sq38 (x : ℤ → ℂ) : Bx x ^ 2 = mass x + ham x / (4 * Real.pi ^ 2) := by
  unfold Bx
  rw [Real.sq_sqrt]
  exact add_nonneg (mass_nonneg x) (div_nonneg (ham_nonneg x) (by positivity))

theorem hn_sq_le_Bx_sq38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    hn 1 x ^ 2 ≤ Bx x ^ 2 := by
  rw [Bx_sq38, hn_one_sq hx]
  have : kin x / (4 * Real.pi ^ 2) ≤ ham x / (4 * Real.pi ^ 2) :=
    div_le_div_of_nonneg_right (by rw [ham_def]; linarith [quart_nonneg x]) (by positivity)
  linarith

theorem hn_le_Bx38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : hn 1 x ≤ Bx x := by
  by_contra h
  push Not at h
  have := hn_sq_le_Bx_sq38 hx
  nlinarith [Bx_nonneg38 x]

theorem continuous_Bx_coe38 : Continuous fun y : H1C38 => Bx (carrierCoe38 _ y) := by
  unfold Bx
  exact Real.continuous_sqrt.comp
    (continuous_mass_coe.add (continuous_ham_coe.div_const _))

theorem hn_one_continuous38 {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) : Continuous fun t => hn 1 (u t) := by
  have := hu.cont.norm
  refine this.congr fun t => ?_
  exact (hn_one_eq_norm _ (hu.mem t)).symm

theorem hn_one_continuous_cut38 {R : ℝ} {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) :
    Continuous fun t => hn 1 (u t) := by
  have := hu.cont.norm
  refine this.congr fun t => ?_
  exact (hn_one_eq_norm _ (hu.mem t)).symm

/-! ## `h³` data -/

theorem inactive_h3_38 {x : ℤ → ℂ} (hx3 : x ∈ seqSobolev38 ((3 : ℕ) : ℝ)) (R : ℝ)
    (hR : Bx x + 2 ≤ R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) (h0 : u 0 = x) :
    ∀ t, hn 1 (u t) ≤ Bx x ∧ mass (u t) = mass x ∧ ham (u t) = ham x := by
  have hR0 : 0 < R := by linarith [Bx_nonneg38 x]
  have h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ) := h0 ▸ hx3
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := h0 ▸ hu.mem 0
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hsq : ∀ t, hn 1 (u t) ^ 2 =
      mass (u t) + kin (u t) / (4 * Real.pi ^ 2) := fun t => hn_one_sq (hu.mem t)
  have hbound : ∀ t, mass (u t) = mass x → ham (u t) = ham x → hn 1 (u t) ^ 2 ≤ Bx x ^ 2 := by
    intro t hm hh
    rw [hsq, Bx_sq38, ← hm, ← hh]
    have : kin (u t) / (4 * Real.pi ^ 2) ≤ ham (u t) / (4 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right (by rw [ham_def]; linarith [quart_nonneg (u t)]) hpi.le
    linarith
  have hφ : Continuous fun t => hn 1 (u t) ^ 2 := (hn_one_continuous_cut38 hu).pow 2
  have hBR : Bx x ^ 2 < R ^ 2 := by nlinarith [Bx_nonneg38 x]
  have hno := no_exit hφ hBR (by
      have := hn_sq_le_Bx_sq38 hx1
      simpa [h0] using this) (fun t hlt => by
    have hin : ∀ s ∈ Set.uIcc 0 t, hn 1 (u s) < R := fun s hs => by
      by_contra hc
      push Not at hc
      have := hlt s hs
      nlinarith [hn_nonneg38 1 (u s)]
    obtain ⟨hm, hh⟩ := conserved_inside R hR0 hu h3 t hin
    rw [h0] at hm hh
    exact hbound t hm hh)
  intro t
  have hle : hn 1 (u t) ≤ Bx x := by
    by_contra hc
    push Not at hc
    have := hno t
    nlinarith [Bx_nonneg38 x]
  have hin : ∀ s ∈ Set.uIcc 0 t, hn 1 (u s) < R := fun s _ => by
    have : hn 1 (u s) ≤ Bx x := by
      by_contra hc
      push Not at hc
      have := hno s
      nlinarith [Bx_nonneg38 x]
    linarith
  obtain ⟨hm, hh⟩ := conserved_inside R hR0 hu h3 t hin
  rw [h0] at hm hh
  exact ⟨hle, hm, hh⟩

/-! ## `h¹` data by density -/

theorem conserved_limit38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) {u : ℝ → ℤ → ℂ}
    (hu : IsCutSol (Bx x + 3) u) (h0 : u 0 = x) :
    ∀ t, mass (u t) = mass x ∧ ham (u t) = ham x := by
  intro t
  have hR0 : 0 < Bx x + 3 := by linarith [Bx_nonneg38 x]
  set X : H1C38 := carrierMk38 ((1 : ℕ) : ℝ) x hx with hX
  have hXc : carrierCoe38 _ X = x := rfl
  set XN : ℕ → H1C38 := fun N => projC38 ((1 : ℕ) : ℝ) N X with hXN
  have hXNt : Tendsto XN atTop (𝓝 X) := tendsto_projC38 _ X
  have hxN3 : ∀ N, carrierCoe38 _ (XN N) ∈ seqSobolev38 ((3 : ℕ) : ℝ) := fun N => by
    refine finiteSupport_mem_seqSobolev38 _ _ ((symmetricModes N).finite_toSet.subset fun n hn => ?_)
    by_contra hc
    exact hn (by simp [hXN, carrierCoe38_projC38, Finset.mem_coe.not.1 hc])
  choose uN huN h0N using fun N : ℕ =>
    exists_cutSol (Bx x + 3) hR0 (carrierCoe38 _ (XN N)) (carrierCoe38_mem _ _)
  obtain ⟨L, hL⟩ := cutSol_lipschitz (Bx x + 3) hR0
  set U : H1C38 := carrierMk38 ((1 : ℕ) : ℝ) (u t) (hu.mem t) with hU
  set UN : ℕ → H1C38 := fun N => carrierMk38 ((1 : ℕ) : ℝ) (uN N t) ((huN N).mem t) with hUN
  have hle : ∀ N, ‖UN N - U‖ ≤ Real.exp (L * |t|) * ‖XN N - X‖ := fun N => by
    have h := hL (uN N) u (huN N) hu t
    rw [h0N N, h0] at h
    have e1 : ‖UN N - U‖ = hn 1 (fun n => uN N t n - u t n) := (hn_coe38 1 (UN N - U)).symm
    have e2 : ‖XN N - X‖ = hn 1 (fun n => carrierCoe38 _ (XN N) n - x n) :=
      (hn_coe38 1 (XN N - X)).symm
    rw [e1, e2]
    exact h
  have hUt : Tendsto UN atTop (𝓝 U) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun N => Real.exp (L * |t|) * ‖XN N - X‖) atTop (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 hXNt).const_mul (Real.exp (L * |t|)))
      simpa using this
    exact squeeze_zero (fun _ => norm_nonneg _) hle h2
  -- eventually the cutoff `Bx x + 3` is inactive for the truncated data
  have hev : ∀ᶠ N in atTop, Bx (carrierCoe38 _ (XN N)) + 2 ≤ Bx x + 3 := by
    have hF := (continuous_Bx_coe38.tendsto X).comp hXNt
    have := hF.eventually (Iio_mem_nhds (show Bx (carrierCoe38 _ X) < Bx x + 1 by
      rw [hXc]; linarith))
    filter_upwards [this] with N hN
    simp only [Function.comp] at hN
    linarith
  have hcons : ∀ᶠ N in atTop, mass (carrierCoe38 _ (UN N)) = mass (carrierCoe38 _ (XN N)) ∧
      ham (carrierCoe38 _ (UN N)) = ham (carrierCoe38 _ (XN N)) := by
    filter_upwards [hev] with N hN
    have := inactive_h3_38 (hxN3 N) (Bx x + 3) hN (huN N) (h0N N) t
    exact ⟨this.2.1, this.2.2⟩
  have hm1 := (continuous_mass_coe.tendsto U).comp hUt
  have hm2 := (continuous_mass_coe.tendsto X).comp hXNt
  have hh1 := (continuous_ham_coe.tendsto U).comp hUt
  have hh2 := (continuous_ham_coe.tendsto X).comp hXNt
  have em := tendsto_nhds_unique_of_eventuallyEq hm1 hm2 (hcons.mono fun N h => h.1)
  have eh := tendsto_nhds_unique_of_eventuallyEq hh1 hh2 (hcons.mono fun N h => h.2)
  exact ⟨em, eh⟩

theorem cutSol_inactive (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (R : ℝ)
    (hR : Bx x + 2 ≤ R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) (h0 : u 0 = x) :
    ∀ t, hn 1 (u t) ≤ Bx x ∧ mass (u t) = mass x ∧ ham (u t) = ham x := by
  have hR0 : 0 < R := by linarith [Bx_nonneg38 x]
  have hR3 : 0 < Bx x + 3 := by linarith [Bx_nonneg38 x]
  obtain ⟨v, hv, hv0⟩ := exists_cutSol (Bx x + 3) hR3 x hx
  have hcons := conserved_limit38 hx hv hv0
  have hbv : ∀ t, hn 1 (v t) ≤ Bx x := fun t => by
    have h := hn_le_Bx38 (hv.mem t)
    have : Bx (v t) = Bx x := by
      unfold Bx; rw [(hcons t).1, (hcons t).2]
    linarith
  have hvn : IsNLSSol v := isNLSSol_of_cutSol hv fun t => by linarith [hbv t]
  have hvR : IsCutSol R v := isCutSol_of_nlsSol hvn fun t => by linarith [hbv t]
  have huv : u = v := cutSol_unique R hR0 hu hvR (by rw [h0, hv0])
  subst huv
  exact fun t => ⟨hbv t, hcons t⟩

theorem cutSol_isNLSSol (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (R : ℝ)
    (hR : Bx x + 2 ≤ R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) (h0 : u 0 = x) : IsNLSSol u :=
  isNLSSol_of_cutSol hu fun t => by
    linarith [(cutSol_inactive x hx R hR hu h0 t).1]

theorem nls_exists (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    ∃ u : ℝ → ℤ → ℂ, IsNLSSol u ∧ u 0 = x := by
  have hR0 : 0 < Bx x + 2 := by linarith [Bx_nonneg38 x]
  obtain ⟨u, hu, h0⟩ := exists_cutSol (Bx x + 2) hR0 x hx
  exact ⟨u, cutSol_isNLSSol x hx _ le_rfl hu h0, h0⟩

/-! ## Uniqueness (interval-local, note N1) -/

theorem exists_bound_on_Icc38 {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) (T : ℝ) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc (-T) T, hn 1 (u t) ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (hn_one_continuous38 hu).continuousOn
  exact ⟨B, fun t ht => (le_abs_self _).trans (hB t ht)⟩

theorem nls_unique {u w : ℝ → ℤ → ℂ} (hu : IsNLSSol u) (hw : IsNLSSol w) (h0 : u 0 = w 0) :
    u = w := by
  funext t
  set T : ℝ := |t| + 1 with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨Bu, hBu⟩ := exists_bound_on_Icc38 hu T
  obtain ⟨Bw, hBw⟩ := exists_bound_on_Icc38 hw T
  have hR : 0 < max (max Bu Bw) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine nls_unique_on (max (max Bu Bw) 1) T hR hT0 hu hw h0
    (fun s hs => (hBu s hs).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun s hs => (hBw s hs).trans ((le_max_right _ _).trans (le_max_left _ _))) t ?_
  constructor <;> (have := abs_nonneg t; have := neg_abs_le t; have := le_abs_self t; linarith)

/-! ## Conservation -/

theorem nls_conserved {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) :
    ∀ t, mass (u t) = mass (u 0) ∧ ham (u t) = ham (u 0) := by
  intro t
  have hx := hu.mem 0
  have hR0 : 0 < Bx (u 0) + 2 := by linarith [Bx_nonneg38 (u 0)]
  obtain ⟨v, hv, hv0⟩ := exists_cutSol (Bx (u 0) + 2) hR0 (u 0) hx
  have hvn := cutSol_isNLSSol _ hx _ le_rfl hv hv0
  have huv : v = u := nls_unique hvn hu hv0
  subst huv
  exact ⟨(cutSol_inactive _ hx _ le_rfl hv hv0 t).2.1, (cutSol_inactive _ hx _ le_rfl hv hv0 t).2.2⟩

/-! ## Regression probes: plane waves -/

section Probes

theorem planeWaveAmp38_zero (k : ℤ) (a : ℂ) : planeWaveAmp38 k a 0 = a := by
  simp [planeWaveAmp38]

/-- `Bx` of a plane wave: `Bx² = (1 + k²)|a|² + |a|⁴ / (4π²)`. -/
theorem Bx_single_sq38 (k : ℤ) (a : ℂ) :
    Bx (Pi.single k a) ^ 2 = (1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2 + ‖a‖ ^ 4 / (4 * Real.pi ^ 2) := by
  rw [Bx_sq38, ham_def, mass_single, kin_single, quart_single, disp_eq]
  have : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `nls_exists` and `nls_unique` on a plane wave agree with `isNLSSol_planeWave`: the solution
through `δ_k a` is the plane wave, mass and energy are constant. -/
theorem nls_planeWave_probe38 (k : ℤ) (a : ℂ) :
    ∃ u : ℝ → ℤ → ℂ, IsNLSSol u ∧ u 0 = Pi.single k a ∧
      u = (fun t => (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ)) ∧
      ∀ t, mass (u t) = ‖a‖ ^ 2 ∧ ham (u t) = disp k * ‖a‖ ^ 2 + ‖a‖ ^ 4 := by
  obtain ⟨u, hu, h0⟩ := nls_exists (Pi.single k a) (single_mem_h1 k a)
  have hpw := isNLSSol_planeWave k a
  have h0' : u 0 = (Pi.single k (planeWaveAmp38 k a 0) : ℤ → ℂ) := by
    rw [h0]; simp [planeWaveAmp38_zero]
  have huw := nls_unique hu hpw h0'
  refine ⟨u, hu, h0, huw, fun t => ?_⟩
  have := nls_conserved hu t
  rw [h0, mass_single] at this
  refine ⟨this.1, ?_⟩
  rw [this.2, ham_def, kin_single, quart_single]

/-- `nls_unique` forces any solution through `δ_k a` to be the plane wave. -/
theorem nls_unique_planeWave38 (k : ℤ) (a : ℂ) {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u)
    (h0 : u 0 = Pi.single k a) : u = fun t => (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ) :=
  nls_unique hu (isNLSSol_planeWave k a) (by rw [h0]; simp [planeWaveAmp38_zero])

end Probes

end NlsGge.NLS38
