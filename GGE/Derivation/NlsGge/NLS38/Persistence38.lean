import NlsGge.NLS38.Persistence38a

/-! # GWP piece A6a: persistence of regularity for cutoff solutions

Plan: `campaign/GWP_PLAN.md` §5.1 item 4 and §7 Part A, piece A6a (revised: note N2, risk R4).

* `cutSol_persistence m hm`: for every `R > 0`, an `h^1` cutoff solution with `u 0 ∈ h^m` is an
  `IsCutSolM m R` solution, and `hn m (u t) ≤ hn m (u 0) e^{C R² |t|}` with `C` depending only on `m`.
  Proof by frequency-truncated weights (`Persistence38a`): the `h^m` norm of an `h^1` solution is never
  differentiated; the monotone limit `K → ∞` gives membership and the bound.  Continuity in `h^m` is a
  Lipschitz-in-time estimate for the interaction variable `v = e^{itΛ} u`, again with truncated weights
  (mean-value inequality for `t ↦ TK v(t)` and the same limit).
* `cutSol_C1_h1`: for `h³` data the solution is a `C¹` curve of the `h¹` carrier.

Cast convention (§6.0): all Sobolev indices are natural casts.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal InnerProductSpace

/-! ## Continuity in `h^m` -/

theorem carrierMk38_eq_phaseC38 (m : ℕ) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) (t : ℝ)
    {y : ℤ → ℂ} (hy : y ∈ seqSobolev38 (m : ℝ)) (h : y = phase (-t) x) :
    carrierMk38 (m : ℝ) x hx = phaseC (m : ℝ) t (carrierMk38 (m : ℝ) y hy) := by
  apply carrierExt38
  rw [carrierCoe38_mk, carrierCoe38_phaseC, carrierCoe38_mk, h, phase_phase_neg_apply]

/-- Continuity of a cutoff solution in `h^m`, given `K`-uniform locally bounded truncated norms. -/
theorem cutSol_cont_hm38 (m : ℕ) (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ}
    (hu : IsCutSol R u) (hmem : ∀ t, u t ∈ seqSobolev38 (m : ℝ))
    (hbd : ∀ T : ℝ, ∃ B : ℝ, ∀ (K : ℕ) (t : ℝ), |t| ≤ T → wl2 (wK m K) (u t) ≤ B) :
    Continuous fun t => carrierMk38 (m : ℝ) (u t) (hmem t) := by
  obtain ⟨C0, hC0, hC⟩ := hnK_nonlin_le m hm
  obtain ⟨v, hv1, hv2⟩ := cutSol_interaction38 hu
  have hmv : ∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (v t) ∈ seqSobolev38 (m : ℝ) := fun t => by
    rw [hv1]; exact phase_mem_seqSobolev38 _ _ (hmem t)
  let W : ℝ → SobolevCarrier38 (m : ℝ) := fun t =>
    carrierMk38 (m : ℝ) (carrierCoe38 ((1 : ℕ) : ℝ) (v t)) (hmv t)
  have hWu : ∀ t, carrierMk38 (m : ℝ) (u t) (hmem t) = phaseC (m : ℝ) t (W t) := fun t => by
    exact carrierMk38_eq_phaseC38 m (hmem t) t (hmv t) (hv1 t)
  have hW : Continuous W := by
    refine continuous_iff_continuousAt.2 fun t0 => ?_
    set T : ℝ := |t0| + 1 with hT
    obtain ⟨B, hB⟩ := hbd T
    have hB0 : 0 ≤ B := (wl2_nonneg38 _ _).trans (hB 0 0 (by rw [abs_zero]; positivity))
    have hlip : ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, dist (W t) (W s) ≤ (4 * R ^ 2 * C0 * B) * dist t s := by
      intro s hs t ht
      have hTab : ∀ r ∈ Icc (-T) T, |r| ≤ T := fun r hr => abs_le.2 hr
      have key : ∀ K : ℕ, wl2 (wK m K) (fun n => carrierCoe38 ((1 : ℕ) : ℝ) (v t) n -
          carrierCoe38 ((1 : ℕ) : ℝ) (v s) n) ≤ 4 * R ^ 2 * C0 * B * dist t s := by
        intro K
        have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => TK38 m K (v r)) (f' := fun r => TK38 m K (Gc 1 le_rfl R r (v r)))
          (s := Icc (-T) T) (C := 4 * R ^ 2 * C0 * B)
          (fun r _ => (hasDerivAt_TK38 m K (hv2 r)).hasDerivWithinAt)
          (fun r hr => by
            refine (norm_TK_Gc_le38 m K hC0.le (fun K x hx => (hC K x hx).2) hR hu.mem hv1 r).trans ?_
            exact mul_le_mul_of_nonneg_left (hB K r (hTab r hr)) (by positivity))
          (convex_Icc _ _) hs ht
        rw [← map_sub, norm_TK38] at h
        rw [Real.dist_eq, ← Real.norm_eq_abs]
        exact h
      have hx1 : (fun n => carrierCoe38 ((1 : ℕ) : ℝ) (v t) n - carrierCoe38 ((1 : ℕ) : ℝ) (v s) n) ∈
          seqSobolev38 ((1 : ℕ) : ℝ) := carrierCoe38_mem _ (v t - v s)
      obtain ⟨-, hh⟩ := mem_and_hn_le_of_wK38 m hx1 key
      rw [dist_eq_norm, ← hn_coe38 m (W t - W s)]
      exact hh
    have hc : ContinuousOn W (Icc (-T) T) := by
      refine (LipschitzOnWith.of_dist_le_mul (K := (4 * R ^ 2 * C0 * B).toNNReal) fun s hs t ht => ?_).continuousOn
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hlip t ht s hs
    exact hc.continuousAt (Icc_mem_nhds (by rw [hT]; linarith [neg_abs_le t0, abs_nonneg t0])
      (by rw [hT]; linarith [le_abs_self t0]))
  have : (fun t => carrierMk38 (m : ℝ) (u t) (hmem t)) = fun t => phaseC (m : ℝ) t (W t) := funext hWu
  rw [this]
  exact (continuous_phaseC (m : ℝ)).comp (continuous_id.prodMk hW)

/-! ## Persistence -/

/-- **Persistence of regularity for cutoff solutions** (A6a). -/
theorem cutSol_persistence (m : ℕ) (hm : 1 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
    (u : ℝ → ℤ → ℂ), IsCutSol R u → u 0 ∈ seqSobolev38 (m : ℝ) →
    IsCutSolM m R u ∧ ∀ t, hn m (u t) ≤ hn m (u 0) * Real.exp (C * R ^ 2 * |t|) := by
  obtain ⟨C, hC, hb⟩ := cutSol_wK_bound38 m hm
  refine ⟨C, hC, fun R hR u hu h0 => ?_⟩
  have hK : ∀ (K : ℕ) (t : ℝ), wl2 (wK m K) (u t) ≤ hn m (u 0) * Real.exp (C * R ^ 2 * |t|) :=
    fun K t => (hb R hR u hu K t).trans
      (mul_le_mul_of_nonneg_right (wl2_wK_le_hn38 m K hm h0) (Real.exp_nonneg _))
  have hlim : ∀ t, u t ∈ seqSobolev38 (m : ℝ) ∧ hn m (u t) ≤ hn m (u 0) * Real.exp (C * R ^ 2 * |t|) :=
    fun t => mem_and_hn_le_of_wK38 m (hu.mem t) (fun K => hK K t)
  refine ⟨⟨fun t => (hlim t).1, cutSol_cont_hm38 m hm hR hu (fun t => (hlim t).1) ?_, hu.deriv⟩,
    fun t => (hlim t).2⟩
  intro T
  refine ⟨hn m (u 0) * Real.exp (C * R ^ 2 * T), fun K t ht => (hK K t).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht (by positivity)))
    (hn_nonneg38 _ _)

/-! ## `C¹` in `h¹` for `h³` data -/

/-- The derivative of `s ↦ e^{-isΛ}`-twisted curves, with the index shift `r + 2 = s` as a hypothesis
(so that casts such as `((1 : ℕ) : ℝ) + 2 = ((3 : ℕ) : ℝ)` need no transport of carriers). -/
theorem hasDerivAt_phase_incl38 (r s : ℝ) (hs : r + 2 = s) (h : r ≤ s) {γ : ℝ → SobolevCarrier38 s}
    {γ' : SobolevCarrier38 s} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    ∃ D : SobolevCarrier38 r, HasDerivAt (fun τ => carrierIncl38 h (phaseC s τ (γ τ))) D t ∧
      ∀ n, carrierCoe38 r D n = phase t (carrierCoe38 s γ') n +
        (-(Complex.I * ((disp n : ℝ) : ℂ))) * phase t (carrierCoe38 s (γ t)) n := by
  subst hs
  refine ⟨_, hasDerivAt_phaseC_comp r hγ, fun n => ?_⟩
  show carrierCoe38 r (carrierIncl38 _ (phaseC (r + 2) t γ')) n +
    carrierCoe38 r (lam r (phaseC (r + 2) t (γ t))) n = _
  rw [carrierCoe38_incl38, carrierCoe38_lam, carrierCoe38_phaseC]
  rfl

theorem cutSol_mem_h3 {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u)
    (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ)) : IsCutSolM 3 R u :=
  (cutSol_persistence 3 (by norm_num)).choose_spec.2 R hR u hu h3 |>.1

/-- Auxiliary form of `cutSol_C1_h1`: the derivative is exhibited with its coordinates. -/
theorem cutSol_C1_h1_aux {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u)
    (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    ∃ γ : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ), (∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (γ t) = u t) ∧
      ∀ t, ∃ D : SobolevCarrier38 ((1 : ℕ) : ℝ), HasDerivAt γ D t ∧
        carrierCoe38 ((1 : ℕ) : ℝ) D = fun n => -Complex.I * (((disp n : ℝ) : ℂ) * u t n +
          ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n) := by
  have h3' := cutSol_mem_h3 hR hu h3
  obtain ⟨hmem, v, hv1, hv2⟩ := (isCutSolM_iff 3 (by norm_num) R u).1 h3'
  have hrs : ((1 : ℕ) : ℝ) + 2 = ((3 : ℕ) : ℝ) := by norm_num
  have hle : ((1 : ℕ) : ℝ) ≤ ((3 : ℕ) : ℝ) := by norm_num
  refine ⟨fun τ => carrierIncl38 hle (phaseC ((3 : ℕ) : ℝ) τ (v τ)), fun t => ?_, fun t => ?_⟩
  · rw [carrierCoe38_incl38, carrierCoe38_phaseC, hv1, phase_phase_neg_apply]
  · obtain ⟨D, hD, hDc⟩ := hasDerivAt_phase_incl38 _ _ hrs hle (hv2 t)
    refine ⟨D, hD, funext fun n => ?_⟩
    have hph : phase t (carrierCoe38 ((3 : ℕ) : ℝ) (v t)) = u t := by
      rw [hv1, phase_phase_neg_apply]
    have hn1 : hn 1 (carrierCoe38 ((3 : ℕ) : ℝ) (v t)) = hn 1 (u t) := by
      rw [hv1, hn_phase38]
    have hG := carrierCoe38_Gchi 3 (by norm_num) (cutoff R) t (v t) n
    rw [norm_inclOne38_eq_hn, hn1, hph] at hG
    have hG' : carrierCoe38 ((3 : ℕ) : ℝ) (Gc 3 (by norm_num) R t (v t)) n = _ := hG
    have hu_n : phase t (carrierCoe38 ((3 : ℕ) : ℝ) (v t)) n = u t n := congrFun hph n
    have hpG : phase t (carrierCoe38 ((3 : ℕ) : ℝ) (Gc 3 (by norm_num) R t (v t))) n =
        Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) *
          carrierCoe38 ((3 : ℕ) : ℝ) (Gc 3 (by norm_num) R t (v t)) n := rfl
    rw [hDc, hu_n, hpG, hG']
    have hexp : Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) *
        Complex.exp (-(Complex.I * ((-t * disp n : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast; ring
    linear_combination (-(Complex.I * ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) * hexp

/-- The right-hand side `-i(Λu + χ N(u))` lies in `h¹` for `h³` data (the proof obligation `_` of the
plan statement of `cutSol_C1_h1`). -/
theorem cutSol_rhs_mem38 {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u)
    (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ)) (t : ℝ) :
    (fun n => -Complex.I * (((disp n : ℝ) : ℂ) * u t n +
      ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
  obtain ⟨γ, -, hγ⟩ := cutSol_C1_h1_aux hR hu h3
  obtain ⟨D, -, hD⟩ := hγ t
  rw [← hD]
  exact carrierCoe38_mem _ D

/-- **`C¹` regularity in `h¹` for `h³` data** (A6a). -/
theorem cutSol_C1_h1 (R : ℝ) (hR : 0 < R) (u : ℝ → ℤ → ℂ) (hu : IsCutSol R u)
    (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    ∃ γ : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ), (∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (γ t) = u t) ∧
      ∀ t, HasDerivAt γ (carrierMk38 ((1 : ℕ) : ℝ) (fun n => -Complex.I *
        (((disp n : ℝ) : ℂ) * u t n + ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n))
        (cutSol_rhs_mem38 hR hu h3 t)) t := by
  obtain ⟨γ, hγ0, hγ⟩ := cutSol_C1_h1_aux hR hu h3
  refine ⟨γ, hγ0, fun t => ?_⟩
  obtain ⟨D, hD, hDc⟩ := hγ t
  have : carrierMk38 ((1 : ℕ) : ℝ) (fun n => -Complex.I *
      (((disp n : ℝ) : ℂ) * u t n + ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n))
      (cutSol_rhs_mem38 hR hu h3 t) = D := by
    apply carrierExt38
    rw [carrierCoe38_mk, hDc]
  rw [this]
  exact hD

/-! ## Regression probes (plane waves) -/

section Probes

theorem hn_single38 (m : ℕ) (k : ℤ) (a : ℂ) : hn m (Pi.single k a) = japaneseBracket k ^ m * ‖a‖ := by
  rw [hn_eq_wl2_38, wl2_single38 _ (fun n => by have := japaneseBracket_pos n; positivity)]

/-- The plane wave keeps its `h^m` norm: consistent with the persistence bound for every `C`. -/
theorem hn_planeWave_const38 (m : ℕ) (k : ℤ) (a : ℂ) (t : ℝ) :
    hn m (Pi.single k (planeWaveAmp38 k a t)) = hn m (Pi.single k (planeWaveAmp38 k a 0)) := by
  have h : ∀ s, ‖planeWaveAmp38 k a s‖ = ‖a‖ := fun s => by
    unfold planeWaveAmp38
    rw [norm_mul, norm_phaseFactor, one_mul]
  rw [hn_single38, hn_single38, h, h]

/-- End-to-end probe: the plane wave through `δ_k a` (`⟨k⟩‖a‖ ≤ R`) is an `h^m` cutoff solution, and
`cutSol_persistence` applies to it. -/
theorem planeWave_persistence38 (m : ℕ) (hm : 1 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (k : ℤ) (a : ℂ),
    Real.sqrt ((1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2) ≤ R →
    IsCutSolM m R (fun t => Pi.single k (planeWaveAmp38 k a t)) ∧
      ∀ t, hn m (Pi.single k (planeWaveAmp38 k a t)) ≤
        hn m (Pi.single k (planeWaveAmp38 k a 0)) * Real.exp (C * R ^ 2 * |t|) := by
  obtain ⟨C, hC, h⟩ := cutSol_persistence m hm
  exact ⟨C, hC, fun R hR k a hRa =>
    h R hR _ (isCutSol_planeWave R k a hRa) (single_mem_seqSobolev38 _ k _)⟩

/-- Gronwall probe (equality case, both time directions): `S t = e^{c t}` has `S' = c S`. -/
theorem scalar_gronwall_exp_probe38 (c : ℝ≥0) (t : ℝ) :
    Real.exp (c * t) ≤ Real.exp (c * |t|) := by
  have h := scalar_gronwall_two_sided38 (S := fun s => Real.exp (c * s))
    (S' := fun s => c * Real.exp (c * s)) (c := c)
    (fun s => by
      have := ((hasDerivAt_id s).const_mul (c : ℝ)).exp
      simpa [mul_comm] using this)
    (fun s => by
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _), NNReal.abs_eq])
    t
  simpa [abs_of_nonneg (Real.exp_nonneg _)] using h

end Probes

end NlsGge.NLS38
