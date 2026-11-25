import NlsGge.NLS38.SolutionNotion38b

/-! # GWP piece A4: solution notions, interaction picture, interval-local link (entry point)

Plan: `campaign/GWP_PLAN.md` §6.1, §7 Part A (piece A4, revised after the G1 review, note N1).
Definitions (`cutoff`, `IsNLSSolM`, `IsCutSolM`, `Gc`, `Gn`) are in `SolutionNotion38a`, the generic
equivalence `isChiSolM_iff` in `SolutionNotion38b`.  Here:

* `isCutSolM_iff`, `isNLSSolM_iff` (carrier ODE `v' = G(t, v)` for `v = e^{itΛ}u`),
* `Gc_eq_Gn_of_norm_le`, `nlsSol_cutOn` (note N1: interval-local link, no global bound),
* `isNLSSol_iff_cutSol` (GLOBAL in time, existence direction only; see the docstring for the
  corrected form of the plan's statement), `hn_one_eq_norm`,
* time shift and reflection symmetry of solutions.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate NNReal

/-! ## Specialisations of the generic equivalence -/

theorem isCutSolM_iff_chi (m : ℕ) (R : ℝ) (u : ℝ → ℤ → ℂ) :
    IsCutSolM m R u ↔ IsChiSolM m (cutoff R) u :=
  ⟨fun h => ⟨h.mem, h.cont, h.deriv⟩, fun h => ⟨h.mem, h.cont, h.deriv⟩⟩

theorem isNLSSolM_iff_chi (m : ℕ) (u : ℝ → ℤ → ℂ) :
    IsNLSSolM m u ↔ IsChiSolM m (fun _ => 1) u := by
  constructor
  · intro h
    exact ⟨h.mem, h.cont, fun t n => by simpa using h.deriv t n⟩
  · intro h
    exact ⟨h.mem, h.cont, fun t n => by simpa using h.deriv t n⟩

theorem isCutSolM_iff (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (u : ℝ → ℤ → ℂ) :
    IsCutSolM m R u ↔
      ∃ (hmem : ∀ t, u t ∈ seqSobolev38 (m : ℝ)) (v : ℝ → SobolevCarrier38 (m : ℝ)),
        (∀ t, carrierCoe38 (m : ℝ) (v t) = phase (-t) (u t)) ∧
          ∀ t, HasDerivAt v (Gc m hm R t (v t)) t := by
  rw [isCutSolM_iff_chi]
  exact isChiSolM_iff m hm (cutoff_continuous R) u

theorem isNLSSolM_iff (m : ℕ) (hm : 1 ≤ m) (u : ℝ → ℤ → ℂ) :
    IsNLSSolM m u ↔
      ∃ (hmem : ∀ t, u t ∈ seqSobolev38 (m : ℝ)) (v : ℝ → SobolevCarrier38 (m : ℝ)),
        (∀ t, carrierCoe38 (m : ℝ) (v t) = phase (-t) (u t)) ∧
          ∀ t, HasDerivAt v (Gn m hm t (v t)) t := by
  rw [isNLSSolM_iff_chi, isChiSolM_iff m hm (χ := fun _ => (1 : ℝ)) continuous_const]
  simp only [Gn_eq_Gchi]

/-! ## The interval-local link (review note N1) -/

theorem cutoff_eq_one_of_nonneg {R r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ R) : cutoff R r = 1 := by
  rcases lt_trichotomy R 0 with hR | hR | hR
  · linarith
  · subst hR
    have : r = 0 := le_antisymm hr hr0
    subst this
    simp [cutoff]
  · exact cutoff_eq_one hR hr

/-- Where `‖v‖_{h¹} ≤ R` the cutoff is inactive. -/
theorem Gc_eq_Gn_of_norm_le (m : ℕ) (hm : 1 ≤ m) (R t : ℝ) {v : SobolevCarrier38 (m : ℝ)}
    (hv : ‖carrierIncl38 (Nat.cast_le.2 hm : ((1 : ℕ) : ℝ) ≤ (m : ℝ)) v‖ ≤ R) :
    Gc m hm R t v = Gn m hm t v := by
  unfold Gc Gn
  rw [cutoff_eq_one_of_nonneg (norm_nonneg _) hv, one_smul]

/-- Interval-local link: a true solution bounded by `R` in `h¹` on `[-T, T]` has an interaction
picture solving the cutoff ODE on `[-T, T]`.  No global bound on `u` is assumed. -/
theorem nlsSol_cutOn (R T : ℝ) {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u)
    (hb : ∀ t ∈ Set.Icc (-T) T, hn 1 (u t) ≤ R) :
    ∃ v : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (v t) = phase (-t) (u t)) ∧
        ContinuousOn v (Set.Icc (-T) T) ∧
        ∀ t ∈ Set.Icc (-T) T, HasDerivAt v (Gc 1 le_rfl R t (v t)) t := by
  obtain ⟨hmem, v, hcoe, hv⟩ := (isNLSSolM_iff 1 le_rfl u).1 hu
  refine ⟨v, hcoe, fun t _ => (hv t).continuousAt.continuousWithinAt, fun t ht => ?_⟩
  have hnorm : ‖inclOne38 1 le_rfl (v t)‖ ≤ R := by
    rw [norm_inclOne38_eq_hn, hcoe t, hn_phase38]
    exact hb t ht
  have := Gc_eq_Gn_of_norm_le 1 le_rfl R t hnorm
  rw [this]
  exact hv t

/-! ## The global-in-time link (existence direction) -/

/-- GLOBAL in time: used only for the existence direction (A8 `cutSol_isNLSSol`), never for
uniqueness (that is `nlsSol_cutOn`).

Defect of the plan's statement, recorded in `STATUS.md`: `IsNLSSol u ↔ IsCutSol R u ∧ ∀ t, hn 1 (u t) ≤ R`
quantified over all `R` and `u` is false (`isNLSSol_iff_cutSol_verbatim_false` below: `u = 0`,
`R = -1`; for `R > 0` any plane wave with `‖a‖ > R`), because a true solution need not satisfy the
bound.  The correct statement assumes the bound on the left. -/
theorem isNLSSol_iff_cutSol (R : ℝ) (u : ℝ → ℤ → ℂ) (hb : ∀ t, hn 1 (u t) ≤ R) :
    IsNLSSol u ↔ IsCutSol R u := by
  have hc : ∀ t, cutoff R (hn 1 (u t)) = 1 := fun t =>
    cutoff_eq_one_of_nonneg (by unfold hn; exact Real.sqrt_nonneg _) (hb t)
  constructor
  · intro h
    exact ⟨h.mem, h.cont, fun t n => by simpa [hc t] using h.deriv t n⟩
  · intro h
    exact ⟨h.mem, h.cont, fun t n => by simpa [hc t] using h.deriv t n⟩

/-- Existence direction in the form used by A8: a cutoff solution bounded by `R` is a true solution. -/
theorem isNLSSol_of_cutSol {R : ℝ} {u : ℝ → ℤ → ℂ} (hu : IsCutSol R u) (hb : ∀ t, hn 1 (u t) ≤ R) :
    IsNLSSol u :=
  (isNLSSol_iff_cutSol R u hb).2 hu

theorem isCutSol_of_nlsSol {R : ℝ} {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) (hb : ∀ t, hn 1 (u t) ≤ R) :
    IsCutSol R u :=
  (isNLSSol_iff_cutSol R u hb).1 hu

theorem isNLSSol_zero : IsNLSSol (fun _ _ => (0 : ℂ)) := by
  refine ⟨fun t => (weightedSubmodule (sobolevModeWeight ((1 : ℕ) : ℝ))).zero_mem, ?_, fun t n => ?_⟩
  · exact continuous_const
  · have h0 : nonlin (fun _ => (0 : ℂ)) n = 0 := congrFun nonlin_zero38 n
    simp only [h0]
    simpa using hasDerivAt_const t (0 : ℂ)

/-- The plan's `isNLSSol_iff_cutSol`, read verbatim (`∀ R u`, bound on the right-hand side only), is
false: `u = 0` is a solution, but `hn 1 0 = 0 > -1`. -/
theorem isNLSSol_iff_cutSol_verbatim_false :
    ¬ ∀ (R : ℝ) (u : ℝ → ℤ → ℂ), IsNLSSol u ↔ IsCutSol R u ∧ ∀ t, hn 1 (u t) ≤ R := by
  intro h
  have h1 := ((h (-1) (fun _ _ => 0)).1 isNLSSol_zero).2 0
  have h2 : hn 1 (fun _ : ℤ => (0 : ℂ)) = 0 := by simp [hn]
  rw [h2] at h1
  linarith

theorem hn_one_eq_norm (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    hn 1 x = ‖carrierMk38 ((1 : ℕ) : ℝ) x hx‖ :=
  (norm_carrierMk38_eq_hn 1 x hx).symm

/-! ## Time shift -/

theorem isChiSolM_shift {m : ℕ} {χ : ℝ → ℝ} {u : ℝ → ℤ → ℂ} (h : IsChiSolM m χ u) (s : ℝ) :
    IsChiSolM m χ (fun t => u (t + s)) :=
  ⟨fun t => h.mem (t + s), h.cont.comp (by fun_prop : Continuous fun t : ℝ => t + s),
    fun t n => (h.deriv (t + s) n).comp_add_const t s⟩

theorem isNLSSol_shift {m : ℕ} {u : ℝ → ℤ → ℂ} (h : IsNLSSolM m u) (s : ℝ) :
    IsNLSSolM m (fun t => u (t + s)) :=
  (isNLSSolM_iff_chi m _).2 (isChiSolM_shift ((isNLSSolM_iff_chi m u).1 h) s)

theorem isCutSol_shift {m : ℕ} {R : ℝ} {u : ℝ → ℤ → ℂ} (h : IsCutSolM m R u) (s : ℝ) :
    IsCutSolM m R (fun t => u (t + s)) :=
  (isCutSolM_iff_chi m R _).2 (isChiSolM_shift ((isCutSolM_iff_chi m R u).1 h) s)

/-! ## Reflection symmetry -/

theorem refl_mem_seqSobolev38 {r : ℝ} {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) :
    refl x ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff] at hx ⊢
  unfold SobolevSquareSummable at hx ⊢
  rw [← (Equiv.neg ℤ).summable_iff] at hx
  refine hx.congr (fun n => ?_)
  have hb : japaneseBracket (-n) = japaneseBracket n := by simp [japaneseBracket]
  simp only [Function.comp, Equiv.neg_apply, refl, norm_neg, hb]

/-- `x ↦ refl x` (`(𝓕x)_n = -x_{-n}`) as a real-linear isometry of `h^r`. -/
def reflCarrier38 (r : ℝ) : SobolevCarrier38 r →ₗᵢ[ℝ] SobolevCarrier38 r where
  toFun x := carrierMk38 r (refl (carrierCoe38 r x)) (refl_mem_seqSobolev38 (carrierCoe38_mem r x))
  map_add' x y := carrierExt38 (funext fun n => by
    show -(carrierCoe38 r x (-n) + carrierCoe38 r y (-n)) =
      -carrierCoe38 r x (-n) + -carrierCoe38 r y (-n)
    ring)
  map_smul' c x := carrierExt38 (funext fun n => by
    show -((c : ℂ) * carrierCoe38 r x (-n)) = (c : ℂ) * -carrierCoe38 r x (-n)
    ring)
  norm_map' x := by
    have h1 := carrier_hasSum_norm_sq38 r (carrierMk38 r (refl (carrierCoe38 r x))
      (refl_mem_seqSobolev38 (carrierCoe38_mem r x)))
    have h2 := (Equiv.neg ℤ).hasSum_iff.2 (carrier_hasSum_norm_sq38 r x)
    have e : (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (carrierMk38 r
        (refl (carrierCoe38 r x)) (refl_mem_seqSobolev38 (carrierCoe38_mem r x))) n‖ ^ 2) =
        (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) ∘ (Equiv.neg ℤ) := by
      funext n
      simp [Function.comp, sobolevModeWeight_neg, refl]
    rw [e] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

theorem carrierCoe38_reflCarrier38 (r : ℝ) (x : SobolevCarrier38 r) :
    carrierCoe38 r (reflCarrier38 r x) = refl (carrierCoe38 r x) := rfl

theorem disp_neg38 (n : ℤ) : disp (-n) = disp n := by
  simp [disp]

/-- The equation commutes with the reflection `𝓕` (from `nonlin_refl`); no `m ≥ 1` guard is
needed for the statement, but the notion is meaningful only for `m ≥ 1`. -/
theorem isNLSSol_refl {m : ℕ} {u : ℝ → ℤ → ℂ} (h : IsNLSSolM m u) :
    IsNLSSolM m (fun t => refl (u t)) := by
  refine ⟨fun t => refl_mem_seqSobolev38 (h.mem t), ?_, fun t n => ?_⟩
  · have hc : (fun t => carrierMk38 (m : ℝ) (refl (u t)) (refl_mem_seqSobolev38 (h.mem t))) =
        fun t => reflCarrier38 (m : ℝ) (carrierMk38 (m : ℝ) (u t) (h.mem t)) := rfl
    rw [hc]
    exact (reflCarrier38 (m : ℝ)).continuous.comp h.cont
  · have hd := (h.deriv t (-n)).neg
    have e : (fun s => refl (u s) n) = fun s => -u s (-n) := rfl
    rw [e]
    refine hd.congr_deriv ?_
    have hn' : nonlin (refl (u t)) n = - nonlin (u t) (-n) := by
      rw [nonlin_refl]; rfl
    rw [hn', disp_neg38]
    show _ = -Complex.I * (((disp n : ℝ) : ℂ) * -u t (-n) + -nonlin (u t) (-n))
    ring

/-! ## Regression probe: plane waves -/

/-- Time-dependent amplitude of the plane wave `u(t) = e^{-i((2πk)² + 2|a|²) t} a e^{2πikx}`. -/
def planeWaveAmp38 (k : ℤ) (a : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((t * (disp k + 2 * ‖a‖ ^ 2) : ℝ) : ℂ))) * a

/-- The plane wave `exp(-i((2πk)²+2|a|²)t) a δ_k` satisfies `IsNLSSol` (the exact solution of
`i u_t = -u_xx + 2|u|² u` with `u = a e^{-iωt} e^{2πikx}`, `ω = (2πk)² + 2|a|²`).  Probe for the
definition of `IsNLSSolM` (statement only in the plan; proved here). -/
theorem isNLSSol_planeWave (k : ℤ) (a : ℂ) :
    IsNLSSol (fun t => Pi.single k (planeWaveAmp38 k a t)) := by
  have hnorm : ∀ t, ‖planeWaveAmp38 k a t‖ = ‖a‖ := fun t => by
    unfold planeWaveAmp38
    rw [norm_mul, norm_phaseFactor, one_mul]
  refine ⟨fun t => single_mem_seqSobolev38 _ k _, ?_, fun t n => ?_⟩
  · set r : ℝ := ((1 : ℕ) : ℝ) with hr
    set e1 : SobolevCarrier38 r := carrierMk38 r (Pi.single k 1) (single_mem_seqSobolev38 r k 1)
    have hb : Continuous fun t : ℝ => planeWaveAmp38 k a t := by
      unfold planeWaveAmp38
      fun_prop
    have hfun : (fun t => carrierMk38 r (Pi.single k (planeWaveAmp38 k a t))
        (single_mem_seqSobolev38 r k _)) =
        fun t => (planeWaveAmp38 k a t).re • e1 + (planeWaveAmp38 k a t).im • J38 r e1 := by
      funext t
      apply carrierExt38
      funext n
      show (Pi.single k (planeWaveAmp38 k a t) : ℤ → ℂ) n =
        ((planeWaveAmp38 k a t).re : ℂ) * (Pi.single k (1 : ℂ) : ℤ → ℂ) n +
          ((planeWaveAmp38 k a t).im : ℂ) * (Complex.I * (Pi.single k (1 : ℂ) : ℤ → ℂ) n)
      by_cases hnk : n = k
      · subst hnk
        simp only [Pi.single_eq_same]
        apply Complex.ext <;> simp
      · simp [hnk]
    rw [hfun]
    exact ((Complex.continuous_re.comp hb).smul continuous_const).add
      ((Complex.continuous_im.comp hb).smul continuous_const)
  · have hn1 : nonlin (Pi.single k (planeWaveAmp38 k a t)) n =
        (Pi.single k (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * planeWaveAmp38 k a t) : ℤ → ℂ) n := by
      rw [nonlin_single, hnorm]
    rw [hn1]
    by_cases hnk : n = k
    · subst hnk
      have h := hasDerivAt_phaseFactor (disp n + 2 * ‖a‖ ^ 2) t
      have h2 := h.mul_const a
      simp only [Pi.single_eq_same]
      refine h2.congr_deriv ?_
      unfold planeWaveAmp38
      push_cast
      ring
    · simp only [Pi.single_apply, hnk, ite_false, mul_zero, add_zero]
      simpa using hasDerivAt_const t (0 : ℂ)

end NlsGge.NLS38
