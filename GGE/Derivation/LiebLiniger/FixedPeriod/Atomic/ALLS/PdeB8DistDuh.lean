import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8DuhDist

/-! # Track B, contract 6, direction `IsDistributionalNLS ⇒ IsHm1Duhamel`

Test functions `φ(t,x) = θ(t) e^{-2πinx}` with `θ(t) = ψ(t) e^{it(2πn)²}`
(`ψ ∈ C_c^∞(ℝ;ℝ)`) turn the approved distributional identity into
`∫ ψ' a_n = -∫ ψ g_n` for the interaction-picture coefficient `a_n = intA u n` and the forcing
`g_n = intG U n`. Integration by parts against the primitive of `g_n` and the du
Bois-Reymond lemma (`dbr`, from Mathlib `ae_eq_zero_of_integral_contDiff_smul_eq_zero`) give
`a_n(t) = a_n(0) + ∫₀ᵗ g_n`, i.e. the approved `IsHm1Duhamel` (`isHm1Duhamel_iff_intA`).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem exists_vanish_of_hasCompactSupport {E : Type*} [Zero E] {f : ℝ → E}
    (hf : HasCompactSupport f) : ∃ T, ∀ t, T < |t| → f t = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun t ht => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith

theorem hasCompactSupport_of_vanish {E : Type*} [Zero E] {f : ℝ → E} {T : ℝ}
    (hT : ∀ t, T < |t| → f t = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -|T|) (b := |T|)) fun t ht => hT t ?_
  by_contra h
  rw [not_lt] at h
  exact ht (abs_le.mp (h.trans (le_abs_self T)))

theorem integrable_of_vanish {g : ℝ → ℂ} (hg : Continuous g) {T : ℝ}
    (hT : ∀ t, T < |t| → g t = 0) : Integrable g :=
  hg.integrable_of_hasCompactSupport (hasCompactSupport_of_vanish hT)

theorem integral_eq_interval_of_vanish_real {f : ℝ → ℝ} {T R : ℝ} (hR : T < R) (hR0 : 0 ≤ R)
    (hf : ∀ t, T < |t| → f t = 0) : ∫ t, f t = ∫ t in -R..R, f t := by
  have hle : -R ≤ R := by linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hf t ?_).symm
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-! ### du Bois-Reymond -/

/-- A continuous function with vanishing distributional derivative is constant. -/
theorem dbr {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, ((deriv ψ t : ℝ) : ℂ) * f t = 0) (t : ℝ) : f t = f 0 := by
  let θ₀ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set b : ℝ → ℝ := θ₀.normed volume with hbdef
  have hbs : ContDiff ℝ ∞ b := θ₀.contDiff_normed
  have hbc : Continuous b := θ₀.continuous_normed
  have hbi : ∫ s, b s = 1 := θ₀.integral_normed
  obtain ⟨Tb, hTb⟩ : ∃ T, ∀ t, T < |t| → b t = 0 :=
    exists_vanish_of_hasCompactSupport (θ₀.hasCompactSupport_normed (μ := volume))
  set c : ℂ := ∫ s, (b s : ℂ) * f s with hcdef
  have hbfi : Integrable (fun s => (b s : ℂ) * f s) :=
    integrable_of_vanish (T := Tb) ((Complex.continuous_ofReal.comp hbc).mul hf)
      (fun s hs => by simp [hTb s hs])
  have claim : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ s, χ s • (f s - c) = 0 := by
    intro χ hχ hχc
    obtain ⟨Tχ, hTχ⟩ := exists_vanish_of_hasCompactSupport hχc
    have hχcont : Continuous χ := hχ.continuous
    set I0 : ℝ := ∫ s, χ s with hI0
    set k : ℝ → ℝ := fun s => χ s - I0 * b s with hkdef
    have hks : ContDiff ℝ ∞ k := hχ.sub (contDiff_const.mul hbs)
    have hkc : Continuous k := hks.continuous
    set R : ℝ := max |Tχ| |Tb| + 1 with hRdef
    have hR0 : 0 < R := by positivity
    have hkv : ∀ s, R - 1 < |s| → k s = 0 := by
      intro s hs
      have h1 : Tχ < |s| := by linarith [le_abs_self Tχ, le_max_left |Tχ| |Tb|]
      have h2 : Tb < |s| := by linarith [le_abs_self Tb, le_max_right |Tχ| |Tb|]
      simp only [hkdef, hTχ s h1, hTb s h2, mul_zero, sub_zero]
    have hχi : Integrable χ := hχcont.integrable_of_hasCompactSupport hχc
    have hbi' : Integrable b := hbc.integrable_of_hasCompactSupport (θ₀.hasCompactSupport_normed)
    have hkint : ∫ s, k s = 0 := by
      rw [hkdef, integral_sub hχi (hbi'.const_mul I0), integral_const_mul, hbi, mul_one, sub_self]
    set Ψ : ℝ → ℝ := fun t => ∫ s in (-R)..t, k s with hΨdef
    have hΨd : ∀ t, HasDerivAt Ψ (k t) t := fun t => (hkc.integral_hasStrictDerivAt (-R) t).hasDerivAt
    have hderiv : deriv Ψ = k := funext fun t => (hΨd t).deriv
    have hΨs : ContDiff ℝ ∞ Ψ :=
      contDiff_infty_iff_deriv.2 ⟨fun t => (hΨd t).differentiableAt, by rw [hderiv]; exact hks⟩
    have hzero : ∀ a b : ℝ, (∀ s, s ∈ Set.uIcc a b → k s = 0) → ∫ s in a..b, k s = 0 := by
      intro a b hab
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) hab, intervalIntegral.integral_zero]
    have hΨc : HasCompactSupport Ψ := by
      refine hasCompactSupport_of_vanish (T := R) fun t ht => ?_
      rcases le_or_gt t 0 with htn | htp
      · rw [abs_of_nonpos htn] at ht
        refine hzero _ _ fun s hs => hkv s ?_
        rw [Set.uIcc_of_ge (by linarith)] at hs
        rw [abs_of_nonpos (by linarith [hs.2])]
        linarith [hs.2]
      · rw [abs_of_pos htp] at ht
        simp only [hΨdef]
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := -t)
          (hkc.intervalIntegrable _ _) (hkc.intervalIntegrable _ _),
          intervalIntegral.integral_symm (-t) (-R)]
        have e1 : ∫ s in (-t)..(-R), k s = 0 := by
          refine hzero _ _ fun s hs => hkv s ?_
          rw [Set.uIcc_of_le (by linarith)] at hs
          rw [abs_of_nonpos (by linarith [hs.2])]
          linarith [hs.2]
        have e2 : ∫ s in (-t)..t, k s = 0 := by
          rw [← integral_eq_interval_of_vanish_real (f := k) (T := R - 1) (by linarith) htp.le
            (fun s hs => hkv s hs), hkint]
        rw [e1, e2, neg_zero, zero_add]
    have hk := h Ψ hΨs hΨc
    rw [hderiv] at hk
    have e3 : (fun s => ((k s : ℝ) : ℂ) * f s) =
        fun s => (χ s : ℂ) * f s - (I0 : ℂ) * ((b s : ℂ) * f s) := by
      funext s
      simp only [hkdef]
      push_cast
      ring
    have hχfi : Integrable (fun s => (χ s : ℂ) * f s) :=
      integrable_of_vanish (T := Tχ) ((Complex.continuous_ofReal.comp hχcont).mul hf)
        (fun s hs => by simp [hTχ s hs])
    rw [e3, integral_sub hχfi (hbfi.const_mul _), integral_const_mul] at hk
    have e4 : (fun s => χ s • (f s - c)) = fun s => (χ s : ℂ) * f s - c * (χ s : ℂ) := by
      funext s
      rw [Complex.real_smul]
      ring
    have hχi' : Integrable (fun s => (χ s : ℂ)) := hχi.ofReal
    rw [e4, integral_sub hχfi (hχi'.const_mul c), integral_const_mul, integral_complex_ofReal]
    rw [← hI0]
    try rw [← hcdef] at hk
    linear_combination hk
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.sub continuous_const).locallyIntegrable claim
  have hfun := (Continuous.ae_eq_iff_eq volume (hf.sub continuous_const) continuous_const).1 hae
  have h1 := congrFun hfun t
  have h2 := congrFun hfun 0
  simp only [Pi.sub_apply] at h1 h2
  rw [sub_eq_zero] at h1 h2
  rw [h1, h2]

/-! ### The modal test functions -/

/-- `θ(t) = ψ(t) e^{it(2πn)²}`. -/
def tfn (ψ : ℝ → ℝ) (n : ℤ) (t : ℝ) : ℂ := (ψ t : ℂ) * freePhase (-t) n

/-- Its derivative. -/
def tfn' (ψ : ℝ → ℝ) (n : ℤ) (t : ℝ) : ℂ :=
  ((deriv ψ t : ℝ) : ℂ) * freePhase (-t) n + (ψ t : ℂ) * (((disp n : ℝ) : ℂ) * Complex.I * freePhase (-t) n)

theorem hasDerivAt_freePhase_neg (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s => freePhase (-s) n) (((disp n : ℝ) : ℂ) * Complex.I * freePhase (-t) n) t := by
  have h : HasDerivAt (fun s => freePhase (-s) n)
      ((-1 : ℝ) • (-((disp n : ℝ) : ℂ) * Complex.I * freePhase (-t) n)) t :=
    (hasDerivAt_freePhase n (-t)).scomp t (hasDerivAt_neg t)
  convert h using 1
  rw [Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_tfn {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (n : ℤ) (t : ℝ) :
    HasDerivAt (tfn ψ n) (tfn' ψ n t) t :=
  ((hψ t).hasDerivAt.ofReal_comp).mul (hasDerivAt_freePhase_neg n t)

theorem contDiff_freePhase_neg (n : ℤ) : ContDiff ℝ ∞ (fun t : ℝ => freePhase (-t) n) := by
  unfold freePhase
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_neg.mul contDiff_const)).neg.mul contDiff_const)

theorem ex_eq (m : ℤ) : ex m = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * m * (x : ℂ)) := by
  funext x
  simp only [ex, fourier_coe_apply, Complex.ofReal_one, div_one]

theorem contDiff_ex (m : ℤ) : ContDiff ℝ ∞ (ex m) := by
  rw [ex_eq]
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem ex_add_one (m : ℤ) (x : ℝ) : ex m (x + 1) = ex m x := by
  simp only [ex]
  rw [AddCircle.coe_add_period]

theorem isSpacetimeTest_mode {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ)
    (n : ℤ) : IsSpacetimeTest (fun p : ℝ × ℝ => tfn ψ n p.1 * ex (-n) p.2) where
  smooth := by
    have h1 : ContDiff ℝ ∞ (tfn ψ n) :=
      (Complex.ofRealCLM.contDiff.comp hψ).mul (contDiff_freePhase_neg n)
    exact (h1.comp contDiff_fst).mul ((contDiff_ex (-n)).comp contDiff_snd)
  periodic := fun t x => by simp only [ex_add_one]
  compact_time := by
    obtain ⟨T, hT⟩ := exists_vanish_of_hasCompactSupport hcs
    exact ⟨T, fun t x ht => by simp [tfn, hT t ht]⟩

theorem mode_lhs_pt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (n : ℤ) (p : ℝ × ℝ) :
    iteratedDeriv 2 (fun y => tfn ψ n p.1 * ex (-n) y) p.2 -
        Complex.I * deriv (fun s => tfn ψ n s * ex (-n) p.2) p.1 =
      (-((disp n : ℝ) : ℂ) * tfn ψ n p.1 - Complex.I * tfn' ψ n p.1) * ex (-n) p.2 := by
  have hd1 : deriv (fun y => tfn ψ n p.1 * ex (-n) y) =
      fun y => tfn ψ n p.1 * (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * ex (-n) y) :=
    funext fun y => ((hasDerivAt_ex (-n) y).const_mul (tfn ψ n p.1)).deriv
  have hd2 : deriv (fun y => tfn ψ n p.1 * (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * ex (-n) y))
      p.2 = tfn ψ n p.1 * (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * ex (-n) p.2)) :=
    (((hasDerivAt_ex (-n) p.2).const_mul (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ))).const_mul
      (tfn ψ n p.1)).deriv
  have hd3 : deriv (fun s => tfn ψ n s * ex (-n) p.2) p.1 = tfn' ψ n p.1 * ex (-n) p.2 :=
    ((hasDerivAt_tfn (hψ.differentiable (by simp)) n p.1).mul_const (ex (-n) p.2)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2, hd3, disp]
  push_cast
  linear_combination (tfn ψ n p.1 * ex (-n) p.2 * (2 * Real.pi * n) ^ 2) * Complex.I_mul_I

/-- The weak form of one interaction-picture mode equation. -/
theorem weak_mode {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} (hU : IsSpacetimeRep u U)
    (hD : IsDistributionalNLS U) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ)
    (n : ℤ) :
    ∫ t, ((deriv ψ t : ℝ) : ℂ) * intA u n t = -∫ t, (ψ t : ℂ) * intG U n t := by
  obtain ⟨hl, hr, he⟩ := hD _ (isSpacetimeTest_mode hψ hcs n)
  have hlhs : (fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
      (iteratedDeriv 2 (fun y => tfn ψ n p.1 * ex (-n) y) p.2 -
        Complex.I * deriv (fun s => tfn ψ n s * ex (-n) p.2) p.1)) =
      fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
        ((-((disp n : ℝ) : ℂ) * tfn ψ n p.1 - Complex.I * tfn' ψ n p.1) * ex (-n) p.2) := by
    funext p
    rw [mode_lhs_pt hψ n p]
  have hl' : Integrable (fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
      ((-((disp n : ℝ) : ℂ) * tfn ψ n p.1 - Complex.I * tfn' ψ n p.1) * ex (-n) p.2))
      stripMeasure := by
    rw [← hlhs]; exact hl
  have he' : ∫ p, U (p.1, (p.2 : PhysicalCircle)) *
      ((-((disp n : ℝ) : ℂ) * tfn ψ n p.1 - Complex.I * tfn' ψ n p.1) * ex (-n) p.2)
        ∂stripMeasure =
      ∫ p, cubicNL (U (p.1, (p.2 : PhysicalCircle))) * (tfn ψ n p.1 * ex (-n) p.2)
        ∂stripMeasure := by
    rw [← hlhs]; exact he
  have hm1 := strip_mode (F := U)
    (d := fun t => -((disp n : ℝ) : ℂ) * tfn ψ n t - Complex.I * tfn' ψ n t) (-n) hl'
  have hm2 := strip_mode (F := fun q => cubicNL (U q)) (d := tfn ψ n) (-n) hr
  rw [neg_neg] at hm1 hm2
  rw [hm1, hm2] at he'
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      (-((disp n : ℝ) : ℂ) * tfn ψ n t - Complex.I * tfn' ψ n t) *
        physicalFourier (fun y => U (t, y)) n =
      (-((disp n : ℝ) : ℂ) * tfn ψ n t - Complex.I * tfn' ψ n t) * physicalFourier (u t) n := by
    filter_upwards [hU.slice] with t ht
    rw [physicalFourier_congr_ae ht]
  rw [integral_congr_ae hae, mode_lhs_eq u n (tfn ψ n) (tfn' ψ n), mode_rhs_eq U n (tfn ψ n)] at he'
  have p1 : ∀ t, (tfn' ψ n t * freePhase t n +
      tfn ψ n t * (-((disp n : ℝ) : ℂ) * Complex.I * freePhase t n)) = ((deriv ψ t : ℝ) : ℂ) := by
    intro t
    simp only [tfn, tfn']
    linear_combination ((deriv ψ t : ℝ) : ℂ) * freePhase_neg_mul t n
  have p2 : ∀ t, tfn ψ n t * freePhase t n = (ψ t : ℂ) := by
    intro t
    simp only [tfn]
    linear_combination (ψ t : ℂ) * freePhase_neg_mul t n
  simp only [p1, p2] at he'
  linear_combination Complex.I * he' + ((∫ t, ((deriv ψ t : ℝ) : ℂ) * intA u n t) +
    ∫ t, (ψ t : ℂ) * intG U n t) * Complex.I_mul_I

theorem continuous_intA {u : ℝ → PhysicalL2} (hc : Continuous u) (n : ℤ) :
    Continuous (intA u n) :=
  ((continuous_freePhase_t n).comp continuous_neg).mul ((continuous_physicalFourier_coord n).comp hc)

/-- **Distributional ⇒ Duhamel** (direction `⇒` of approved contract 6). -/
theorem duhamel_of_isDistributionalNLS {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ}
    (hc : Continuous u) (hU : IsSpacetimeRep u U) (h4 : IsL4Loc U) (hD : IsDistributionalNLS U) :
    IsHm1Duhamel u U := by
  rw [isHm1Duhamel_iff_intA h4]
  intro n
  have hg := intervalIntegrable_intG_loc h4 n
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℂ, G = fun t => ∫ r in (0 : ℝ)..t, intG U n r := ⟨_, rfl⟩
  have hGc : Continuous G := by rw [hGdef]; exact intervalIntegral.continuous_primitive hg 0
  have hfc : Continuous fun t => intA u n t - G t := (continuous_intA hc n).sub hGc
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ t, ((deriv ψ t : ℝ) : ℂ) * (intA u n t - G t) = 0 := by
    intro ψ hψ hcs
    obtain ⟨T, hT⟩ := exists_vanish_of_hasCompactSupport hcs
    have hψd : ∀ t, HasDerivAt (fun s => (ψ s : ℂ)) ((deriv ψ t : ℝ) : ℂ) t := fun t =>
      ((hψ.differentiable (by simp)) t).hasDerivAt.ofReal_comp
    have hψ'c : Continuous fun t => ((deriv ψ t : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hψ.continuous_deriv (by simp))
    have hTc : ∀ t, T < |t| → (ψ t : ℂ) = 0 := fun t ht => by rw [hT t ht, Complex.ofReal_zero]
    have hd0 : ∀ t, T < |t| → ((deriv ψ t : ℝ) : ℂ) = 0 := fun t ht =>
      hasDerivAt_eq_zero_of_vanish hψd hTc ht
    have h1 := weak_mode hU hD hψ hcs n
    have hGa : ∀ t, G t = G 0 + ∫ r in (0 : ℝ)..t, intG U n r := fun t => by
      rw [hGdef]; simp only [intervalIntegral.integral_same, zero_add]
    have h2 := ibp_primitive hg hGa hψd hψ'c hTc
    have i1 : Integrable fun t => ((deriv ψ t : ℝ) : ℂ) * intA u n t :=
      integrable_of_vanish (hψ'c.mul (continuous_intA hc n)) fun t ht => by rw [hd0 t ht, zero_mul]
    have i2 : Integrable fun t => ((deriv ψ t : ℝ) : ℂ) * G t :=
      integrable_of_vanish (hψ'c.mul hGc) fun t ht => by rw [hd0 t ht, zero_mul]
    have e : (fun t => ((deriv ψ t : ℝ) : ℂ) * (intA u n t - G t)) =
        fun t => ((deriv ψ t : ℝ) : ℂ) * intA u n t - ((deriv ψ t : ℝ) : ℂ) * G t := by
      funext t; ring
    rw [e, integral_sub i1 i2, h1, h2, sub_self]
  intro t
  have h := dbr hfc key t
  have hG0 : G 0 = 0 := by rw [hGdef]; simp only [intervalIntegral.integral_same]
  have hGt : G t = ∫ r in (0 : ℝ)..t, intG U n r := by rw [hGdef]
  rw [hG0, sub_zero, hGt] at h
  rw [← h]
  ring

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
