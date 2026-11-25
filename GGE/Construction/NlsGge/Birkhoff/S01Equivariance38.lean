import NlsGge.Birkhoff.BirkhoffAPI38

/-! # S01 (translation equivariance), part a: Φ-free sequence-level infrastructure

Φ-free facts on the Sobolev carriers `SobolevCarrier38 r = h^r`:

* bounded diagonal multipliers as continuous real-linear maps (`multC38`);
* the rotation action `(S_θ x)_n = e^{inθ} x_n` (`rotSeq38`, `rotC38`), an isometry of every `h^r`;
* the generator `(X x)_n = i n x_n` and differentiability of `θ ↦ S_θ x` in `h⁰` for `x ∈ h¹`;
* the momentum quadratic form `N(x) = Σ n |x_n|²` on `h¹` and the identity
  `Σ n Re(conj (f x)_n (Df(x) ξ)_n) = Σ n Re(conj x_n ξ_n)` for any map `f` of `h¹`
  that preserves `N`;
* density of finitely supported sequences.

Nothing here mentions `BirkhoffInput38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped Topology

/-! ## Bounded diagonal multipliers -/

theorem sobolevModeWeight_natCast38 (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold sobolevModeWeight japaneseBracket
  show Real.rpow (Real.sqrt (1 + (n : ℝ) ^ 2)) (2 * (k : ℝ)) = _
  rw [Real.rpow_eq_pow, show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, pow_mul, Real.sq_sqrt (by positivity)]

/-- Membership in `h^r` is stable under multiplication by a bounded sequence. -/
theorem mult_mem_seqSobolev38 (r : ℝ) (c : ℤ → ℂ) (K : ℝ) (hc : ∀ n, ‖c n‖ ≤ K)
    (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) : (fun n => c n * x n) ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff] at hx ⊢
  have hK : 0 ≤ K := (norm_nonneg _).trans (hc 0)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _))
    (fun n => ?_) (hx.mul_left (K ^ 2))
  show sobolevModeWeight r n * ‖c n * x n‖ ^ 2 ≤ K ^ 2 * (sobolevModeWeight r n * ‖x n‖ ^ 2)
  rw [norm_mul, mul_pow]
  have h1 : ‖c n‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc n) 2
  have := sobolevModeWeight_pos r n
  nlinarith [sq_nonneg ‖x n‖, mul_nonneg this.le (sq_nonneg ‖x n‖)]

/-- Bounded diagonal multiplier on `h^r`, as a continuous real-linear map. -/
def multC38 (r : ℝ) (c : ℤ → ℂ) (K : ℝ) (hc : ∀ n, ‖c n‖ ≤ K) :
    SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  LinearMap.mkContinuous
    { toFun := carrierMap38 r r (fun x n => c n * x n) (mult_mem_seqSobolev38 r c K hc)
      map_add' := fun x y => carrierExt38 (funext fun n => by
        show c n * (carrierCoe38 r x n + carrierCoe38 r y n) =
          c n * carrierCoe38 r x n + c n * carrierCoe38 r y n
        ring)
      map_smul' := fun a x => carrierExt38 (funext fun n => by
        show c n * ((a : ℂ) * carrierCoe38 r x n) = (a : ℂ) * (c n * carrierCoe38 r x n)
        ring) }
    (max K 0) (fun x => by
      have hK : 0 ≤ max K 0 := le_max_right _ _
      have hc' : ∀ n, ‖c n‖ ≤ max K 0 := fun n => (hc n).trans (le_max_left _ _)
      have h1 := carrier_hasSum_norm_sq38 r x
      have h2 := carrier_hasSum_norm_sq38 r
        (carrierMap38 r r (fun x n => c n * x n) (mult_mem_seqSobolev38 r c K hc) x)
      have hle : ‖carrierMap38 r r (fun x n => c n * x n) (mult_mem_seqSobolev38 r c K hc) x‖ ^ 2 ≤
          (max K 0 * ‖x‖) ^ 2 := by
        rw [mul_pow]
        rw [← h2.tsum_eq, ← h1.tsum_eq, ← h1.summable.tsum_mul_left]
        refine Summable.tsum_le_tsum (fun n => ?_) h2.summable (h1.summable.mul_left _)
        simp only [carrierMap38_coe]
        show sobolevModeWeight r n * ‖c n * carrierCoe38 r x n‖ ^ 2 ≤
          (max K 0) ^ 2 * (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2)
        rw [norm_mul, mul_pow]
        have h3 : ‖c n‖ ^ 2 ≤ (max K 0) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc' n) 2
        have := sobolevModeWeight_pos r n
        nlinarith [mul_nonneg this.le (sq_nonneg ‖carrierCoe38 r x n‖)]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).1 hle)

theorem multC38_coe (r : ℝ) (c : ℤ → ℂ) (K : ℝ) (hc : ∀ n, ‖c n‖ ≤ K)
    (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (multC38 r c K hc x) n = c n * carrierCoe38 r x n := rfl


/-! ## The rotation action `(S_θ x)_n = e^{inθ} x_n` -/

/-- The phase `e^{inθ}`. -/
def rotPhase38 (θ : ℝ) (n : ℤ) : ℂ := Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)

theorem norm_rotPhase38 (θ : ℝ) (n : ℤ) : ‖rotPhase38 θ n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem rotPhase38_zero (n : ℤ) : rotPhase38 0 n = 1 := by simp [rotPhase38]

theorem rotPhase38_add (θ φ : ℝ) (n : ℤ) :
    rotPhase38 (θ + φ) n = rotPhase38 θ n * rotPhase38 φ n := by
  unfold rotPhase38
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `S_θ` on sequences: `(S_θ x)_n = e^{inθ} x_n` (v2 `D:eq:equivariance`). -/
def rotSeq38 (θ : ℝ) (x : ℤ → ℂ) : ℤ → ℂ := fun n => rotPhase38 θ n * x n

theorem rotSeq38_apply (θ : ℝ) (x : ℤ → ℂ) (n : ℤ) : rotSeq38 θ x n = rotPhase38 θ n * x n := rfl

theorem rotSeq38_zero (x : ℤ → ℂ) : rotSeq38 0 x = x := by
  funext n; simp [rotSeq38, rotPhase38_zero]

theorem rotSeq38_add (θ φ : ℝ) (x : ℤ → ℂ) :
    rotSeq38 (θ + φ) x = rotSeq38 θ (rotSeq38 φ x) := by
  funext n; simp only [rotSeq38, rotPhase38_add]; ring

theorem norm_rotSeq38_apply (θ : ℝ) (x : ℤ → ℂ) (n : ℤ) : ‖rotSeq38 θ x n‖ = ‖x n‖ := by
  rw [rotSeq38_apply, norm_mul, norm_rotPhase38, one_mul]

theorem rotSeq38_mem (r : ℝ) (θ : ℝ) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) :
    rotSeq38 θ x ∈ seqSobolev38 r :=
  mult_mem_seqSobolev38 r (rotPhase38 θ) 1 (fun n => (norm_rotPhase38 θ n).le) x hx

/-- `S_θ` as a continuous real-linear map of `h^r`. -/
def rotC38 (r : ℝ) (θ : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  multC38 r (rotPhase38 θ) 1 (fun n => (norm_rotPhase38 θ n).le)

theorem rotC38_coe (r θ : ℝ) (x : SobolevCarrier38 r) :
    carrierCoe38 r (rotC38 r θ x) = rotSeq38 θ (carrierCoe38 r x) := rfl

theorem norm_rotC38 (r θ : ℝ) (x : SobolevCarrier38 r) : ‖rotC38 r θ x‖ = ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r x
  have h2 := carrier_hasSum_norm_sq38 r (rotC38 r θ x)
  have e : (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (rotC38 r θ x) n‖ ^ 2) =
      fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 := by
    funext n
    rw [rotC38_coe, norm_rotSeq38_apply]
  rw [e] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h2.unique h1)

theorem continuous_rotC38 (r θ : ℝ) : Continuous (rotC38 r θ) := (rotC38 r θ).continuous

/-- The rotation `S_θ` on `h^r`, as an isometry of the carrier. -/
theorem isometry_rotC38 (r θ : ℝ) : Isometry (rotC38 r θ) :=
  AddMonoidHomClass.isometry_of_norm (rotC38 r θ) (fun x => norm_rotC38 r θ x)


/-! ## The generator `(X x)_n = i n x_n` and differentiability of `θ ↦ S_θ x` in `h⁰` -/

/-- The generator of the rotation group, `(X x)_n = i n x_n`. -/
def genSeq38 (x : ℤ → ℂ) : ℤ → ℂ := fun n => Complex.I * (n : ℂ) * x n

theorem genSeq38_apply (x : ℤ → ℂ) (n : ℤ) : genSeq38 x n = Complex.I * (n : ℂ) * x n := rfl

theorem norm_genSeq38_apply (x : ℤ → ℂ) (n : ℤ) : ‖genSeq38 x n‖ = |(n : ℝ)| * ‖x n‖ := by
  rw [genSeq38_apply, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
  rw [this]

theorem genSeq38_mem_zero {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    genSeq38 x ∈ seqSobolev38 0 := by
  rw [mem_seqSobolev38_iff] at hx ⊢
  change Summable (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖x n‖ ^ 2) at hx
  change Summable (fun n : ℤ => sobolevModeWeight 0 n * ‖genSeq38 x n‖ ^ 2)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sobolevModeWeight_pos 0 n).le (sq_nonneg _))
    (fun n => ?_) hx
  rw [norm_genSeq38_apply, mul_pow, sq_abs]
  have e1 : sobolevModeWeight 0 n = 1 := by simpa using sobolevModeWeight_natCast_zero n
  have e2 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
    simpa using sobolevModeWeight_natCast38 1 n
  rw [e1, e2]
  nlinarith [sq_nonneg ‖x n‖]

theorem mem_zero_of_mem_one38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    x ∈ seqSobolev38 0 := seqSobolev38_natCast_mono hx

theorem hasDerivAt_rotPhase38 (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => rotPhase38 t n) (Complex.I * (n : ℂ) * rotPhase38 θ n) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (((n : ℝ) * t : ℝ) : ℂ)) (n : ℂ) θ := by
    have := (hasDerivAt_id θ).const_mul (n : ℝ)
    have := this.ofReal_comp
    simpa using this
  have h2 := (h1.mul_const Complex.I).cexp
  refine HasDerivAt.congr_deriv h2 ?_
  simp only [rotPhase38]
  ring

/-- The difference quotient of the phase, minus its limit. -/
def phaseQuot38 (n : ℤ) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * (rotPhase38 t n - 1) - Complex.I * (n : ℂ)

theorem tendsto_phaseQuot38 (n : ℤ) : Filter.Tendsto (phaseQuot38 n) (𝓝[≠] 0) (𝓝 0) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_rotPhase38 n 0)
  have h2 := h.sub_const (Complex.I * (n : ℂ) * rotPhase38 0 n)
  rw [sub_self] at h2
  refine h2.congr (fun t => ?_)
  simp only [phaseQuot38, rotPhase38_zero, zero_add, mul_one, Complex.real_smul]
  push_cast
  ring_nf

theorem norm_phaseQuot38_le (n : ℤ) {t : ℝ} (ht : t ≠ 0) : ‖phaseQuot38 n t‖ ≤ 2 * |(n : ℝ)| := by
  have h1 : ‖rotPhase38 t n - 1‖ ≤ |(n : ℝ)| * |t| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (n : ℝ) * t)
    have e : rotPhase38 t n = Complex.exp (Complex.I * (((n : ℝ) * t : ℝ) : ℂ)) := by
      unfold rotPhase38; rw [mul_comm]
    rw [e]
    simpa [Real.norm_eq_abs, abs_mul] using this
  have h2 : ‖(t : ℂ)⁻¹ * (rotPhase38 t n - 1)‖ ≤ |(n : ℝ)| := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have ht' : 0 < |t| := abs_pos.2 ht
    calc |t|⁻¹ * ‖rotPhase38 t n - 1‖ ≤ |t|⁻¹ * (|(n : ℝ)| * |t|) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |(n : ℝ)| := by field_simp
  have h3 : ‖Complex.I * (n : ℂ)‖ = |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_I, one_mul,
      show (n : ℂ) = ((n : ℝ) : ℂ) by simp, Complex.norm_real, Real.norm_eq_abs]
  calc ‖phaseQuot38 n t‖ ≤ ‖(t : ℂ)⁻¹ * (rotPhase38 t n - 1)‖ + ‖Complex.I * (n : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * |(n : ℝ)| := by rw [h3]; linarith

/-- For `x ∈ h¹` the orbit `θ ↦ S_θ x` is differentiable into `h⁰` with derivative `X S_θ x`. -/
theorem hasDerivAt_rotCurve38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => carrierZero38 (rotSeq38 t x)
        (mem_zero_of_mem_one38 (rotSeq38_mem _ t hx)))
      (carrierZero38 (genSeq38 (rotSeq38 θ x))
        (genSeq38_mem_zero (rotSeq38_mem _ θ hx))) θ := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  set D : ℝ → SobolevCarrier38 ((0 : ℕ) : ℝ) := fun t =>
    t⁻¹ • (carrierZero38 (rotSeq38 (θ + t) x) (mem_zero_of_mem_one38 (rotSeq38_mem _ _ hx)) -
      carrierZero38 (rotSeq38 θ x) (mem_zero_of_mem_one38 (rotSeq38_mem _ _ hx))) -
      carrierZero38 (genSeq38 (rotSeq38 θ x)) (genSeq38_mem_zero (rotSeq38_mem _ θ hx)) with hD
  have hcoord : ∀ t n, carrierCoe38 ((0 : ℕ) : ℝ) (D t) n =
      rotPhase38 θ n * phaseQuot38 n t * x n := by
    intro t n
    show ((t⁻¹ : ℝ) : ℂ) * (rotPhase38 (θ + t) n * x n - rotPhase38 θ n * x n) -
      Complex.I * (n : ℂ) * (rotPhase38 θ n * x n) = _
    rw [rotPhase38_add]
    unfold phaseQuot38
    push_cast
    ring
  have hsq : ∀ t, ‖D t‖ ^ 2 = ∑' n : ℤ, ‖rotPhase38 θ n * phaseQuot38 n t * x n‖ ^ 2 := by
    intro t
    rw [← (carrier_hasSum_norm_sq_zero38 (D t)).tsum_eq]
    exact tsum_congr (fun n => by rw [hcoord])
  have hx1 : Summable (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖x n‖ ^ 2) :=
    (mem_seqSobolev38_iff _ x).1 hx
  have hbound : Summable (fun n : ℤ => 4 * (sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖x n‖ ^ 2)) :=
    hx1.mul_left 4
  have hlim : Filter.Tendsto (fun t : ℝ => ∑' n : ℤ, ‖rotPhase38 θ n * phaseQuot38 n t * x n‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∑' n : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) ?_
    · have h0 := (tendsto_phaseQuot38 n)
      have h1 : Filter.Tendsto (fun t : ℝ => ‖rotPhase38 θ n * phaseQuot38 n t * x n‖) (𝓝[≠] 0)
          (𝓝 ‖rotPhase38 θ n * 0 * x n‖) :=
        ((continuous_const.mul continuous_id).mul continuous_const).norm.continuousAt.tendsto.comp h0
      simpa using (h1.pow 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht n
      have ht' : t ≠ 0 := ht
      have e1 : ‖‖rotPhase38 θ n * phaseQuot38 n t * x n‖ ^ 2‖ =
          ‖phaseQuot38 n t‖ ^ 2 * ‖x n‖ ^ 2 := by
        rw [norm_pow, norm_norm, norm_mul, norm_mul, norm_rotPhase38, one_mul, mul_pow]
      rw [e1]
      have h2 := norm_phaseQuot38_le n ht'
      have e2 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
        simpa using sobolevModeWeight_natCast38 1 n
      rw [e2]
      have h3 : ‖phaseQuot38 n t‖ ^ 2 ≤ (2 * |(n : ℝ)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 : (2 * |(n : ℝ)|) ^ 2 = 4 * (n : ℝ) ^ 2 := by rw [mul_pow, sq_abs]; ring
      nlinarith [sq_nonneg ‖x n‖, mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖x n‖)]
  simp only [tsum_zero] at hlim
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp (hlim.congr (fun t => (hsq t).symm))
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr (fun t => ?_)
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)


/-! ## The momentum quadratic form on `h¹` -/

/-- Coordinate formula for the real inner product of the carrier `h^r`. -/
theorem hasSum_inner_carrier38 (r : ℝ) (a b : SobolevCarrier38 r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n *
      (starRingEnd ℂ (carrierCoe38 r a n) * carrierCoe38 r b n).re) (inner ℝ a b) := by
  have h1 : inner ℝ a b = (inner ℂ (show WeightedHilbert (sobolevModeWeight r) from a)
      (show WeightedHilbert (sobolevModeWeight r) from b)).re := rfl
  have h2 := lp.hasSum_inner (𝕜 := ℂ)
    (weightedLinearMap (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from a))
    (weightedLinearMap (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from b))
  have h3 := h2.mapL Complex.reCLM
  rw [h1]
  refine (h3.congr_fun ?_)
  intro n
  have hw := sobolevModeWeight_pos r n
  simp only [Complex.reCLM_apply, RCLike.inner_apply]
  have hs : (Real.sqrt (sobolevModeWeight r n)) ^ 2 = sobolevModeWeight r n := Real.sq_sqrt hw.le
  show _ = (((Real.sqrt (sobolevModeWeight r n) : ℝ) : ℂ) * carrierCoe38 r b n *
    (starRingEnd ℂ) (((Real.sqrt (sobolevModeWeight r n) : ℝ) : ℂ) * carrierCoe38 r a n)).re
  set q := Real.sqrt (sobolevModeWeight r n)
  have : ((q : ℂ) * carrierCoe38 r b n * (starRingEnd ℂ) ((q : ℂ) * carrierCoe38 r a n)) =
      ((q ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (carrierCoe38 r a n) * carrierCoe38 r b n) := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul, hs]

/-- The momentum bilinear form `Σ n Re(conj a_n b_n)` (only used on `h¹ × h¹`). -/
def momBil38 (a b : ℤ → ℂ) : ℝ := ∑' n : ℤ, (n : ℝ) * (starRingEnd ℂ (a n) * b n).re

/-- The momentum quadratic form `N(x) = Σ n |x_n|²` (only used on `h¹`). -/
def momSeq38 (x : ℤ → ℂ) : ℝ := ∑' n : ℤ, (n : ℝ) * ‖x n‖ ^ 2

theorem momBil38_symm (a b : ℤ → ℂ) : momBil38 a b = momBil38 b a := by
  unfold momBil38
  refine tsum_congr (fun n => ?_)
  congr 1
  rw [← Complex.conj_re]
  simp [mul_comm]

theorem momSeq38_eq_momBil38 (x : ℤ → ℂ) : momSeq38 x = momBil38 x x := by
  unfold momSeq38 momBil38
  refine tsum_congr (fun n => ?_)
  congr 1
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The multiplier `n / (1 + n²)`. -/
def momMult38 (n : ℤ) : ℂ := (((n : ℝ) / (1 + (n : ℝ) ^ 2) : ℝ) : ℂ)

theorem norm_momMult38_le (n : ℤ) : ‖momMult38 n‖ ≤ 1 := by
  unfold momMult38
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + (n : ℝ) ^ 2)]
  rw [div_le_one (by positivity)]
  nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]

/-- `M x = (n/(1+n²) x_n)`, a bounded self-adjoint multiplier on `h¹`. -/
def momOp38 : SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  multC38 ((1 : ℕ) : ℝ) momMult38 1 norm_momMult38_le

/-- `⟪a, M b⟫ = Σ n Re(conj a_n b_n)` on `h¹`. -/
theorem inner_momOp38 (a b : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    inner ℝ a (momOp38 b) = momBil38 (carrierCoe38 _ a) (carrierCoe38 _ b) := by
  have h := hasSum_inner_carrier38 ((1 : ℕ) : ℝ) a (momOp38 b)
  have h2 : HasSum (fun n : ℤ => (n : ℝ) *
      (starRingEnd ℂ (carrierCoe38 ((1 : ℕ) : ℝ) a n) * carrierCoe38 ((1 : ℕ) : ℝ) b n).re)
      (inner ℝ a (momOp38 b)) := by
    refine h.congr_fun (fun n => ?_)
    have e2 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
      simpa using sobolevModeWeight_natCast38 1 n
    have e3 : carrierCoe38 ((1 : ℕ) : ℝ) (momOp38 b) n =
        momMult38 n * carrierCoe38 ((1 : ℕ) : ℝ) b n := rfl
    rw [e2, e3, momMult38]
    have : (starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) a n) *
        ((((n : ℝ) / (1 + (n : ℝ) ^ 2) : ℝ) : ℂ) * carrierCoe38 ((1 : ℕ) : ℝ) b n) =
        (((n : ℝ) / (1 + (n : ℝ) ^ 2) : ℝ) : ℂ) *
          ((starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) a n) * carrierCoe38 ((1 : ℕ) : ℝ) b n) := by
      ring
    rw [this, Complex.re_ofReal_mul]
    field_simp
  exact h2.tsum_eq.symm


theorem inner_self_momOp38 (a : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    inner ℝ a (momOp38 a) = momSeq38 (carrierCoe38 _ a) := by
  rw [inner_momOp38, momSeq38_eq_momBil38]

/-- Differentiating `N ∘ f = N` on `h¹`: if `f` is Fréchet differentiable at `x` and preserves
the momentum form `N`, then `B(f x, Df(x) ξ) = B(x, ξ)` for the momentum bilinear form `B`. -/
theorem momBil_fderiv38 (f : SobolevCarrier38 ((1 : ℕ) : ℝ) → SobolevCarrier38 ((1 : ℕ) : ℝ))
    (x ξ : SobolevCarrier38 ((1 : ℕ) : ℝ)) (f' : SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hf : HasFDerivAt f f' x)
    (hN : ∀ y, momSeq38 (carrierCoe38 _ (f y)) = momSeq38 (carrierCoe38 _ y)) :
    momBil38 (carrierCoe38 _ (f x)) (carrierCoe38 _ (f' ξ)) = momBil38 (carrierCoe38 _ x) (carrierCoe38 _ ξ) := by
  set g : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ) := fun t => x + t • ξ with hg
  have hg' : HasDerivAt g ξ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add x
    simpa only [one_smul, id_eq] using this
  have hf0 : HasFDerivAt f f' (g 0) := by simpa [hg] using hf
  have hφ : HasDerivAt (fun t => f (g t)) (f' ξ) 0 := hf0.comp_hasDerivAt (0 : ℝ) hg'
  have h1 : HasDerivAt (fun t => inner ℝ (f (g t)) (momOp38 (f (g t))))
      (inner ℝ (f (g 0)) (momOp38 (f' ξ)) + inner ℝ (f' ξ) (momOp38 (f (g 0)))) 0 :=
    hφ.inner ℝ ((momOp38.hasFDerivAt (x := f (g 0))).comp_hasDerivAt (0 : ℝ) hφ)
  have h2 : HasDerivAt (fun t => inner ℝ (g t) (momOp38 (g t)))
      (inner ℝ (g 0) (momOp38 ξ) + inner ℝ ξ (momOp38 (g 0))) 0 :=
    hg'.inner ℝ ((momOp38.hasFDerivAt (x := g 0)).comp_hasDerivAt (0 : ℝ) hg')
  have hfun : (fun t => inner ℝ (f (g t)) (momOp38 (f (g t)))) =
      fun t => inner ℝ (g t) (momOp38 (g t)) := by
    funext t
    rw [inner_self_momOp38, inner_self_momOp38]
    exact hN (g t)
  rw [hfun] at h1
  have h3 := h1.unique h2
  simp only [inner_momOp38] at h3
  have e0 : g 0 = x := by simp [hg]
  rw [e0] at h3
  rw [momBil38_symm (carrierCoe38 _ (f' ξ)) (carrierCoe38 _ (f x)),
    momBil38_symm (carrierCoe38 _ ξ) (carrierCoe38 _ x)] at h3
  linarith


/-! ## Symplectic pairing with the generator, and single-mode test vectors -/

theorem stdSymplectic38_gen_left (y η : ℤ → ℂ) :
    stdSymplectic38 (genSeq38 y) η = -momBil38 y η := by
  unfold stdSymplectic38 momBil38
  rw [← tsum_neg]
  refine tsum_congr (fun n => ?_)
  rw [genSeq38_apply]
  have hn : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]; exact Complex.conj_ofReal _
  simp only [map_mul, Complex.conj_I, hn]
  have : (-Complex.I * (n : ℂ) * (starRingEnd ℂ) (y n) * η n) =
      -Complex.I * (((n : ℝ) : ℂ) * ((starRingEnd ℂ) (y n) * η n)) := by
    push_cast; ring
  rw [this]
  set w := (starRingEnd ℂ) (y n) * η n
  rw [neg_mul, Complex.neg_im, ← mul_assoc ]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re]
  ring

theorem stdSymplectic38_single (ξ : ℤ → ℂ) (m : ℤ) (u : ℂ) :
    stdSymplectic38 ξ (Pi.single m u) = (starRingEnd ℂ (ξ m) * u).im := by
  unfold stdSymplectic38
  rw [tsum_eq_single m]
  · simp
  · intro n hn
    simp [hn]


/-! ## Coordinates and finite truncations on `h^r` -/

/-- The `n`-th coordinate as a continuous real-linear functional on `h^r`. -/
def coordC38 (r : ℝ) (n : ℤ) : SobolevCarrier38 r →L[ℝ] ℂ where
  toFun x := carrierCoe38 r x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_carrierCoe_apply38 r n

@[simp] theorem coordC38_apply (r : ℝ) (n : ℤ) (x : SobolevCarrier38 r) :
    coordC38 r n x = carrierCoe38 r x n := rfl

/-- Truncation of `y ∈ h^r` to the modes `-N … N`. -/
def truncC38 (r : ℝ) (N : ℕ) (y : SobolevCarrier38 r) : SobolevCarrier38 r :=
  toCarrier38 r (weightedProjection (sobolevModeWeight r) (symmetricModes N) (ofCarrier38 r y))

theorem carrierCoe38_truncC38 (r : ℝ) (N : ℕ) (y : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (truncC38 r N y) n = if n ∈ symmetricModes N then carrierCoe38 r y n else 0 :=
  weightedProjection_apply (sobolevModeWeight r) (symmetricModes N) (ofCarrier38 r y) n

theorem finiteSupport_truncC38 (r : ℝ) (N : ℕ) (y : SobolevCarrier38 r) :
    {n : ℤ | carrierCoe38 r (truncC38 r N y) n ≠ 0}.Finite := by
  refine (symmetricModes N).finite_toSet.subset (fun n hn => ?_)
  by_contra h
  apply hn
  have h' : n ∉ symmetricModes N := by simpa using h
  simp [carrierCoe38_truncC38, h']

theorem tendsto_truncC38 (r : ℝ) (y : SobolevCarrier38 r) :
    Filter.Tendsto (fun N : ℕ => truncC38 r N y) Filter.atTop (𝓝 y) :=
  weightedProjection_tendsto (sobolevModeWeight r) (ofCarrier38 r y)

end NlsGge.Birkhoff
