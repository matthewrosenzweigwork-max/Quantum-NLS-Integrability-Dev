import NlsGge.Birkhoff.S01Equivariance38
import NlsGge.Birkhoff.S01Equivariance38b

/-! # S01.03 / S01.04: physical translation, its Fourier action, and the intertwining with `𝓕`

Phi-free (no `BirkhoffInput38`).  Orientation (v2, `D:eq:equivariance`): the canonical flow of the
momentum Hamiltonian is `u(x) ↦ u(x+t)` physically and `z_n ↦ e^{-2π i n t} z_n` in the
coordinates of `𝓕`, `(𝓕u)_n = -û(-n)`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations MeasureTheory
open NlsGge.HierarchyRiccati.Core
open scoped Topology ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

local instance : spatialMeasure.IsAddHaarMeasure := by
  unfold spatialMeasure
  infer_instance

/-! ## Physical translation on `L²(ℝ/ℤ)` -/

/-- Translation of the circle point by the real number `t` (period one). -/
def shiftPt38 (t : ℝ) : PhysicalCircle → PhysicalCircle := fun x => x + (t : PhysicalCircle)

theorem measurePreserving_shiftPt38 (t : ℝ) :
    MeasurePreserving (shiftPt38 t) spatialMeasure spatialMeasure :=
  measurePreserving_add_right spatialMeasure (t : PhysicalCircle)

theorem shiftPt38_add (s t : ℝ) :
    shiftPt38 s ∘ shiftPt38 t = shiftPt38 (s + t) := by
  funext x
  simp only [Function.comp, shiftPt38, AddCircle.coe_add]
  abel

theorem shiftPt38_zero : shiftPt38 0 = id := by
  funext x; simp [shiftPt38]

/-- Physical translation `(τ_t u)(x) = u(x + t)` on `PhysicalL2 = L²(AddCircle 1)`. -/
def translateL2_38 (t : ℝ) : PhysicalL2 →ₗᵢ[ℂ] PhysicalL2 :=
  haveI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  Lp.compMeasurePreservingₗᵢ ℂ (shiftPt38 t) (measurePreserving_shiftPt38 t)

theorem translateL2_38_ae (t : ℝ) (u : PhysicalL2) :
    (translateL2_38 t u : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun x => (u : PhysicalCircle → ℂ) (x + (t : PhysicalCircle)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_shiftPt38 t)

theorem norm_translateL2_38 (t : ℝ) (u : PhysicalL2) : ‖translateL2_38 t u‖ = ‖u‖ :=
  (translateL2_38 t).norm_map u

theorem translateL2_38_zero (u : PhysicalL2) : translateL2_38 0 u = u := by
  have h : Lp.compMeasurePreserving (E := ℂ) (p := (2 : ENNReal)) (shiftPt38 0)
      (measurePreserving_shiftPt38 0) u = u := by
    have e : ∀ (f : PhysicalCircle → PhysicalCircle) (hf : MeasurePreserving f spatialMeasure spatialMeasure)
        (hid : f = id), Lp.compMeasurePreserving (E := ℂ) (p := (2 : ENNReal)) f hf u = u := by
      intro f hf hid
      subst hid
      exact Lp.compMeasurePreserving_id_apply u
    exact e _ _ shiftPt38_zero
  exact h

/-- Group law: `τ_{s+t} = τ_s ∘ τ_t`. -/
theorem translateL2_38_add (s t : ℝ) (u : PhysicalL2) :
    translateL2_38 (s + t) u = translateL2_38 s (translateL2_38 t u) := by
  have key : ∀ (f : PhysicalCircle → PhysicalCircle)
      (hf : MeasurePreserving f spatialMeasure spatialMeasure)
      (hfe : f = shiftPt38 t ∘ shiftPt38 s),
      Lp.compMeasurePreserving (E := ℂ) (p := (2 : ENNReal)) f hf u =
        Lp.compMeasurePreserving (E := ℂ) (p := (2 : ENNReal)) (shiftPt38 s)
          (measurePreserving_shiftPt38 s)
          (Lp.compMeasurePreserving (E := ℂ) (p := (2 : ENNReal)) (shiftPt38 t)
            (measurePreserving_shiftPt38 t) u) := by
    intro f hf hfe
    subst hfe
    exact Lp.compMeasurePreserving_comp_apply u (measurePreserving_shiftPt38 t)
      (measurePreserving_shiftPt38 s)
  have := key (shiftPt38 (s + t)) (measurePreserving_shiftPt38 (s + t))
    (by rw [shiftPt38_add, add_comm])
  exact this

/-- The translation as a linear isometric equivalence (inverse `τ_{-t}`). -/
def translateEquiv38 (t : ℝ) : PhysicalL2 ≃ₗᵢ[ℂ] PhysicalL2 :=
  { translateL2_38 t with
    invFun := translateL2_38 (-t)
    left_inv := fun u => by
      change translateL2_38 (-t) (translateL2_38 t u) = u
      rw [← translateL2_38_add, neg_add_cancel, translateL2_38_zero]
    right_inv := fun u => by
      change translateL2_38 t (translateL2_38 (-t) u) = u
      rw [← translateL2_38_add, add_neg_cancel, translateL2_38_zero] }

/-! ## Fourier coefficients of a translate -/

/-- `(τ_t u)^_n = e^{2π i n t} û_n`. -/
theorem physicalFourier_translate38 (t : ℝ) (u : PhysicalL2) (n : ℤ) :
    physicalFourier (translateL2_38 t u) n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) * physicalFourier u n := by
  unfold physicalFourier
  have h1 : fourierCoeff (translateL2_38 t u : PhysicalCircle → ℂ) n =
      fourierCoeff (fun x : PhysicalCircle => (u : PhysicalCircle → ℂ) (x + (t : PhysicalCircle))) n :=
    congrFun (fourierCoeff_congr_ae (translateL2_38_ae t u)) n
  rw [h1]
  unfold fourierCoeff
  have h2 := integral_add_right_eq_self (μ := (AddCircle.haarAddCircle : Measure PhysicalCircle))
    (fun y : PhysicalCircle => fourier (-n) (y + -(t : PhysicalCircle)) •
      (u : PhysicalCircle → ℂ) y) (t : PhysicalCircle)
  have h3 : (fun x : PhysicalCircle => fourier (-n) x •
      (u : PhysicalCircle → ℂ) (x + (t : PhysicalCircle))) =
      fun x => fourier (-n) (x + (t : PhysicalCircle) + -(t : PhysicalCircle)) •
        (u : PhysicalCircle → ℂ) (x + (t : PhysicalCircle)) := by
    funext x; simp
  have h4 : ∀ y : PhysicalCircle, fourier (-n) (y + -(t : PhysicalCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) * fourier (-n) y := by
    intro y
    have e1 : fourier (-n) (y + -(t : PhysicalCircle)) =
        fourier (-n) y * fourier (-n) (-(t : PhysicalCircle)) := by
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    have e2 : fourier (-n) (-(t : PhysicalCircle)) = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) := by
      have : fourier (-n) (-(t : PhysicalCircle)) = fourier n (t : PhysicalCircle) := by
        simp only [fourier_apply, smul_neg, neg_smul, neg_neg]
      rw [this, fourier_coe_apply]
      simp
    rw [e1, e2, mul_comm]
  have h5 : ∫ y : PhysicalCircle, fourier (-n) (y + -(t : PhysicalCircle)) •
      (u : PhysicalCircle → ℂ) y ∂(AddCircle.haarAddCircle : Measure PhysicalCircle) =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) *
        ∫ y : PhysicalCircle, fourier (-n) y • (u : PhysicalCircle → ℂ) y
          ∂(AddCircle.haarAddCircle : Measure PhysicalCircle) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [h4 y, smul_eq_mul, mul_assoc]
  have hmeas : (spatialMeasure : Measure PhysicalCircle) = AddCircle.haarAddCircle := rfl
  rw [hmeas] at *
  rw [show (fun x : PhysicalCircle => fourier (-n) x • (u : PhysicalCircle → ℂ) (x + (t : PhysicalCircle))) = _ from h3]
  rw [h2, h5]

/-! ## S01.04: the reflected Fourier linearization intertwines `τ_t` and `S_{-2πt}` -/

/-- **S01.04.**  `𝓕(τ_t u) = S_{-2πt}(𝓕 u)`, i.e. `(𝓕 τ_t u)_n = e^{-2π i n t} (𝓕u)_n`, with the
project's reflected convention `(𝓕u)_n = -û(-n)`.  The sign of the rotation angle is `-2πt`. -/
theorem fourierSeq38_translate38 (t : ℝ) (u : PhysicalL2) :
    fourierSeq38 (translateL2_38 t u) = rotSeq38 (-(2 * Real.pi * t)) (fourierSeq38 u) := by
  funext n
  rw [fourierSeq38_apply, rotSeq38_apply, fourierSeq38_apply, physicalFourier_translate38]
  unfold rotPhase38
  have : Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (t : ℂ)) =
      Complex.exp ((((n : ℝ) * -(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [this]; ring


/-! ## Canonical coordinates: the flow `S_{-2πt}` and its Hamiltonian `H = π N` -/

/-- The canonical flow `z_n ↦ e^{-2π i n t} z_n` (v2: "`z_n ↦ e^{-2π i n t} z_n`"). -/
def canFlow38 (t : ℝ) (x : ℤ → ℂ) : ℤ → ℂ := rotSeq38 (-(2 * Real.pi * t)) x

theorem canFlow38_apply (t : ℝ) (x : ℤ → ℂ) (n : ℤ) :
    canFlow38 t x n = Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) * x n := by
  unfold canFlow38 rotSeq38 rotPhase38
  congr 2
  push_cast; ring

theorem canFlow38_zero (x : ℤ → ℂ) : canFlow38 0 x = x := by
  unfold canFlow38; simp [rotSeq38_zero]

/-- Group law of the canonical flow. -/
theorem canFlow38_add (s t : ℝ) (x : ℤ → ℂ) :
    canFlow38 (s + t) x = canFlow38 s (canFlow38 t x) := by
  unfold canFlow38
  rw [← rotSeq38_add]; congr 1; ring

theorem canFlow38_mem (r s : ℝ) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) :
    canFlow38 s x ∈ seqSobolev38 r := rotSeq38_mem r _ hx

/-- The canonical flow is differentiable into `h⁰` on `h¹`, with velocity `-2π X x`,
`(X x)_n = i n x_n`. -/
theorem hasDerivAt_canFlow38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => carrierZero38 (canFlow38 s x)
        (mem_zero_of_mem_one38 (rotSeq38_mem _ _ hx)))
      ((-(2 * Real.pi)) • carrierZero38 (genSeq38 (canFlow38 t x))
        (genSeq38_mem_zero (rotSeq38_mem _ _ hx))) t := by
  have h := hasDerivAt_rotCurve38 x hx (-(2 * Real.pi * t))
  have hc : HasDerivAt (fun s : ℝ => -(2 * Real.pi * s)) (-(2 * Real.pi)) t := by
    have := (((hasDerivAt_id' t).const_mul (2 * Real.pi)).neg).congr_deriv
      (show -(2 * Real.pi * 1) = -(2 * Real.pi) by ring)
    exact this
  exact h.scomp t hc

/-! ## The momentum forms on `h¹` -/

theorem summable_weight_sq38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2) := by
  have h : Summable (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖x n‖ ^ 2) :=
    (mem_seqSobolev38_iff _ x).1 hx
  refine h.congr (fun n => ?_)
  have e2 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
    simpa using sobolevModeWeight_natCast38 1 n
  rw [e2]

theorem abs_int_le_weight38 (n : ℤ) : |(n : ℝ)| ≤ 1 + (n : ℝ) ^ 2 := by
  nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]

theorem summable_mom_sq38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (n : ℝ) * ‖x n‖ ^ 2) := by
  refine Summable.of_norm_bounded (summable_weight_sq38 hx) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖x n‖)]
  exact mul_le_mul_of_nonneg_right (abs_int_le_weight38 n) (sq_nonneg _)

theorem summable_momBil38 {a b : ℤ → ℂ} (ha : a ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hb : b ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (n : ℝ) * (starRingEnd ℂ (a n) * b n).re) := by
  refine Summable.of_norm_bounded
    (((summable_weight_sq38 ha).add (summable_weight_sq38 hb)).mul_left (1 / 2)) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(starRingEnd ℂ (a n) * b n).re| ≤ ‖a n‖ * ‖b n‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ‖a n‖ * ‖b n‖ ≤ (‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
  have hw := abs_int_le_weight38 n
  have hw0 : 0 ≤ 1 + (n : ℝ) ^ 2 := by positivity
  calc |(n : ℝ)| * |(starRingEnd ℂ (a n) * b n).re|
      ≤ (1 + (n : ℝ) ^ 2) * ((‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2) :=
        mul_le_mul hw (h1.trans h2) (abs_nonneg _) hw0
    _ = 1 / 2 * ((1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2 + (1 + (n : ℝ) ^ 2) * ‖b n‖ ^ 2) := by ring

/-- Exact quadratic expansion of the momentum form along a line, for `x, η ∈ h¹`. -/
theorem momSeq38_line (x η : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hη : η ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (s : ℝ) :
    momSeq38 (fun n => x n + (s : ℂ) * η n) =
      momSeq38 x + 2 * s * momBil38 x η + s ^ 2 * momSeq38 η := by
  have h1 := (summable_mom_sq38 hx).hasSum
  have h2 := ((summable_momBil38 hx hη).hasSum).mul_left (2 * s)
  have h3 := ((summable_mom_sq38 hη).hasSum).mul_left (s ^ 2)
  have h := (h1.add h2).add h3
  have hterm : ∀ n : ℤ, (n : ℝ) * ‖x n + (s : ℂ) * η n‖ ^ 2 =
      (n : ℝ) * ‖x n‖ ^ 2 + 2 * s * ((n : ℝ) * (starRingEnd ℂ (x n) * η n).re) +
        s ^ 2 * ((n : ℝ) * ‖η n‖ ^ 2) := by
    intro n
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hfun : (fun n : ℤ => (n : ℝ) * ‖x n + (s : ℂ) * η n‖ ^ 2) = fun n : ℤ =>
      (n : ℝ) * ‖x n‖ ^ 2 + 2 * s * ((n : ℝ) * (starRingEnd ℂ (x n) * η n).re) +
        s ^ 2 * ((n : ℝ) * ‖η n‖ ^ 2) := funext hterm
  unfold momSeq38 momBil38
  rw [hfun]
  exact h.tsum_eq

/-- `d/ds N(x + sη)|_{s=0} = 2 B(x, η)` for `x, η ∈ h¹`. -/
theorem hasDerivAt_momSeq_line38 (x η : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hη : η ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    HasDerivAt (fun s : ℝ => momSeq38 (fun n => x n + (s : ℂ) * η n))
      (2 * momBil38 x η) 0 := by
  have hfun : (fun s : ℝ => momSeq38 (fun n => x n + (s : ℂ) * η n)) =
      fun s : ℝ => momSeq38 x + 2 * s * momBil38 x η + s ^ 2 * momSeq38 η :=
    funext (fun s => momSeq38_line x η hx hη s)
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => 2 * s * momBil38 x η) (2 * momBil38 x η) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_mul 2).mul_const (momBil38 x η)
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * momSeq38 η) 0 0 := by
    have := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (momSeq38 η)
    simpa using this
  have h3 := ((h1.const_add (momSeq38 x)).add h2)
  exact h3.congr_deriv (by ring)

/-- Real scalar multiples pull out of the standard symplectic form. -/
theorem stdSymplectic38_real_mul_left (c : ℝ) (ξ η : ℤ → ℂ) :
    stdSymplectic38 (fun n => (c : ℂ) * ξ n) η = c * stdSymplectic38 ξ η := by
  unfold stdSymplectic38
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.im_ofReal_mul]

/-- The canonical Hamiltonian vector field of the momentum, `Y(x)_n = -2π i n x_n`. -/
def canField38 (x : ℤ → ℂ) : ℤ → ℂ := fun n => ((-(2 * Real.pi) : ℝ) : ℂ) * genSeq38 x n

/-- The canonical Hamiltonian of the momentum flow: `H_can(x) = π Σ n |x_n|²`. -/
def canHam38 (x : ℤ → ℂ) : ℝ := Real.pi * momSeq38 x

/-- Hamilton's equation in canonical coordinates for the std. form `ω(ξ,η) = Σ Im(conj ξ_n η_n)`:
`ω(Y(x), η) = dH_can(x)[η]`, and `Y(x) = d/dt` of the flow `canFlow38`. -/
theorem canonical_hamilton38 (x η : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hη : η ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    HasDerivAt (fun s : ℝ => canHam38 (fun n => x n + (s : ℂ) * η n))
      (stdSymplectic38 (canField38 x) η) 0 := by
  have h := (hasDerivAt_momSeq_line38 x η hx hη).const_mul Real.pi
  have e : stdSymplectic38 (canField38 x) η = Real.pi * (2 * momBil38 x η) := by
    unfold canField38
    rw [stdSymplectic38_real_mul_left, stdSymplectic38_gen_left]
    ring
  rw [e]
  exact h

/-! ## `𝓕` is symplectic for the standard forms; the Hamiltonian is `-P/2` -/

/-- The physical symplectic form `ω(V,W) = Im ∫₀¹ conj(V) W` on `L²(ℝ/ℤ)`. -/
def omegaPhys38 (V W : PhysicalL2) : ℝ := (inner ℂ V W).im

/-- The reflected Fourier map carries the physical form to the standard form on sequences. -/
theorem stdSymplectic38_fourierSeq38 (V W : PhysicalL2) :
    stdSymplectic38 (fourierSeq38 V) (fourierSeq38 W) = omegaPhys38 V W := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (reflectedFourierL2 V) (reflectedFourierL2 W)
  rw [LinearIsometryEquiv.inner_map_map] at h
  have h2 := h.mapL Complex.imCLM
  unfold stdSymplectic38 omegaPhys38
  have : (fun n : ℤ => (starRingEnd ℂ (fourierSeq38 V n) * fourierSeq38 W n).im) =
      fun n : ℤ => Complex.imCLM (inner ℂ (reflectedFourierL2 V n) (reflectedFourierL2 W n)) := by
    funext n
    simp only [Complex.imCLM_apply, RCLike.inner_apply]
    show _ = (fourierSeq38 W n * (starRingEnd ℂ) (fourierSeq38 V n)).im
    rw [mul_comm]
  rw [this]
  exact h2.tsum_eq

/-- The physical momentum `P(u) = Σ 2π n |û_n|²` (Parseval form of `Im ∫ ū u_x`). -/
def momentumFourier38 (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2

/-- For smooth period-one `U`, `Im ∫₀¹ Ū U'` is the Fourier momentum. -/
theorem momentumE02_eq_momentumFourier38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    momentumE02_38 U = momentumFourier38 (smoothL2_38 U hU hper) :=
  ((momentum_hasSum38 U hU hper).tsum_eq).symm

/-- Under `𝓕`, the physical momentum is `P(u) = -2π N(𝓕u)`, so `-P/2 = π N∘𝓕 = H_can ∘ 𝓕`. -/
theorem momentumFourier38_eq_neg_canonical (u : PhysicalL2) :
    momentumFourier38 u = -(2 * Real.pi) * momSeq38 (fourierSeq38 u) := by
  unfold momentumFourier38 momSeq38
  rw [← tsum_mul_left]
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, fourierSeq38_apply, norm_neg]
  push_cast
  ring

theorem neg_half_momentum_eq_canHam38 (u : PhysicalL2) :
    -(momentumFourier38 u) / 2 = canHam38 (fourierSeq38 u) := by
  rw [momentumFourier38_eq_neg_canonical]; unfold canHam38; ring

/-! ## Physical derivative identity `d/dt τ_t u = τ_t u_x` -/

theorem fourierSeq38_add38 (u v : PhysicalL2) (n : ℤ) :
    fourierSeq38 (u + v) n = fourierSeq38 u n + fourierSeq38 v n := by
  show (reflectedFourierL2 (u + v) : ℤ → ℂ) n = _
  rw [map_add]; rfl

theorem fourierSeq38_smul38 (c : ℂ) (u : PhysicalL2) (n : ℤ) :
    fourierSeq38 (c • u) n = c * fourierSeq38 u n := by
  show (reflectedFourierL2 (c • u) : ℤ → ℂ) n = _
  rw [map_smul]; rfl

theorem fourierSeq38_zero38 (n : ℤ) : fourierSeq38 (0 : PhysicalL2) n = 0 := by
  rw [fourierSeq38_zero]; rfl

/-- `w = u_x` in Fourier form: `ŵ_n = 2π i n û_n` (the weak `L²` derivative of `u`). -/
def IsFourierDeriv38 (u w : PhysicalL2) : Prop :=
  ∀ n : ℤ, physicalFourier w n = 2 * Real.pi * Complex.I * (n : ℂ) * physicalFourier u n

theorem fourierSeq38_of_deriv38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) :
    fourierSeq38 w = canField38 (fourierSeq38 u) := by
  funext n
  rw [fourierSeq38_apply, hw (-n)]
  unfold canField38 genSeq38
  rw [fourierSeq38_apply]
  push_cast
  ring

theorem summable_sq_zero38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 0) :
    Summable (fun n : ℤ => ‖x n‖ ^ 2) := by
  have h := (mem_seqSobolev38_iff _ x).1 hx
  refine h.congr (fun n => ?_)
  have e1 : sobolevModeWeight 0 n = 1 := by simpa using sobolevModeWeight_natCast_zero n
  show sobolevModeWeight 0 n * ‖x n‖ ^ 2 = _
  rw [e1, one_mul]

/-- A field with an `L²` Fourier derivative lies in `H¹` (as a sequence, `𝓕u ∈ h¹`). -/
theorem fourierSeq38_mem_one_of_deriv38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) :
    fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
  have h0 := summable_sq_zero38 (fourierSeq38_mem_zero u)
  have hw0 := summable_sq_zero38 (fourierSeq38_mem_zero w)
  rw [fourierSeq38_of_deriv38 hw] at hw0
  rw [mem_seqSobolev38_iff]
  have : Summable (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖fourierSeq38 u n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))
      (fun n => ?_) (h0.add hw0)
    have e2 : sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
      simpa using sobolevModeWeight_natCast38 1 n
    rw [e2]
    have hn : ‖canField38 (fourierSeq38 u) n‖ ^ 2 = (2 * Real.pi) ^ 2 * ((n : ℝ) ^ 2 * ‖fourierSeq38 u n‖ ^ 2) := by
      unfold canField38
      rw [norm_mul, mul_pow, norm_genSeq38_apply, mul_pow, sq_abs, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, neg_sq]
    rw [hn]
    have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg ‖fourierSeq38 u n‖),
      mul_le_mul_of_nonneg_right hpi (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg ‖fourierSeq38 u n‖))]
  exact this

/-- Every `H¹` field has an `L²` Fourier derivative. -/
theorem exists_fourierDeriv38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : ∃ w, IsFourierDeriv38 u w := by
  have hx1 : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) u).2 (by simpa using hu)
  have hy : canField38 (fourierSeq38 u) ∈ seqSobolev38 0 :=
    mult_mem_seqSobolev38 0 (fun _ => ((-(2 * Real.pi) : ℝ) : ℂ)) (2 * Real.pi)
      (fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity)]) _ (genSeq38_mem_zero hx1)
  refine ⟨physInv38 _ hy, fun n => ?_⟩
  have h1 := fourierSeq38_physInv38 _ hy
  have h2 := congrFun h1 (-n)
  rw [fourierSeq38_apply, neg_neg] at h2
  have h3 : physicalFourier (physInv38 _ hy) n = -canField38 (fourierSeq38 u) (-n) := by
    rw [← h2]; ring
  rw [h3]
  unfold canField38 genSeq38
  rw [fourierSeq38_apply]
  push_cast
  ring_nf

theorem exists_fourierDeriv_unique38 {u w w' : PhysicalL2} (hw : IsFourierDeriv38 u w)
    (hw' : IsFourierDeriv38 u w') : w = w' := by
  apply fourierSeq38_injective
  rw [fourierSeq38_of_deriv38 hw, fourierSeq38_of_deriv38 hw']

/-- The isometry `h⁰ → L²`, `x ↦ 𝓕⁻¹ x`, as a real-linear isometry. -/
def carrierToPhysL38 : SobolevCarrier38 ((0 : ℕ) : ℝ) →ₗᵢ[ℝ] PhysicalL2 where
  toFun := carrierToPhys38
  map_add' a b := by
    apply fourierSeq38_injective
    funext n
    rw [fourierSeq38_add38]
    unfold carrierToPhys38
    rw [fourierSeq38_physInv38, fourierSeq38_physInv38, fourierSeq38_physInv38]
    rfl
  map_smul' r a := by
    apply fourierSeq38_injective
    funext n
    show fourierSeq38 (carrierToPhys38 (r • a)) n = fourierSeq38 ((r • carrierToPhys38 a)) n
    rw [show r • carrierToPhys38 a = (r : ℂ) • carrierToPhys38 a from (Complex.coe_smul r _).symm,
      fourierSeq38_smul38]
    unfold carrierToPhys38
    rw [fourierSeq38_physInv38, fourierSeq38_physInv38]
    rfl
  norm_map' x := by
    have h := norm_carrierToPhys38_sub x 0
    have h0 : carrierToPhys38 (0 : SobolevCarrier38 ((0 : ℕ) : ℝ)) = 0 := by
      apply fourierSeq38_injective
      funext n
      unfold carrierToPhys38
      rw [fourierSeq38_physInv38, fourierSeq38_zero38]
      rfl
    rw [h0, sub_zero, sub_zero] at h
    exact h

theorem fourierSeq38_carrierToPhysL38 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    fourierSeq38 (carrierToPhysL38 x) = carrierCoe38 _ x :=
  fourierSeq38_physInv38 _ _

/-- **S01.03 (physical derivative identity).**  If `w = u_x` (Fourier form) then
`t ↦ τ_t u` is differentiable in `L²` with derivative `τ_t w`: the PDE `u_t = u_x`. -/
theorem hasDerivAt_translate38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translateL2_38 s u) (translateL2_38 t w) t := by
  have hx1 := fourierSeq38_mem_one_of_deriv38 hw
  have hD := hasDerivAt_canFlow38 (fourierSeq38 u) hx1 t
  have hL := (carrierToPhysL38.toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t hD
  convert hL using 1
  · funext s
    apply fourierSeq38_injective
    show fourierSeq38 (translateL2_38 s u) = fourierSeq38 (carrierToPhysL38 _)
    rw [fourierSeq38_carrierToPhysL38, fourierSeq38_translate38]
    rfl
  · apply fourierSeq38_injective
    funext n
    show fourierSeq38 (translateL2_38 t w) n = fourierSeq38 (carrierToPhysL38 _) n
    rw [fourierSeq38_carrierToPhysL38, fourierSeq38_translate38, fourierSeq38_of_deriv38 hw]
    show canFlow38 t (canField38 (fourierSeq38 u)) n = _
    unfold canField38
    rw [canFlow38_apply]
    show _ = (-(2 * Real.pi)) • (genSeq38 (canFlow38 t (fourierSeq38 u)) n)
    rw [Complex.real_smul]
    simp only [genSeq38_apply, canFlow38_apply]
    push_cast
    ring

/-! ## Hamilton's equation in physical coordinates -/

/-- `ω(u_x, v) = 2π B(𝓕u, 𝓕v)`: the physical field `u_x` is the `ω`-Hamiltonian vector field of
`-P/2`, since `P = -2π N∘𝓕` (see `hasDerivAt_neg_half_momentum_line38`). -/
theorem omegaPhys_deriv38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) (v : PhysicalL2) :
    omegaPhys38 w v = 2 * Real.pi * momBil38 (fourierSeq38 u) (fourierSeq38 v) := by
  rw [← stdSymplectic38_fourierSeq38, fourierSeq38_of_deriv38 hw]
  unfold canField38
  rw [stdSymplectic38_real_mul_left, stdSymplectic38_gen_left]
  ring

theorem fourierSeq38_line38 (u v : PhysicalL2) (s : ℝ) :
    fourierSeq38 (u + (s : ℂ) • v) = fun n => fourierSeq38 u n + (s : ℂ) * fourierSeq38 v n := by
  funext n
  rw [fourierSeq38_add38, fourierSeq38_smul38]

/-- First variation of the physical momentum: `d/ds P(u + s v)|_{s=0} = -2 ω(u_x, v)`, i.e.
`ω(u_x, v) = d(-P/2)(u)[v]`; so `u_x` is the Hamiltonian field of `-P/2` for the form
`ω = Im ∫ ū v` (equivalently of `-P` for the normalization `{u,ū} = -iδ`, in which `ω` is doubled). -/
theorem hasDerivAt_momentum_line38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) (v : PhysicalL2)
    (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    HasDerivAt (fun s : ℝ => momentumFourier38 (u + (s : ℂ) • v)) (-2 * omegaPhys38 w v) 0 := by
  have hx := fourierSeq38_mem_one_of_deriv38 hw
  have hη : fourierSeq38 v ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) v).2 (by simpa using hv)
  have h := (hasDerivAt_momSeq_line38 _ _ hx hη).const_mul (-(2 * Real.pi))
  have hfun : (fun s : ℝ => momentumFourier38 (u + (s : ℂ) • v)) =
      fun s : ℝ => -(2 * Real.pi) * momSeq38 (fun n => fourierSeq38 u n + (s : ℂ) * fourierSeq38 v n) := by
    funext s
    rw [momentumFourier38_eq_neg_canonical, fourierSeq38_line38]
  rw [hfun, omegaPhys_deriv38 hw]
  exact h.congr_deriv (by ring)

theorem hasDerivAt_neg_half_momentum_line38 {u w : PhysicalL2} (hw : IsFourierDeriv38 u w)
    (v : PhysicalL2) (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    HasDerivAt (fun s : ℝ => -(momentumFourier38 (u + (s : ℂ) • v)) / 2) (omegaPhys38 w v) 0 := by
  have h := (hasDerivAt_momentum_line38 hw v hv).neg.div_const 2
  exact h.congr_deriv (by ring)

/-! ## Smooth fields -/

theorem contDiff_deriv38 {U : ℝ → ℂ} (hU : ContDiff ℝ ∞ U) : ContDiff ℝ ∞ (deriv U) :=
  (contDiff_infty_iff_deriv.1 hU).2

/-- For smooth period-one `U`, `(smoothL2 U')^_n = 2π i n (smoothL2 U)^_n`. -/
theorem isFourierDeriv_smoothL2_38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) :
    IsFourierDeriv38 (smoothL2_38 U hU hper)
      (smoothL2_38 (deriv U) (contDiff_deriv38 hU) (periodicDerivComplex_S01_38 U hU hper)) := by
  intro n
  have hdc : Continuous (deriv U) := hU.continuous_deriv (by simp)
  have hdp := periodicDerivComplex_S01_38 U hU hper
  have h1 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
    (deriv U) hdc hdp n
  have h2 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
    U hU.continuous hper n
  have h3 := riccatiFourierCoeffOn_deriv_periodOneRecovery29 U hU hper n
  unfold smoothL2_38
  rw [h1, h2, h3]
  unfold fourierMultiplier
  rfl

/-- **S01.03, smooth case.**  `t ↦ τ_t U` (as `L²` classes) has derivative `τ_t U'`: `u_t = u_x`. -/
theorem hasDerivAt_translate_smooth38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => translateL2_38 s (smoothL2_38 U hU hper))
      (translateL2_38 t (smoothL2_38 (deriv U) (contDiff_deriv38 hU)
        (periodicDerivComplex_S01_38 U hU hper))) t :=
  hasDerivAt_translate38 (isFourierDeriv_smoothL2_38 U hU hper) t

theorem liftIoc_coe_of_periodic38 (f : ℝ → ℂ) (hper : Function.Periodic f 1) (x : ℝ) :
    AddCircle.liftIoc 1 0 f (x : PhysicalCircle) = f x := by
  obtain ⟨t, ht, hte⟩ := exists_Ioc_rep38 (x : PhysicalCircle)
  have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  rw [← hte, AddCircle.liftIoc_coe_apply ht']
  have h0 : ((t - x : ℝ) : PhysicalCircle) = 0 := by
    rw [AddCircle.coe_sub, hte, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h0
  have : t = x + k • (1 : ℝ) := by rw [hk]; ring
  rw [this]; exact (hper.zsmul k) x

/-- Under `τ_s`, the smooth representative is translated pointwise: `(τ_s U)(x) = U(x+s)`. -/
theorem translateL2_38_smoothL2_38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (s : ℝ) :
    translateL2_38 s (smoothL2_38 U hU hper) =
      smoothL2_38 (fun x => U (x + s)) (hU.comp (contDiff_id.add contDiff_const))
        (fun x => by simp only [show x + 1 + s = (x + s) + 1 by ring]; exact hper (x + s)) := by
  apply Lp.ext
  have hmp := (measurePreserving_shiftPt38 s).quasiMeasurePreserving
  have h1 := translateL2_38_ae s (smoothL2_38 U hU hper)
  have h2 : (smoothL2_38 U hU hper : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure _
  have h3 := hmp.ae_eq_comp h2
  have h4 : (smoothL2_38 (fun x => U (x + s)) (hU.comp (contDiff_id.add contDiff_const))
        (fun x => by simp only [show x + 1 + s = (x + s) + 1 by ring]; exact hper (x + s)) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      riccatiSmoothPeriodicLiftContinuousMapRecovery30First (fun x => U (x + s))
        (hU.comp (contDiff_id.add contDiff_const)).continuous
        (fun x => by simp only [show x + 1 + s = (x + s) + 1 by ring]; exact hper (x + s)) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure _
  filter_upwards [h1, h3, h4] with y hy1 hy3 hy4
  rw [hy1, hy4]
  simp only [Function.comp, shiftPt38] at hy3
  rw [hy3]
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk]
  rw [← AddCircle.coe_add]
  rw [liftIoc_coe_of_periodic38 _ hper, liftIoc_coe_of_periodic38 _
    (fun x => by simp only [show x + 1 + s = (x + s) + 1 by ring]; exact hper (x + s))]

/-! ## Strong continuity of the translation group -/

/-- `t ↦ τ_t u` is continuous into `L²`, for every `u ∈ L²`. -/
theorem continuous_translate38 (u : PhysicalL2) : Continuous (fun t : ℝ => translateL2_38 t u) := by
  let g : ℝ → C(PhysicalCircle, PhysicalCircle) := fun t => ⟨shiftPt38 t, by
    unfold shiftPt38; fun_prop⟩
  have hg : Continuous g := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : ℝ × PhysicalCircle => p.2 + (p.1 : PhysicalCircle))
    fun_prop
  have h := Continuous.compMeasurePreservingLp (μ := spatialMeasure) (ν := spatialMeasure)
    (f := fun _ : ℝ => u) (g := g) continuous_const hg
    (fun t => measurePreserving_shiftPt38 t) (by norm_num)
  exact h

end NlsGge.Birkhoff
