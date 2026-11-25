import Mathlib
import QuantumNLS.SymplecticBracket

/-!
# LOCAL-015 `lem:reset:ray-period-upgrade` (projective return and its symplectic normalization)

Source: `source/chapters/local/quantum_periods.tex`, lines 405 ff (statement and printed proof),
`\ReportID{LOCAL-015}`, status `Proved`.

Printed statement.  Let `ℋ` have complex dimension at least two and let `F` be a continuously
Fréchet differentiable symplectic map on a punctured norm ball.  Suppose `F(u)` lies on the complex
unit ray of `u` for every nonzero `u`.  If each mass sphere contains one point fixed by `F`, then `F`
is the identity on that punctured ball.

## Formal statement (`ray_period_upgrade`, all hypotheses literal)
* `H` : a complex Hilbert space (`NormedAddCommGroup`, `InnerProductSpace ℂ`, `CompleteSpace`);
  inner product linear in the second slot.
* complex dimension `≥ 2` : `hdim : 2 ≤ Module.rank ℂ H` (`two_le_rank_of_orthonormal`: two
  orthonormal vectors give this).
* punctured norm ball : `puncturedBall H R = Metric.ball 0 R \ {0} = {u | 0 < ‖u‖ < R}` (open).
* `F : H → H`, `hF : ContDiffOn ℝ 1 F (puncturedBall H R)` : continuously Fréchet differentiable over
  `ℝ` on the realification (`attribute [local instance] InnerProductSpace.complexToReal`, the DEF-015
  / DEF-016 convention of `StrongSymplectic`).
* symplectic : `hsymp : ∀ u ∈ ball, ∀ h k, omega (fderiv ℝ F u h) (fderiv ℝ F u k) = omega h k`, with
  `omega = QuantumNLS.SymplecticBracket.omega` the realized DEF-015 form `2 Im⟨·,·⟩`, used read-only.
  (This is `F^*ω = ω` pointwise, exactly the `symplectic` field of `StrongSymplectic.IsStronglySymplectic`.)
* ray : `hray : ∀ u ∈ ball, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u` (`F u` lies on the complex unit ray of `u`).
* fixed points : `hfix : ∀ m, 0 < m → m < R ^ 2 → ∃ v, ‖v‖ ^ 2 = m ∧ F v = v` (each mass sphere
  `{‖v‖² = m}` of the ball contains a point fixed by `F`; mass `m(u) = ‖u‖²`).
* conclusion : `∀ u ∈ puncturedBall H R, F u = u`.

## Proof (printed route, bookkeeping adjusted; every step proved)
1. `c(u) := ⟨u,F(u)⟩/‖u‖²` (`cfun`); `F(u) = c(u) u`, `|c| = 1` (`cfun_of_ray`, `norm_cfun`);
   `c` is `C¹` on the ball (`cfun_differentiableAt`: inner product, `‖·‖²`, inverse), hence
   `DF(u)h = c(u) h + dc(u)[h] u` (`fderiv_ray`).
2. Differentiating `|c|² = 1` gives `Re(c̄ dc[h]) = 0` (`re_conj_cfun_mul_fderiv`), i.e.
   `c̄ dc[h] = i dθ[h]` (the printed `dθ`, defined as `Im(c̄ dc)`).
3. Substituting into `Ω(DF h, DF k)` and taking `h = u` (radial, `dm[u] = 2‖u‖² ≠ 0`) and `k` with
   `Re⟨u,k⟩ = 0` (tangent to the mass sphere), the cross terms of `F^*ω − ω = dm ∧ dθ` give
   `dθ[k] ‖u‖² = 0` (`alg`, `alg2`, `fderiv_cfun_tangent`): `dc[k] = 0`.
4. `c` is constant on mass spheres: for `y ≠ -x` of equal norm, along the normalised segment
   `γ(s) = ‖x‖ (x + s(y−x))/‖x + s(y−x)‖` the derivative of `c ∘ γ` is `dc[γ'(s)] = 0`
   (`γ'` is tangent since `‖γ‖` is constant) so `c(x) = c(y)` (`cfun_eq_of_ne_neg`,
   `is_const_of_deriv_eq_zero`); for `y = −x`, route through a third point of the sphere off the
   real line `ℝ x`, available because `dim_ℂ H ≥ 2` (`exists_not_mem_span`, `cfun_const_on_sphere`).
5. The fixed point on the sphere forces the constant to be `1` (`ray_period_upgrade`).

## Deviations from the printed proof (nothing weakened)
* No local real argument `θ` with `c = e^{iθ}` is chosen.  The printed `dθ` is represented by
  `Im(c̄ dc)`, which is global and only needs `|c| = 1` differentiated; this is the same computation
  and avoids the local-branch argument.
* Path connectedness of the mass sphere is replaced by explicit `C¹` normalised-segment paths plus one
  intermediate point (this uses exactly `dim_ℂ H ≥ 2`); the printed "orthogonal unit vector" paths are
  not needed.
* Only differentiability of `F` on the open punctured ball is used (not continuity of `DF`);
  `ContDiffOn ℝ 1` is kept as the literal hypothesis.  Completeness of `H` is not used.
* The ball radius `R` is a real number (`R = ∞` is not separately formalised; any `R` is covered,
  and the statement is vacuous for `R ≤ 0`).
-/

set_option autoImplicit false
noncomputable section

open InnerProductSpace ComplexConjugate Filter Topology

-- realification of the complex Hilbert space (as in DEF-015 / DEF-016): real Fréchet derivatives
-- and the real inner product `Re ⟨·,·⟩`
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RayPeriodUpgrade

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The punctured norm ball `{u : 0 < ‖u‖ < R}`. -/
def puncturedBall (H : Type*) [NormedAddCommGroup H] (R : ℝ) : Set H :=
  Metric.ball (0 : H) R \ {0}

lemma isOpen_puncturedBall (R : ℝ) : IsOpen (puncturedBall H R) :=
  Metric.isOpen_ball.sdiff isClosed_singleton

lemma mem_puncturedBall {R : ℝ} {u : H} : u ∈ puncturedBall H R ↔ 0 < ‖u‖ ∧ ‖u‖ < R := by
  simp [puncturedBall, norm_pos_iff, and_comm]

lemma ne_zero_of_mem {R : ℝ} {u : H} (hu : u ∈ puncturedBall H R) : u ≠ 0 :=
  norm_pos_iff.mp (mem_puncturedBall.mp hu).1

/-- `c(u) = ⟨u, F(u)⟩ / ‖u‖²` (printed proof). -/
def cfun (F : H → H) (u : H) : ℂ := inner ℂ u (F u) / ((‖u‖ ^ 2 : ℝ) : ℂ)

lemma norm_sq_ne_zero {u : H} (hu : u ≠ 0) : ((‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)

lemma cfun_of_ray {F : H → H} {u : H} (hu : u ≠ 0) {c : ℂ} (h : F u = c • u) :
    cfun F u = c := by
  unfold cfun
  rw [h, inner_smul_right, QuantumNLS.SymplecticBracket.inner_self_eq_ofReal]
  exact mul_div_cancel_right₀ _ (norm_sq_ne_zero hu)

lemma cfun_differentiableAt {R : ℝ} {F : H → H} (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    {u : H} (hu : u ∈ puncturedBall H R) : DifferentiableAt ℝ (cfun F) u := by
  have hFd : DifferentiableAt ℝ F u :=
    (hF.contDiffAt ((isOpen_puncturedBall R).mem_nhds hu)).differentiableAt one_ne_zero
  have h1 : DifferentiableAt ℝ (fun v => inner ℂ v (F v)) u :=
    DifferentiableAt.inner ℂ differentiableAt_id hFd
  have h2 : DifferentiableAt ℝ (fun v : H => ((‖v‖ ^ 2 : ℝ) : ℂ)) u :=
    Complex.ofRealCLM.differentiableAt.comp u (differentiableAt_id.norm_sq ℝ)
  have h3 := h1.mul (h2.inv (norm_sq_ne_zero (ne_zero_of_mem hu)))
  have e : cfun F = (fun v => inner ℂ v (F v)) * (fun v : H => ((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    funext v; simp [cfun, div_eq_mul_inv]
  rw [e]; exact h3

/-- On `F(u) = c(u) u`: the derivative of `F`. -/
lemma fderiv_ray {R : ℝ} {F : H → H} (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {u : H} (hu : u ∈ puncturedBall H R) (h : H) :
    fderiv ℝ F u h = cfun F u • h + (fderiv ℝ (cfun F) u h) • u := by
  have hc := cfun_differentiableAt hF hu
  have hev : (fun v => cfun F v • v) =ᶠ[𝓝 u] F := by
    filter_upwards [(isOpen_puncturedBall R).mem_nhds hu] with v hv
    obtain ⟨c0, -, h0⟩ := hray v hv
    rw [h0, cfun_of_ray (ne_zero_of_mem hv) h0]
  have hd : HasFDerivAt (fun v => cfun F v • v)
      (cfun F u • ContinuousLinearMap.id ℝ H + (fderiv ℝ (cfun F) u).smulRight u) u :=
    hc.hasFDerivAt.smul (hasFDerivAt_id u)
  have := (hd.congr_of_eventuallyEq hev.symm).fderiv
  rw [this]
  simp

lemma norm_cfun {R : ℝ} {F : H → H}
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {u : H} (hu : u ∈ puncturedBall H R) : ‖cfun F u‖ = 1 := by
  obtain ⟨c0, h1, h0⟩ := hray u hu
  rw [cfun_of_ray (ne_zero_of_mem hu) h0, h1]

/-- Differentiating `|c|² = 1`: `Re(c̄ dc[h]) = 0`. -/
lemma re_conj_cfun_mul_fderiv {R : ℝ} {F : H → H} (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {u : H} (hu : u ∈ puncturedBall H R) (h : H) :
    (conj (cfun F u) * fderiv ℝ (cfun F) u h).re = 0 := by
  have hc := cfun_differentiableAt hF hu
  have hn := hc.hasFDerivAt.norm_sq
  have hn' : HasFDerivAt (fun v => ‖cfun F v‖ ^ 2) (0 : H →L[ℝ] ℝ) u := by
    refine (hasFDerivAt_const (1 : ℝ) u).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_puncturedBall R).mem_nhds hu] with v hv
    simp [norm_cfun hray hv]
  have := congrArg (fun T : H →L[ℝ] ℝ => T h) (hn.unique hn')
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.zero_apply] at this
  rw [Complex.inner] at this
  have h2 : (fderiv ℝ (cfun F) u h * conj (cfun F u)).re = 0 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, nsmul_eq_mul, Nat.cast_ofNat] at this ⊢
    linarith
  rw [mul_comm]; exact h2

/-- The purely algebraic core: the two cross terms. -/
lemma alg2 (A B z : ℂ) (r : ℝ) (hr : 0 < r) (hA : A.re = 0) (hB : B.re = 0) (hz : z.re = 0)
    (h : (z + B * (r : ℂ) + conj A * z + conj A * B * (r : ℂ)).im = z.im) : B = 0 := by
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, hA, hB, hz] at h
  have hb : B.im * r = 0 := by nlinarith
  have : B.im = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact absurd h hr.ne'
  exact Complex.ext hB this

lemma alg (cu du dk z : ℂ) (r : ℝ) (hr : 0 < r) (hcu : conj cu * cu = 1)
    (hA : (conj cu * du).re = 0) (hB : (conj cu * dk).re = 0) (hz : z.re = 0)
    (h : (conj cu * (cu * z + dk * (r : ℂ)) + conj du * (cu * z + dk * (r : ℂ))).im = z.im) :
    dk = 0 := by
  have e : conj cu * (cu * z + dk * (r : ℂ)) + conj du * (cu * z + dk * (r : ℂ)) =
      z + (conj cu * dk) * (r : ℂ) + conj (conj cu * du) * z +
        conj (conj cu * du) * (conj cu * dk) * (r : ℂ) := by
    simp only [map_mul, Complex.conj_conj]
    linear_combination (z - conj du * dk * (r : ℂ)) * hcu
  rw [e] at h
  have hB0 := alg2 _ _ z r hr hA hB hz h
  have : dk = cu * (conj cu * dk) := by
    calc dk = (conj cu * cu) * dk := by rw [hcu, one_mul]
      _ = _ := by ring
  rw [this, hB0, mul_zero]

/-- **Tangential derivative.**  The symplectic condition forces `dc[k] = 0` for every `k` with
`Re⟨u,k⟩ = 0` (the tangent space of the mass sphere through `u`). -/
lemma fderiv_cfun_tangent {R : ℝ} {F : H → H} (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hsymp : ∀ u ∈ puncturedBall H R, ∀ h k : H,
      QuantumNLS.SymplecticBracket.omega (fderiv ℝ F u h) (fderiv ℝ F u k) =
        QuantumNLS.SymplecticBracket.omega h k)
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {u : H} (hu : u ∈ puncturedBall H R) {k : H} (hk : (inner ℂ u k).re = 0) :
    fderiv ℝ (cfun F) u k = 0 := by
  have hs := hsymp u hu u k
  unfold QuantumNLS.SymplecticBracket.omega at hs
  rw [fderiv_ray hF hray hu, fderiv_ray hF hray hu] at hs
  have hr : 0 < ‖u‖ ^ 2 := pow_pos (mem_puncturedBall.mp hu).1 2
  have hcu : conj (cfun F u) * cfun F u = 1 := by
    rw [Complex.conj_mul']; simp [norm_cfun hray hu]
  refine alg (cfun F u) (fderiv ℝ (cfun F) u u) (fderiv ℝ (cfun F) u k) (inner ℂ u k) (‖u‖ ^ 2)
    hr hcu (re_conj_cfun_mul_fderiv hF hray hu u) (re_conj_cfun_mul_fderiv hF hray hu k) hk ?_
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    QuantumNLS.SymplecticBracket.inner_self_eq_ofReal] at hs
  ring_nf at hs ⊢
  linarith

/-- Two points of equal norm, `y ≠ -x`: the normalised segment stays on the sphere, and `c` is
constant along it (its derivative vanishes on tangent vectors). -/
lemma cfun_eq_of_ne_neg {R : ℝ} {F : H → H} (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hsymp : ∀ u ∈ puncturedBall H R, ∀ h k : H,
      QuantumNLS.SymplecticBracket.omega (fderiv ℝ F u h) (fderiv ℝ F u k) =
        QuantumNLS.SymplecticBracket.omega h k)
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {x y : H} (hx : x ∈ puncturedBall H R) (hy : y ∈ puncturedBall H R) (hxy : ‖x‖ = ‖y‖)
    (hne : y ≠ -x) : cfun F x = cfun F y := by
  have hr : 0 < ‖x‖ := (mem_puncturedBall.mp hx).1
  have hrR : ‖x‖ < R := (mem_puncturedBall.mp hx).2
  set n : ℝ → H := fun s => x + s • (y - x) with hn
  have hn0 : ∀ s, n s ≠ 0 := by
    intro s h0
    have h1 : (1 - s) • x = -(s • y) := by
      have : (1 - s) • x + s • y = 0 := by
        rw [← h0]; simp only [hn]; module
      exact eq_neg_of_add_eq_zero_left this
    have h2 := congrArg norm h1
    rw [norm_neg, norm_smul, norm_smul, ← hxy, Real.norm_eq_abs, Real.norm_eq_abs] at h2
    have h3 : |1 - s| = |s| := mul_right_cancel₀ hr.ne' h2
    rcases abs_eq_abs.mp h3 with h | h
    · have hs : s = 1 / 2 := by linarith
      apply hne
      have : y = (2 : ℝ) • (x + (1 / 2 : ℝ) • (y - x)) - x := by module
      rw [this]
      have h0' : x + (1 / 2 : ℝ) • (y - x) = 0 := by rw [← hs]; exact h0
      rw [h0']; simp
    · linarith
  have hnd : ∀ s, DifferentiableAt ℝ n s := fun s => by
    simp only [hn]
    fun_prop
  set γ : ℝ → H := fun s => (‖x‖ / ‖n s‖) • n s with hγ
  have hγnorm : ∀ s, ‖γ s‖ = ‖x‖ := fun s => by
    have : ‖n s‖ ≠ 0 := norm_ne_zero_iff.mpr (hn0 s)
    simp only [hγ, norm_smul, Real.norm_eq_abs, abs_div, abs_norm]
    field_simp
  have hγP : ∀ s, γ s ∈ puncturedBall H R := fun s =>
    mem_puncturedBall.mpr ⟨by rw [hγnorm]; exact hr, by rw [hγnorm]; exact hrR⟩
  have hγd : ∀ s, DifferentiableAt ℝ γ s := fun s => by
    have h1 : DifferentiableAt ℝ (fun s => ‖n s‖) s := (hnd s).norm ℝ (hn0 s)
    have h2 : DifferentiableAt ℝ (fun s => ‖x‖ / ‖n s‖) s :=
      (differentiableAt_const _).div h1 (norm_ne_zero_iff.mpr (hn0 s))
    exact h2.smul (hnd s)
  have hγ0 : γ 0 = x := by
    simp only [hγ, hn, zero_smul, add_zero]
    rw [div_self hr.ne', one_smul]
  have hγ1 : γ 1 = y := by
    have : n 1 = y := by simp [hn]
    simp only [hγ]
    rw [this, ← hxy, div_self hr.ne', one_smul]
  have hg : ∀ s, HasDerivAt (fun s => cfun F (γ s)) (fderiv ℝ (cfun F) (γ s) (deriv γ s)) s :=
    fun s => (cfun_differentiableAt hF (hγP s)).hasFDerivAt.comp_hasDerivAt s (hγd s).hasDerivAt
  have htan : ∀ s, (inner ℂ (γ s) (deriv γ s)).re = 0 := by
    intro s
    have h1 := (hγd s).hasDerivAt.norm_sq
    have h2 : HasDerivAt (fun s => ‖γ s‖ ^ 2) 0 s := by
      have : (fun s => ‖γ s‖ ^ 2) = fun _ => ‖x‖ ^ 2 := funext fun s => by rw [hγnorm]
      rw [this]; exact hasDerivAt_const s _
    have h3 := h1.unique h2
    have h4 : inner ℝ (γ s) (deriv γ s) = 0 := by linarith
    rwa [real_inner_eq_re_inner ℂ] at h4
  have hderiv : ∀ s, deriv (fun s => cfun F (γ s)) s = 0 := fun s => by
    rw [(hg s).deriv]
    exact fderiv_cfun_tangent hF hsymp hray (hγP s) (htan s)
  have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) hderiv 0 1
  simpa only [hγ0, hγ1] using this


/-- With complex dimension `≥ 2`, no vector spans the whole space. -/
lemma exists_not_mem_span (hdim : 2 ≤ Module.rank ℂ H) (x : H) :
    ∃ w : H, w ∉ Submodule.span ℂ {x} := by
  by_contra hcon
  push_neg at hcon
  have htop : Submodule.span ℂ {x} = ⊤ := Submodule.eq_top_iff'.mpr hcon
  have h1 : Module.rank ℂ H ≤ 1 := by
    calc Module.rank ℂ H = Module.rank ℂ (Submodule.span ℂ {x}) := by
          rw [htop]; exact (rank_top ℂ H).symm
      _ ≤ 1 := (rank_span_le _).trans (by simp)
  exact absurd (lt_of_lt_of_le Cardinal.one_lt_two hdim) (not_lt.mpr h1)

/-- **Mass spheres are connected for the problem.**  `c` is constant on every sphere of the
punctured ball (this is where `dim_ℂ H ≥ 2` is used: two antipodal points are joined through a third
point of the sphere off the real line they span). -/
lemma cfun_const_on_sphere (hdim : 2 ≤ Module.rank ℂ H) {R : ℝ} {F : H → H}
    (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hsymp : ∀ u ∈ puncturedBall H R, ∀ h k : H,
      QuantumNLS.SymplecticBracket.omega (fderiv ℝ F u h) (fderiv ℝ F u k) =
        QuantumNLS.SymplecticBracket.omega h k)
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    {x y : H} (hx : x ∈ puncturedBall H R) (hy : y ∈ puncturedBall H R) (hxy : ‖x‖ = ‖y‖) :
    cfun F x = cfun F y := by
  by_cases hne : y = -x
  swap
  · exact cfun_eq_of_ne_neg hF hsymp hray hx hy hxy hne
  obtain ⟨w, hw⟩ := exists_not_mem_span hdim x
  have hw0 : w ≠ 0 := fun h => hw (h ▸ Submodule.zero_mem _)
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hr : 0 < ‖x‖ := (mem_puncturedBall.mp hx).1
  have hrR : ‖x‖ < R := (mem_puncturedBall.mp hx).2
  set z : H := (‖x‖ / ‖w‖) • w with hz
  have hzn : ‖z‖ = ‖x‖ := by
    rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hwn)]
    field_simp
  have hzP : z ∈ puncturedBall H R :=
    mem_puncturedBall.mpr ⟨by rw [hzn]; exact hr, by rw [hzn]; exact hrR⟩
  have hnot : ∀ t : ℝ, z ≠ t • x := by
    intro t ht
    apply hw
    have : w = ((‖w‖ / ‖x‖) * t) • x := by
      have h1 : w = (‖w‖ / ‖x‖) • z := by
        have hc : (‖w‖ / ‖x‖) * (‖x‖ / ‖w‖) = 1 := by field_simp
        rw [hz, smul_smul, hc, one_smul]
      calc w = (‖w‖ / ‖x‖) • z := h1
        _ = _ := by rw [ht, smul_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have hzx : z ≠ x := by simpa using hnot 1
  have hzx' : z ≠ -x := by simpa using hnot (-1)
  have h1 := cfun_eq_of_ne_neg hF hsymp hray hx hzP hzn.symm hzx'
  have h2 : y ≠ -z := by
    intro h; apply hzx; rw [hne] at h; exact neg_inj.mp h.symm
  have h3 := cfun_eq_of_ne_neg hF hsymp hray hzP hy (hzn.trans hxy) h2
  exact h1.trans h3

/-- **LOCAL-015 `lem:reset:ray-period-upgrade`.**  Let `H` be a complex Hilbert space of complex
dimension at least `2`, `R > 0` (any real `R`), and `F : H → H` continuously Fréchet differentiable
(over `ℝ`, on the realification) on the punctured norm ball `{0 < ‖u‖ < R}`, symplectic there
(`Ω(DF(u)h, DF(u)k) = Ω(h,k)`, `Ω = 2 Im⟨·,·⟩`, `SymplecticBracket.omega`), with `F(u)` on the complex
unit ray of `u` for every `u ≠ 0` in the ball.  If each mass sphere `{‖v‖² = m}` (`0 < m < R²`) contains a
point fixed by `F`, then `F` is the identity on the punctured ball. -/
theorem ray_period_upgrade (hdim : 2 ≤ Module.rank ℂ H) {R : ℝ} {F : H → H}
    (hF : ContDiffOn ℝ 1 F (puncturedBall H R))
    (hsymp : ∀ u ∈ puncturedBall H R, ∀ h k : H,
      QuantumNLS.SymplecticBracket.omega (fderiv ℝ F u h) (fderiv ℝ F u k) =
        QuantumNLS.SymplecticBracket.omega h k)
    (hray : ∀ u ∈ puncturedBall H R, ∃ c : ℂ, ‖c‖ = 1 ∧ F u = c • u)
    (hfix : ∀ m : ℝ, 0 < m → m < R ^ 2 → ∃ v : H, ‖v‖ ^ 2 = m ∧ F v = v) :
    ∀ u ∈ puncturedBall H R, F u = u := by
  intro u hu
  obtain ⟨hu0, huR⟩ := mem_puncturedBall.mp hu
  obtain ⟨v, hv, hFv⟩ := hfix (‖u‖ ^ 2) (pow_pos hu0 2) (pow_lt_pow_left₀ huR hu0.le two_ne_zero)
  have hvu : ‖v‖ = ‖u‖ := by
    have := hv
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  have hvP : v ∈ puncturedBall H R :=
    mem_puncturedBall.mpr ⟨by rw [hvu]; exact hu0, by rw [hvu]; exact huR⟩
  have hcv : cfun F v = 1 := by
    obtain ⟨c0, -, h0⟩ := hray v hvP
    rw [cfun_of_ray (ne_zero_of_mem hvP) h0]
    have h1 : (c0 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h0, hFv, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right (ne_zero_of_mem hvP))
  obtain ⟨c0, -, h0⟩ := hray u hu
  have hcu : c0 = 1 := by
    rw [← cfun_of_ray (ne_zero_of_mem hu) h0, cfun_const_on_sphere hdim hF hsymp hray hu hvP hvu.symm,
      hcv]
  rw [h0, hcu, one_smul]

/-- Two orthonormal vectors give complex dimension at least two. -/
theorem two_le_rank_of_orthonormal {e₁ e₂ : H} (h : Orthonormal ℂ ![e₁, e₂]) :
    2 ≤ Module.rank ℂ H := by
  have := h.linearIndependent.cardinal_lift_le_rank
  simpa using this

end QuantumNLS.RayPeriodUpgrade

#print axioms QuantumNLS.RayPeriodUpgrade.ray_period_upgrade
#print axioms QuantumNLS.RayPeriodUpgrade.cfun_const_on_sphere
#print axioms QuantumNLS.RayPeriodUpgrade.cfun_eq_of_ne_neg
#print axioms QuantumNLS.RayPeriodUpgrade.fderiv_cfun_tangent
#print axioms QuantumNLS.RayPeriodUpgrade.two_le_rank_of_orthonormal
