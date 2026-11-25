import Mathlib
import QuantumNLS.SymplecticBracket
import QuantumNLS.StrongSymplectic
import QuantumNLS.Fourier

/-!
# LOCAL-022 `thm:reset-normalization-uniqueness`: uniqueness under the quantum real symmetry

Source: `source/chapters/local/local_covariance.tex`, lines 219 ff (statement and printed proof),
`\ReportID{LOCAL-022}`, status `Proved`.

Printed statement.  Two real-analytic canonical maps from the same full `L²` ball onto the same
sequence ball, having exactly the indexed masses as squared moduli, derivative `𝓕` at zero, and
intertwining `u ↦ conj(u(−x))` with componentwise conjugation, are identical.  (Also: without the
last condition there is, in general, action-dependent canonical phase freedom.)

## Formal statement (`reset_normalization_uniqueness`)
* Spaces: `L²(𝕋_L) = Lp ℂ 2 volume` (DEF-001), `ℓ²(ℤ) = lp (fun _ => ℂ) 2` (DEF-002, `S2 ℤ`),
  `𝓕 = Fourier.fourierL2 L` (read-only).  Balls `Metric.ball 0 r`, `r > 0`.
* "Canonical map" = `IsStronglySymplecticOn` (local DEF-016 on balls: diffeomorphism onto, derivative
  a real-linear isomorphism, `Ω(DΦh, DΦk) = Ω(h,k)` with `Ω = SymplecticBracket.omega`, DEF-015).
  For `s = t = univ` it is exactly `StrongSymplectic.IsStronglySymplectic`
  (`isStronglySymplecticOn_univ`).
* Real-analytic: `AnalyticOnNhd ℝ Φ ball` recorded literally; the proof uses only differentiability.
* Indexed masses (pinned): the report's `a_n(u) = |w_n(u)|²`, `w_n = Φ^q(u)_n`, equals the indexed mass
  `M_{κ,u}((b_{n−1},b_n))` of DEF-014 / `core/coordinate_conventions.tex` ("exact indexed mass").  DEF-014
  is not realized as an object in this repository, so `q : ℤ → L² → ℝ` is an abstract family; the proof
  uses only `‖Φ₁(u)_n‖² = q_n(u) = ‖Φ₂(u)_n‖²` and `q_n(0) = 0` (mass of the zero field).
* Derivative `𝓕` at zero: `fderiv ℝ Φ_i 0 h = 𝓕 h` for all `h`.
* Real symmetry: `C : L² → L²` with `𝓕(Cu)_n = conj(𝓕(u)_n)` and `Φ_i(Cu) = star(Φ_i u)`
  (`star` = componentwise conjugation on `ℓ²`).  `C` is `u ↦ conj(u(−x))` by `fourier_reflConj`
  (any `C` representing `conj(u(−·))` almost everywhere has this Fourier property, by
  `Fourier.coeff_conj_reflect`); the `Lp`-level reflection-conjugation map is not itself constructed.
* Conclusion: `Φ₁ = Φ₂` on the ball.

## Proof (printed route)
`T = Φ₂ ∘ Φ₁⁻¹` is a canonical diffeomorphism of the sequence ball (`comp_inv_props`), preserves every
`|a_n|`, commutes with `star`, has `DT(0) = id` (`KeyHyp`).  Then:
1. (`KeyHyp.fderiv_vecX`) full symplectic chain rule: `DT X_{q_i} = X_{q_i} ∘ T`, from `q_i ∘ T = q_i`
   and nondegeneracy of `Ω`; `X_i(a) = i a_i e_i`.
2. (`KeyHyp.commute_rot`) both `t ↦ T(R_t a)` and `t ↦ R_t T(a)` solve `y' = X_i(y)` (Lipschitz), so `T`
   commutes with every single-coordinate rotation `R_{i,t}` (ODE uniqueness `ODE_solution_unique_univ`).
3. (`KeyHyp.fixed_of_nonneg`) for `b` real nonnegative: `T(sb)` is real with the same moduli, so
   `T(sb)_n = ±s b_n`; the sign is continuous in `s ∈ (0,1]` hence constant; `DT(0) = id` makes it `+1`.
4. (`KeyHyp.fixed_of_finite`) finite collections of coordinate rotations of a nonnegative sequence.
5. (`KeyHyp.eq_id`) every `z` is the limit of its finite truncations (`lp.hasSum_single`); continuity.
6. `reset_normalization_uniqueness` assembles these (`Φ₂ = T ∘ Φ₁` etc.).

## Deviations / gaps (nothing hidden)
* Local (ball) version of DEF-016, as the statement is about balls.
* `q_n` abstract (DEF-014 not realized); `C` specified by its Fourier action (see above).
* Hypothesis `q_n(0) = 0` is used to get `Φ_i(0) = 0` (implicit in "derivative 𝓕 at zero").
* Real analyticity is not used beyond differentiability.
* The non-uniqueness assertion is formalized as an explicit counterexample family (below), not as a
  statement about all chart pairs: the printed text says "in general".

## Non-uniqueness without the conjugation condition (`reset_normalization_nonuniqueness`)
For every `κ > 0`: `Φ₁ = 𝓕` and `Φ₂ = Th_κ ∘ 𝓕`, `Th_κ z = e^{iκ‖z‖²} z` (the time-one flow of the
degree-four radial Hamiltonian, the printed `F(z) = c‖z‖⁴` example), are two *distinct* real-analytic
canonical maps (`IsStronglySymplecticOn`) of the same `L²` ball onto the same `ℓ²(ℤ)` ball with the
same squared moduli `q_n(u) = |𝓕(u)_n|²` and derivative `𝓕` at zero; `Φ₁` intertwines the conjugation and
`Φ₂` does not (`reset_normalization_conj_condition_necessary`, a corollary of the uniqueness theorem).
`Th_κ` is canonical because `F^*ω − ω = dm ∧ dθ` with `dθ = κ dm` (`omega_cross`: the two cross terms
cancel), real analytic (`analyticOnNhd_Th`), with explicit inverse `Th_{-κ}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open InnerProductSpace ComplexConjugate Filter Topology
open scoped ENNReal

set_option autoImplicit false
noncomputable section

-- real structure of the complex Hilbert spaces (DEF-015 / DEF-016 convention)
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.ResetNormalizationUniqueness

/-- The sequence Hilbert space `ℓ²(ι; ℂ)` (`ℓ²(ℤ)` for DEF-002 at `s = 0`). -/
abbrev S2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

section Lp

variable {ι : Type*} [DecidableEq ι]

lemma norm_eq_of_norm_apply_eq {a b : S2 ι} (h : ∀ n, ‖a n‖ = ‖b n‖) : ‖a‖ = ‖b‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp a
  have h2 := lp.norm_rpow_eq_tsum hp b
  simp only [h] at h1
  have h3 : ‖a‖ ^ (2 : ℝ≥0∞).toReal = ‖b‖ ^ (2 : ℝ≥0∞).toReal := by rw [h1, h2]
  exact (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp h3

/-- Multiplication of the `i`-th coordinate by `e^{iφ}` (the time-`φ` flow of `q_i = |a_i|²`). -/
def rot (i : ι) (φ : ℝ) (a : S2 ι) : S2 ι :=
  a + (Complex.exp (φ * Complex.I) - 1) • (a i • lp.single 2 i (1 : ℂ))

lemma rot_apply (i : ι) (φ : ℝ) (a : S2 ι) (n : ι) :
    rot i φ a n = if n = i then Complex.exp (φ * Complex.I) * a i else a n := by
  simp only [rot, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, lp.single_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · simp

lemma norm_rot (i : ι) (φ : ℝ) (a : S2 ι) : ‖rot i φ a‖ = ‖a‖ := by
  refine norm_eq_of_norm_apply_eq fun n => ?_
  rw [rot_apply]
  split_ifs with h
  · subst h; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · rfl

lemma rot_zero (i : ι) (a : S2 ι) : rot i 0 a = a := by
  ext n; rw [rot_apply]; split_ifs with h <;> simp [h]

/-- The Hamiltonian vector field of `q_i = |a_i|²` (up to the sign fixed by `Ω`): `X_i(a) = i a_i e_i`. -/
def vecX (i : ι) (a : S2 ι) : S2 ι := (Complex.I * a i) • lp.single 2 i (1 : ℂ)

lemma vecX_apply (i : ι) (a : S2 ι) (n : ι) :
    vecX i a n = if n = i then Complex.I * a i else 0 := by
  simp only [vecX, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

lemma lipschitz_vecX (i : ι) : LipschitzWith 1 (vecX i) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h : vecX i a - vecX i b = (Complex.I * (a i - b i)) • lp.single 2 i (1 : ℂ) := by
    simp only [vecX, ← sub_smul]; congr 1; ring
  rw [h, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one, norm_mul, Complex.norm_I,
    one_mul]
  have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (a - b) i
  simpa using this

lemma hasDerivAt_rot (i : ι) (y : S2 ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => rot i s y) (vecX i (rot i t y)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.exp (s * Complex.I))
      (Complex.exp (t * Complex.I) * (1 * Complex.I)) t :=
    (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  have h2 : HasDerivAt
      (fun s : ℝ => (Complex.exp (s * Complex.I) - 1) • (y i • (lp.single 2 i (1 : ℂ) : S2 ι)))
      ((Complex.exp (t * Complex.I) * (1 * Complex.I)) • (y i • (lp.single 2 i (1 : ℂ) : S2 ι))) t :=
    (h1.sub_const 1).smul_const (y i • (lp.single 2 i (1 : ℂ) : S2 ι))
  have h3 := h2.const_add y
  have e : (Complex.exp (t * Complex.I) * (1 * Complex.I)) •
      (y i • (lp.single 2 i (1 : ℂ) : S2 ι)) = vecX i (rot i t y) := by
    unfold vecX
    rw [rot_apply, if_pos rfl, smul_smul]
    congr 1
    ring
  exact h3.congr_deriv e

/-- `Ω(X_i(y), k) = -2 Re(ȳ_i k_i)`. -/
lemma omega_vecX (i : ι) (y k : S2 ι) :
    QuantumNLS.SymplecticBracket.omega (vecX i y) k = -2 * (conj (y i) * k i).re := by
  unfold QuantumNLS.SymplecticBracket.omega vecX
  rw [inner_smul_left, lp.inner_single_left]
  simp [Complex.mul_im, Complex.mul_re]
  ring

end Lp


section Key

variable {ι : Type*} [DecidableEq ι]

/-- `Ω(x - y, z) = Ω(x,z) - Ω(y,z)`. -/
lemma omega_sub_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y z : H) :
    QuantumNLS.SymplecticBracket.omega (x - y) z =
      QuantumNLS.SymplecticBracket.omega x z - QuantumNLS.SymplecticBracket.omega y z := by
  unfold QuantumNLS.SymplecticBracket.omega
  rw [inner_sub_left, Complex.sub_im]; ring

/-- Nondegeneracy: `Ω(v, i v) = 2‖v‖²`. -/
lemma omega_self_I {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : H) :
    QuantumNLS.SymplecticBracket.omega v (Complex.I • v) = 2 * ‖v‖ ^ 2 := by
  unfold QuantumNLS.SymplecticBracket.omega
  rw [inner_smul_right, QuantumNLS.SymplecticBracket.inner_self_eq_ofReal]
  simp
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The structural hypotheses on `T = Φ₂ ∘ Φ₁⁻¹` used by the printed uniqueness proof: `T` is a
canonical (strongly symplectic) diffeomorphism of the ball `{‖a‖ < r}` of `ℓ²(ι)` onto itself which
preserves every modulus `|a_n|` (the indexed masses), commutes with componentwise conjugation and
has derivative the identity at `0`. -/
structure KeyHyp (T : S2 ι → S2 ι) (r : ℝ) : Prop where
  mem : ∀ a ∈ Metric.ball (0 : S2 ι) r, T a ∈ Metric.ball (0 : S2 ι) r
  diff : ∀ a ∈ Metric.ball (0 : S2 ι) r, DifferentiableAt ℝ T a
  surj : ∀ a ∈ Metric.ball (0 : S2 ι) r, Function.Surjective (fderiv ℝ T a)
  symp : ∀ a ∈ Metric.ball (0 : S2 ι) r, ∀ h k : S2 ι,
    QuantumNLS.SymplecticBracket.omega (fderiv ℝ T a h) (fderiv ℝ T a k) =
      QuantumNLS.SymplecticBracket.omega h k
  modulus : ∀ a ∈ Metric.ball (0 : S2 ι) r, ∀ n, ‖T a n‖ = ‖a n‖
  cjcomm : ∀ a ∈ Metric.ball (0 : S2 ι) r, T (star a) = star (T a)
  deriv0 : fderiv ℝ T 0 = ContinuousLinearMap.id ℝ (S2 ι)

variable {T : S2 ι → S2 ι} {r : ℝ}

lemma rot_mem_ball {a : S2 ι} (ha : a ∈ Metric.ball (0 : S2 ι) r) (i : ι) (φ : ℝ) :
    rot i φ a ∈ Metric.ball (0 : S2 ι) r := by
  rw [mem_ball_zero_iff] at *; rwa [norm_rot]

/-- The key identity from `q_i ∘ T = q_i`: `Re(\overline{(Tc)_i} (DT k)_i) = Re(\bar c_i k_i)`. -/
lemma KeyHyp.re_identity (hT : KeyHyp T r) {c : S2 ι} (hc : c ∈ Metric.ball (0 : S2 ι) r)
    (i : ι) (k : S2 ι) :
    (conj (T c i) * (fderiv ℝ T c k) i).re = (conj (c i) * k i).re := by
  set D := fderiv ℝ T c with hD
  have hl : HasDerivAt (fun s : ℝ => c + s • k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add c
  have hTc : HasFDerivAt T D (c + (0 : ℝ) • k) := by
    simpa using (hT.diff c hc).hasFDerivAt
  have hcomp := hTc.comp_hasDerivAt 0 hl
  let ev : S2 ι →L[ℝ] ℂ := lp.evalCLM ℝ (fun _ : ι => ℂ) 2 i
  have h1 : HasDerivAt (fun s : ℝ => T (c + s • k) i) (D k i) 0 :=
    ev.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have h2 : HasDerivAt (fun s : ℝ => (c + s • k) i) (k i) 0 :=
    ev.hasFDerivAt.comp_hasDerivAt 0 hl
  have h1' := h1.norm_sq
  have h2' := h2.norm_sq
  have hev : (fun s : ℝ => ‖T (c + s • k) i‖ ^ 2) =ᶠ[𝓝 0] fun s : ℝ => ‖(c + s • k) i‖ ^ 2 := by
    have hcont : ContinuousAt (fun s : ℝ => c + s • k) 0 := by fun_prop
    have hball : ∀ᶠ s : ℝ in 𝓝 0, c + s • k ∈ Metric.ball (0 : S2 ι) r :=
      hcont.eventually_mem (by simpa using Metric.isOpen_ball.mem_nhds hc)
    filter_upwards [hball] with s hs
    rw [hT.modulus _ hs i]
  have h3 := h1'.unique (h2'.congr_of_eventuallyEq hev)
  simp only [Complex.inner, zero_smul, add_zero, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
    or_false] at h3
  have e1 : (D k i * conj (T c i)).re = (conj (T c i) * D k i).re := by rw [mul_comm]
  have e2 : (k i * conj (c i)).re = (conj (c i) * k i).re := by rw [mul_comm]
  rw [← e1, ← e2]
  exact h3

/-- `DT(c) X_i(c) = X_i(T c)`: a canonical map preserving `q_i` maps the Hamiltonian field of `q_i`
to itself (the printed full symplectic chain rule). -/
theorem KeyHyp.fderiv_vecX (hT : KeyHyp T r) {c : S2 ι} (hc : c ∈ Metric.ball (0 : S2 ι) r)
    (i : ι) : fderiv ℝ T c (vecX i c) = vecX i (T c) := by
  set D := fderiv ℝ T c with hD
  set v : S2 ι := vecX i (T c) - D (vecX i c) with hv
  have hk : ∀ k, QuantumNLS.SymplecticBracket.omega v (D k) = 0 := by
    intro k
    rw [hv, omega_sub_left, omega_vecX, hT.re_identity hc i k, ← omega_vecX, ← hT.symp c hc]
    ring
  obtain ⟨k, hk'⟩ := hT.surj c hc (Complex.I • v)
  have h0 := hk k
  rw [show D k = Complex.I • v from hk', omega_self_I] at h0
  have hv0 : v = 0 := by
    have : ‖v‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  exact (sub_eq_zero.mp hv0).symm

/-- **`T` commutes with the rotation of every single coordinate.**  Both `t ↦ T(R_t a)` and
`t ↦ R_t T(a)` solve the Lipschitz equation `y' = X_i(y)` with the same initial value. -/
theorem KeyHyp.commute_rot (hT : KeyHyp T r) {a : S2 ι} (ha : a ∈ Metric.ball (0 : S2 ι) r)
    (i : ι) (φ : ℝ) : T (rot i φ a) = rot i φ (T a) := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => T (rot i s a)) (vecX i (T (rot i t a))) t := by
    intro t
    have hm := rot_mem_ball ha i t
    have := (hT.diff _ hm).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_rot i a t)
    rwa [hT.fderiv_vecX hm i] at this
  have hδ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => rot i s (T a)) (vecX i (rot i t (T a))) t :=
    fun t => hasDerivAt_rot i (T a) t
  have := ODE_solution_unique_univ (v := fun (_ : ℝ) => vecX i) (s := fun _ => Set.univ) (K := 1)
    (f := fun s : ℝ => T (rot i s a)) (g := fun s : ℝ => rot i s (T a)) (t₀ := 0)
    (fun _ => (lipschitz_vecX i).lipschitzOnWith) (fun t => ⟨hγ t, trivial⟩)
    (fun t => ⟨hδ t, trivial⟩) (by simp only [rot_zero])
  exact congrFun this φ


/-- `T(0) = 0`. -/
lemma KeyHyp.map_zero (hT : KeyHyp T r) (hr : 0 < r) : T 0 = 0 := by
  have h0 : (0 : S2 ι) ∈ Metric.ball (0 : S2 ι) r := Metric.mem_ball_self hr
  ext n
  have := hT.modulus 0 h0 n
  simpa using this

/-- **Real nonnegative sequences are fixed** (printed step: `T(b)` is real with the same moduli, the
sign along `s b`, `0 < s ≤ 1`, is continuous hence constant, and the identity derivative at `0` makes
it positive). -/
theorem KeyHyp.fixed_of_nonneg (hT : KeyHyp T r) (hr : 0 < r) {b : S2 ι}
    (hb : b ∈ Metric.ball (0 : S2 ι) r) (hnr : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ b n = x) : T b = b := by
  have h0ball : (0 : S2 ι) ∈ Metric.ball (0 : S2 ι) r := Metric.mem_ball_self hr
  have hT0 := hT.map_zero hr
  have hstar : ∀ s : ℝ, star (s • b) = s • b := by
    intro s; ext m; obtain ⟨y, -, hy⟩ := hnr m; simp [hy]
  ext n
  by_cases hbn : b n = 0
  · have := hT.modulus b hb n
    rw [hbn] at this ⊢
    simpa using this
  obtain ⟨x, hx0, hx⟩ := hnr n
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (fun h => hbn (by rw [hx, ← h]; simp))
  have hsb : ∀ s ∈ Set.Ioc (0 : ℝ) 1, s • b ∈ Metric.ball (0 : S2 ι) r := by
    intro s hs
    rw [mem_ball_zero_iff] at hb ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hs.2) hb
  have hreal : ∀ s ∈ Set.Ioc (0 : ℝ) 1, (T (s • b) n).im = 0 := by
    intro s hs
    have h := hT.cjcomm (s • b) (hsb s hs)
    rw [hstar s] at h
    have h2 := congrArg (fun w : S2 ι => w n) h
    simp only [lp.star_apply] at h2
    exact Complex.conj_eq_iff_im.mp h2.symm
  have hmod : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖T (s • b) n‖ = s * x := by
    intro s hs
    rw [hT.modulus _ (hsb s hs)]
    simp [hx, abs_of_pos hs.1, abs_of_nonneg hx0]
  set f : ℝ → ℂ := fun s => T (s • b) n / ((s : ℂ) * b n) with hf
  have hvals : ∀ s ∈ Set.Ioc (0 : ℝ) 1, f s = 1 ∨ f s = -1 := by
    intro s hs
    have hz : T (s • b) n = ((T (s • b) n).re : ℂ) := Complex.ext (by simp) (by simpa using hreal s hs)
    have habs : |(T (s • b) n).re| = s * x := by
      have := hmod s hs
      rw [hz, Complex.norm_real, Real.norm_eq_abs] at this
      simpa using this
    have hsx : 0 < s * x := mul_pos hs.1 hxpos
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.1.ne'
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    rcases (abs_eq hsx.le).mp habs with h | h
    · left
      simp only [hf]; rw [hz, h, hx]; push_cast; field_simp
    · right
      simp only [hf]; rw [hz, h, hx]; push_cast; field_simp
  have hc1 : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ContinuousAt (fun s : ℝ => T (s • b) n) s := by
    intro s hs
    have hTc : ContinuousAt T (s • b) := (hT.diff _ (hsb s hs)).continuousAt
    have hline : ContinuousAt (fun s : ℝ => s • b) s := by fun_prop
    exact (lp.evalCLM ℝ (fun _ : ι => ℂ) 2 n).continuous.continuousAt.comp
      (ContinuousAt.comp (g := T) (f := fun s' : ℝ => s' • b) (x := s) hTc hline)
  have hfc : ContinuousOn f (Set.Ioc 0 1) := by
    intro s hs
    refine ContinuousAt.continuousWithinAt ?_
    have hden : ((s : ℂ) * b n) ≠ 0 := mul_ne_zero (by exact_mod_cast hs.1.ne') hbn
    exact (hc1 s hs).div (by fun_prop) hden
  have hdisc : IsDiscrete ({1, -1} : Set ℂ) := by
    rw [Set.insert_eq]
    exact (Set.Subsingleton.isDiscrete Set.subsingleton_singleton).union
      (Set.Subsingleton.isDiscrete Set.subsingleton_singleton) isClosed_singleton isClosed_singleton
  have hmaps : Set.MapsTo f (Set.Ioc 0 1) {1, -1} := fun s hs => by
    simpa using hvals s hs
  have h1mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hconst : ∀ s ∈ Set.Ioc (0 : ℝ) 1, f s = f 1 := fun s hs =>
    isPreconnected_Ioc.constant_of_mapsTo hdisc hfc hmaps hs h1mem
  -- limit at `0+`
  have hd : HasDerivAt (fun s : ℝ => T (s • b)) b 0 := by
    have hl : HasDerivAt (fun s : ℝ => s • b) b 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const b
    have hTc : HasFDerivAt T (fderiv ℝ T 0) ((0 : ℝ) • b) := by
      simpa using (hT.diff 0 h0ball).hasFDerivAt
    have := hTc.comp_hasDerivAt 0 hl
    rw [hT.deriv0] at this
    exact this
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simp only [zero_add, zero_smul, hT0, sub_zero] at hslope
  have hcoord := ((lp.evalCLM ℝ (fun _ : ι => ℂ) 2 n).continuous.tendsto b).comp hslope
  have hlim0 : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h3 : Tendsto (fun t : ℝ => ((t⁻¹ • T (t • b)) n) / b n) (𝓝[≠] (0 : ℝ)) (𝓝 (b n / b n)) :=
      hcoord.div_const (b n)
    rw [div_self hbn] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    simp only [hf, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
    push_cast
    field_simp
  have hNe : (𝓝[Set.Ioc (0 : ℝ) 1] (0 : ℝ)).NeBot := by
    rw [nhdsWithin_Ioc_eq_nhdsGT zero_lt_one]; infer_instance
  have hlim : Tendsto f (𝓝[Set.Ioc (0 : ℝ) 1] (0 : ℝ)) (𝓝 1) :=
    hlim0.mono_left (nhdsWithin_mono _ (fun s hs => ne_of_gt hs.1))
  have hconstlim : Tendsto f (𝓝[Set.Ioc (0 : ℝ) 1] (0 : ℝ)) (𝓝 (f 1)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs using (hconst s hs).symm)
  have hf1 : f 1 = 1 := tendsto_nhds_unique hconstlim hlim
  simp only [hf, one_smul, Complex.ofReal_one, one_mul] at hf1
  exact (div_eq_one_iff_eq hbn).mp hf1

/-- Finite collections of coordinates may be rotated: `T w = w` when all but finitely many
coordinates of `w` are real nonnegative. -/
theorem KeyHyp.fixed_of_finite (hT : KeyHyp T r) (hr : 0 < r) (S : Finset ι) :
    ∀ w ∈ Metric.ball (0 : S2 ι) r, (∀ n ∉ S, ∃ x : ℝ, 0 ≤ x ∧ w n = x) → T w = w := by
  induction S using Finset.induction_on with
  | empty =>
    intro w hw h
    exact hT.fixed_of_nonneg hr hw (fun n => h n (by simp))
  | insert i S hi ih =>
    intro w hw h
    set w' : S2 ι := w + (((‖w i‖ : ℝ) : ℂ) - w i) • (lp.single 2 i (1 : ℂ) : S2 ι) with hw'
    have hw'apply : ∀ n, w' n = if n = i then ((‖w i‖ : ℝ) : ℂ) else w n := by
      intro n
      simp only [hw', lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul]
      split_ifs with hni
      · subst hni; ring
      · simp
    have hw'norm : ‖w'‖ = ‖w‖ := by
      refine norm_eq_of_norm_apply_eq fun n => ?_
      rw [hw'apply]
      split_ifs with hni
      · subst hni; simp
      · rfl
    have hw'ball : w' ∈ Metric.ball (0 : S2 ι) r := by
      rw [mem_ball_zero_iff] at hw ⊢; rwa [hw'norm]
    have hw'h : ∀ n ∉ S, ∃ x : ℝ, 0 ≤ x ∧ w' n = x := by
      intro n hn
      rw [hw'apply]
      by_cases hni : n = i
      · exact ⟨‖w i‖, norm_nonneg _, by simp [hni]⟩
      · simp only [hni, if_false]
        exact h n (by simp [hni, hn])
    have hTw' := ih w' hw'ball hw'h
    have hrw : rot i (Complex.arg (w i)) w' = w := by
      ext n
      rw [rot_apply]
      split_ifs with hni
      · subst hni
        rw [hw'apply, if_pos rfl, mul_comm]
        exact Complex.norm_mul_exp_arg_mul_I (w n)
      · rw [hw'apply, if_neg hni]
    calc T w = T (rot i (Complex.arg (w i)) w') := by rw [hrw]
      _ = rot i (Complex.arg (w i)) (T w') := hT.commute_rot hw'ball i _
      _ = rot i (Complex.arg (w i)) w' := by rw [hTw']
      _ = w := hrw

/-- **The key rigidity theorem.**  Under `KeyHyp T r` (and `r > 0`), `T` is the identity on the ball:
every `z` is the limit of its finite truncations, each of which is a finite coordinate rotation of a
nonnegative real sequence. -/
theorem KeyHyp.eq_id (hT : KeyHyp T r) (hr : 0 < r) : ∀ z ∈ Metric.ball (0 : S2 ι) r, T z = z := by
  intro z hz
  have ht : Tendsto (fun S : Finset ι => ∑ i ∈ S, lp.single 2 i (z i)) atTop (𝓝 z) :=
    lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) z
  have hev : ∀ᶠ S in atTop, (∑ i ∈ S, lp.single 2 i (z i)) ∈ Metric.ball (0 : S2 ι) r :=
    ht.eventually (Metric.isOpen_ball.mem_nhds hz)
  have hfix : ∀ᶠ S in atTop,
      T (∑ i ∈ S, lp.single 2 i (z i)) = ∑ i ∈ S, lp.single 2 i (z i) :=
    hev.mono fun S hS => hT.fixed_of_finite hr S _ hS (fun n hn => ⟨0, le_rfl, by
      simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single, if_neg hn]
      simp⟩)
  have hTcont : ContinuousAt T z := (hT.diff z hz).continuousAt
  have h1 : Tendsto (fun S : Finset ι => T (∑ i ∈ S, lp.single 2 i (z i))) atTop (𝓝 (T z)) :=
    hTcont.tendsto.comp ht
  have h2 : Tendsto (fun S : Finset ι => T (∑ i ∈ S, lp.single 2 i (z i))) atTop (𝓝 z) :=
    ht.congr' (hfix.mono fun S hS => hS.symm)
  exact tendsto_nhds_unique h1 h2

end Key


section Canon

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Local DEF-016.**  `Φ` maps the open set `s ⊆ H` bijectively onto `t ⊆ E`, is a real
differentiable diffeomorphism there (differentiable inverse), its derivative is a bounded real-linear
isomorphism at every point, and `Ω(DΦ(u)h, DΦ(u)k) = Ω(h,k)` with `Ω = SymplecticBracket.omega`
(DEF-015).  For `s = t = univ` this is exactly `StrongSymplectic.IsStronglySymplectic`
(`isStronglySymplecticOn_univ`); DEF-016 as printed is global, and no local version is defined in the
source, so this is the evident restriction to a ball, as required by the statement of LOCAL-022. -/
structure IsStronglySymplecticOn (s : Set H) (t : Set E) (Φ : H → E) : Prop where
  mapsTo : Set.MapsTo Φ s t
  exists_inverse : ∃ Ψ : E → H, Set.MapsTo Ψ t s ∧ (∀ x ∈ s, Ψ (Φ x) = x) ∧
    (∀ y ∈ t, Φ (Ψ y) = y) ∧ ∀ y ∈ t, DifferentiableAt ℝ Ψ y
  differentiable : ∀ u ∈ s, DifferentiableAt ℝ Φ u
  deriv_iso : ∀ u ∈ s, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ u
  symplectic : ∀ u ∈ s, ∀ h k : H,
    QuantumNLS.SymplecticBracket.omega (fderiv ℝ Φ u h) (fderiv ℝ Φ u k) =
      QuantumNLS.SymplecticBracket.omega h k

/-- The global DEF-016 (`StrongSymplectic.IsStronglySymplectic`) is the case `s = t = univ`. -/
theorem isStronglySymplecticOn_univ {Φ : H → E}
    (h : QuantumNLS.StrongSymplectic.IsStronglySymplectic Φ) :
    IsStronglySymplecticOn (Set.univ : Set H) (Set.univ : Set E) Φ where
  mapsTo := fun _ _ => trivial
  exists_inverse := by
    obtain ⟨Ψ, hl, hr, hd⟩ := h.exists_inverse
    exact ⟨Ψ, fun _ _ => trivial, fun x _ => hl x, fun y _ => hr y, fun y _ => hd y⟩
  differentiable := fun u _ => h.differentiable u
  deriv_iso := fun u _ => h.deriv_iso u
  symplectic := fun u _ => h.symplectic u

/-- `T = Φ₂ ∘ Φ₁⁻¹` is a canonical diffeomorphism of `t`: the structural facts used by the printed
proof. -/
theorem comp_inv_props {s : Set H} {t : Set E} (hs : IsOpen s) (ht : IsOpen t) {Φ₁ Φ₂ : H → E}
    (h1 : IsStronglySymplecticOn s t Φ₁) (h2 : IsStronglySymplecticOn s t Φ₂) {Ψ : E → H}
    (hΨm : Set.MapsTo Ψ t s) (hΨl : ∀ x ∈ s, Ψ (Φ₁ x) = x) (hΨr : ∀ y ∈ t, Φ₁ (Ψ y) = y)
    (hΨd : ∀ y ∈ t, DifferentiableAt ℝ Ψ y) :
    (∀ a ∈ t, Φ₂ (Ψ a) ∈ t) ∧ (∀ a ∈ t, DifferentiableAt ℝ (Φ₂ ∘ Ψ) a) ∧
    (∀ a ∈ t, Function.Surjective (fderiv ℝ (Φ₂ ∘ Ψ) a)) ∧
    (∀ a ∈ t, ∀ h k : E, QuantumNLS.SymplecticBracket.omega (fderiv ℝ (Φ₂ ∘ Ψ) a h)
        (fderiv ℝ (Φ₂ ∘ Ψ) a k) = QuantumNLS.SymplecticBracket.omega h k) := by
  have hchain : ∀ a ∈ t, ∀ x, fderiv ℝ Φ₁ (Ψ a) (fderiv ℝ Ψ a x) = x := by
    intro a ha x
    have hev : (Φ₁ ∘ Ψ) =ᶠ[nhds a] id := by
      filter_upwards [ht.mem_nhds ha] with y hy using hΨr y hy
    have h1' : fderiv ℝ (Φ₁ ∘ Ψ) a = ContinuousLinearMap.id ℝ E := by
      rw [hev.fderiv_eq, fderiv_id]
    rw [fderiv_comp a (h1.differentiable _ (hΨm ha)) (hΨd a ha)] at h1'
    simpa using congrArg (fun T => T x) h1'
  have hchain' : ∀ a ∈ t, ∀ x, fderiv ℝ Ψ a (fderiv ℝ Φ₁ (Ψ a) x) = x := by
    intro a ha x
    have hu := hΨm ha
    have hev : (Ψ ∘ Φ₁) =ᶠ[nhds (Ψ a)] id := by
      filter_upwards [hs.mem_nhds hu] with y hy using hΨl y hy
    have h1' : fderiv ℝ (Ψ ∘ Φ₁) (Ψ a) = ContinuousLinearMap.id ℝ H := by
      rw [hev.fderiv_eq, fderiv_id]
    have hΨ' : DifferentiableAt ℝ Ψ (Φ₁ (Ψ a)) := by rw [hΨr a ha]; exact hΨd a ha
    rw [fderiv_comp (Ψ a) hΨ' (h1.differentiable _ hu)] at h1'
    have := congrArg (fun T => T x) h1'
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rwa [hΨr a ha] at this
  have hDT : ∀ a ∈ t, fderiv ℝ (Φ₂ ∘ Ψ) a = (fderiv ℝ Φ₂ (Ψ a)).comp (fderiv ℝ Ψ a) := fun a ha =>
    fderiv_comp a (h2.differentiable _ (hΨm ha)) (hΨd a ha)
  refine ⟨fun a ha => h2.mapsTo (hΨm ha), fun a ha =>
    (h2.differentiable _ (hΨm ha)).comp a (hΨd a ha), fun a ha => ?_, fun a ha h k => ?_⟩
  · rw [hDT a ha]
    obtain ⟨e, he⟩ := h2.deriv_iso _ (hΨm ha)
    have hs1 : Function.Surjective (fderiv ℝ Ψ a) := fun x =>
      ⟨fderiv ℝ Φ₁ (Ψ a) x, hchain' a ha x⟩
    have hs2 : Function.Surjective (fderiv ℝ Φ₂ (Ψ a)) := by rw [← he]; exact e.surjective
    exact hs2.comp hs1
  · rw [hDT a ha]
    simp only [ContinuousLinearMap.comp_apply]
    rw [h2.symplectic _ (hΨm ha), ← h1.symplectic _ (hΨm ha), hchain a ha, hchain a ha]

end Canon


section Main

open MeasureTheory AddCircle

variable (L : ℝ) [Fact (0 < L)]

/-- The reflection-conjugation `u ↦ \overline{u(-x)}` acts on Fourier coefficients as componentwise
conjugation (`Fourier.coeff_conj_reflect`).  Hence any map `C` on `L²(𝕋_L)` that represents
`u ↦ \overline{u(-·)}` almost everywhere satisfies the Fourier-side property `hC` used below. -/
theorem fourier_reflConj (C : Lp ℂ 2 (volume : Measure (AddCircle L)) →
      Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hC : ∀ u, ((C u : Lp ℂ 2 (volume : Measure (AddCircle L))) : AddCircle L → ℂ) =ᵐ[volume]
      fun x => conj ((u : AddCircle L → ℂ) (-x))) (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (n : ℤ) : QuantumNLS.Fourier.fourierL2 L (C u) n = conj (QuantumNLS.Fourier.fourierL2 L u n) := by
  rw [QuantumNLS.Fourier.fourierL2_apply, QuantumNLS.Fourier.fourierL2_apply,
    ← QuantumNLS.Fourier.coeff_conj_reflect]
  unfold QuantumNLS.Fourier.coeff
  exact integral_congr_ae (by filter_upwards [hC u] with x hx; rw [hx])

/-- **LOCAL-022 `thm:reset-normalization-uniqueness` (uniqueness part).**

Let `𝓕 = Fourier.fourierL2 L : L²(𝕋_L) ≃ₗᵢ[ℂ] ℓ²(ℤ)` and let `Φ₁, Φ₂` be canonical
(strongly symplectic, `IsStronglySymplecticOn`) real-analytic maps from the same full `L²` ball
`{‖u‖ < r}` onto the same `ℓ²(ℤ)` ball, with squared moduli the indexed masses `q_n`
(`‖Φ_i(u)_n‖² = q_n(u)`, `q_n(0) = 0`), derivative `𝓕` at zero, and intertwining the
reflection-conjugation `C` (`u ↦ \overline{u(-x)}`, characterized by its Fourier coefficients
`𝓕(Cu)_n = \overline{𝓕(u)_n}`, cf. `fourier_reflConj`) with componentwise conjugation
`star`.  Then `Φ₁ = Φ₂` on the ball.

The indexed masses `q_n` enter only through `‖Φ₁(u)_n‖ = ‖Φ₂(u)_n‖`; DEF-014 (`a_n(u)` = mass of the
spectral measure on `(b_{n-1}, b_n)`) is not realized as an object in this repository, so `q` is an
abstract family of functions, with the single property `q_n(0) = 0` used (mass of the zero field).
Real-analyticity is recorded literally (`AnalyticOnNhd ℝ` on the ball) but only differentiability
(contained in `IsStronglySymplecticOn`) is used. -/
theorem reset_normalization_uniqueness {r : ℝ} (hr : 0 < r)
    (q : ℤ → Lp ℂ 2 (volume : Measure (AddCircle L)) → ℝ) (hq0 : ∀ n, q n 0 = 0)
    (C : Lp ℂ 2 (volume : Measure (AddCircle L)) → Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hC : ∀ u n, QuantumNLS.Fourier.fourierL2 L (C u) n = conj (QuantumNLS.Fourier.fourierL2 L u n))
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (_han₁ : AnalyticOnNhd ℝ Φ₁ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (_han₂ : AnalyticOnNhd ℝ Φ₂ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₁ u n‖ ^ 2 = q n u)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₂ u n‖ ^ 2 = q n u)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hc₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (C u) = star (Φ₁ u))
    (hc₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (C u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, Φ₁ u = Φ₂ u := by
  set Bs := Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r with hBs
  set Bt := Metric.ball (0 : S2 ℤ) r with hBt
  obtain ⟨Ψ, hΨm, hΨl, hΨr, hΨd⟩ := hΦ₁.exists_inverse
  obtain ⟨hmem, hdiff, hsurj, hsymp⟩ := comp_inv_props Metric.isOpen_ball Metric.isOpen_ball
    hΦ₁ hΦ₂ hΨm hΨl hΨr hΨd
  have h0s : (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) ∈ Bs := Metric.mem_ball_self hr
  have h0t : (0 : S2 ℤ) ∈ Bt := Metric.mem_ball_self hr
  have hΦ10 : Φ₁ 0 = 0 := by
    ext n
    have := hm₁ 0 h0s n
    rw [hq0] at this
    have h2 : ‖Φ₁ 0 n‖ = 0 := by nlinarith [norm_nonneg (Φ₁ 0 n)]
    simpa using h2
  have hΨ0 : Ψ 0 = 0 := by rw [← hΦ10, hΨl 0 h0s]
  have hCnorm : ∀ u, ‖C u‖ = ‖u‖ := by
    intro u
    have h : QuantumNLS.Fourier.fourierL2 L (C u) = star (QuantumNLS.Fourier.fourierL2 L u) := by
      ext n; rw [hC]; rfl
    rw [← QuantumNLS.Fourier.norm_fourierL2 L (C u), h, norm_star,
      QuantumNLS.Fourier.norm_fourierL2]
  have hKey : KeyHyp (Φ₂ ∘ Ψ) r := by
    refine ⟨hmem, hdiff, hsurj, hsymp, ?_, ?_, ?_⟩
    · intro a ha n
      have hu := hΨm ha
      have h1 := hm₁ _ hu n
      have h2 := hm₂ _ hu n
      rw [hΨr a ha] at h1
      have : ‖(Φ₂ ∘ Ψ) a n‖ ^ 2 = ‖a n‖ ^ 2 := by simp only [Function.comp]; rw [h2, h1]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
    · intro a ha
      have hu := hΨm ha
      have hCu : C (Ψ a) ∈ Bs := by
        rw [hBs, mem_ball_zero_iff] at hu ⊢; rwa [hCnorm]
      have hstar : star a = Φ₁ (C (Ψ a)) := by rw [hc₁ _ hu, hΨr a ha]
      have hΨs : Ψ (star a) = C (Ψ a) := by rw [hstar, hΨl _ hCu]
      simp only [Function.comp, hΨs, hc₂ _ hu]
    · have hd1 := hΦ₁.differentiable
      -- chain rule at 0
      have hcomp : fderiv ℝ (Φ₂ ∘ Ψ) 0 =
          (fderiv ℝ Φ₂ (Ψ 0)).comp (fderiv ℝ Ψ 0) :=
        fderiv_comp 0 (hΦ₂.differentiable _ (hΨm h0t)) (hΨd 0 h0t)
      have hchain : ∀ x, fderiv ℝ Φ₁ (Ψ 0) (fderiv ℝ Ψ 0 x) = x := by
        intro x
        have hev : (Φ₁ ∘ Ψ) =ᶠ[nhds (0 : S2 ℤ)] id := by
          filter_upwards [Metric.isOpen_ball.mem_nhds h0t] with y hy using hΨr y hy
        have h1' : fderiv ℝ (Φ₁ ∘ Ψ) 0 = ContinuousLinearMap.id ℝ (S2 ℤ) := by
          rw [hev.fderiv_eq, fderiv_id]
        rw [fderiv_comp 0 (hΦ₁.differentiable _ (hΨm h0t)) (hΨd 0 h0t)] at h1'
        simpa using congrArg (fun T => T x) h1'
      ext x : 1
      rw [hcomp, ContinuousLinearMap.comp_apply, hΨ0, hD₂, ← hD₁]
      rw [hΨ0] at hchain
      exact hchain x
  have hid := hKey.eq_id hr
  intro u hu
  have h1 : Φ₁ u ∈ Bt := hΦ₁.mapsTo hu
  have := hid _ h1
  simp only [Function.comp, hΨl u hu] at this
  exact this.symm

end Main


section Phase

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The mass-dependent common phase `e^{iκ‖z‖²}` (time-one flow of the radial Hamiltonian
`∝ κ‖z‖⁴`, a degree-four function of the coordinates). -/
def ph (κ : ℝ) (z : H) : ℂ := Complex.exp (((κ * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I)

/-- The canonical near-identity map `z ↦ e^{iκ‖z‖²} z`. -/
def Th (κ : ℝ) (z : H) : H := ph κ z • z

lemma norm_ph (κ : ℝ) (z : H) : ‖ph κ z‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma norm_Th (κ : ℝ) (z : H) : ‖Th κ z‖ = ‖z‖ := by
  rw [Th, norm_smul, norm_ph, one_mul]

lemma ph_Th (κ : ℝ) (z : H) : ph κ (Th κ z) = ph κ z := by
  unfold ph; rw [norm_Th]

lemma Th_Th (κ : ℝ) (z : H) : Th (-κ) (Th κ z) = z := by
  have : ph (-κ) (Th κ z) * ph κ z = 1 := by
    unfold ph; rw [norm_Th, ← Complex.exp_add]
    rw [show (((-κ * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I) + ((κ * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I = 0 by
      push_cast; ring]
    simp
  have e : Th (-κ) (Th κ z) = ph (-κ) (Th κ z) • (ph κ z • z) := rfl
  rw [e, smul_smul, this, one_smul]

lemma Th_zero_kappa (z : H) : Th 0 z = z := by
  simp [Th, ph]

/-- Derivative of the phase `z ↦ e^{iκ‖z‖²}`. -/
def dph (κ : ℝ) (z : H) : H →L[ℝ] ℂ :=
  (ph κ z * Complex.I * ((2 * κ : ℝ) : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ z))

lemma hasFDerivAt_ph (κ : ℝ) (z : H) : HasFDerivAt (ph κ) (dph κ z) z := by
  have h1 : HasFDerivAt (fun x : H => ‖x‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := h1.const_mul κ
  have h3 := (Complex.ofRealCLM.hasFDerivAt (x := κ * ‖z‖ ^ 2)).comp z h2
  have h4 := h3.mul_const Complex.I
  have h5 := ((Complex.hasDerivAt_exp (((κ * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I)).hasFDerivAt.restrictScalars
    ℝ).comp z h4
  have hfun : ph κ = Complex.exp ∘ fun y : H =>
      (Complex.ofRealCLM ∘ fun y : H => κ * ‖y‖ ^ 2) y * Complex.I := by
    funext y; simp [ph]
  rw [hfun]
  refine h5.congr_fderiv ?_
  ext h
  simp [dph, ph, ContinuousLinearMap.smul_apply, innerSL_apply_apply, nsmul_eq_mul]
  push_cast
  ring

lemma hasFDerivAt_Th (κ : ℝ) (z : H) :
    HasFDerivAt (Th κ) (ph κ z • ContinuousLinearMap.id ℝ H + (dph κ z).smulRight z) z :=
  (hasFDerivAt_ph κ z).smul (hasFDerivAt_id z)

lemma fderiv_Th_apply (κ : ℝ) (z h : H) :
    fderiv ℝ (Th κ) z h = ph κ z • h + (dph κ z h) • z := by
  rw [(hasFDerivAt_Th κ z).fderiv]; simp

/-- `Ω(c x, c y) = Ω(x, y)` for a unit complex number `c`. -/
lemma omega_unit_smul {c : ℂ} (hc : ‖c‖ = 1) (x y : H) :
    QuantumNLS.SymplecticBracket.omega (c • x) (c • y) = QuantumNLS.SymplecticBracket.omega x y := by
  unfold QuantumNLS.SymplecticBracket.omega
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

/-- The two cross terms of `F^*ω − ω = dm ∧ dθ` cancel when `dθ = κ dm`. -/
lemma omega_cross (κ : ℝ) (z h k : H) :
    QuantumNLS.SymplecticBracket.omega
      (h + (Complex.I * ((2 * κ * (inner ℂ z h).re : ℝ) : ℂ)) • z)
      (k + (Complex.I * ((2 * κ * (inner ℂ z k).re : ℝ) : ℂ)) • z) =
      QuantumNLS.SymplecticBracket.omega h k := by
  unfold QuantumNLS.SymplecticBracket.omega
  have hzh : inner ℂ h z = conj (inner ℂ z h) := (inner_conj_symm h z).symm
  have hre : (inner ℂ h z).re = (inner ℂ z h).re := by rw [hzh, Complex.conj_re]
  have him0 : (((‖z‖ : ℂ)) ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    QuantumNLS.SymplecticBracket.inner_self_eq_ofReal, hzh]
  simp [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, him0, hre]
  ring


/-- `Th κ` is `C^∞`-differentiable everywhere, with derivative `D Th`. -/
lemma differentiable_Th (κ : ℝ) : Differentiable ℝ (Th κ : H → H) := fun z => (hasFDerivAt_Th κ z).differentiableAt

/-- `Th κ` is real analytic. -/
theorem analyticOnNhd_Th (κ : ℝ) : AnalyticOnNhd ℝ (Th κ : H → H) Set.univ := by
  intro z _
  have hn : AnalyticAt ℝ (fun x : H => ‖x‖ ^ 2) z := by
    have h : (fun x : H => ‖x‖ ^ 2) = fun x : H => innerSL ℝ x x := by
      funext x; simp [real_inner_self_eq_norm_sq]
    rw [h]
    have hb : AnalyticAt ℝ (fun p : H × H => innerSL ℝ p.1 p.2) (z, z) :=
      (innerSL ℝ (E := H)).analyticAt_bilinear (z, z)
    have hid : AnalyticAt ℝ (id : H → H) z := analyticAt_id
    have hdiag : AnalyticAt ℝ (fun x : H => (x, x)) z := AnalyticAt.prod hid hid
    exact AnalyticAt.comp (f := fun x : H => (x, x)) hb hdiag
  have hg : AnalyticAt ℝ (fun x : H => (((κ * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I)) z :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_const.mul hn) |>.mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp (((κ * ‖z‖ ^ 2 : ℝ) : ℂ) * Complex.I) :=
    analyticAt_cexp.restrictScalars
  have hph : AnalyticAt ℝ (ph κ) z :=
    AnalyticAt.comp (f := fun x : H => ((κ * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I) hexp hg
  exact hph.smul analyticAt_id

/-- Local DEF-016 for a map with explicit inverse, from a symplectic derivative formula.  Used for
`Th κ` between two `Th`-invariant sets. -/
theorem isStronglySymplecticOn_Th (κ : ℝ) {s t : Set H} (hst : Set.MapsTo (Th κ) s t)
    (hts : Set.MapsTo (Th (-κ)) t s) : IsStronglySymplecticOn s t (Th κ : H → H) := by
  have hr : ∀ w : H, Th κ (Th (-κ) w) = w := fun w => by
    have := Th_Th (-κ) w; rwa [neg_neg] at this
  refine ⟨hst, ⟨Th (-κ), hts, fun x _ => Th_Th κ x, fun y _ => hr y,
    fun y _ => (hasFDerivAt_Th (-κ) y).differentiableAt⟩, fun u _ => differentiable_Th κ u,
    fun u _ => ?_, fun u _ h k => ?_⟩
  · -- the derivative is invertible with inverse `D Th(-κ)` at `Th κ u`
    have hl : (fderiv ℝ (Th (-κ)) (Th κ u)).comp (fderiv ℝ (Th κ) u) = ContinuousLinearMap.id ℝ H := by
      have h1 := fderiv_comp u (differentiable_Th (-κ) (Th κ u)) (differentiable_Th κ u)
      have h2 : ((Th (-κ) : H → H) ∘ (Th κ : H → H)) = id := funext fun x => Th_Th κ x
      rw [h2, fderiv_id] at h1
      exact h1.symm
    have hrr : (fderiv ℝ (Th κ) u).comp (fderiv ℝ (Th (-κ)) (Th κ u)) = ContinuousLinearMap.id ℝ H := by
      have h1 := fderiv_comp (Th κ u) (differentiable_Th κ (Th (-κ) (Th κ u)))
        (differentiable_Th (-κ) (Th κ u))
      have h2 : ((Th κ : H → H) ∘ (Th (-κ) : H → H)) = id := funext fun x => hr x
      rw [h2, fderiv_id] at h1
      have h3 : Th (-κ) (Th κ u) = u := Th_Th κ u
      rw [h3] at h1
      exact h1.symm
    exact ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ (Th κ) u) (fderiv ℝ (Th (-κ)) (Th κ u))
      (fun x => by simpa using congrArg (fun T => T x) hl)
      (fun x => by simpa using congrArg (fun T => T x) hrr), rfl⟩
  · rw [fderiv_Th_apply, fderiv_Th_apply]
    have hdph : ∀ w, dph κ u w = ph κ u * (Complex.I * ((2 * κ * (inner ℂ u w).re : ℝ) : ℂ)) := by
      intro w
      simp only [dph, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul]
      rw [real_inner_eq_re_inner ℂ, RCLike.re_to_complex]
      push_cast; ring
    have e : ∀ (x : H) (a : ℂ), ph κ u • x + (ph κ u * a) • u = ph κ u • (x + a • u) :=
      fun x a => by rw [smul_add, smul_smul]
    rw [hdph h, hdph k, e, e, omega_unit_smul (norm_ph κ u), omega_cross]


end Phase

section Compose

variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A unitary `e : H ≃ₗᵢ[ℂ] E` is canonical between any sets it maps onto each other. -/
theorem isStronglySymplecticOn_isometry (e : H ≃ₗᵢ[ℂ] E) {s : Set H} {t : Set E}
    (hst : Set.MapsTo e s t) (hts : Set.MapsTo e.symm t s) : IsStronglySymplecticOn s t e := by
  let fR : H →L[ℝ] E := e.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  let gR : E →L[ℝ] H := e.symm.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  let eR : H ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse fR gR
    (fun x => e.symm_apply_apply x) (fun y => e.apply_symm_apply y)
  have hd : ∀ z, HasFDerivAt (e : H → E) fR z := fun z => fR.hasFDerivAt
  refine ⟨hst, ⟨e.symm, hts, fun x _ => e.symm_apply_apply x, fun y _ => e.apply_symm_apply y,
    fun y _ => gR.differentiableAt⟩,
    fun z _ => (hd z).differentiableAt, fun z _ => ⟨eR, by rw [(hd z).fderiv]; rfl⟩,
    fun z _ h k => ?_⟩
  rw [(hd z).fderiv]
  show QuantumNLS.SymplecticBracket.omega (e h) (e k) = _
  unfold QuantumNLS.SymplecticBracket.omega
  rw [e.inner_map_map]

/-- Composition of canonical maps between sets is canonical. -/
theorem IsStronglySymplecticOn.comp {s : Set H} {t : Set E} {u : Set F} {Φ : H → E} {Ψ : E → F}
    (hΦ : IsStronglySymplecticOn s t Φ) (hΨ : IsStronglySymplecticOn t u Ψ) :
    IsStronglySymplecticOn s u (Ψ ∘ Φ) := by
  obtain ⟨Φi, hΦim, hΦl, hΦr, hΦid⟩ := hΦ.exists_inverse
  obtain ⟨Ψi, hΨim, hΨl, hΨr, hΨid⟩ := hΨ.exists_inverse
  refine ⟨fun x hx => hΨ.mapsTo (hΦ.mapsTo hx), ⟨Φi ∘ Ψi, fun y hy => hΦim (hΨim hy),
    fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩, fun x hx => ?_, fun x hx => ?_,
    fun x hx h k => ?_⟩
  · simp only [Function.comp]; rw [hΨl _ (hΦ.mapsTo hx), hΦl x hx]
  · simp only [Function.comp]; rw [hΦr _ (hΨim hy), hΨr y hy]
  · exact (hΦid _ (hΨim hy)).comp y (hΨid y hy)
  · exact (hΨ.differentiable _ (hΦ.mapsTo hx)).comp x (hΦ.differentiable x hx)
  · obtain ⟨eΦ, heΦ⟩ := hΦ.deriv_iso x hx
    obtain ⟨eΨ, heΨ⟩ := hΨ.deriv_iso (Φ x) (hΦ.mapsTo hx)
    refine ⟨eΦ.trans eΨ, ?_⟩
    rw [fderiv_comp x (hΨ.differentiable _ (hΦ.mapsTo hx)) (hΦ.differentiable x hx)]
    funext z
    rw [ContinuousLinearMap.comp_apply, ← heΦ, ← heΨ]
    rfl
  · rw [fderiv_comp x (hΨ.differentiable _ (hΦ.mapsTo hx)) (hΦ.differentiable x hx),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      hΨ.symplectic _ (hΦ.mapsTo hx), hΦ.symplectic x hx]


lemma Th_apply_S2 (κ : ℝ) (z : S2 ℤ) (n : ℤ) : Th κ z n = ph κ z * z n := rfl

lemma ph_zero (κ : ℝ) : ph κ (0 : S2 ℤ) = 1 := by simp [ph]

end Compose

section Counter

open MeasureTheory AddCircle

variable (L : ℝ) [Fact (0 < L)]

/-- **Action-dependent canonical phase freedom (the non-uniqueness assertion of LOCAL-022).**

For every `κ > 0` the maps `Φ₁ = 𝓕` and `Φ₂ = Th_κ ∘ 𝓕` (`Th_κ z = e^{iκ‖z‖²} z`, the time-one flow of a
degree-four radial Hamiltonian, i.e. the printed example `F(z) = c‖z‖⁴`) are two distinct real-analytic
canonical (`IsStronglySymplecticOn`) maps of the same full `L²` ball onto the same `ℓ²(ℤ)` ball with
exactly the same squared moduli `q_n(u) = |𝓕(u)_n|²`, both with derivative `𝓕` at zero.  `Φ₁` satisfies the
conjugation intertwining and `Φ₂` does not (`reset_normalization_nonuniqueness'`): exact moduli and the
derivative at zero alone do not remove the phase freedom. -/
theorem reset_normalization_nonuniqueness {r : ℝ} (hr : 0 < r) {κ : ℝ} (hκ : 0 < κ)
    (C : Lp ℂ 2 (volume : Measure (AddCircle L)) → Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hC : ∀ u n, QuantumNLS.Fourier.fourierL2 L (C u) n = conj (QuantumNLS.Fourier.fourierL2 L u n)) :
    ∃ Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ,
      IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
        (Metric.ball (0 : S2 ℤ) r) Φ₁ ∧
      IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
        (Metric.ball (0 : S2 ℤ) r) Φ₂ ∧
      AnalyticOnNhd ℝ Φ₁ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r) ∧
      AnalyticOnNhd ℝ Φ₂ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r) ∧
      Φ₁ 0 = 0 ∧ (∀ u n, ‖Φ₁ u n‖ = ‖Φ₂ u n‖) ∧
      (∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h) ∧
      (∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h) ∧
      (∀ u, Φ₁ (C u) = star (Φ₁ u)) ∧
      ∃ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, Φ₁ u ≠ Φ₂ u := by
  set F : Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ] S2 ℤ := QuantumNLS.Fourier.fourierL2 L with hF
  let fR : Lp ℂ 2 (volume : Measure (AddCircle L)) →L[ℝ] S2 ℤ :=
    F.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  have hFR : ∀ z, HasFDerivAt (F : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ) fR z :=
    fun z => fR.hasFDerivAt
  have hst : Set.MapsTo F (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢; rwa [LinearIsometryEquiv.norm_map]
  have hts : Set.MapsTo F.symm (Metric.ball (0 : S2 ℤ) r)
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r) := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢; rwa [LinearIsometryEquiv.norm_map]
  have hThst : ∀ κ' : ℝ, Set.MapsTo (Th κ' : S2 ℤ → S2 ℤ) (Metric.ball (0 : S2 ℤ) r)
      (Metric.ball (0 : S2 ℤ) r) := fun κ' u hu => by
    rw [mem_ball_zero_iff] at hu ⊢; rwa [norm_Th]
  have hΦ₁ := isStronglySymplecticOn_isometry F hst hts
  have hΦ₂ := hΦ₁.comp (isStronglySymplecticOn_Th κ (hThst κ) (hThst (-κ)))
  have han₁ : AnalyticOnNhd ℝ (F : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ) Set.univ :=
    fun z _ => fR.analyticAt z
  refine ⟨F, Th κ ∘ F, hΦ₁, hΦ₂, fun z _ => han₁ z trivial,
    (analyticOnNhd_Th κ).comp han₁ (fun _ _ => trivial) |>.mono (Set.subset_univ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using F.map_zero
  · intro u n
    simp only [Function.comp, Th_apply_S2, norm_mul, norm_ph, one_mul]
  · intro h
    rw [(hFR 0).fderiv]; rfl
  · intro h
    have hD := ((hasFDerivAt_Th κ (F 0)).comp 0 (hFR 0)).fderiv
    rw [hD]
    simp [F.map_zero, ph_zero]
    rfl
  · intro u
    ext n
    rw [hC]; rfl
  · -- the witness `z₀ = ρ e₀` with `κρ² ∈ (0,1]`
    set t : ℝ := min (r ^ 2 / 2) (1 / κ) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have htr : t < r ^ 2 := lt_of_le_of_lt (min_le_left _ _) (by nlinarith)
    have htκ : κ * t ≤ 1 := by
      calc κ * t ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hκ.le
        _ = 1 := by field_simp
    set ρ : ℝ := Real.sqrt t with hρ
    have hρ2 : ρ ^ 2 = t := Real.sq_sqrt ht0.le
    have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
    set z0 : S2 ℤ := lp.single 2 (0 : ℤ) ((ρ : ℝ) : ℂ) with hz0
    have hz0n : ‖z0‖ = ρ := by
      rw [hz0, lp.norm_single (by norm_num), Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    refine ⟨F.symm z0, ?_, ?_⟩
    · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, hz0n]
      rw [hρ]; exact (Real.sqrt_lt' hr).mpr htr
    · intro heq
      simp only [Function.comp, LinearIsometryEquiv.apply_symm_apply] at heq
      have h0 := congrArg (fun w : S2 ℤ => w 0) heq
      simp only [Th_apply_S2, hz0, lp.single_apply_self] at h0
      have hρc : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have hph : ph κ z0 = 1 := by
        have := h0
        field_simp at this
        exact this.symm
      unfold ph at hph
      rw [hz0n, hρ2] at hph
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hph
      have hm' : κ * t = m * (2 * Real.pi) := by
        have := congrArg Complex.im hm
        simpa using this
      have hmpos : (0 : ℝ) < m := by
        by_contra hneg
        push_neg at hneg
        have : (m : ℝ) * (2 * Real.pi) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
        have : 0 < κ * t := mul_pos hκ ht0
        linarith
      have hmi : (0 : ℤ) < m := by exact_mod_cast hmpos
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      nlinarith [Real.pi_gt_three]


/-- **The conjugation condition is exactly what removes the freedom.**  The map `Φ₂ = Th_κ ∘ 𝓕` of
`reset_normalization_nonuniqueness` does *not* intertwine `C` with componentwise conjugation (otherwise
`reset_normalization_uniqueness` would force `Φ₂ = Φ₁`). -/
theorem reset_normalization_conj_condition_necessary {r : ℝ} (hr : 0 < r) {κ : ℝ} (hκ : 0 < κ)
    (C : Lp ℂ 2 (volume : Measure (AddCircle L)) → Lp ℂ 2 (volume : Measure (AddCircle L)))
    (hC : ∀ u n, QuantumNLS.Fourier.fourierL2 L (C u) n = conj (QuantumNLS.Fourier.fourierL2 L u n)) :
    ∃ Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ,
      IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
        (Metric.ball (0 : S2 ℤ) r) Φ₁ ∧
      IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
        (Metric.ball (0 : S2 ℤ) r) Φ₂ ∧
      (∀ u n, ‖Φ₁ u n‖ = ‖Φ₂ u n‖) ∧
      (∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h) ∧
      ¬ (∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
          Φ₂ (C u) = star (Φ₂ u)) := by
  obtain ⟨Φ₁, Φ₂, h1, h2, a1, a2, h0, hmod, hd1, hd2, hc1, u, hu, hne⟩ :=
    reset_normalization_nonuniqueness L hr hκ C hC
  refine ⟨Φ₁, Φ₂, h1, h2, hmod, hd2, fun hc2 => hne ?_⟩
  exact reset_normalization_uniqueness L hr (fun n u => ‖Φ₁ u n‖ ^ 2) (fun n => by simp [h0]) C hC
    Φ₁ Φ₂ h1 h2 a1 a2 (fun u _ n => rfl) (fun u _ n => by rw [← hmod u n]) hd1 hd2
    (fun u _ => hc1 u) hc2 u hu

end Counter

end QuantumNLS.ResetNormalizationUniqueness

#print axioms QuantumNLS.ResetNormalizationUniqueness.norm_eq_of_norm_apply_eq
#print axioms QuantumNLS.ResetNormalizationUniqueness.hasDerivAt_rot
#print axioms QuantumNLS.ResetNormalizationUniqueness.omega_vecX
#print axioms QuantumNLS.ResetNormalizationUniqueness.KeyHyp.fderiv_vecX
#print axioms QuantumNLS.ResetNormalizationUniqueness.KeyHyp.commute_rot
#print axioms QuantumNLS.ResetNormalizationUniqueness.KeyHyp.fixed_of_nonneg
#print axioms QuantumNLS.ResetNormalizationUniqueness.KeyHyp.fixed_of_finite
#print axioms QuantumNLS.ResetNormalizationUniqueness.KeyHyp.eq_id
#print axioms QuantumNLS.ResetNormalizationUniqueness.isStronglySymplecticOn_univ
#print axioms QuantumNLS.ResetNormalizationUniqueness.comp_inv_props
#print axioms QuantumNLS.ResetNormalizationUniqueness.fourier_reflConj
#print axioms QuantumNLS.ResetNormalizationUniqueness.reset_normalization_uniqueness

#print axioms QuantumNLS.ResetNormalizationUniqueness.Th_Th
#print axioms QuantumNLS.ResetNormalizationUniqueness.hasFDerivAt_Th
#print axioms QuantumNLS.ResetNormalizationUniqueness.omega_unit_smul
#print axioms QuantumNLS.ResetNormalizationUniqueness.omega_cross
#print axioms QuantumNLS.ResetNormalizationUniqueness.analyticOnNhd_Th
#print axioms QuantumNLS.ResetNormalizationUniqueness.isStronglySymplecticOn_Th
#print axioms QuantumNLS.ResetNormalizationUniqueness.isStronglySymplecticOn_isometry
#print axioms QuantumNLS.ResetNormalizationUniqueness.IsStronglySymplecticOn.comp
#print axioms QuantumNLS.ResetNormalizationUniqueness.reset_normalization_nonuniqueness
#print axioms QuantumNLS.ResetNormalizationUniqueness.reset_normalization_conj_condition_necessary
