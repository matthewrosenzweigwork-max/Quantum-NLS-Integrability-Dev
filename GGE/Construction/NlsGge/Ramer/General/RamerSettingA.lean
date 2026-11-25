import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import NlsGge.Sobolev.PhysicalProjection

/-!
# The general Ramer setting with anisotropic `E` (G0, part A: sections 1-3)

See `NlsGge/Ramer/RAMER_GENERALIZATION_PLAN.md` (section "G0 FINAL SPEC").

* §1 `ModeForm`: a positive definite real quadratic/bilinear form on `ℂ ≅ ℝ²`
  (`M(z,w) = a z.re w.re + b (z.re w.im + z.im w.re) + d z.im w.im`,
  `a > 0`, `a d - b² > 0`), with an explicit Cholesky isomorphism `ℂ ≃L[ℝ] ℝ²`.
* §2 `RamerSetting`: rates `q n > 0`, per-mode forms `M n` of `E`, and the single
  summability hypothesis `Σ tr(M n) / (2 q n) < ∞` (HS condition = full support).
* §3 the spaces.  `H = WeightedRealHilbert (2q)` (isotropic Cameron–Martin space) and
  `E = lp(ℤ; ℝ²)` as a type synonym, with the coordinate API
  `coord`, `E_ext`, `E_norm_sq`, `E_inner`, `memE`, `ofSeq`, `coord_ofSeq`, `ofSeq_coord`,
  `memE_of_finite_support`, and the orthogonal coordinate projections `projE`.

Everything later (G1–G5) should use only this coordinate API, never the `lp` internals.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators Topology
open Filter NlsGge.Pilot

namespace NlsGge.Ramer.General

/-! ## §1  Per-mode positive definite forms -/

/-- A positive definite symmetric real bilinear form on `ℂ ≅ ℝ²`, in the coordinates
`(re, im)`: `M(z,w) = a z.re w.re + b (z.re w.im + z.im w.re) + d z.im w.im`. -/
structure ModeForm where
  a : ℝ
  b : ℝ
  d : ℝ
  a_pos : 0 < a
  det_pos : 0 < a * d - b ^ 2

namespace ModeForm

variable (M : ModeForm)

theorem d_pos : 0 < M.d := by
  by_contra h
  rw [not_lt] at h
  nlinarith [M.a_pos, M.det_pos, sq_nonneg M.b, mul_nonneg M.a_pos.le (neg_nonneg.2 h)]

/-- The form `M(z,w)`. -/
def form (z w : ℂ) : ℝ :=
  M.a * z.re * w.re + M.b * (z.re * w.im + z.im * w.re) + M.d * z.im * w.im

/-- The trace `M(1,1) + M(i,i) = a + d`. -/
def tr : ℝ := M.a + M.d

theorem tr_pos : 0 < M.tr := add_pos M.a_pos M.d_pos

theorem form_symm (z w : ℂ) : M.form z w = M.form w z := by
  unfold form; ring

theorem form_add_left (z z' w : ℂ) : M.form (z + z') w = M.form z w + M.form z' w := by
  simp only [form, Complex.add_re, Complex.add_im]; ring

theorem form_smul_left (r : ℝ) (z w : ℂ) : M.form ((r : ℂ) * z) w = r * M.form z w := by
  simp only [form, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

theorem form_smul_right (r : ℝ) (z w : ℂ) : M.form z ((r : ℂ) * w) = r * M.form z w := by
  rw [form_symm, form_smul_left, form_symm]

/-- The form as an `ℝ`-bilinear map. -/
def bilin : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ M.form
    (fun z z' w => M.form_add_left z z' w)
    (fun r z w => by
      have := M.form_smul_left r z w
      simpa [Complex.real_smul] using this)
    (fun z w w' => by
      rw [M.form_symm z (w + w'), M.form_add_left, M.form_symm w z, M.form_symm w' z])
    (fun r z w => by
      have := M.form_smul_left r w z
      rw [M.form_symm z (r • w), M.form_symm z w]
      simpa [Complex.real_smul] using this)

theorem form_bilinear (z w : ℂ) : M.bilin z w = M.form z w := rfl

theorem form_self (z : ℂ) :
    M.form z z = M.a * z.re ^ 2 + 2 * M.b * (z.re * z.im) + M.d * z.im ^ 2 := by
  unfold form; ring

theorem form_pos {z : ℂ} (hz : z ≠ 0) : 0 < M.form z z := by
  have ha := M.a_pos
  have hdet := M.det_pos
  rw [form_self]
  have key : M.a * (M.a * z.re ^ 2 + 2 * M.b * (z.re * z.im) + M.d * z.im ^ 2) =
      (M.a * z.re + M.b * z.im) ^ 2 + (M.a * M.d - M.b ^ 2) * z.im ^ 2 := by ring
  have : 0 < M.a * (M.a * z.re ^ 2 + 2 * M.b * (z.re * z.im) + M.d * z.im ^ 2) := by
    rw [key]
    by_cases him : z.im = 0
    · have hre : z.re ≠ 0 := fun h => hz (Complex.ext h him)
      rw [him]
      have hne : M.a * z.re ≠ 0 := mul_ne_zero ha.ne' hre
      simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have := mul_pos hdet (pow_pos (abs_pos.2 him) 2)
      nlinarith [sq_nonneg (M.a * z.re + M.b * z.im), sq_abs z.im]
  exact pos_of_mul_pos_right this ha.le

theorem form_nonneg (z : ℂ) : 0 ≤ M.form z z := by
  by_cases hz : z = 0
  · subst hz; simp [form]
  · exact (M.form_pos hz).le

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `form z z ≤ tr · ‖z‖²`. -/
theorem form_le_tr (z : ℂ) : M.form z z ≤ M.tr * ‖z‖ ^ 2 := by
  have ha := M.a_pos
  have hd := M.d_pos
  have hdet := M.det_pos
  rw [form_self, norm_sq_eq]
  unfold tr
  set x := z.re
  set y := z.im
  have h1 : 0 ≤ M.d * (M.d * x ^ 2 + M.a * y ^ 2 - 2 * M.b * (x * y)) := by
    nlinarith [sq_nonneg (M.d * x - M.b * y), mul_nonneg hdet.le (sq_nonneg y)]
  have h2 : 0 ≤ M.d * (M.d * x ^ 2 + M.a * y ^ 2 + 2 * M.b * (x * y)) := by
    nlinarith [sq_nonneg (M.d * x + M.b * y), mul_nonneg hdet.le (sq_nonneg y)]
  have h1' := nonneg_of_mul_nonneg_right h1 hd
  nlinarith

/-- `(ad - b²)/tr · ‖z‖² ≤ form z z`. -/
theorem lam_min_le (z : ℂ) :
    (M.a * M.d - M.b ^ 2) / M.tr * ‖z‖ ^ 2 ≤ M.form z z := by
  have htr := M.tr_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ htr, form_self, norm_sq_eq]
  unfold tr
  nlinarith [sq_nonneg (M.a * z.re + M.b * z.im), sq_nonneg (M.d * z.im + M.b * z.re)]

@[simp] theorem form_one_one : M.form 1 1 = M.a := by simp [form]

@[simp] theorem form_I_I : M.form Complex.I Complex.I = M.d := by simp [form]

theorem form_one_one_add_form_I_I : M.form 1 1 + M.form Complex.I Complex.I = M.tr := by
  simp [tr]

/-- The isotropic form `w ‖z‖²`. -/
def iso (w : ℝ) (hw : 0 < w) : ModeForm := ⟨w, 0, w, hw, by nlinarith⟩

theorem iso_form (w : ℝ) (hw : 0 < w) (z : ℂ) : (iso w hw).form z z = w * ‖z‖ ^ 2 := by
  rw [norm_sq_eq]; simp only [iso, form]; ring

theorem iso_tr (w : ℝ) (hw : 0 < w) : (iso w hw).tr = 2 * w := by
  simp [iso, tr]; ring

/-! ### Cholesky factor -/

theorem sqrt_a_pos : 0 < Real.sqrt M.a := Real.sqrt_pos.2 M.a_pos

theorem sqrt_a_sq : Real.sqrt M.a ^ 2 = M.a := Real.sq_sqrt M.a_pos.le

/-- The auxiliary constant `√((ad-b²)/a)`. -/
def cholC : ℝ := Real.sqrt ((M.a * M.d - M.b ^ 2) / M.a)

theorem cholC_pos : 0 < M.cholC :=
  Real.sqrt_pos.2 (div_pos M.det_pos M.a_pos)

theorem cholC_sq : M.cholC ^ 2 = (M.a * M.d - M.b ^ 2) / M.a :=
  Real.sq_sqrt (div_pos M.det_pos M.a_pos).le

/-- Forward Cholesky map `z ↦ (√a re + (b/√a) im, √((ad-b²)/a) im)`. -/
def cholFwd (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.sqrt M.a * z.re + (M.b / Real.sqrt M.a) * z.im, M.cholC * z.im]

/-- Inverse Cholesky map. -/
def cholInv (u : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ⟨(u 0 - (M.b / Real.sqrt M.a) * (u 1 / M.cholC)) / Real.sqrt M.a, u 1 / M.cholC⟩

/-- Explicit Cholesky factor `ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2)`,
`z ↦ (√a re + (b/√a) im, √((ad−b²)/a) im)`. -/
def chol : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := M.cholFwd
      map_add' := fun z w => by
        ext i; fin_cases i <;> simp [cholFwd] <;> ring
      map_smul' := fun r z => by
        ext i; fin_cases i <;> simp [cholFwd] <;> ring
      invFun := M.cholInv
      left_inv := fun z => by
        have h1 := M.sqrt_a_pos.ne'
        have h2 := M.cholC_pos.ne'
        apply Complex.ext <;> simp [cholFwd, cholInv] <;> field_simp <;> ring
      right_inv := fun u => by
        have h1 := M.sqrt_a_pos.ne'
        have h2 := M.cholC_pos.ne'
        ext i; fin_cases i <;> simp [cholFwd, cholInv] <;> field_simp <;> ring }

theorem chol_apply_zero (z : ℂ) :
    M.chol z 0 = Real.sqrt M.a * z.re + (M.b / Real.sqrt M.a) * z.im := rfl

theorem chol_apply_one (z : ℂ) : M.chol z 1 = M.cholC * z.im := rfl

theorem chol_inner (z w : ℂ) :
    inner ℝ (M.chol z) (M.chol w) = M.form z w := by
  have h1 := M.sqrt_a_pos.ne'
  have h2 := M.sqrt_a_sq
  have h3 := M.cholC_sq
  have h4 := M.a_pos.ne'
  simp only [PiLp.inner_apply, Fin.sum_univ_two, chol_apply_zero, chol_apply_one,
    RCLike.inner_apply, conj_trivial, form]
  field_simp
  simp only [h2, h3]
  field_simp
  ring

theorem chol_norm_sq (z : ℂ) : ‖M.chol z‖ ^ 2 = M.form z z := by
  rw [← real_inner_self_eq_norm_sq, chol_inner]

end ModeForm


/-! ## §2  The setting -/

/-- The general Ramer setting.

* `q n > 0` are the rates: each Fourier coordinate of the Gaussian law is a complex
  Gaussian whose real components have variance `1/(2 q n)`; the Cameron–Martin space is
  `H = WeightedRealHilbert (2q)`, `‖h‖²_H = Σ 2 q_n |h_n|²`.
* `M n` is the per-mode positive definite form of `E`:
  `‖x‖²_E = Σ_n (M n)(x_n, x_n)`.
* `hs`: `Σ tr(M n) / (2 q n) < ∞`.  This single hypothesis is both the Hilbert–Schmidt
  condition on `H ↪ E` (`‖incl‖²_HS = Σ tr(M n)/(2 q n)`) and the full support
  `γ(E) = 1` of the Gaussian (`E_γ M_n(z_n,z_n) = tr(M_n)/(2 q_n)`). -/
structure RamerSetting where
  q : ℤ → ℝ
  q_pos : ∀ n, 0 < q n
  M : ℤ → ModeForm
  hs : Summable (fun n => (M n).tr / (2 * q n))

namespace RamerSetting

variable (S : RamerSetting)

/-- The weights `2 q_n` of the Cameron–Martin space. -/
abbrev cmWeight : ℤ → ℝ := fun n => 2 * S.q n

theorem cmWeight_pos (n : ℤ) : 0 < S.cmWeight n := by
  have := S.q_pos n
  change 0 < 2 * S.q n
  positivity

instance instFactCmWeight : Fact (∀ n : ℤ, 0 < S.cmWeight n) := ⟨S.cmWeight_pos⟩

/-- The summand `tr(M n) / (2 q n)` of the Hilbert–Schmidt norm. -/
def ratio (n : ℤ) : ℝ := (S.M n).tr / (2 * S.q n)

theorem ratio_pos (n : ℤ) : 0 < S.ratio n :=
  div_pos (S.M n).tr_pos (S.cmWeight_pos n)

theorem summable_ratio : Summable S.ratio := S.hs

/-! ## §3  The spaces -/

/-- The (isotropic) Cameron–Martin space `H`, `‖h‖² = Σ 2 q_n |h_n|²`. -/
abbrev H : Type := WeightedRealHilbert S.cmWeight

/-- The Fourier coordinates of an element of `H`. -/
def hcoord (h : S.H) (n : ℤ) : ℂ := (show WeightedHilbert S.cmWeight from h) n

/-- The carrier of `E`: `lp(ℤ; ℝ²)`.  Only `RamerSetting.E` is to be used downstream, through
the coordinate API below; the `lp` structure is an implementation detail. -/
def E (_S : RamerSetting) : Type := lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2

instance instNormedAddCommGroupE : NormedAddCommGroup S.E :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2))

instance instNormedSpaceE : NormedSpace ℝ S.E :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2))

instance instInnerProductSpaceE : InnerProductSpace ℝ S.E :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2))

instance instCompleteSpaceE : CompleteSpace S.E :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2))

/-- The underlying `lp` element (implementation detail). -/
def toLp (x : S.E) : lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 := x

/-- Build an element of `E` from an `lp` element (implementation detail). -/
def ofLp (x : lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2) : S.E := x

/-- The Cholesky coordinates `(S.M n).chol (x_n) ∈ ℝ²` of `x ∈ E` (implementation detail). -/
def raw (x : S.E) (n : ℤ) : EuclideanSpace ℝ (Fin 2) := (S.toLp x : ℤ → _) n

theorem raw_ofLp (y : lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2) (n : ℤ) :
    S.raw (S.ofLp y) n = (y : ℤ → _) n := rfl

theorem raw_add (x y : S.E) (n : ℤ) : S.raw (x + y) n = S.raw x n + S.raw y n := rfl
theorem raw_smul (r : ℝ) (x : S.E) (n : ℤ) : S.raw (r • x) n = r • S.raw x n := rfl
theorem raw_zero (n : ℤ) : S.raw (0 : S.E) n = 0 := rfl

theorem norm_raw_le (x : S.E) (n : ℤ) : ‖S.raw x n‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by norm_num) (S.toLp x) n

/-- The `n`-th coordinate `x_n ∈ ℂ` of `x ∈ E`: the Cholesky inverse of the `n`-th `ℝ²`-component.
So `‖x‖²_E = Σ_n (M n)(x_n, x_n)` (`E_norm_sq`). -/
def coord (n : ℤ) : S.E →L[ℝ] ℂ :=
  ((S.M n).chol.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ).comp
    (lp.evalCLM ℝ (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 n)

theorem coord_def (x : S.E) (n : ℤ) : S.coord n x = (S.M n).chol.symm (S.raw x n) := rfl

theorem chol_coord (x : S.E) (n : ℤ) : (S.M n).chol (S.coord n x) = S.raw x n := by
  rw [coord_def]; exact (S.M n).chol.apply_symm_apply _

theorem coord_add (x y : S.E) (n : ℤ) : S.coord n (x + y) = S.coord n x + S.coord n y :=
  map_add _ x y

theorem coord_smul (r : ℝ) (x : S.E) (n : ℤ) : S.coord n (r • x) = (r : ℂ) * S.coord n x := by
  rw [map_smul, Complex.real_smul]

theorem coord_zero (n : ℤ) : S.coord n (0 : S.E) = 0 := map_zero _

/-- Elements of `E` are determined by their coordinates. -/
theorem E_ext {x y : S.E} (h : ∀ n, S.coord n x = S.coord n y) : x = y := by
  have : S.toLp x = S.toLp y := by
    apply lp.ext
    funext n
    have := congrArg (S.M n).chol (h n)
    rwa [S.chol_coord, S.chol_coord] at this
  exact this

theorem memℓp_two_iff {f : ℤ → EuclideanSpace ℝ (Fin 2)} :
    Memℓp f 2 ↔ Summable (fun n => ‖f n‖ ^ 2) := by
  constructor
  · intro hf
    have := hf.summable (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
  · intro hf
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hf

theorem hasSum_raw_norm_sq (x : S.E) : HasSum (fun n => ‖S.raw x n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (S.toLp x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h

theorem form_coord_self (x : S.E) (n : ℤ) :
    (S.M n).form (S.coord n x) (S.coord n x) = ‖S.raw x n‖ ^ 2 := by
  rw [← (S.M n).chol_norm_sq, S.chol_coord]

/-- `‖x‖²_E = Σ_n M_n(x_n, x_n)`, as a `HasSum`. -/
theorem E_norm_sq_hasSum (x : S.E) :
    HasSum (fun n => (S.M n).form (S.coord n x) (S.coord n x)) (‖x‖ ^ 2) := by
  simpa only [form_coord_self] using S.hasSum_raw_norm_sq x

/-- `‖x‖²_E = Σ_n M_n(x_n, x_n)`. -/
theorem E_norm_sq (x : S.E) :
    ‖x‖ ^ 2 = ∑' n, (S.M n).form (S.coord n x) (S.coord n x) :=
  (S.E_norm_sq_hasSum x).tsum_eq.symm

theorem summable_form_coord (x : S.E) :
    Summable (fun n => (S.M n).form (S.coord n x) (S.coord n x)) :=
  (S.E_norm_sq_hasSum x).summable

theorem form_coord_le_norm_sq (x : S.E) (n : ℤ) :
    (S.M n).form (S.coord n x) (S.coord n x) ≤ ‖x‖ ^ 2 := by
  rw [form_coord_self]
  exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_raw_le x n) 2

theorem form_coord_inner (x y : S.E) (n : ℤ) :
    (S.M n).form (S.coord n x) (S.coord n y) = inner ℝ (S.raw x n) (S.raw y n) := by
  rw [← (S.M n).chol_inner, S.chol_coord, S.chol_coord]

/-- `⟪x, y⟫_E = Σ_n M_n(x_n, y_n)`, as a `HasSum`. -/
theorem E_inner_hasSum (x y : S.E) :
    HasSum (fun n => (S.M n).form (S.coord n x) (S.coord n y)) (inner ℝ x y) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) (G := fun _ : ℤ => EuclideanSpace ℝ (Fin 2))
    (S.toLp x) (S.toLp y)
  have e : (fun n => (S.M n).form (S.coord n x) (S.coord n y)) =
      fun n => inner ℝ (S.raw x n) (S.raw y n) := funext (S.form_coord_inner x y)
  rw [e]
  exact h

/-- `⟪x, y⟫_E = Σ_n M_n(x_n, y_n)`. -/
theorem E_inner (x y : S.E) :
    inner ℝ x y = ∑' n, (S.M n).form (S.coord n x) (S.coord n y) :=
  (S.E_inner_hasSum x y).tsum_eq.symm

/-- Membership of a complex sequence in `E`: `Σ_n M_n(z_n, z_n) < ∞`. -/
def memE (z : ℤ → ℂ) : Prop := Summable (fun n => (S.M n).form (z n) (z n))

theorem memE_coord (x : S.E) : S.memE (fun n => S.coord n x) := S.summable_form_coord x

/-- The element of `E` with the given coordinates. -/
def ofSeq (z : ℤ → ℂ) (hz : S.memE z) : S.E :=
  S.ofLp ⟨fun n => (S.M n).chol (z n), (memℓp_two_iff (f := fun n => (S.M n).chol (z n))).2 (by
    simp only [ModeForm.chol_norm_sq]; exact hz)⟩

theorem raw_ofSeq (z : ℤ → ℂ) (hz : S.memE z) (n : ℤ) :
    S.raw (S.ofSeq z hz) n = (S.M n).chol (z n) := rfl

@[simp] theorem coord_ofSeq (z : ℤ → ℂ) (hz : S.memE z) (n : ℤ) :
    S.coord n (S.ofSeq z hz) = z n := by
  rw [coord_def, raw_ofSeq]; exact (S.M n).chol.symm_apply_apply _

@[simp] theorem ofSeq_coord (x : S.E) (hz : S.memE (fun n => S.coord n x)) :
    S.ofSeq (fun n => S.coord n x) hz = x :=
  S.E_ext (fun n => S.coord_ofSeq _ _ n)

theorem memE_of_finite_support {z : ℤ → ℂ} (hz : {n | z n ≠ 0}.Finite) : S.memE z := by
  apply summable_of_hasFiniteSupport
  refine hz.subset ?_
  intro n hn
  by_contra h
  apply hn
  have h0 : z n = 0 := by simpa using h
  show (S.M n).form (z n) (z n) = 0
  rw [h0]
  simp [ModeForm.form]

theorem memE_zero : S.memE (fun _ => 0) := S.memE_of_finite_support (by simp)


/-! ### Coordinate projections on `E` -/

theorem form_zero_left (n : ℤ) (w : ℂ) : (S.M n).form 0 w = 0 := by simp [ModeForm.form]

theorem form_zero_right (n : ℤ) (z : ℂ) : (S.M n).form z 0 = 0 := by simp [ModeForm.form]

theorem memE_truncate (m : Finset ℤ) (x : S.E) :
    S.memE (fun n => if n ∈ m then S.coord n x else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (S.summable_form_coord x)
  · exact (S.M n).form_nonneg _
  · by_cases hn : n ∈ m
    · simp only [if_pos hn, le_refl]
    · simp only [if_neg hn, S.form_zero_left]
      exact (S.M n).form_nonneg _

/-- Keeping exactly the coordinates in a finset `m` (not yet known to be continuous). -/
def truncLin (m : Finset ℤ) : S.E →ₗ[ℝ] S.E where
  toFun x := S.ofSeq (fun n => if n ∈ m then S.coord n x else 0) (S.memE_truncate m x)
  map_add' x y := by
    apply S.E_ext; intro n
    simp only [coord_ofSeq, S.coord_add]
    split_ifs <;> simp
  map_smul' r x := by
    apply S.E_ext; intro n
    simp only [coord_ofSeq, S.coord_smul, RingHom.id_apply]
    split_ifs <;> simp

theorem coord_truncLin (m : Finset ℤ) (x : S.E) (n : ℤ) :
    S.coord n (S.truncLin m x) = if n ∈ m then S.coord n x else 0 := by
  simp [truncLin]

theorem truncLin_norm_le (m : Finset ℤ) (x : S.E) : ‖S.truncLin m x‖ ≤ ‖x‖ := by
  have hsq : ‖S.truncLin m x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [S.E_norm_sq, S.E_norm_sq x]
    refine Summable.tsum_le_tsum (fun n => ?_) (S.summable_form_coord _)
      (S.summable_form_coord _)
    rw [coord_truncLin]
    by_cases hn : n ∈ m
    · simp only [if_pos hn, le_refl]
    · simp only [if_neg hn, S.form_zero_left]
      exact (S.M n).form_nonneg _
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The orthogonal coordinate projection `P_m` of `E` onto the modes in the finset `m`. -/
def projEFinset (m : Finset ℤ) : S.E →L[ℝ] S.E :=
  (S.truncLin m).mkContinuous 1 (fun x => by
    rw [one_mul]; exact S.truncLin_norm_le m x)

/-- The orthogonal coordinate projection `P_N` of `E` onto the modes `-N ≤ n ≤ N`. -/
def projE (N : ℕ) : S.E →L[ℝ] S.E := S.projEFinset (symmetricModes N)

theorem coord_projEFinset (m : Finset ℤ) (x : S.E) (n : ℤ) :
    S.coord n (S.projEFinset m x) = if n ∈ m then S.coord n x else 0 :=
  S.coord_truncLin m x n

/-- `coord n (P_N x) = coord n x` for `|n| ≤ N` and `0` otherwise. -/
theorem coord_projE (N : ℕ) (x : S.E) (n : ℤ) :
    S.coord n (S.projE N x) = if n ∈ symmetricModes N then S.coord n x else 0 :=
  S.coord_projEFinset _ x n

theorem projEFinset_norm_le (m : Finset ℤ) (x : S.E) : ‖S.projEFinset m x‖ ≤ ‖x‖ :=
  S.truncLin_norm_le m x

theorem projE_norm_le (N : ℕ) (x : S.E) : ‖S.projE N x‖ ≤ ‖x‖ :=
  S.truncLin_norm_le _ x

theorem projEFinset_idem (m : Finset ℤ) (x : S.E) :
    S.projEFinset m (S.projEFinset m x) = S.projEFinset m x := by
  apply S.E_ext; intro n
  simp only [coord_projEFinset]
  split_ifs <;> rfl

/-- `P_N` is idempotent. -/
theorem projE_idem (N : ℕ) (x : S.E) : S.projE N (S.projE N x) = S.projE N x :=
  S.projEFinset_idem _ x

theorem projEFinset_selfAdjoint (m : Finset ℤ) (x y : S.E) :
    inner ℝ (S.projEFinset m x) y = inner ℝ x (S.projEFinset m y) := by
  rw [S.E_inner, S.E_inner]
  refine tsum_congr (fun n => ?_)
  simp only [coord_projEFinset]
  split_ifs
  · rfl
  · simp [S.form_zero_left, S.form_zero_right]

/-- `P_N` is self-adjoint; together with `projE_idem`, an orthogonal projection. -/
theorem projE_selfAdjoint (N : ℕ) (x y : S.E) :
    inner ℝ (S.projE N x) y = inner ℝ x (S.projE N y) :=
  S.projEFinset_selfAdjoint _ x y

/-- Orthogonality of the residual: `⟪P_N y, x - P_N x⟫ = 0`. -/
theorem projE_range_residual (N : ℕ) (x y : S.E) :
    inner ℝ (S.projE N y) (x - S.projE N x) = 0 := by
  rw [inner_sub_right, ← S.projE_selfAdjoint, S.projE_idem, sub_self]

/-- `P_N x → x` in `E`. -/
theorem projE_tendsto (x : S.E) :
    Tendsto (fun N : ℕ => S.projE N x) atTop (𝓝 x) := by
  classical
  have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (S.toLp x)
  have ht := hs.comp symmetricModes_tendsto
  have heq : ∀ N : ℕ, S.projE N x =
      S.ofLp (∑ n ∈ symmetricModes N, lp.single 2 n ((S.toLp x : ℤ → _) n)) := by
    intro N
    apply S.E_ext; intro n
    apply (S.M n).chol.injective
    rw [S.chol_coord, S.chol_coord, raw_ofLp, lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.single_apply, Finset.sum_pi_single]
    rw [← S.chol_coord (S.projE N x) n, coord_projE]
    split_ifs with hn
    · exact S.chol_coord x n
    · exact map_zero _
  simp_rw [heq]
  exact ht

/-! ### Separability -/

/-- The countable family of `E`: the `ℝ²`-coordinate unit vectors at each mode. -/
def unitVec (p : ℤ × Fin 2) : S.E :=
  S.ofLp (lp.single 2 p.1 (EuclideanSpace.single p.2 (1 : ℝ)))

theorem single_mem_span (n : ℤ) (v : EuclideanSpace ℝ (Fin 2)) :
    S.ofLp (lp.single 2 n v) ∈ Submodule.span ℝ (Set.range S.unitVec) := by
  classical
  have hv : v = ∑ j : Fin 2, v j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    fin_cases i <;> simp
  have : S.ofLp (lp.single 2 n v) = ∑ j : Fin 2, v j • S.unitVec (n, j) := by
    conv_lhs => rw [hv]
    simp only [unitVec, ofLp]
    induction (Finset.univ : Finset (Fin 2)) using Finset.induction_on with
    | empty => simp; rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lp.single_add, ih, lp.single_smul]
      rfl
  rw [this]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨(n, j), rfl⟩))

instance instSeparableSpaceE : TopologicalSpace.SeparableSpace S.E := by
  classical
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range S.unitVec) : Set S.E) :=
    ((Set.countable_range S.unitVec).isSeparable).span
  have hclosure : closure (Submodule.span ℝ (Set.range S.unitVec) : Set S.E) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hs := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (S.toLp x)
    have hmem : ∀ F : Finset ℤ, ∑ n ∈ F, S.ofLp (lp.single 2 n ((S.toLp x : ℤ → _) n)) ∈
        Submodule.span ℝ (Set.range S.unitVec) :=
      fun F => Submodule.sum_mem _ (fun n _ => S.single_mem_span n _)
    refine mem_closure_of_tendsto (f := fun F : Finset ℤ =>
      ∑ n ∈ F, S.ofLp (lp.single 2 n ((S.toLp x : ℤ → _) n))) (b := atTop) hs ?_
    exact Eventually.of_forall hmem
  apply TopologicalSpace.isSeparable_univ_iff.mp
  rw [← hclosure]
  exact hspan.closure

instance instSecondCountableTopologyE : SecondCountableTopology S.E :=
  UniformSpace.secondCountable_of_separable S.E

example : PolishSpace S.E := inferInstance

end RamerSetting

end NlsGge.Ramer.General
