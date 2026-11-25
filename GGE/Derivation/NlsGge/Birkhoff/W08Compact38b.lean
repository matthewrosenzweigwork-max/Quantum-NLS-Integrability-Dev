import NlsGge.Birkhoff.W08Compact38

/-! # W08 (Birkhoff wave B2), file 2: the finite map `T_N = P_N T|_{P_N h⁰}` -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open NlsGge.Analysis.RegularizedDeterminant
open Filter Topology Metric

theorem carrierIncl38_injective {r s : ℝ} (h : r ≤ s) : Function.Injective (carrierIncl38 h) := by
  intro x y hxy
  apply carrierExt38
  have := congrArg (carrierCoe38 r) hxy
  rwa [carrierCoe38_incl38, carrierCoe38_incl38] at this

theorem i10_38_injective : Function.Injective i10_38 := carrierIncl38_injective _
theorem i20_38_injective : Function.Injective i20_38 := carrierIncl38_injective _
theorem i21_38_injective : Function.Injective i21_38 := carrierIncl38_injective _

/-- `{x ∈ P_N h⁰ : x ∈ h², ‖x‖_{h²} ≤ R}` (v2: the set on which `T_N` is injective). -/
def ballV38 (N : ℕ) (R : ℝ) : Set (cp38 N).V :=
  {x | ∃ y : H2_38, ‖y‖ ≤ R ∧ i20_38 y = (x : H0_38)}

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- `T_N = P_N T |_{P_N h⁰} : P_N h⁰ → P_N h⁰`. -/
def TN (N : ℕ) : (cp38 N).V → (cp38 N).V :=
  fun x => ⟨projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (x : H0_38)), (cp38 N).P_mem_V _⟩

theorem TN_coe (N : ℕ) (x : (cp38 N).V) :
    ((B.TN N x : (cp38 N).V) : H0_38) = projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (x : H0_38)) := rfl

/-- The (continuous linear) candidate derivative `P_N DT(x) |_{P_N h⁰}`. -/
def DTN (N : ℕ) (x : (cp38 N).V) : (cp38 N).V →L[ℝ] (cp38 N).V :=
  ((projC38 ((0 : ℕ) : ℝ) N).comp ((B.Lop (x : H0_38)).comp (cp38 N).V.subtypeL)).codRestrict
    (cp38 N).V (fun _ => (cp38 N).P_mem_V _)

theorem hasFDerivAt_TN (N : ℕ) (x : (cp38 N).V) : HasFDerivAt (B.TN N) (B.DTN N x) x := by
  have h1 : HasFDerivAt (fun z : (cp38 N).V => B.TC 0 (z : H0_38)) ((B.Lop (x : H0_38)).comp (cp38 N).V.subtypeL) x :=
    (B.differentiableAt_TC0 (x : H0_38)).hasFDerivAt.comp x (cp38 N).V.subtypeL.hasFDerivAt
  have h2 : HasFDerivAt (fun z : (cp38 N).V => projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (z : H0_38)))
      ((projC38 ((0 : ℕ) : ℝ) N).comp ((B.Lop (x : H0_38)).comp (cp38 N).V.subtypeL)) x :=
    (projC38 ((0 : ℕ) : ℝ) N).hasFDerivAt.comp x h1
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at h2 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h2 ⊢
  refine h2.congr_left (fun h => ?_)
  rfl

theorem fderiv_TN (N : ℕ) (x : (cp38 N).V) : fderiv ℝ (B.TN N) x = B.DTN N x :=
  (B.hasFDerivAt_TN N x).fderiv

/-- The determinant of the derivative of `T_N` at `x ∈ P_N h⁰` (a real endomorphism of the
finite-dimensional space `P_N h⁰`). -/
def detTN (N : ℕ) (x : (cp38 N).V) : ℝ :=
  LinearMap.det (((fderiv ℝ (B.TN N) x : (cp38 N).V →L[ℝ] (cp38 N).V)) : (cp38 N).V →ₗ[ℝ] (cp38 N).V)

/-- The derivative of `T_N` at `x = ι₁₀ x₁` (`P_N x₁ = x₁`) is the compression `L_N` of F01 at
the base point `x_N = P_N x₁ = x₁`. -/
theorem DTN_eq_LNmap (N : ℕ) (x1 : H1_38) (hx1 : projC38 ((1 : ℕ) : ℝ) N x1 = x1)
    (x : (cp38 N).V) (hx : (x : H0_38) = i10_38 x1) :
    ((B.DTN N x : (cp38 N).V →L[ℝ] (cp38 N).V) : (cp38 N).V →ₗ[ℝ] (cp38 N).V) = B.LNmap x1 N := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have hu : projC38 ((0 : ℕ) : ℝ) N (u : H0_38) = (u : H0_38) := ((cp38 N).mem_V_iff _).1 u.2
  have e1 : B.LxN x1 N = B.Lop (x : H0_38) := by
    unfold LxN baseN38
    rw [hx1, hx]
  show projC38 ((0 : ℕ) : ℝ) N (B.Lop (x : H0_38) (u : H0_38)) =
    (cp38 N).Lt (B.LxN x1 N) (u : H0_38)
  rw [CplxProj38.Lt_apply, e1]
  show _ = projC38 ((0 : ℕ) : ℝ) N (B.Lop (x : H0_38) (projC38 ((0 : ℕ) : ℝ) N (u : H0_38)))
  rw [hu]

theorem detTN_eq_detLN (N : ℕ) (x1 : H1_38) (hx1 : projC38 ((1 : ℕ) : ℝ) N x1 = x1)
    (x : (cp38 N).V) (hx : (x : H0_38) = i10_38 x1) : B.detTN N x = B.detLN x1 N := by
  unfold detTN detLN
  rw [B.fderiv_TN, B.DTN_eq_LNmap N x1 hx1 x hx]

/-- Points of `ballV38` come from points of the `h²` ball lying in `P_N h¹`. -/
theorem exists_of_mem_ballV38 {N : ℕ} {R : ℝ} {x : (cp38 N).V} (hx : x ∈ ballV38 N R) :
    ∃ x1 : H1_38, x1 ∈ ballH1 R ∧ projC38 ((1 : ℕ) : ℝ) N x1 = x1 ∧ (x : H0_38) = i10_38 x1 := by
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨i21_38 y, (mem_ballH1_iff R _).2 ⟨y, hy, rfl⟩, ?_, ?_⟩
  · apply i10_38_injective
    have hu : projC38 ((0 : ℕ) : ℝ) N (x : H0_38) = (x : H0_38) := ((cp38 N).mem_V_iff _).1 x.2
    rw [← hyx] at hu
    have : i10_38 (projC38 ((1 : ℕ) : ℝ) N (i21_38 y)) =
        projC38 ((0 : ℕ) : ℝ) N (i10_38 (i21_38 y)) := projC38_incl _ N _
    rw [this, i10_38_i21_38]
    exact hu
  · rw [← hyx, i10_38_i21_38]

/-- **W08 (injectivity).** For every `R < ∞` and all sufficiently large `N`, `T_N = P_N T|_{P_N h⁰}`
is injective on `{x ∈ P_N h⁰ : ‖x‖_{h²} ≤ R}`. -/
theorem injOn_TN_ballV38 (O : OneSmoothingInput38 B) (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Set.InjOn (B.TN N) (ballV38 N R) := by
  obtain ⟨N₀, hN₀⟩ := B.injOn_projTC1_ballH1 O R
  refine ⟨N₀, fun N hN x hx x' hx' hxx' => ?_⟩
  obtain ⟨x1, hb1, hP1, hxe⟩ := exists_of_mem_ballV38 hx
  obtain ⟨x1', hb1', hP1', hxe'⟩ := exists_of_mem_ballV38 hx'
  have h0 : projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (x : H0_38)) = projC38 ((0 : ℕ) : ℝ) N (B.TC 0 (x' : H0_38)) :=
    congrArg (fun z : (cp38 N).V => (z : H0_38)) hxx'
  rw [hxe, hxe', B.TC0_i10, B.TC0_i10] at h0
  have e : ∀ z : H1_38, projC38 ((0 : ℕ) : ℝ) N (i10_38 z) = i10_38 (projC38 ((1 : ℕ) : ℝ) N z) :=
    fun z => (projC38_incl _ N z).symm
  rw [e, e] at h0
  have h1 := hN₀ N hN x1 hb1 x1' hb1' hP1 hP1' (i10_38_injective h0)
  apply Subtype.ext
  rw [hxe, hxe', h1]

/-! ## Determinant control -/

/-- **W08.05 (squared form).** `|det DT_N|² → 1` uniformly on `{x ∈ P_N h⁰ : ‖x‖_{h²} ≤ R}`:
for every `ε > 0` and all large `N`, every `x` of that set has `| |det DT_N(x)|² − 1 | < ε`.
(F01.07 applied to the compact closure of the `h²` ball in `h¹`.) -/
theorem eventually_abs_sq_detTN_sub_one_lt (O : OneSmoothingInput38 B) (R : ℝ) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, |(|B.detTN N x|) ^ 2 - 1| < ε := by
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.1
    (B.tendstoUniformlyOn_sq_detLN O (isCompact_closure_ballH1 R))) ε hε
  filter_upwards [h] with N hN x hx
  obtain ⟨x1, hb1, hP1, hxe⟩ := exists_of_mem_ballV38 hx
  have := hN x1 (subset_closure hb1)
  rw [B.detTN_eq_detLN N x1 hP1 x hxe]
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

/-- **W08.05 (absolute value).** `|det DT_N| → 1` uniformly on the same set (v2: "Its derivative
determinant tends uniformly to one in absolute value on that ball"). -/
theorem eventually_abs_detTN_sub_one_lt (O : OneSmoothingInput38 B) (R : ℝ) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, abs (|B.detTN N x| - 1) < ε := by
  intro ε hε
  filter_upwards [B.eventually_abs_sq_detTN_sub_one_lt O R ε hε] with N hN x hx
  have h := hN x hx
  have ha : 0 ≤ |B.detTN N x| := abs_nonneg _
  have e : |B.detTN N x| ^ 2 - 1 = (|B.detTN N x| - 1) * (|B.detTN N x| + 1) := by ring
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < |B.detTN N x| + 1)] at h
  have : abs (|B.detTN N x| - 1) * 1 ≤ abs (|B.detTN N x| - 1) * (|B.detTN N x| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  linarith

/-- **W08.05 (reciprocal).** For all sufficiently large `N`, `det DT_N(x) ≠ 0` and
`|det DT_N(x)|⁻¹ ≤ 2` for every `x ∈ P_N h⁰` with `‖x‖_{h²} ≤ R`. -/
theorem eventually_inv_abs_detTN_le_two (O : OneSmoothingInput38 B) (R : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, B.detTN N x ≠ 0 ∧ |B.detTN N x|⁻¹ ≤ 2 := by
  filter_upwards [B.eventually_abs_detTN_sub_one_lt O R (1 / 2) (by norm_num)] with N hN x hx
  have h := hN x hx
  have h1 : 1 / 2 < |B.detTN N x| := by
    have := (abs_lt.1 h).1
    linarith
  refine ⟨fun h0 => by rw [h0, abs_zero] at h1; linarith, ?_⟩
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-! ## Hilbert-Schmidt tail control on the ball (last paragraph of the v2 proof) -/

/-- `sup_{‖x‖_{h²} ≤ R} ‖(1 − P_N) B(x) P_N‖_{HS(h⁰)} → 0`: for every `ε > 0` and all large `N`,
every `x` in the `h²` ball has `‖(1 − P_N) B(x) P_N‖_HS < ε`. (Continuity of `B` in `HS(h⁰)`, F01.03,
and compactness of the ball in `h¹`.) -/
theorem eventually_norm_tail_BHS_lt (O : OneSmoothingInput38 B) (R : ℝ) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballH1 R,
      ‖HilbertSchmidt.precompose
          (HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) (B.BHS O x))
          (projC38 ((0 : ℕ) : ℝ) N)‖ < ε := by
  intro ε hε
  have hK : IsCompact (B.BHS O '' closure (ballH1 R)) :=
    (isCompact_closure_ballH1 R).image (B.continuous_BHS O)
  filter_upwards [eventually_norm_postcompose_lt38 hK ε hε] with N hN x hx
  have h1 := hN (B.BHS O x) ⟨x, subset_closure hx, rfl⟩
  refine lt_of_le_of_lt ((HilbertSchmidt.norm_precompose_le _ _).trans ?_) h1
  calc _ ≤ ‖HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) (B.BHS O x)‖ * 1 :=
        mul_le_mul_of_nonneg_left (opNorm_projC38_le _ N) (norm_nonneg _)
    _ = _ := mul_one _

/-- **W08 (`D:lem:localinject`), conditional on `B`, `O`.** For every `R < ∞`:
(1) for all sufficiently large `N`, `T_N = P_N T|_{P_N h⁰}` is injective on
`{x ∈ P_N h⁰ : ‖x‖_{h²} ≤ R}`; (2) `|det DT_N| → 1` uniformly on that set;
(3) eventually the determinant is nonzero with reciprocal at most `2` on that set. -/
theorem W08_localInject_determinant (O : OneSmoothingInput38 B) (R : ℝ) :
    (∃ N₀ : ℕ, ∀ N ≥ N₀, Set.InjOn (B.TN N) (ballV38 N R)) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, abs (|B.detTN N x| - 1) < ε) ∧
    (∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, B.detTN N x ≠ 0 ∧ |B.detTN N x|⁻¹ ≤ 2) :=
  ⟨B.injOn_TN_ballV38 O R, B.eventually_abs_detTN_sub_one_lt O R,
    B.eventually_inv_abs_detTN_le_two O R⟩

end BirkhoffInput38

end NlsGge.Birkhoff
