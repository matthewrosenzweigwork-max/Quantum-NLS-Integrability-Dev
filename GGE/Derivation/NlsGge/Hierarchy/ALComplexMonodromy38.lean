import NlsGge.Hierarchy.ALExteriorBranch38
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Batch 38, L02b-1: complexified AL transfer matrix, monodromy trace polynomial and its joint
analyticity (paper/v2.tex D:thm:ALfinite, proof l.1969).

`alScalar38 a b = (1 - a b)^{-1/2}` (principal cpow), `alTransferTilde38 a b ζ = ζ · A(1/ζ; a, b)`
written polynomially: `s(a,b) • [[1, aζ],[bζ, ζ²]]`.  `alComplexT38 a b ζ = tr` of the ordered
product (`ζ^L tr M(1/ζ; a, b)`).  On the real slice `b = conj a` it equals `alExtT38 α ζ`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix
open Filter Topology Complex

/-- `(1 - a b)^{-1/2}` with the principal branch. -/
def alScalar38 (a b : ℂ) : ℂ := (1 - a * b) ^ (-(1 / 2 : ℂ))

/-- `ζ · A(1/ζ; a, b)`, with `A(z;a,b) = (1-ab)^{-1/2} [[z, a],[b, z⁻¹]]`. -/
def alTransferTilde38 (a b ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  alScalar38 a b • !![1, a * ζ; b * ζ, ζ ^ 2]

/-- Partial products `P_0 = 1`, `P_{k+1} = Ã_k P_k`. -/
def alComplexPartial38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | k + 1 => alTransferTilde38 (a (k : ZMod L)) (b (k : ZMod L)) ζ * alComplexPartial38 a b ζ k

/-- The complexified (ζ-scaled) monodromy `ζ^L M(1/ζ; a, b)`. -/
def alComplexMonodromy38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  alComplexPartial38 a b ζ L

/-- `T(ζ; a, b) = ζ^L tr M(1/ζ; a, b)`. -/
def alComplexT38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  Matrix.trace (alComplexMonodromy38 a b ζ)

/-- Slit-plane domain: `1 - a_j b_j ∉ (-∞, 0]` for all `j`. -/
def alComplexDomain38 (L : ℕ) : Set ((ZMod L → ℂ) × (ZMod L → ℂ)) :=
  {p | ∀ j, 1 - p.1 j * p.2 j ∈ slitPlane}

theorem isOpen_alComplexDomain38 (L : ℕ) [NeZero L] : IsOpen (alComplexDomain38 L) := by
  have : alComplexDomain38 L = ⋂ j : ZMod L, {p | 1 - p.1 j * p.2 j ∈ slitPlane} := by
    ext p; simp [alComplexDomain38]
  rw [this]
  refine isOpen_iInter_of_finite fun j => isOpen_slitPlane.preimage ?_
  fun_prop

theorem alRealSlice_mem_domain38 {L : ℕ} {α : ZMod L → ℂ} (hα : IsALField38 α) :
    (α, fun j => star (α j)) ∈ alComplexDomain38 L := by
  intro j
  have h : (1 : ℂ) - α j * star (α j) = ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  show 1 - α j * star (α j) ∈ slitPlane
  rw [h, Complex.ofReal_mem_slitPlane]
  have := hα j
  have h0 : 0 ≤ ‖α j‖ := norm_nonneg _
  nlinarith

/-! ### Analyticity -/

theorem analyticAt_alScalar38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ}
    {x : E} (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (h : 1 - a x * b x ∈ slitPlane) :
    AnalyticAt ℂ (fun y => alScalar38 (a y) (b y)) x := by
  unfold alScalar38
  exact AnalyticAt.cpow (by fun_prop) analyticAt_const h

theorem analyticAt_alComplexPartial38 {L : ℕ} [NeZero L] (k : ℕ)
    (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ)) (hq : q.2 ∈ alComplexDomain38 L) (i j : Fin 2) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
      alComplexPartial38 r.2.1 r.2.2 r.1 k i j) q := by
  have hz : AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => r.1) q :=
    (ContinuousLinearMap.fst ℂ ℂ ((ZMod L → ℂ) × (ZMod L → ℂ))).analyticAt q
  have hA : ∀ m : ZMod L, AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => r.2.1 m) q :=
    fun m => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ZMod L => ℂ) m).comp
      ((ContinuousLinearMap.fst ℂ (ZMod L → ℂ) (ZMod L → ℂ)).comp
        (ContinuousLinearMap.snd ℂ ℂ ((ZMod L → ℂ) × (ZMod L → ℂ))))).analyticAt q
  have hB : ∀ m : ZMod L, AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => r.2.2 m) q :=
    fun m => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ZMod L => ℂ) m).comp
      ((ContinuousLinearMap.snd ℂ (ZMod L → ℂ) (ZMod L → ℂ)).comp
        (ContinuousLinearMap.snd ℂ ℂ ((ZMod L → ℂ) × (ZMod L → ℂ))))).analyticAt q
  induction k generalizing i j with
  | zero =>
    have : ∀ r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ),
        alComplexPartial38 r.2.1 r.2.2 r.1 0 i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
      fun _ => rfl
    simp_rw [this]
    exact analyticAt_const
  | succ k ih =>
    have hs : AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
        alScalar38 (r.2.1 (k : ZMod L)) (r.2.2 (k : ZMod L))) q :=
      analyticAt_alScalar38 (hA _) (hB _) (hq _)
    have e : ∀ r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ),
        alComplexPartial38 r.2.1 r.2.2 r.1 (k + 1) i j =
        alScalar38 (r.2.1 (k : ZMod L)) (r.2.2 (k : ZMod L)) *
          ((if i = 0 then 1 else r.2.2 (k : ZMod L) * r.1) *
              alComplexPartial38 r.2.1 r.2.2 r.1 k 0 j +
           (if i = 0 then r.2.1 (k : ZMod L) * r.1 else r.1 ^ 2) *
             alComplexPartial38 r.2.1 r.2.2 r.1 k 1 j) := by
      intro r
      simp only [alComplexPartial38, alTransferTilde38, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply]
      fin_cases i <;> simp [Matrix.of_apply] <;> ring
    simp_rw [e]
    have h0 := ih 0 j
    have h1 := ih 1 j
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      exact hs.mul ((analyticAt_const.mul h0).add (((hA _).mul hz).mul h1))
    · simp only [hi, ite_false]
      exact hs.mul ((((hB _).mul hz).mul h0).add ((hz.pow 2).mul h1))

/-- Joint analyticity of `(ζ, a, b) ↦ T(ζ; a, b)` at every point over the slit-plane domain. -/
theorem analyticAt_alComplexT38 {L : ℕ} [NeZero L] (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ))
    (hq : q.2 ∈ alComplexDomain38 L) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexT38 r.2.1 r.2.2 r.1) q := by
  have e : ∀ r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ), alComplexT38 r.2.1 r.2.2 r.1 =
      alComplexPartial38 r.2.1 r.2.2 r.1 L 0 0 + alComplexPartial38 r.2.1 r.2.2 r.1 L 1 1 :=
    fun r => Matrix.trace_fin_two _
  simp_rw [e]
  exact (analyticAt_alComplexPartial38 L q hq 0 0).add (analyticAt_alComplexPartial38 L q hq 1 1)

/-- For fixed `(a,b)` in the domain, `T` is analytic (hence continuous) in `ζ`. -/
theorem analyticOnNhd_alComplexT38_zeta {L : ℕ} [NeZero L] {a b : ZMod L → ℂ}
    (h : (a, b) ∈ alComplexDomain38 L) :
    AnalyticOnNhd ℂ (alComplexT38 a b) Set.univ := by
  intro ζ _
  have := (analyticAt_alComplexT38 (L := L) (ζ, a, b) h).comp
    (g := fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexT38 r.2.1 r.2.2 r.1)
    (f := fun z : ℂ => ((z, a, b) : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ)))
    (by fun_prop)
  exact this

/-! ### Reduction to the real slice -/

theorem alScalar38_real {a : ℂ} (ha : ‖a‖ < 1) :
    alScalar38 a (star a) = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ)⁻¹ := by
  have h : (1 : ℂ) - a * star a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hp : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  unfold alScalar38
  have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.cpow_neg, h2, ← Complex.ofReal_cpow hp, ← Real.sqrt_eq_rpow]

theorem alComplexPartial38_real {L : ℕ} {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ≠ 0) (k : ℕ) :
    alComplexPartial38 α (fun j => star (α j)) ζ k = ζ ^ k • alPartial38 α ζ⁻¹ k := by
  induction k with
  | zero => simp [alComplexPartial38, alPartial38]
  | succ k ih =>
    simp only [alComplexPartial38, alPartial38, ih]
    have hT : alTransferTilde38 (α (k : ZMod L)) (star (α (k : ZMod L))) ζ =
        ζ • alTransfer38 (α (k : ZMod L)) ζ⁻¹ := by
      unfold alTransferTilde38 alTransfer38
      rw [alScalar38_real (hα _)]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;> field_simp
    rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]
    congr 1; ring

theorem alComplexT38_real {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (ζ : ℂ) :
    alComplexT38 α (fun j => star (α j)) ζ = alExtT38 α ζ := by
  have hd := alRealSlice_mem_domain38 hα
  have hc1 : Continuous (alComplexT38 α (fun j => star (α j))) :=
    continuous_iff_continuousAt.2 fun ζ => (analyticOnNhd_alComplexT38_zeta hd ζ trivial).continuousAt
  have hc2 : Continuous (alExtT38 α) := (alExtT38_differentiable α).continuous
  have heq : Set.EqOn (alComplexT38 α (fun j => star (α j))) (alExtT38 α) {0}ᶜ := by
    intro ζ hζ
    have hζ' : ζ ≠ 0 := hζ
    rw [alExtT38_eq hα hζ', alComplexT38, alComplexMonodromy38, alComplexPartial38_real hα hζ' L,
      alMonodromy38, Matrix.trace_smul, smul_eq_mul]
  exact congrFun (hc1.ext_on (dense_compl_singleton (0 : ℂ)) hc2 heq) ζ

end NlsGge.AblowitzLadik

end
