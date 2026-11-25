import Mathlib
import QuantumNLS.SpatialTransfer

/-!
# Global existence for linear ODEs with continuous coefficient; DEF-013 made total

Closes the existence gap of `SpatialTransfer` (DEF-013): `spatialTransfer` / `discriminant` no longer need the
premise `∃ M, IsFundamental ...`.

## Result (all proved, no smallness condition)
`exists_fundamental`: for every continuous `A : ℝ → 𝔸` into a complete normed `ℝ`-algebra `𝔸` there is
`M : ℝ → 𝔸` with `M 0 = 1` and `HasDerivAt M (A x * M x) x` for all `x ∈ ℝ`.

Route (Dyson/Volterra series): `M_0 = 1`, `M_{k+1}(x) = ∫₀ˣ A M_k` (`dyson`); each `M_k` is continuous
(`continuous_dyson`); on `[-R, R]` with `‖A‖ ≤ K`, `‖M_k(x)‖ ≤ ‖1‖ (K|x|)^k / k!` (`norm_dyson_le`, using
`|∫₀ˣ |s|^k ds| = |x|^{k+1}/(k+1)`, `abs_integral_abs_pow`, valid for both signs of `x`); the series
`M = ∑ M_k` converges uniformly on compacts, so `M` is continuous (`continuousOn_tsum`); termwise integration
(`hasSum_integral_of_dominated_convergence`) gives `M(x) = 1 + ∫₀ˣ A M`; the fundamental theorem of calculus for the
continuous integrand gives `M' = A M`.

## DEF-013 total
For `Mat2 = Matrix (Fin 2) (Fin 2) ℂ` (ℓ^∞-operator norm, complete):
`exists_isFundamental`, `exists_isFundamental_coef` (every coupling `(p,q)`, continuous `u`, every `z`),
`existsUnique_isFundamental_bal`, `spatialTransfer_spec'` (`spatialTransfer` is the fundamental solution with no
existence premise), `discriminant_wellDefined` (`Δ_u(z) = trace M(L,z)` is the trace of the unique fundamental
solution for every continuous `u` and every `z`), `discriminant_eq_trace'`, and `discriminant_eq_unbalanced`
(the same value is the trace of the unbalanced solution, which also exists).

Class of `u` unchanged: continuous representatives (smooth / `H¹` profiles); the `L¹`-coefficient Carathéodory
solutions for `u ∈ L² \ H¹` remain outside this module.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped Nat Interval

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.LinearFundamental

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The Dyson/Volterra iterates `M_0 = 1`, `M_{k+1}(x) = ∫₀ˣ A(s) M_k(s) ds`. -/
def dyson (A : ℝ → 𝔸) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | k + 1 => fun x => ∫ s in (0 : ℝ)..x, A s * dyson A k s

theorem continuous_dyson {A : ℝ → 𝔸} (hA : Continuous A) : ∀ k, Continuous (dyson A k)
  | 0 => continuous_const
  | k + 1 => by
    have h : Continuous fun s => A s * dyson A k s := hA.mul (continuous_dyson hA k)
    exact intervalIntegral.continuous_primitive (fun a b => h.intervalIntegrable a b) 0

theorem integral_abs_pow_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∫ s in (0 : ℝ)..y, |s| ^ k = y ^ (k + 1) / (k + 1) := by
  have : ∫ s in (0 : ℝ)..y, |s| ^ k = ∫ s in (0 : ℝ)..y, s ^ k := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hy] at hs
    simp [abs_of_nonneg hs.1]
  rw [this, integral_pow]
  simp

/-- `|∫₀ˣ |s|^k ds| = |x|^{k+1}/(k+1)`. -/
theorem abs_integral_abs_pow (k : ℕ) (x : ℝ) :
    |∫ s in (0 : ℝ)..x, |s| ^ k| = |x| ^ (k + 1) / (k + 1) := by
  rcases le_total 0 x with hx | hx
  · rw [integral_abs_pow_nonneg k hx, abs_of_nonneg hx,
      abs_of_nonneg (div_nonneg (pow_nonneg hx _) (by positivity))]
  · have h1 : ∫ s in (0 : ℝ)..x, |s| ^ k = -∫ s in (0 : ℝ)..(-x), |s| ^ k := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) (fun s : ℝ => |s| ^ k)
      simp only [abs_neg, neg_zero] at this
      rw [this, intervalIntegral.integral_symm]
    rw [h1, integral_abs_pow_nonneg k (neg_nonneg.mpr hx), abs_neg,
      abs_of_nonneg (div_nonneg (pow_nonneg (neg_nonneg.mpr hx) _) (by positivity)),
      abs_of_nonpos hx]



theorem norm_dyson_le {A : ℝ → 𝔸} {K R : ℝ} (hR : 0 ≤ R) (hK : ∀ s ∈ Icc (-R) R, ‖A s‖ ≤ K) :
    ∀ k : ℕ, ∀ x ∈ Icc (-R) R, ‖dyson A k x‖ ≤ ‖(1 : 𝔸)‖ * (K * |x|) ^ k / k ! := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨by linarith, hR⟩)
  intro k
  induction k with
  | zero => intro x _; simp [dyson]
  | succ k ih =>
    intro x hx
    have hsub : ∀ s ∈ Ι (0 : ℝ) x, s ∈ Icc (-R) R ∧ |s| ≤ |x| := by
      intro s hs
      have hs' : s ∈ uIcc (0 : ℝ) x := Set.uIoc_subset_uIcc hs
      refine ⟨Set.uIcc_subset_Icc ⟨by linarith, hR⟩ hx hs', ?_⟩
      rcases le_total 0 x with h | h
      · rw [Set.uIcc_of_le h] at hs'
        rw [abs_of_nonneg hs'.1, abs_of_nonneg h]; exact hs'.2
      · rw [Set.uIcc_of_ge h] at hs'
        rw [abs_of_nonpos hs'.2, abs_of_nonpos h]; linarith [hs'.1]
    set c : ℝ := ‖(1 : 𝔸)‖ * K ^ (k + 1) / k ! with hc
    have hc0 : 0 ≤ c := by positivity
    have hbound : ‖∫ s in (0 : ℝ)..x, A s * dyson A k s‖ ≤
        |∫ s in (0 : ℝ)..x, c * |s| ^ k| := by
      refine intervalIntegral.norm_integral_le_abs_of_norm_le (g := fun s => c * |s| ^ k) ?_ ?_
      · refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun s hs => ?_)
        obtain ⟨h1, h2⟩ := hsub s hs
        calc ‖A s * dyson A k s‖ ≤ ‖A s‖ * ‖dyson A k s‖ := norm_mul_le _ _
          _ ≤ K * (‖(1 : 𝔸)‖ * (K * |s|) ^ k / k !) :=
              mul_le_mul (hK s h1) (ih s h1) (norm_nonneg _) hK0
          _ = c * |s| ^ k := by rw [hc, mul_pow, pow_succ]; ring
      · exact (by fun_prop : Continuous fun s : ℝ => c * |s| ^ k).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hc0, abs_integral_abs_pow] at hbound
    refine hbound.trans (le_of_eq ?_)
    show c * (|x| ^ (k + 1) / (↑k + 1)) = ‖(1 : 𝔸)‖ * (K * |x|) ^ (k + 1) / ((k + 1)! : ℕ)
    rw [hc, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Global existence for linear ODEs with continuous coefficient** (Dyson/Volterra series): for every
continuous `A : ℝ → 𝔸` into a complete normed `ℝ`-algebra there is `M` with `M 0 = 1` and
`M' = A M` on all of `ℝ`. -/
theorem exists_fundamental {A : ℝ → 𝔸} (hA : Continuous A) :
    ∃ M : ℝ → 𝔸, M 0 = 1 ∧ ∀ x, HasDerivAt M (A x * M x) x := by
  classical
  have hbd : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (-R) R, ‖A s‖ ≤ K := by
    intro R hR
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hA.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun s hs => (hC s hs).trans (le_max_left _ _)⟩
  have hu : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ, 0 ≤ K ∧ (∀ s ∈ Icc (-R) R, ‖A s‖ ≤ K) ∧
      Summable (fun k : ℕ => ‖(1 : 𝔸)‖ * (K * R) ^ k / k !) ∧
      ∀ k : ℕ, ∀ x ∈ Icc (-R) R, ‖dyson A k x‖ ≤ ‖(1 : 𝔸)‖ * (K * R) ^ k / k ! := by
    intro R hR
    obtain ⟨K, hK0, hK⟩ := hbd R hR
    refine ⟨K, hK0, hK, ?_, fun k x hx => ?_⟩
    · have := (Real.summable_pow_div_factorial (K * R)).mul_left ‖(1 : 𝔸)‖
      refine this.congr fun k => ?_
      ring
    · refine (norm_dyson_le hR hK k x hx).trans ?_
      have hxR : |x| ≤ R := abs_le.mpr ⟨hx.1, hx.2⟩
      have : (K * |x|) ^ k ≤ (K * R) ^ k :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hxR hK0) k
      gcongr
  set M : ℝ → 𝔸 := fun x => ∑' k, dyson A k x with hM
  have hMcont : Continuous M := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨K, hK0, hK, hsum, hb⟩ := hu (|x| + 1) (by positivity)
    have hon : ContinuousOn M (Icc (-(|x| + 1)) (|x| + 1)) :=
      continuousOn_tsum (fun k => (continuous_dyson hA k).continuousOn) hsum
        (fun k y hy => hb k y hy)
    exact hon.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x]))
  have hint : ∀ x, M x = 1 + ∫ s in (0 : ℝ)..x, A s * M s := by
    intro x
    obtain ⟨K, hK0, hK, hsum, hb⟩ := hu |x| (abs_nonneg x)
    have hsub : ∀ s ∈ Ι (0 : ℝ) x, s ∈ Icc (-|x|) |x| := by
      intro s hs
      have hs' : s ∈ uIcc (0 : ℝ) x := Set.uIoc_subset_uIcc hs
      refine Set.uIcc_subset_Icc ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
        ⟨by linarith [neg_abs_le x], le_abs_self x⟩ hs'
    have hxmem : x ∈ Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
    have hS : HasSum (fun k => dyson A k x) (M x) :=
      (Summable.of_norm_bounded hsum (fun k => hb k x hxmem)).hasSum
    have hI : HasSum (fun k => ∫ s in (0 : ℝ)..x, A s * dyson A k s)
        (∫ s in (0 : ℝ)..x, A s * M s) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence
        (fun k _ => K * (‖(1 : 𝔸)‖ * (K * |x|) ^ k / k !)) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
      · exact (hA.mul (continuous_dyson hA k)).aestronglyMeasurable
      · refine ae_of_all _ fun s hs => ?_
        have hs1 := hsub s hs
        calc ‖A s * dyson A k s‖ ≤ ‖A s‖ * ‖dyson A k s‖ := norm_mul_le _ _
          _ ≤ K * (‖(1 : 𝔸)‖ * (K * |x|) ^ k / k !) :=
              mul_le_mul (hK s hs1) (hb k s hs1) (norm_nonneg _) hK0
      · exact ae_of_all _ fun s hs => hsum.mul_left K
      · exact intervalIntegrable_const
      · refine ae_of_all _ fun s hs => ?_
        have hSs : HasSum (fun k => dyson A k s) (M s) :=
          (Summable.of_norm_bounded hsum (fun k => hb k s (hsub s hs))).hasSum
        exact hSs.mul_left (A s)
    have hS1 : HasSum (fun k => dyson A (k + 1) x) (M x - 1) := by
      have := (hasSum_nat_add_iff' 1).mpr hS
      simpa [dyson] using this
    have := hS1.unique hI
    rw [← this]; abel
  refine ⟨M, ?_, fun x => ?_⟩
  · rw [hint 0]; simp
  · have hc : Continuous fun s => A s * M s := hA.mul hMcont
    have h1 := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add 1
    have hfun : M = fun u => 1 + ∫ s in (0 : ℝ)..u, A s * M s := funext hint
    have h2 : HasDerivAt (fun u => 1 + ∫ s in (0 : ℝ)..u, A s * M s) (A x * M x) x := h1
    rw [← hfun] at h2
    exact h2

end General


section Mat2Case

open QuantumNLS.SpatialTransfer

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance : CompleteSpace Mat2 := inferInstanceAs (CompleteSpace (Fin 2 → Fin 2 → ℂ))

/-- **Existence of the fundamental solution** for every continuous `A : ℝ → Mat2`. -/
theorem exists_isFundamental {A : ℝ → Mat2} (hA : Continuous A) : ∃ M, IsFundamental A M :=
  exists_fundamental hA

/-- Existence for every coupling `(p,q)`, continuous `u` and every `z`. -/
theorem exists_isFundamental_coef (p q : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    ∃ M, IsFundamental (coef p q u z) M :=
  exists_isFundamental (continuous_coef p q hu z)

/-- **Existence and uniqueness** of the balanced fundamental solution (DEF-013 spatial matrix). -/
theorem existsUnique_isFundamental_bal (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    ∃! M, IsFundamental (balCoef κ u z) M := by
  obtain ⟨M, hM⟩ := exists_isFundamental_coef (Real.sqrt κ) (Real.sqrt κ) hu z
  exact ⟨M, hM, fun M' hM' =>
    IsFundamental.unique (continuous_coef _ _ hu z) hM' hM⟩

/-- `spatialTransfer` is the fundamental solution for every continuous `u`: no existence premise. -/
theorem spatialTransfer_spec' (κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    IsFundamental (balCoef κ u z) (spatialTransfer κ u z) :=
  spatialTransfer_spec (exists_isFundamental_coef _ _ hu z)

/-- `Δ_u(z) = trace M(L,z)` is well defined for every continuous `u` and every `z`: it is the trace of the
(unique) fundamental solution, and `discriminant_eq_trace` holds for it without any existence premise. -/
theorem discriminant_wellDefined (L κ : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    ∃ M, IsFundamental (balCoef κ u z) M ∧ discriminant L κ u z = (M L).trace ∧
      ∀ M', IsFundamental (balCoef κ u z) M' → M' = M := by
  refine ⟨spatialTransfer κ u z, spatialTransfer_spec' κ hu z, rfl, fun M' hM' => ?_⟩
  exact IsFundamental.unique (continuous_coef _ _ hu z) hM' (spatialTransfer_spec' κ hu z)

theorem discriminant_eq_trace' (L κ : ℝ) {u : ℝ → ℂ} {z : ℂ} {M : ℝ → Mat2} (hu : Continuous u)
    (h : IsFundamental (balCoef κ u z) M) : discriminant L κ u z = (M L).trace :=
  discriminant_eq_trace hu h

/-- The discriminant equals the trace of the *unbalanced* fundamental solution (gauge identity), which
exists for every continuous `u` as well. -/
theorem discriminant_eq_unbalanced (L κ : ℝ) (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    ∃ Mu, IsFundamental (unbalCoef κ u z) Mu ∧ discriminant L κ u z = (Mu L).trace := by
  obtain ⟨Mu, hMu⟩ := exists_isFundamental_coef κ 1 hu z
  refine ⟨Mu, hMu, ?_⟩
  rw [discriminant_eq_trace hu (spatialTransfer_spec' κ hu z)]
  exact trace_bal_eq_trace_unbal hκ hu (spatialTransfer_spec' κ hu z) hMu L

end Mat2Case

end QuantumNLS.LinearFundamental

#print axioms QuantumNLS.LinearFundamental.abs_integral_abs_pow
#print axioms QuantumNLS.LinearFundamental.norm_dyson_le
#print axioms QuantumNLS.LinearFundamental.exists_fundamental
#print axioms QuantumNLS.LinearFundamental.exists_isFundamental_coef
#print axioms QuantumNLS.LinearFundamental.existsUnique_isFundamental_bal
#print axioms QuantumNLS.LinearFundamental.spatialTransfer_spec'
#print axioms QuantumNLS.LinearFundamental.discriminant_wellDefined
#print axioms QuantumNLS.LinearFundamental.discriminant_eq_unbalanced
