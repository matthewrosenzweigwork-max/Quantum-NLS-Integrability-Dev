import NlsGge.Atomic.Support.ContourCycleIndex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Actual dyadic polygonal approximation inside an arbitrary open trace neighborhood.

The original path is merely continuous. Every approximant is an actual finite
Chain with affine C1 leaves, exact dyadic cell parameters, and unchanged endpoints.
A constructed straight endpoint-fixed continuous homotopy stays in the neighborhood.
Only analytic transport requires the original accepted finite-piecewise C1 proof;
actual integrability precedes the holomorphic, scalar-index, and ZS integral identities.
No simplicity, immersion, orientation, nesting, index-one, Jordan, or idempotence
statement is included. The construction uses pinned Mathlib compact-tube and
uniform-continuity theorems and the accepted actual Chain/homotopy bridges.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology unitInterval

namespace NlsGge.Atomic.ContourPolygon
open ContourChain ContourPiecewise

lemma contDiffOn_segment (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend (Icc 0 1) := by
  apply (show ContDiff ℝ 1 (fun t : ℝ => (1-t) • a + t • b) by fun_prop).contDiffOn.congr
  intro t ht
  rw [Path.extend_apply _ ht]
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module]

def lineChain (a b : ℂ) : Chain a b :=
  .leaf (Path.segment a b) (contDiffOn_segment a b)

@[simp] lemma lineChain_path (a b : ℂ) : (lineChain a b).path = Path.segment a b := rfl

/-- The actual midpoint parameter, including both half-path endpoints. -/
def midpointTime : I := ⟨1/2, by constructor <;> norm_num⟩

def leftPath {a b : ℂ} (γ : Path a b) : Path a (γ midpointTime) where
  toFun t := γ (leftHalf t)
  continuous_toFun := γ.continuous.comp continuous_leftHalf
  source' := by simp
  target' := by congr 1

def rightPath {a b : ℂ} (γ : Path a b) : Path (γ midpointTime) b where
  toFun t := γ (rightHalf t)
  continuous_toFun := γ.continuous.comp continuous_rightHalf
  source' := by
    congr 1
    ext
    norm_num [rightHalf, midpointTime]
  target' := by simp

@[simp] lemma leftPath_apply {a b : ℂ} (γ : Path a b) (t : I) :
    leftPath γ t = γ (leftHalf t) := rfl
@[simp] lemma rightPath_apply {a b : ℂ} (γ : Path a b) (t : I) :
    rightPath γ t = γ (rightHalf t) := rfl

def dyadicPolygon : {a b : ℂ} → (γ : Path a b) → ℕ → Chain a b
  | _, _, _γ, 0 => lineChain _ _
  | _, _, γ, n+1 => .join (dyadicPolygon (leftPath γ) n) (dyadicPolygon (rightPath γ) n)

/-- Actual parameter in cell i, where the local parameter ranges over the closed unit interval. -/
def cellTime (n i : ℕ) (hi : i < 2^n) (u : I) : I :=
  ⟨((i:ℝ) + (u:ℝ)) / (2:ℝ)^n, by
    have hp : (0:ℝ) < 2^n := by positivity
    have hh : (i:ℝ)+1 ≤ (2:ℝ)^n := by exact_mod_cast hi
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg i) u.property.1) hp.le
    · apply (div_le_one hp).2
      linarith [u.property.2]⟩

lemma cellTime_succ_left (n i : ℕ) (hi : i < 2^n) (u : I) :
    cellTime (n+1) i (by rw [pow_succ]; omega) u = leftHalf (cellTime n i hi u) := by
  apply Subtype.ext
  dsimp [cellTime, leftHalf]
  rw [pow_succ]
  ring

lemma cellTime_succ_right (n i : ℕ) (hi : i < 2^n) (u : I) :
    cellTime (n+1) (2^n+i) (by rw [pow_succ]; omega) u =
      rightHalf (cellTime n i hi u) := by
  apply Subtype.ext
  dsimp [cellTime, rightHalf]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- Cell interpolation is exact at both endpoints, including every trans midpoint. -/
theorem dyadicPolygon_cell {a b : ℂ} (γ : Path a b) (n i : ℕ)
    (hi : i < 2^n) (u : I) :
    (dyadicPolygon γ n).path (cellTime n i hi u) =
      AffineMap.lineMap (γ (cellTime n i hi 0)) (γ (cellTime n i hi 1)) (u:ℝ) := by
  induction n generalizing a b i with
  | zero =>
      have hi0 : i = 0 := by simpa using hi
      subst i
      simpa [dyadicPolygon, cellTime, lineChain] using (Path.segment_apply a b u)
  | succ n ih =>
      by_cases hil : i < 2^n
      · rw [cellTime_succ_left n i hil, dyadicPolygon, Chain.path_join, trans_leftHalf]
        rw [ih (leftPath γ) i hil]
        simp only [cellTime_succ_left n i hil, leftPath_apply]
      · have hij : i = 2^n + (i-2^n) := by omega
        have hir : i-2^n < 2^n := by rw [pow_succ] at hi; omega
        generalize hj : i-2^n = j at *
        subst i
        rw [cellTime_succ_right n j hir, dyadicPolygon, Chain.path_join, trans_rightHalf]
        rw [ih (rightPath γ) j hir]
        simp only [cellTime_succ_right n j hir, rightPath_apply]

/-- Every actual parameter belongs to a closed dyadic cell; t=1 is included. -/
theorem exists_cellTime (n : ℕ) (t : I) :
    ∃ (i : ℕ) (hi : i < 2^n) (u : I), cellTime n i hi u = t := by
  induction n generalizing t with
  | zero => exact ⟨0, by norm_num, t, by ext; simp [cellTime]⟩
  | succ n ih =>
      by_cases ht : (t:ℝ) ≤ 1/2
      · let v : I := ⟨2*(t:ℝ), by constructor <;> nlinarith [t.property.1]⟩
        obtain ⟨i,hi,u,hu⟩ := ih v
        refine ⟨i, by rw [pow_succ]; omega, u, ?_⟩
        rw [cellTime_succ_left n i hi, hu]
        ext
        dsimp [leftHalf,v]
        ring
      · let v : I := ⟨2*(t:ℝ)-1, by constructor <;> nlinarith [t.property.2]⟩
        obtain ⟨i,hi,u,hu⟩ := ih v
        refine ⟨2^n+i, by rw [pow_succ]; omega, u, ?_⟩
        rw [cellTime_succ_right n i hi, hu]
        ext
        dsimp [rightHalf,v]
        ring



lemma cellTime_dist_le (n i : ℕ) (hi : i < 2^n) (u v : I) :
    dist (cellTime n i hi u) (cellTime n i hi v) ≤ (1/2:ℝ)^n := by
  have hp : (0:ℝ) < 2^n := by positivity
  change |((i:ℝ)+(u:ℝ))/(2:ℝ)^n - ((i:ℝ)+(v:ℝ))/(2:ℝ)^n| ≤ _
  rw [← sub_div, show (i:ℝ)+(u:ℝ)-((i:ℝ)+(v:ℝ)) = (u:ℝ)-(v:ℝ) by ring,
    abs_div, abs_of_pos hp, div_pow, one_pow]
  apply div_le_div_of_nonneg_right _ hp.le
  exact abs_le.mpr ⟨by linarith [u.property.1, v.property.2],
    by linarith [u.property.2, v.property.1]⟩

/-- Uniform approximation is proved for the original continuous path, without a C1 premise. -/
theorem exists_dyadicPolygon_dist_lt {a b : ℂ} (γ : Path a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ t : I, dist ((dyadicPolygon γ n).path t) (γ t) < ε := by
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2:ℝ)<1)
  refine ⟨n,fun t => ?_⟩
  obtain ⟨i,hi,u,hu⟩ := exists_cellTime n t
  rw [← hu, dyadicPolygon_cell]
  exact (convex_ball (γ (cellTime n i hi u)) ε).lineMap_mem
    (hmod ((cellTime_dist_le n i hi 0 u).trans_lt hn))
    (hmod ((cellTime_dist_le n i hi 1 u).trans_lt hn)) u.property

/-- Literal straight interpolation of two paths with the same actual endpoints. -/
def straightHomotopy {a b : ℂ} (γ δ : Path a b) : γ.Homotopy δ where
  toFun p := AffineMap.lineMap (γ p.2) (δ p.2) (p.1:ℝ)
  continuous_toFun := by simp only [AffineMap.lineMap_apply_module]; fun_prop
  map_zero_left := by intro t; simp
  map_one_left := by intro t; simp
  prop' := by
    intro s t ht
    rcases ht with ht | ht
    · subst t; simp
    · subst t; simp

@[simp] lemma straightHomotopy_apply {a b : ℂ} (γ δ : Path a b) (p : I × I) :
    straightHomotopy γ δ p = (1-(p.1:ℝ)) • γ p.2 + (p.1:ℝ) • δ p.2 := by
  exact AffineMap.lineMap_apply_module _ _ _

lemma dist_straightHomotopy_le {a b : ℂ} (γ δ : Path a b) (p : I × I) :
    dist (straightHomotopy γ δ p) (γ p.2) ≤ dist (δ p.2) (γ p.2) := by
  change dist (AffineMap.lineMap (γ p.2) (δ p.2) (p.1:ℝ)) (γ p.2) ≤ _
  rw [dist_lineMap_left, Real.norm_of_nonneg p.1.property.1]
  rw [dist_comm (γ p.2) (δ p.2)]
  exact mul_le_of_le_one_left (dist_nonneg (x := δ p.2) (y := γ p.2)) p.1.property.2

/-- An actual polygon and explicit endpoint-fixed continuous homotopy in any open trace neighborhood.
The polygon and every homotopy point are uniformly ε-close to the original parametrized path. -/
theorem exists_dyadicPolygon_fixed_homotopy {a b : ℂ} (γ : Path a b)
    {U : Set ℂ} (hU : IsOpen U) (hγU : range γ ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ H : γ.Homotopy (dyadicPolygon γ n).path,
      (∀ p : I × I, H p = (1-(p.1:ℝ)) • γ p.2 +
        (p.1:ℝ) • (dyadicPolygon γ n).path p.2) ∧
      range H ⊆ U ∧
      (∀ t : I, dist ((dyadicPolygon γ n).path t) (γ t) < ε) ∧
      (∀ p : I × I, dist (H p) (γ p.2) < ε) := by
  obtain ⟨r,hr,hrU⟩ := (_root_.isCompact_range γ.continuous).exists_cthickening_subset_open hU hγU
  obtain ⟨n,hn⟩ := exists_dyadicPolygon_dist_lt γ (min r ε) (lt_min hr hε)
  refine ⟨n, straightHomotopy γ (dyadicPolygon γ n).path, straightHomotopy_apply _ _, ?_,
    (fun t => (hn t).trans_le (min_le_right _ _)), ?_⟩
  · rintro _ ⟨p,rfl⟩
    apply hrU
    exact mem_cthickening_of_dist_le _ (γ p.2) r (range γ) (mem_range_self _)
      (((dist_straightHomotopy_le _ _ p).trans_lt (hn p.2)).trans_le (min_le_left _ _)).le
  · intro p
    exact ((dist_straightHomotopy_le _ _ p).trans_lt (hn p.2)).trans_le (min_le_right _ _)



/-- Counts actual C1 leaves in the existing finite chain data. -/
def leafCount : {a b : ℂ} → Chain a b → ℕ
  | _, _, .leaf _ _ => 1
  | _, _, .join p q => leafCount p + leafCount q

/-- Every leaf is literally the affine segment with that leaf's endpoints. -/
def IsPolygonal : {a b : ℂ} → Chain a b → Prop
  | a, b, .leaf γ _ => γ = Path.segment a b
  | _, _, .join p q => IsPolygonal p ∧ IsPolygonal q

lemma dyadicPolygon_isPolygonal {a b : ℂ} (γ : Path a b) (n : ℕ) :
    IsPolygonal (dyadicPolygon γ n) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => exact ⟨ih _, ih _⟩

lemma leafCount_dyadicPolygon {a b : ℂ} (γ : Path a b) (n : ℕ) :
    leafCount (dyadicPolygon γ n) = 2^n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [dyadicPolygon, leafCount, ih, pow_succ, Nat.mul_two]

section AnalyticTransport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Both integrals are genuine, and an actually constructed polygon has the same holomorphic integral. -/
theorem exists_dyadicPolygon_integral_eq {a b : ℂ} (γ : Path a b)
    (hγ : LIB042.PiecewiseC1 γ) {U : Set ℂ} (hU : IsOpen U) (hγU : range γ ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (dyadicPolygon γ n).trace ⊆ U ∧
      (∀ t : I, dist ((dyadicPolygon γ n).path t) (γ t) < ε) ∧
      ∀ f : ℂ → F, DifferentiableOn ℂ f U →
      CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ ∧
      (dyadicPolygon γ n).Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) ∧
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
        (dyadicPolygon γ n).integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) := by
  obtain ⟨n,H,_,hHU,hn,_⟩ := exists_dyadicPolygon_fixed_homotopy γ hU hγU ε hε
  have hpU : (dyadicPolygon γ n).trace ⊆ U := by
    rintro _ ⟨t,rfl⟩
    exact hHU ⟨(1,t), by simp⟩
  refine ⟨n,hpU,hn,fun f hf => ?_⟩
  have hiγ := curveIntegrable_of_piecewiseC1 hf.continuousOn hγ
    (fun t => hγU (mem_range_self t))
  have hip := (dyadicPolygon γ n).integrable_toSpanSingleton_of_continuousOn hf.continuousOn hpU
  have he := curveIntegral_eq_of_continuous_homotopy H hU hf hHU hγ
    (dyadicPolygon γ n).path_piecewiseC1
  exact ⟨hiγ,hip,he.trans (Chain.integral_eq_curveIntegral hip).symm⟩

end AnalyticTransport

/-- The actual normalized scalar index is transported for all poles outside the chosen neighborhood.
The approximation and its homotopy are chosen before the pole. Endpoints need not agree. -/
theorem exists_dyadicPolygon_index_eq {a b : ℂ} (c : Chain a b)
    {U : Set ℂ} (hU : IsOpen U) (hcU : c.trace ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (dyadicPolygon c.path n).trace ⊆ U ∧
      (∀ t : I, dist ((dyadicPolygon c.path n).path t) (c.path t) < ε) ∧
      ∀ w : ℂ, w ∉ U → c.index w = (dyadicPolygon c.path n).index w := by
  obtain ⟨n,H,_,hHU,hn,_⟩ := exists_dyadicPolygon_fixed_homotopy c.path hU hcU ε hε
  have hpU : (dyadicPolygon c.path n).trace ⊆ U := by
    rintro _ ⟨t,rfl⟩
    exact hHU ⟨(1,t), by simp⟩
  refine ⟨n,hpU,hn,fun w hw => ?_⟩
  have hf : DifferentiableOn ℂ (fun z => (z-w)⁻¹) U :=
    (differentiableOn_id.sub_const w).inv
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  have hic := c.integrable_toSpanSingleton_of_continuousOn hf.continuousOn hcU
  have hip := (dyadicPolygon c.path n).integrable_toSpanSingleton_of_continuousOn hf.continuousOn hpU
  have he := curveIntegral_eq_of_continuous_homotopy H hU hf hHU c.path_piecewiseC1
    (dyadicPolygon c.path n).path_piecewiseC1
  unfold Chain.index
  rw [Chain.integral_eq_curveIntegral hic, Chain.integral_eq_curveIntegral hip, he]

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB041 NlsGge.Atomic.LIB042

/-- In the actual resolvent set, the constructed polygon preserves the same literal normalized
operator integral for every complex potential and every actual boundary condition. -/
theorem exists_dyadicPolygon_zsRieszProjection_eq
    (φ : SourcePairL2) (bc : ZSBoundaryCondition) {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ)
    (hres : ∀ t, HasBoundedResolvent (zsRealization φ bc) (γ t))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ,
      (∀ t, HasBoundedResolvent (zsRealization φ bc) ((dyadicPolygon γ n).path t)) ∧
      (∀ t : I, dist ((dyadicPolygon γ n).path t) (γ t) < ε) ∧
      CurveIntegrable (resolventForm φ bc) γ ∧
      (dyadicPolygon γ n).Integrable (resolventForm φ bc) ∧
      zsRieszProjection φ bc γ = zsRieszProjection φ bc (dyadicPolygon γ n).path := by
  let U := {z : ℂ | HasBoundedResolvent (zsRealization φ bc) z}
  obtain ⟨n,H,_,hHU,hn,_⟩ := exists_dyadicPolygon_fixed_homotopy γ
    (isOpen_zsResolventSet φ bc) (by rintro _ ⟨t,rfl⟩; exact hres t) ε hε
  have hpU : (dyadicPolygon γ n).trace ⊆ U := by
    rintro _ ⟨t,rfl⟩
    exact hHU ⟨(1,t), by simp⟩
  have hf := (zsResolventFamily_analyticOnNhd φ bc).differentiableOn
  have hform : (fun z => ContinuousLinearMap.toSpanSingleton ℂ (zsResolventFamily φ bc z)) =
      resolventForm φ bc := by funext z; ext v; rfl
  have hiγ := curveIntegrable_of_piecewiseC1 hf.continuousOn hγ hres
  have hip := (dyadicPolygon γ n).integrable_toSpanSingleton_of_continuousOn hf.continuousOn hpU
  rw [hform] at hiγ hip
  have he := zsRieszProjection_eq_of_continuous_homotopy φ bc H hγ
    (dyadicPolygon γ n).path_piecewiseC1 (fun p => hHU (mem_range_self p))
  exact ⟨n,(fun t => hpU (mem_range_self t)),hn,hiγ,hip,he⟩

end NlsGge.Atomic.ContourPolygon
