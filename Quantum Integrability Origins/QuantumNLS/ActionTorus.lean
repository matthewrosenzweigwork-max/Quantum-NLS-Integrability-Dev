import Mathlib
import QuantumNLS.IndexedMasses

/-!
# DEF-019: sequence action torus and its topology

Source: `DEFINITIONS_LEDGER.md:401` (DEF-019), `chapters/definitions.tex`, `def:report-19`.  Ledger text: for
`a ∈ ℓ¹_+(ℤ)` the action torus is `{z ∈ ℓ² : |z_n|² = a_n}` with the inherited norm topology; the product of
circles acts by coordinate rotations; a coordinate with zero action is fixed; compactness follows from fixed
summable tails and finite-coordinate compactness, and does not require choosing angles at zeros.

## What is realized (all proved, no hypotheses)
* `PosL1 := {a : lp (fun _ : ℤ => ℝ) 1 // ∀ n, 0 ≤ a n}` is `ℓ¹_+(ℤ)` with the subspace `ℓ¹`-norm topology.
* `actionTorus a ⊆ S2 ℤ = lp (fun _ : ℤ => ℂ) 2` (DEF-002, `QuantumNLS.ResetNormalizationUniqueness.S2`) is the set
  `{z | ∀ n, ‖z n‖² = a n}`, with the subspace topology of the `ℓ²` norm (it is a `Set` of the metric space `S2 ℤ`).
* `rotate θ z` for `θ : ℤ → Circle` (product topology) multiplies the `n`-th coordinate by `θ n`:
  `rotate_mem` (maps `T_a` to `T_a`), `rotate_apply_of_eq_zero` (coordinates with `a_n = 0` are fixed; they are `0`),
  `rotate_mul`/`rotate_one` (group action), `norm_rotate_sub` (isometry), `continuous_rotate` (joint continuity on all
  of `(ℤ → Circle) × ℓ²`), `continuous_actionOn` (the restricted action `(ℤ → Circle) × T_a → T_a`).
* `isCompact_actionTorus : IsCompact (actionTorus a)`: proved via the continuity criterion `continuousAt_of_tail`
  (fixed summable tail `∑' n ∉ F, 4 a_n` small + finitely many continuous coordinates) applied to the identity from the
  Tychonoff-compact coordinate spheres `{p | ∀ n, ‖p n‖ = √a_n}` (product topology) into `ℓ²`; the range is `T_a`.
  No angle is chosen anywhere, in particular none at zeros of `a`.
* `actionTorus_nonempty` (`sqrtVec a`, `z_n = √a_n`), `norm_sq_eq_tsum_of_mem` (`‖z‖² = ∑ a_n`).
* `chartMasses_iff_mem_actionTorus`: the DEF-014 binding `ChartMasses` (`‖Φ u n‖² = a_n(u)`) is exactly membership in `T_{a(u)}`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology Set
open scoped ENNReal

namespace QuantumNLS.ActionTorus

open QuantumNLS.ResetNormalizationUniqueness

/-! ### `ℓ²` tail machinery -/

theorem tsum_sq_eq (x : S2 ℤ) : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp x
  simpa using h

theorem summable_sq (x : S2 ℤ) : Summable (fun n => ‖x n‖ ^ 2) := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  simpa using x.2.summable hp

/-- **Continuity criterion by fixed summable tails**: if coordinates are continuous at `p` and the squared
coordinate deviations from `Φ p` are dominated by a fixed summable `g`, then `Φ` is continuous at `p` into `ℓ²`. -/
theorem continuousAt_of_tail {X : Type*} [TopologicalSpace X] (Φ : X → S2 ℤ) (p : X) (g : ℤ → ℝ)
    (hg : Summable g) (hdom : ∀ q n, ‖Φ q n - Φ p n‖ ^ 2 ≤ g n)
    (hcoord : ∀ n, ContinuousAt (fun q => Φ q n) p) : ContinuousAt Φ p := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero g).eventually (gt_mem_nhds hε2)).exists
  have hη : 0 < ε ^ 2 / (2 * ((F.card : ℝ) + 1)) := by positivity
  have hn : ∀ n : ℤ, ∀ᶠ q in 𝓝 p, ‖Φ q n - Φ p n‖ ^ 2 < ε ^ 2 / (2 * ((F.card : ℝ) + 1)) := by
    intro n
    have h1 : Tendsto (fun q => ‖Φ q n - Φ p n‖ ^ 2) (𝓝 p) (𝓝 (‖Φ p n - Φ p n‖ ^ 2)) :=
      (((hcoord n).tendsto.sub_const _).norm).pow 2
    have h2 : ‖Φ p n - Φ p n‖ ^ 2 = 0 := by simp
    rw [h2] at h1
    exact h1.eventually (gt_mem_nhds hη)
  filter_upwards [(Filter.eventually_all_finset F).2 (fun n _ => hn n)] with q hq
  rw [dist_eq_norm]
  have hsq : ‖Φ q - Φ p‖ ^ 2 < ε ^ 2 := by
    rw [tsum_sq_eq, ← (summable_sq (Φ q - Φ p)).sum_add_tsum_subtype_compl F]
    have hfin : ∑ n ∈ F, ‖(Φ q - Φ p) n‖ ^ 2 ≤ F.card * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) := by
      calc ∑ n ∈ F, ‖(Φ q - Φ p) n‖ ^ 2
          ≤ ∑ n ∈ F, (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) :=
            Finset.sum_le_sum (fun n hn' => (hq n hn').le)
        _ = _ := by simp
    have hfin2 : (F.card : ℝ) * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) < ε ^ 2 / 2 := by
      have hc : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
      have : (F.card : ℝ) * (ε ^ 2 / (2 * ((F.card : ℝ) + 1))) =
          ε ^ 2 / 2 * ((F.card : ℝ) / ((F.card : ℝ) + 1)) := by
        field_simp
      rw [this]
      have h3 : (F.card : ℝ) / ((F.card : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    have htail : ∑' n : {x : ℤ // x ∉ F}, ‖(Φ q - Φ p) n‖ ^ 2 ≤ ∑' n : {x : ℤ // x ∉ F}, g n := by
      refine Summable.tsum_le_tsum (fun n => ?_)
        ((summable_sq (Φ q - Φ p)).comp_injective Subtype.val_injective)
        (hg.comp_injective Subtype.val_injective)
      simpa using hdom q n
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-! ### The sequence space `ℓ¹_+(ℤ)` and the action torus -/

/-- `ℓ¹_+(ℤ)`: nonnegative summable sequences, with the subspace `ℓ¹` norm topology. -/
abbrev PosL1 := {a : lp (fun _ : ℤ => ℝ) 1 // ∀ n, 0 ≤ a.1 n}

theorem summable_posL1 (a : PosL1) : Summable (fun n : ℤ => a.1 n) :=
  Memℓp.summable_of_one a.1.2

/-- **DEF-019.** The action torus `T_a = {z ∈ ℓ²(ℤ) : |z_n|² = a_n}`, as a subset of `ℓ²(ℤ)` (inherited norm
topology). -/
def actionTorus (a : PosL1) : Set (S2 ℤ) := {z | ∀ n, ‖z n‖ ^ 2 = a.1 n}

theorem mem_actionTorus_iff (a : PosL1) (z : S2 ℤ) : z ∈ actionTorus a ↔ ∀ n, ‖z n‖ ^ 2 = a.1 n := Iff.rfl

theorem norm_sq_eq_tsum_of_mem {a : PosL1} {z : S2 ℤ} (hz : z ∈ actionTorus a) :
    ‖z‖ ^ 2 = ∑' n, a.1 n := by
  rw [tsum_sq_eq]
  exact tsum_congr hz

/-- An `ℓ²` element from a sequence with squared moduli `a`. -/
def ofSq (a : PosL1) (p : ℤ → ℂ) (hp : ∀ n, ‖p n‖ ^ 2 = a.1 n) : S2 ℤ :=
  ⟨p, by
    refine memℓp_gen ?_
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have : (fun n : ℤ => ‖p n‖ ^ (2 : ℝ≥0∞).toReal) = fun n : ℤ => a.1 n := by
      refine funext fun n => ?_
      rw [h2, Real.rpow_two, hp n]
    rw [this]
    exact summable_posL1 a⟩

@[simp] theorem ofSq_apply (a : PosL1) (p : ℤ → ℂ) (hp : ∀ n, ‖p n‖ ^ 2 = a.1 n) (n : ℤ) :
    ofSq a p hp n = p n := rfl

theorem ofSq_mem (a : PosL1) (p : ℤ → ℂ) (hp : ∀ n, ‖p n‖ ^ 2 = a.1 n) : ofSq a p hp ∈ actionTorus a :=
  fun n => hp n

/-- The real point `z_n = √a_n` of the torus. -/
def sqrtVec (a : PosL1) : S2 ℤ :=
  ofSq a (fun n => ((Real.sqrt (a.1 n) : ℝ) : ℂ)) (fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (a.2 n)])

theorem sqrtVec_mem (a : PosL1) : sqrtVec a ∈ actionTorus a := ofSq_mem _ _ _

/-- The action torus is nonempty (take `z_n = √a_n`). -/
theorem actionTorus_nonempty (a : PosL1) : (actionTorus a).Nonempty := ⟨sqrtVec a, sqrtVec_mem a⟩

/-! ### The action of the product of circles -/

/-- Coordinate rotation by `θ : ℤ → Circle`. -/
def rotate (θ : ℤ → Circle) (z : S2 ℤ) : S2 ℤ :=
  ⟨fun n => (θ n : ℂ) * z n, z.2.mono' (fun n => by simp)⟩

@[simp] theorem rotate_apply (θ : ℤ → Circle) (z : S2 ℤ) (n : ℤ) : rotate θ z n = (θ n : ℂ) * z n := rfl

theorem rotate_one (z : S2 ℤ) : rotate 1 z = z := by
  refine lp.ext (funext fun n => ?_)
  simp

theorem rotate_mul (θ φ : ℤ → Circle) (z : S2 ℤ) : rotate (θ * φ) z = rotate θ (rotate φ z) := by
  refine lp.ext (funext fun n => ?_)
  simp [mul_assoc]

/-- The rotation action maps `T_a` into itself. -/
theorem rotate_mem (θ : ℤ → Circle) {a : PosL1} {z : S2 ℤ} (hz : z ∈ actionTorus a) :
    rotate θ z ∈ actionTorus a := fun n => by
  rw [rotate_apply, norm_mul, Circle.norm_coe, one_mul]
  exact hz n

/-- Coordinates with zero action are zero on `T_a`, hence fixed by every rotation. -/
theorem rotate_apply_of_eq_zero (θ : ℤ → Circle) {a : PosL1} {z : S2 ℤ} (hz : z ∈ actionTorus a) {n : ℤ}
    (hn : a.1 n = 0) : rotate θ z n = z n := by
  have h0 : z n = 0 := by
    have := hz n
    rw [hn] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (by simpa using this) |> norm_eq_zero.1
  rw [rotate_apply, h0, mul_zero]

theorem norm_rotate_sub (θ : ℤ → Circle) (z w : S2 ℤ) : ‖rotate θ z - rotate θ w‖ = ‖z - w‖ := by
  refine norm_eq_of_norm_apply_eq (fun n => ?_)
  simp only [lp.coeFn_sub, Pi.sub_apply, rotate_apply]
  rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul]

/-- For fixed `z`, `θ ↦ rotate θ z` is continuous for the product topology on `ℤ → Circle`. -/
theorem continuous_rotate_left (z : S2 ℤ) : Continuous (fun θ : ℤ → Circle => rotate θ z) := by
  refine continuous_iff_continuousAt.2 fun θ0 => ?_
  refine continuousAt_of_tail (fun θ : ℤ → Circle => rotate θ z) θ0 (fun n => 4 * ‖z n‖ ^ 2)
    ((summable_sq z).mul_left 4) (fun θ n => ?_) (fun n => ?_)
  · simp only [rotate_apply]
    rw [← sub_mul, norm_mul, mul_pow]
    have h1 : ‖(θ n : ℂ) - (θ0 n : ℂ)‖ ≤ 2 := by
      calc ‖(θ n : ℂ) - (θ0 n : ℂ)‖ ≤ ‖(θ n : ℂ)‖ + ‖(θ0 n : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp; norm_num
    have h2 : ‖(θ n : ℂ) - (θ0 n : ℂ)‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg ((θ n : ℂ) - (θ0 n : ℂ))]
    nlinarith [sq_nonneg ‖z n‖]
  · have : Continuous (fun θ : ℤ → Circle => (θ n : ℂ) * z n) :=
      (Continuous.mul (continuous_subtype_val.comp (continuous_apply n)) continuous_const)
    exact this.continuousAt

/-- **The action is continuous**, jointly in the rotation parameters and the `ℓ²` point. -/
theorem continuous_rotate : Continuous (fun p : (ℤ → Circle) × S2 ℤ => rotate p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨θ0, z0⟩
  have h1 : Tendsto (fun p : (ℤ → Circle) × S2 ℤ => rotate p.1 z0) (𝓝 (θ0, z0)) (𝓝 (rotate θ0 z0)) :=
    ((continuous_rotate_left z0).tendsto θ0).comp (continuous_fst.tendsto (θ0, z0))
  have h2 : Tendsto (fun p : (ℤ → Circle) × S2 ℤ => rotate p.1 p.2 - rotate p.1 z0) (𝓝 (θ0, z0)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_rotate_sub]
    have := ((continuous_snd.tendsto (θ0, z0)).sub_const z0).norm
    simpa using this
  have h3 := h1.add h2
  have h4 : Tendsto (fun p : (ℤ → Circle) × S2 ℤ => rotate p.1 p.2) (𝓝 (θ0, z0)) (𝓝 (rotate θ0 z0)) := by
    simpa using h3
  exact h4

/-- The action restricted to the torus `T_a`. -/
def actionOn (a : PosL1) (θ : ℤ → Circle) (z : actionTorus a) : actionTorus a :=
  ⟨rotate θ z.1, rotate_mem θ z.2⟩

theorem continuous_actionOn (a : PosL1) :
    Continuous (fun p : (ℤ → Circle) × actionTorus a => actionOn a p.1 p.2) :=
  Continuous.subtype_mk
    (continuous_rotate.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

theorem actionOn_apply_of_eq_zero (a : PosL1) (θ : ℤ → Circle) (z : actionTorus a) {n : ℤ}
    (hn : a.1 n = 0) : (actionOn a θ z).1 n = z.1 n :=
  rotate_apply_of_eq_zero θ z.2 hn

/-! ### Compactness (fixed summable tails + finite-coordinate compactness) -/

/-- The compact coordinate spheres `{p : ℤ → ℂ | ∀ n, ‖p n‖ = √a_n}` in the product topology. -/
def coordSphere (a : PosL1) : Set (ℤ → ℂ) :=
  Set.pi univ fun n => Metric.sphere (0 : ℂ) (Real.sqrt (a.1 n))

theorem isCompact_coordSphere (a : PosL1) : IsCompact (coordSphere a) :=
  isCompact_univ_pi fun _ => isCompact_sphere _ _

theorem sq_of_mem_coordSphere {a : PosL1} {p : ℤ → ℂ} (hp : p ∈ coordSphere a) (n : ℤ) :
    ‖p n‖ ^ 2 = a.1 n := by
  have h : ‖p n‖ = Real.sqrt (a.1 n) := by
    simpa using hp n (mem_univ n)
  rw [h, Real.sq_sqrt (a.2 n)]

/-- The identity from the coordinate spheres (product topology) into `ℓ²`. -/
def sphereToS2 (a : PosL1) (p : coordSphere a) : S2 ℤ :=
  ofSq a p.1 (sq_of_mem_coordSphere p.2)

theorem continuous_sphereToS2 (a : PosL1) : Continuous (sphereToS2 a) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  refine continuousAt_of_tail (sphereToS2 a) p (fun n => 4 * a.1 n)
    ((summable_posL1 a).mul_left 4) (fun q n => ?_) (fun n => ?_)
  · have hq := sq_of_mem_coordSphere q.2 n
    have hp := sq_of_mem_coordSphere p.2 n
    have hq' : ‖q.1 n‖ = Real.sqrt (a.1 n) := by simpa using q.2 n (mem_univ n)
    have hp' : ‖p.1 n‖ = Real.sqrt (a.1 n) := by simpa using p.2 n (mem_univ n)
    show ‖q.1 n - p.1 n‖ ^ 2 ≤ 4 * a.1 n
    have h1 : ‖q.1 n - p.1 n‖ ≤ 2 * Real.sqrt (a.1 n) := by
      calc ‖q.1 n - p.1 n‖ ≤ ‖q.1 n‖ + ‖p.1 n‖ := norm_sub_le _ _
        _ = 2 * Real.sqrt (a.1 n) := by rw [hq', hp']; ring
    calc ‖q.1 n - p.1 n‖ ^ 2 ≤ (2 * Real.sqrt (a.1 n)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 4 * a.1 n := by rw [mul_pow, Real.sq_sqrt (a.2 n)]; norm_num
  · exact ((continuous_apply n).comp continuous_subtype_val).continuousAt

theorem range_sphereToS2 (a : PosL1) : Set.range (sphereToS2 a) = actionTorus a := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ofSq_mem _ _ _
  · intro hz
    have hp : (z : ℤ → ℂ) ∈ coordSphere a := by
      intro n _
      have := hz n
      have h : ‖z n‖ = Real.sqrt (a.1 n) := by
        rw [← this, Real.sqrt_sq (norm_nonneg _)]
      simpa using h
    exact ⟨⟨z, hp⟩, rfl⟩

/-- **DEF-019 compactness.**  `T_a` is compact in `ℓ²`: the continuous image of the Tychonoff-compact coordinate
spheres, by the fixed-summable-tail criterion.  No angle is chosen (in particular none at zeros of `a`). -/
theorem isCompact_actionTorus (a : PosL1) : IsCompact (actionTorus a) := by
  have : CompactSpace (coordSphere a) := isCompact_iff_compactSpace.1 (isCompact_coordSphere a)
  rw [← range_sphereToS2]
  exact isCompact_range (continuous_sphereToS2 a)

/-! ### Link to the DEF-014 chart binding `a_n = |w_n|²` -/

theorem chartMasses_iff_mem_actionTorus {X : Type*} (Φ : X → S2 ℤ) (a : X → PosL1) :
    QuantumNLS.IndexedMasses.ChartMasses Φ (fun n u => (a u).1 n) ↔ ∀ u, Φ u ∈ actionTorus (a u) :=
  ⟨fun h u n => h u n, fun h u n => h u n⟩

end QuantumNLS.ActionTorus

#print axioms QuantumNLS.ActionTorus.continuousAt_of_tail
#print axioms QuantumNLS.ActionTorus.actionTorus_nonempty
#print axioms QuantumNLS.ActionTorus.rotate_mem
#print axioms QuantumNLS.ActionTorus.rotate_apply_of_eq_zero
#print axioms QuantumNLS.ActionTorus.continuous_rotate
#print axioms QuantumNLS.ActionTorus.continuous_actionOn
#print axioms QuantumNLS.ActionTorus.isCompact_actionTorus
#print axioms QuantumNLS.ActionTorus.chartMasses_iff_mem_actionTorus
