import Mathlib
import QuantumNLS.RB7Rot

/-!
# R-7B122087 `thm:hierarchy`, stage T: constant-action rotation flows on weighted sequence spaces

Abstract sequence-side half of the printed proof (nothing here uses REG-015, DEF-024 or any chart).  Given rotation-invariant
frequency data `Ω_r(z)_j` (as produced by `RB7Rot.freq` for rotation-invariant `C²` functionals `F_r`), the printed flows are
`z_j(t) = e^{-i t ω_{r,j}(z)} z_j`.  This module proves, for arbitrary finite families (printed "every finite family of these flows
commutes"), arbitrary positive weights `V`:

* `flow` is a group in the joint time vector, finite families commute, every coordinate modulus is constant and every
  rotation-invariant function is conserved (`flow_add`, `flow_comm`, `norm_flow_val`, `flow_invariant`);
* the full orbit lies in the modulus torus `{rot u z}` and the modulus torus is compact in every weighted norm
  (`isCompact_torus`: "full modulus tori are compact ... by uniform tails and finite-dimensional compactness");
* joint continuity of `(t, z) ↦ flow t z` in the weighted norm, hence uniform continuity on compact time boxes and compact initial classes
  (`continuous_flow`): coordinatewise convergence plus convergence of the (rotation-invariant) norm (`continuousAt_of_coords`);
* time smoothness (`curve_contDiff`): for a fixed `z` all of whose weighted `ν`-moments `Σ V_j ν_j^{2k}|z_j|²` are finite, the curve
  `t ↦ (e^{-itν_j} z_j)_j` is `C^∞` into `WSeq V`, with `∂_t^k` given by `(-iν_j)^k e^{-itν_j} z_j` (printed "every time derivative is controlled by a fixed
  polynomial weight times the rapidly decreasing initial sequence").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

variable {V : PosWeight}

/-! ## Coordinatewise convergence plus norm convergence -/

theorem norm_sq_le_head (a b : WSeq V) (S : Finset ℤ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 +
      ∑ j ∈ S, (V.w j * ‖a.val j - b.val j‖ ^ 2 - 2 * (V.w j * ‖a.val j‖ ^ 2) -
        2 * (V.w j * ‖b.val j‖ ^ 2)) := by
  classical
  have hab : HasSum (fun n => V.w n * ‖a.val n - b.val n‖ ^ 2) (‖a - b‖ ^ 2) := hasSum_norm_sq V (a - b)
  have ha := hasSum_norm_sq V a
  have hb := hasSum_norm_sq V b
  set c : ℤ → ℝ := fun j => V.w j * ‖a.val j - b.val j‖ ^ 2 - 2 * (V.w j * ‖a.val j‖ ^ 2) -
    2 * (V.w j * ‖b.val j‖ ^ 2) with hc
  have hS : HasSum (fun j => if j ∈ S then c j else 0) (∑ j ∈ S, c j) := by
    have : HasSum (fun j => if j ∈ S then c j else 0) (∑ j ∈ S, (if j ∈ S then c j else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by simp [hj])
    rwa [Finset.sum_congr rfl (fun j hj => if_pos hj)] at this
  have hh := ((ha.mul_left 2).add (hb.mul_left 2)).add hS
  refine hasSum_le (fun j => ?_) hab hh
  by_cases hj : j ∈ S
  · simp only [hj, if_true, hc]; linarith
  · simp only [hj, if_false]
    have h1 : ‖a.val j - b.val j‖ ^ 2 ≤ 2 * ‖a.val j‖ ^ 2 + 2 * ‖b.val j‖ ^ 2 := by
      nlinarith [norm_sub_le (a.val j) (b.val j), norm_nonneg (a.val j - b.val j), norm_nonneg (a.val j),
        norm_nonneg (b.val j), sq_nonneg (‖a.val j‖ - ‖b.val j‖)]
    have := mul_le_mul_of_nonneg_left h1 (V.pos j).le
    linarith

theorem continuousAt_of_coords {X : Type*} [TopologicalSpace X] (g : X → WSeq V) (x₀ : X)
    (hc : ∀ j, ContinuousAt (fun x => (g x).val j) x₀) (hn : ContinuousAt (fun x => ‖g x‖) x₀) :
    ContinuousAt g x₀ := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h0 : Tendsto (fun s : Finset ℤ => ∑ j ∈ s, V.w j * ‖(g x₀).val j‖ ^ 2) atTop (𝓝 (‖g x₀‖ ^ 2)) :=
    hasSum_norm_sq V (g x₀)
  have hε8 : 0 < ε ^ 2 / 8 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h0 (ε ^ 2 / 8) hε8
  have hS := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at hS
  set Φ : X → ℝ := fun x => 2 * ‖g x‖ ^ 2 + 2 * ‖g x₀‖ ^ 2 +
    ∑ j ∈ N, (V.w j * ‖(g x).val j - (g x₀).val j‖ ^ 2 - 2 * (V.w j * ‖(g x).val j‖ ^ 2) -
      2 * (V.w j * ‖(g x₀).val j‖ ^ 2)) with hΦ
  have hΦc : ContinuousAt Φ x₀ := by
    have h1 : ContinuousAt (fun x => 2 * ‖g x‖ ^ 2) x₀ := (hn.pow 2).const_mul 2
    have h2 : Tendsto (fun x => ∑ j ∈ N, (V.w j * ‖(g x).val j - (g x₀).val j‖ ^ 2 -
        2 * (V.w j * ‖(g x).val j‖ ^ 2) - 2 * (V.w j * ‖(g x₀).val j‖ ^ 2))) (𝓝 x₀)
        (𝓝 (∑ j ∈ N, (V.w j * ‖(g x₀).val j - (g x₀).val j‖ ^ 2 -
        2 * (V.w j * ‖(g x₀).val j‖ ^ 2) - 2 * (V.w j * ‖(g x₀).val j‖ ^ 2)))) := by
      refine tendsto_finsetSum N (fun j _ => ?_)
      have a1 : ContinuousAt (fun x => V.w j * ‖(g x).val j - (g x₀).val j‖ ^ 2) x₀ :=
        (((hc j).sub continuousAt_const).norm.pow 2).const_mul _
      have a2 : ContinuousAt (fun x => 2 * (V.w j * ‖(g x).val j‖ ^ 2)) x₀ :=
        (((hc j).norm.pow 2).const_mul _).const_mul _
      exact (a1.sub a2).sub continuousAt_const
    exact (h1.add continuousAt_const).add h2
  have hΦ0 : Φ x₀ < ε ^ 2 / 2 := by
    have : Φ x₀ = 4 * (‖g x₀‖ ^ 2 - ∑ j ∈ N, V.w j * ‖(g x₀).val j‖ ^ 2) := by
      simp only [hΦ, sub_self, norm_zero]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring
    rw [this]; linarith [hS.1, hS.2]
  have hev : ∀ᶠ x in 𝓝 x₀, Φ x < ε ^ 2 := by
    have := hΦc.eventually (gt_mem_nhds (show Φ x₀ < ε ^ 2 by nlinarith [hΦ0, sq_nonneg ε]))
    exact this
  filter_upwards [hev] with x hx
  have hle := norm_sq_le_head (g x) (g x₀) N
  have : ‖g x - g x₀‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt hle hx
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

/-! ## The modulus torus -/

theorem continuous_rot_u (z : WSeq V) : Continuous fun u : ℤ → Circle => rot u z := by
  rw [continuous_iff_continuousAt]
  intro u₀
  refine continuousAt_of_coords _ u₀ (fun j => ?_) ?_
  · simp only [rot_val]
    exact (continuous_subtype_val.comp (continuous_apply j)).mul continuous_const |>.continuousAt
  · simp only [norm_rot]; exact continuousAt_const

/-- The full modulus torus of `z` is compact in the weighted norm (uniform tails + Tychonoff). -/
theorem isCompact_torus (z : WSeq V) : IsCompact (Set.range fun u : ℤ → Circle => rot u z) :=
  isCompact_range (continuous_rot_u z)

/-! ## Rotation flows -/

/-- Rotation-invariant frequency data on `WSeq V`, for a family indexed by `ι`. -/
structure FreqData (V : PosWeight) (ι : Type) where
  Ω : ι → WSeq V → ℤ → ℝ
  inv : ∀ r u z j, Ω r (rot u z) j = Ω r z j
  cont : ∀ r (z : WSeq V) j, z.val j ≠ 0 → ContinuousAt (fun y => Ω r y j) z

variable {ι : Type} [Fintype ι]

/-- The rotation angle `-Σ_r t_r Ω_{r,j}(z)`. -/
def angle (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) (j : ℤ) : ℝ := -∑ r, t r * D.Ω r z j

def flowU (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) : ℤ → Circle := fun j => Circle.exp (angle D t z j)

/-- The joint flow `z_j ↦ e^{-i Σ_r t_r Ω_{r,j}(z)} z_j`. -/
def flow (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) : WSeq V := rot (flowU D t z) z

theorem angle_rot (D : FreqData V ι) (t : ι → ℝ) (u : ℤ → Circle) (z : WSeq V) (j : ℤ) :
    angle D t (rot u z) j = angle D t z j := by
  simp [angle, D.inv]

theorem angle_add (D : FreqData V ι) (t s : ι → ℝ) (z : WSeq V) (j : ℤ) :
    angle D (t + s) z j = angle D t z j + angle D s z j := by
  simp only [angle, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring

theorem flowU_add (D : FreqData V ι) (t s : ι → ℝ) (z : WSeq V) :
    flowU D (t + s) z = flowU D t z * flowU D s z := by
  funext j
  simp only [flowU, angle_add, Circle.exp_add, Pi.mul_apply]

theorem flow_zero (D : FreqData V ι) (z : WSeq V) : flow D 0 z = z := by
  have : flowU D 0 z = 1 := by
    funext j; simp [flowU, angle]
  rw [flow, this, rot_one]

theorem flow_add (D : FreqData V ι) (t s : ι → ℝ) (z : WSeq V) :
    flow D (t + s) z = flow D t (flow D s z) := by
  have h1 : flowU D t (flow D s z) = flowU D t z := by
    funext j; simp only [flowU, flow, angle_rot]
  calc flow D (t + s) z = rot (flowU D t z * flowU D s z) z := by rw [flow, flowU_add]
    _ = rot (flowU D t z) (rot (flowU D s z) z) := by rw [rot_rot]
    _ = rot (flowU D t (flow D s z)) (flow D s z) := by rw [h1]; rfl
    _ = flow D t (flow D s z) := rfl

theorem flow_comm (D : FreqData V ι) (t s : ι → ℝ) (z : WSeq V) :
    flow D t (flow D s z) = flow D s (flow D t z) := by
  rw [← flow_add, ← flow_add, add_comm]

theorem freq_flow (D : FreqData V ι) (r : ι) (t : ι → ℝ) (z : WSeq V) (j : ℤ) :
    D.Ω r (flow D t z) j = D.Ω r z j := D.inv r _ z j

theorem norm_flow_val (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) (j : ℤ) :
    ‖(flow D t z).val j‖ = ‖z.val j‖ := by simp [flow]

theorem norm_flow (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) : ‖flow D t z‖ = ‖z‖ := norm_rot _ _

/-- Every rotation-invariant quantity is conserved. -/
theorem flow_invariant {α : Type*} (D : FreqData V ι) (G : WSeq V → α) (hG : ∀ u z, G (rot u z) = G z)
    (t : ι → ℝ) (z : WSeq V) : G (flow D t z) = G z := hG _ z

theorem flow_mem_torus (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) :
    flow D t z ∈ Set.range fun u : ℤ → Circle => rot u z := ⟨flowU D t z, rfl⟩

theorem isCompact_orbit (D : FreqData V ι) (z : WSeq V) :
    IsCompact (closure (Set.range fun t : ι → ℝ => flow D t z)) := by
  have hsub : Set.range (fun t : ι → ℝ => flow D t z) ⊆ Set.range fun u : ℤ → Circle => rot u z :=
    fun _ ⟨t, ht⟩ => ht ▸ flow_mem_torus D t z
  exact (isCompact_torus z).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isCompact_torus z).isClosed)

theorem flow_val (D : FreqData V ι) (t : ι → ℝ) (z : WSeq V) (j : ℤ) :
    (flow D t z).val j = Complex.exp (((angle D t z j : ℝ) : ℂ) * Complex.I) * z.val j := by
  simp [flow, flowU, Circle.coe_exp]

/-- **Joint continuity** of `(t, z) ↦ flow t z` in the weighted norm. -/
theorem continuous_flow (D : FreqData V ι) :
    Continuous fun p : (ι → ℝ) × WSeq V => flow D p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro x₀
  refine continuousAt_of_coords _ x₀ (fun j => ?_) ?_
  · simp only [flow_val]
    by_cases hz : x₀.2.val j = 0
    · have hf : Complex.exp (((angle D x₀.1 x₀.2 j : ℝ) : ℂ) * Complex.I) * x₀.2.val j = 0 := by
        rw [hz, mul_zero]
      rw [ContinuousAt, hf, tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ p : (ι → ℝ) × WSeq V,
          ‖Complex.exp (((angle D p.1 p.2 j : ℝ) : ℂ) * Complex.I) * p.2.val j‖ = ‖p.2.val j‖ := by
        intro p; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      simp only [hnorm]
      have := ((continuous_val j).comp continuous_snd).continuousAt (x := x₀)
      have h2 := this.norm
      rw [ContinuousAt] at h2
      simpa [hz] using h2
    · have hang : ContinuousAt (fun p : (ι → ℝ) × WSeq V => angle D p.1 p.2 j) x₀ := by
        unfold angle
        refine ContinuousAt.neg ?_
        have : Tendsto (fun p : (ι → ℝ) × WSeq V => ∑ r, p.1 r * D.Ω r p.2 j) (𝓝 x₀)
            (𝓝 (∑ r, x₀.1 r * D.Ω r x₀.2 j)) := by
          refine tendsto_finsetSum Finset.univ (fun r _ => ?_)
          have c1 : ContinuousAt (fun p : (ι → ℝ) × WSeq V => p.1 r) x₀ :=
            ((continuous_apply r).comp continuous_fst).continuousAt
          have c2 : ContinuousAt (fun p : (ι → ℝ) × WSeq V => D.Ω r p.2 j) x₀ :=
            (D.cont r x₀.2 j hz).comp (continuous_snd.continuousAt)
          exact c1.mul c2
        exact this
      have c3 : ContinuousAt (fun p : (ι → ℝ) × WSeq V => p.2.val j) x₀ :=
        ((continuous_val j).comp continuous_snd).continuousAt
      exact (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp hang).mul continuousAt_const)).mul c3
  · simp only [norm_flow]
    exact (continuous_snd.norm).continuousAt

/-! ## Time smoothness of a rotating sequence -/

section Curve

variable (ν : ℤ → ℝ) (z : WSeq V)

/-- `(-iν_j)^k e^{-itν_j} z_j`. -/
def coef (k : ℕ) (t : ℝ) (j : ℤ) : ℂ :=
  (-Complex.I * (ν j : ℂ)) ^ k * Complex.exp (((-(t * ν j) : ℝ) : ℂ) * Complex.I) * z.val j

theorem abs_pow_sq (x : ℝ) (k : ℕ) : (|x| ^ k) ^ 2 = x ^ (2 * k) := by
  rw [← pow_mul, mul_comm, pow_mul, sq_abs, ← pow_mul]

theorem norm_coef (k : ℕ) (t : ℝ) (j : ℤ) : ‖coef ν z k t j‖ = |ν j| ^ k * ‖z.val j‖ := by
  unfold coef
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp

variable {ν z}

theorem coef_summable (hz : ∀ k : ℕ, Summable fun j => V.w j * ν j ^ (2 * k) * ‖z.val j‖ ^ 2) (k : ℕ)
    (t : ℝ) : Summable fun j => V.w j * ‖coef ν z k t j‖ ^ 2 := by
  refine (hz k).congr fun j => ?_
  rw [norm_coef, mul_pow, abs_pow_sq, mul_assoc]

/-- The `k`-th time derivative candidate as an element of `WSeq V`. -/
def dcurve (hz : ∀ k : ℕ, Summable fun j => V.w j * ν j ^ (2 * k) * ‖z.val j‖ ^ 2) (k : ℕ) (t : ℝ) :
    WSeq V := WSeq.mk V (coef ν z k t) (coef_summable hz k t)

theorem norm_exp_sub_one_add_le (x : ℝ) :
    ‖Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 1 + (x : ℂ) * Complex.I‖ ≤ 3 * x ^ 2 := by
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := ((-x : ℝ) : ℂ) * Complex.I)
      (by simpa using hx)
    have e : ((-x : ℝ) : ℂ) * Complex.I = -((x : ℂ) * Complex.I) := by push_cast; ring
    rw [e] at h
    have h2 : ‖-((x : ℂ) * Complex.I)‖ ^ 2 = x ^ 2 := by simp
    have e2 : Complex.exp (-((x : ℂ) * Complex.I)) - 1 - -((x : ℂ) * Complex.I) =
        Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 1 + (x : ℂ) * Complex.I := by push_cast; ring_nf
    rw [e2, h2] at h
    nlinarith [sq_nonneg x]
  · push_neg at hx
    have h1 : ‖Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 1 + (x : ℂ) * Complex.I‖ ≤ 2 + |x| := by
      calc _ ≤ ‖Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 1‖ + ‖(x : ℂ) * Complex.I‖ := norm_add_le _ _
        _ ≤ (‖Complex.exp (((-x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) + ‖(x : ℂ) * Complex.I‖ := by
            gcongr; exact norm_sub_le _ _
        _ = 2 + |x| := by
            rw [Complex.norm_exp_ofReal_mul_I]; simp; ring
    have h3 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [abs_nonneg x]

theorem hasDerivAt_dcurve (hz : ∀ k : ℕ, Summable fun j => V.w j * ν j ^ (2 * k) * ‖z.val j‖ ^ 2)
    (k : ℕ) (t : ℝ) : HasDerivAt (fun t => dcurve hz k t) (dcurve hz (k + 1) t) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  set A : ℝ := ∑' j, V.w j * ν j ^ (2 * (k + 2)) * ‖z.val j‖ ^ 2 with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun j =>
    mul_nonneg (mul_nonneg (V.pos j).le (Even.pow_nonneg (even_two_mul _) _)) (sq_nonneg _)
  have hbound : ∀ h : ℝ, ‖dcurve hz k (t + h) - dcurve hz k t - h • dcurve hz (k + 1) t‖ ≤
      (3 * Real.sqrt A) * ‖h ^ 2‖ := by
    intro h
    set X := dcurve hz k (t + h) - dcurve hz k t - h • dcurve hz (k + 1) t with hX
    have hXj : ∀ j, X.val j = coef ν z k t j *
        (Complex.exp (((-(h * ν j) : ℝ) : ℂ) * Complex.I) - 1 + ((h * ν j : ℝ) : ℂ) * Complex.I) := by
      intro j
      have hs : (h • dcurve hz (k + 1) t).val j = (h : ℂ) * coef ν z (k + 1) t j := by
        rw [← Complex.coe_smul]; rfl
      simp only [hX, WSeq.val_sub, Pi.sub_apply, hs]
      show coef ν z k (t + h) j - coef ν z k t j - (h : ℂ) * coef ν z (k + 1) t j = _
      simp only [coef, pow_succ]
      have e : Complex.exp (((-((t + h) * ν j) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-(t * ν j) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((-(h * ν j) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e]; push_cast; ring
    have hterm : ∀ j, V.w j * ‖X.val j‖ ^ 2 ≤ 9 * h ^ 4 * (V.w j * ν j ^ (2 * (k + 2)) * ‖z.val j‖ ^ 2) := by
      intro j
      rw [hXj, norm_mul, norm_coef]
      have h1 := norm_exp_sub_one_add_le (h * ν j)
      have h2 : ‖Complex.exp (((-(h * ν j) : ℝ) : ℂ) * Complex.I) - 1 + ((h * ν j : ℝ) : ℂ) * Complex.I‖ ≤
          3 * (h * ν j) ^ 2 := by simpa using h1
      have h3 : ‖z.val j‖ ≥ 0 := norm_nonneg _
      have h4 : |ν j| ^ k * ‖z.val j‖ * ‖Complex.exp (((-(h * ν j) : ℝ) : ℂ) * Complex.I) - 1 +
          ((h * ν j : ℝ) : ℂ) * Complex.I‖ ≤ |ν j| ^ k * ‖z.val j‖ * (3 * (h * ν j) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h5 : (|ν j| ^ k * ‖z.val j‖ * ‖Complex.exp (((-(h * ν j) : ℝ) : ℂ) * Complex.I) - 1 +
          ((h * ν j : ℝ) : ℂ) * Complex.I‖) ^ 2 ≤ (|ν j| ^ k * ‖z.val j‖ * (3 * (h * ν j) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h4 2
      have h6 : (|ν j| ^ k * ‖z.val j‖ * (3 * (h * ν j) ^ 2)) ^ 2 =
          9 * h ^ 4 * (ν j ^ (2 * (k + 2)) * ‖z.val j‖ ^ 2) := by
        have : (|ν j| ^ k) ^ 2 = ν j ^ (2 * k) := abs_pow_sq _ _
        calc (|ν j| ^ k * ‖z.val j‖ * (3 * (h * ν j) ^ 2)) ^ 2
            = (|ν j| ^ k) ^ 2 * ‖z.val j‖ ^ 2 * (9 * h ^ 4 * ν j ^ 4) := by ring
          _ = 9 * h ^ 4 * (ν j ^ (2 * (k + 2)) * ‖z.val j‖ ^ 2) := by rw [this]; ring
      have := mul_le_mul_of_nonneg_left (h5.trans_eq h6) (V.pos j).le
      linarith
    have hsum : ‖X‖ ^ 2 ≤ 9 * h ^ 4 * A :=
      hasSum_le hterm (hasSum_norm_sq V X) ((hz (k + 2)).hasSum.mul_left (9 * h ^ 4))
    have hb : 0 ≤ (3 * Real.sqrt A) * ‖h ^ 2‖ := by positivity
    refine le_of_sq_le_sq' hb ?_
    have hn : ‖h ^ 2‖ ^ 2 = h ^ 4 := by rw [Real.norm_eq_abs, sq_abs]; ring
    have : ((3 * Real.sqrt A) * ‖h ^ 2‖) ^ 2 = 9 * h ^ 4 * A := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA0, hn]; ring
    rw [this]; exact hsum
  have hO : (fun h : ℝ => dcurve hz k (t + h) - dcurve hz k t - h • dcurve hz (k + 1) t) =O[𝓝 0]
      fun h : ℝ => h ^ 2 :=
    Asymptotics.IsBigO.of_bound (3 * Real.sqrt A) (Eventually.of_forall hbound)
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

theorem iteratedDeriv_dcurve (hz : ∀ k : ℕ, Summable fun j => V.w j * ν j ^ (2 * k) * ‖z.val j‖ ^ 2)
    (m : ℕ) : iteratedDeriv m (fun t : ℝ => dcurve hz 0 t) = fun t => dcurve hz m t := by
  induction m with
  | zero => exact iteratedDeriv_zero
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_dcurve hz m t).deriv

/-- **Time smoothness**: the rotating curve is `C^∞` into `WSeq V`. -/
theorem curve_contDiff (hz : ∀ k : ℕ, Summable fun j => V.w j * ν j ^ (2 * k) * ‖z.val j‖ ^ 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => dcurve hz 0 t) := by
  refine contDiff_of_differentiable_iteratedDeriv (fun m _ => ?_)
  rw [iteratedDeriv_dcurve hz m]
  exact fun t => (hasDerivAt_dcurve hz m t).differentiableAt

end Curve

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.continuous_flow
#print axioms QuantumNLS.RB7.isCompact_torus
#print axioms QuantumNLS.RB7.flow_add
#print axioms QuantumNLS.RB7.curve_contDiff
