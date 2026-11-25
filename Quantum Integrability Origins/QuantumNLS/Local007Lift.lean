import Mathlib

/-! LOCAL-007 stage L: pointwise (Nemytskii) lifting of a power series to bounded continuous functions.

If `G : E → F` has the power series `p` at `0` with radius `r`, then the pointwise composition
`ê ↦ (t ↦ G (ê t))` on `T →ᵇ E` has the lifted series `p̂_n (m_1,…,m_n) (t) = p_n (m_1 t,…,m_n t)` with
`‖p̂_n‖ ≤ ‖p_n‖`, hence at least the same radius, and its sum agrees pointwise with `G ∘ ê` on the ball.
Used for (a) bounded continuous functions on a contour (spectral variable as a function) and (b) the
`ℓ∞(ℤ)`-valued family obtained from one power series by the index isometries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Local007Lift

variable {T : Type*} [TopologicalSpace T]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section
variable {n : ℕ}

theorem update_eval [DecidableEq (Fin n)] (m : Fin n → (T →ᵇ E)) (i : Fin n) (x : T →ᵇ E) (t : T) :
    (fun j => (Function.update m i x j) t) = Function.update (fun j => m j t) i (x t) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem bound_pt (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (m : Fin n → (T →ᵇ E)) (t : T) :
    ‖p (fun i => m i t)‖ ≤ ‖p‖ * ∏ i, ‖m i‖ := by
  refine (p.le_opNorm _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (m i).norm_coe_le_norm t)

/-- The pointwise value of the lifted multilinear map. -/
def liftFun (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (m : Fin n → (T →ᵇ E)) : T →ᵇ F :=
  ofNormedAddCommGroup (fun t => p (fun i => m i t))
    (p.cont.comp (continuous_pi fun i => (m i).continuous))
    (‖p‖ * ∏ i, ‖m i‖) (fun t => bound_pt p m t)

theorem liftFun_apply (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (m : Fin n → (T →ᵇ E))
    (t : T) : liftFun p m t = p (fun i => m i t) := rfl

def liftMultiAlg (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    MultilinearMap ℝ (fun _ : Fin n => T →ᵇ E) (T →ᵇ F) where
  toFun := liftFun p
  map_update_add' := by
    intro _ m i x y
    ext t
    change p (fun j => (Function.update m i (x + y) j) t) =
      p (fun j => (Function.update m i x j) t) + p (fun j => (Function.update m i y j) t)
    rw [update_eval m i (x + y) t, update_eval m i x t, update_eval m i y t,
      BoundedContinuousFunction.add_apply]
    exact p.map_update_add _ _ _ _
  map_update_smul' := by
    intro _ m i c x
    ext t
    change p (fun j => (Function.update m i (c • x) j) t) =
      c • p (fun j => (Function.update m i x j) t)
    rw [update_eval m i (c • x) t, update_eval m i x t, BoundedContinuousFunction.smul_apply]
    exact p.map_update_smul _ _ _ _

/-- The lifted continuous multilinear map, of norm at most `‖p‖`. -/
def liftMulti (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => T →ᵇ E) (T →ᵇ F) :=
  (liftMultiAlg p).mkContinuous ‖p‖ (fun m =>
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => bound_pt p m t)

theorem liftMulti_apply (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (m : Fin n → (T →ᵇ E))
    (t : T) : liftMulti p m t = p (fun i => m i t) := rfl

theorem norm_liftMulti_le (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) :
    ‖(liftMulti p : ContinuousMultilinearMap ℝ (fun _ : Fin n => T →ᵇ E) (T →ᵇ F))‖ ≤ ‖p‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
end

/-- The lifted formal multilinear series. -/
def liftSeries (p : FormalMultilinearSeries ℝ E F) : FormalMultilinearSeries ℝ (T →ᵇ E) (T →ᵇ F) :=
  fun n => liftMulti (p n)

theorem radius_le_liftSeries (p : FormalMultilinearSeries ℝ E F) :
    p.radius ≤ (liftSeries (T := T) p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  exact (liftSeries (T := T) p).le_radius_of_bound C fun n =>
    (mul_le_mul_of_nonneg_right (norm_liftMulti_le (p n)) (by positivity)).trans (hC n)

variable [CompleteSpace F]

theorem hasFPowerSeriesOnBall_lift {G : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall G p 0 r) :
    HasFPowerSeriesOnBall (liftSeries (T := T) p).sum (liftSeries (T := T) p) 0 r := by
  have hr : r ≤ (liftSeries (T := T) p).radius := h.r_le.trans (radius_le_liftSeries p)
  refine ⟨hr, h.r_pos, fun {y} hy => ?_⟩
  rw [zero_add]
  exact (liftSeries (T := T) p).hasSum (lt_of_lt_of_le hy hr)

theorem lift_sum_apply {G : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall G p 0 r) (ê : T →ᵇ E) (hê : ((‖ê‖₊ : ℝ≥0) : ℝ≥0∞) < r) (t : T) :
    (liftSeries (T := T) p).sum ê t = G (ê t) := by
  have hr : r ≤ (liftSeries (T := T) p).radius := h.r_le.trans (radius_le_liftSeries p)
  have hmem : ê ∈ Metric.eball (0 : T →ᵇ E) (liftSeries (T := T) p).radius := by
    rw [Metric.mem_eball, edist_zero_right]; exact lt_of_lt_of_le hê hr
  have h1 := (liftSeries (T := T) p).hasSum hmem
  have h2 := (BoundedContinuousFunction.evalCLM ℝ t).hasSum h1
  have hmem' : ê t ∈ Metric.eball (0 : E) r := by
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_le_of_lt ?_ hê
    exact_mod_cast (ê.norm_coe_le_norm t)
  have h3 := h.hasSum hmem'
  rw [zero_add] at h3
  exact h2.unique h3

end QuantumNLS.Local007Lift
#print axioms QuantumNLS.Local007Lift.hasFPowerSeriesOnBall_lift
#print axioms QuantumNLS.Local007Lift.lift_sum_apply
