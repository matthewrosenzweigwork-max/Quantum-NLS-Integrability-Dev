import QuantumNLS.RealAnalyticDef
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Complexified analytic infrastructure, stage X1: real power series with complex-multilinear terms

Generic, unconditional. For complex normed spaces `E`, `W` (with compatible real structures):
* `norm_eq_of_coe_eq`: a complex and a real continuous multilinear map with the same values have the same operator
  norm;
* `hasFPowerSeriesOnBall_of_coe_eq`: if `f` has a real power series `p` at `x` on `B(x,r)` and every `p n` agrees
  pointwise with a complex continuous multilinear map `q n`, then `f` has the complex power series `q` on the same
  ball; in particular `f` is complex analytic there;
* `IsCHom` (homogeneity in each slot under complex scalars), `liftC` (a real continuous multilinear map that is
  `IsCHom` as a complex continuous multilinear map, same values), and `symC_isCHom` (the symmetrization
  `RealAnalyticDef.symC` preserves `IsCHom`).
This is the input for complex analyticity of the DEF-014 Volterra series when the coefficient depends complex-linearly
on the parameter (stage X2 `ComplexifiedVolterra`).
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal

namespace QuantumNLS.ComplexifiedSeriesLift

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ W] in
theorem norm_eq_of_coe_eq {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) W)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W) (h : ∀ m, q m = p m) : ‖q‖ = ‖p‖ :=
  le_antisymm (q.opNorm_le_bound (norm_nonneg _) fun m => by rw [h]; exact p.le_opNorm m)
    (p.opNorm_le_bound (norm_nonneg _) fun m => by rw [← h]; exact q.le_opNorm m)

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ W] in
theorem radius_eq_of_coe_eq (q : FormalMultilinearSeries ℂ E W) (p : FormalMultilinearSeries ℝ E W)
    (h : ∀ n m, q n m = p n m) : q.radius = p.radius := by
  have hn : ∀ n, ‖q n‖ = ‖p n‖ := fun n => norm_eq_of_coe_eq _ _ (h n)
  simp only [FormalMultilinearSeries.radius, hn]

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ W] in
/-- A real power series whose terms are complex multilinear is a complex power series. -/
theorem hasFPowerSeriesOnBall_of_coe_eq {f : E → W} {x : E} {r : ℝ≥0∞} (q : FormalMultilinearSeries ℂ E W)
    (p : FormalMultilinearSeries ℝ E W) (h : ∀ n m, q n m = p n m) (hp : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall f q x r where
  r_le := (radius_eq_of_coe_eq q p h).symm ▸ hp.r_le
  r_pos := hp.r_pos
  hasSum := fun {y} hy => by simpa only [h] using hp.hasSum hy

/-- Homogeneity under complex scalars in each slot. -/
def IsCHom {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W) : Prop :=
  ∀ (m : Fin n → E) (i : Fin n) (c : ℂ) (x : E),
    p (Function.update m i (c • x)) = c • p (Function.update m i x)

/-- A real continuous multilinear map that is homogeneous under complex scalars, as a complex continuous
multilinear map with the same values. -/
def liftC {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W) (hp : IsCHom p) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) W where
  toFun := p
  map_update_add' m i x y := by convert p.map_update_add m i x y
  map_update_smul' m i c x := by convert hp m i c x
  cont := p.cont

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ W] in
@[simp] theorem liftC_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W) (hp : IsCHom p)
    (m : Fin n → E) : liftC p hp m = p m := rfl

omit [IsScalarTower ℝ ℂ E] in
/-- The symmetrization preserves homogeneity under complex scalars. -/
theorem symC_isCHom {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W) (hA : IsCHom A) :
    IsCHom (RealAnalyticDef.symC A) := by
  intro m i c x
  rw [RealAnalyticDef.symC_apply_eq, RealAnalyticDef.symC_apply_eq, RealAnalyticDef.symM_apply,
    RealAnalyticDef.symM_apply]
  have e1 : ∀ (σ : Equiv.Perm (Fin n)) (y : E),
      (fun k => Function.update m i y (σ k)) = Function.update (fun k => m (σ k)) (σ.symm i) y :=
    fun σ y => Function.update_comp_equiv m σ i y
  have key : ∀ σ : Equiv.Perm (Fin n),
      A.toMultilinearMap (fun k => Function.update m i (c • x) (σ k)) =
        c • A.toMultilinearMap (fun k => Function.update m i x (σ k)) := fun σ => by
    rw [e1 σ (c • x), e1 σ x]
    exact hA _ _ c x
  simp only [key, ← Finset.smul_sum]
  exact smul_comm _ _ _

end QuantumNLS.ComplexifiedSeriesLift

#print axioms QuantumNLS.ComplexifiedSeriesLift.norm_eq_of_coe_eq
#print axioms QuantumNLS.ComplexifiedSeriesLift.hasFPowerSeriesOnBall_of_coe_eq
#print axioms QuantumNLS.ComplexifiedSeriesLift.liftC
#print axioms QuantumNLS.ComplexifiedSeriesLift.symC_isCHom
