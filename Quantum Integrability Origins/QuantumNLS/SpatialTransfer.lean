import Mathlib
import QuantumNLS.EmpiricalRapidity

/-!
# DEF-013: quantum-derived spatial transfer and boundary phase

Source: `DEFINITIONS_LEDGER.md:269` (DEF-013), `chapters/definitions.tex`, `def:report-13`.  Ledger text:
the spatial matrix solves `M_x = [[−iz/2, √κ ū],[√κ u, iz/2]] M`, `M(0,z) = 1`; its trace at one period is
`Δ_u(z)`; the selected phase is `γ_u(z) = Lz/2 − κ G_{M_{κ,u}}(z)` in the upper half-plane; its positive
imaginary part and `2 cos γ_u = Δ_u` are proved from the quantum transfer limit; the unbalanced convention
(entries `κ ū`, `u`) satisfies `M_bal = D⁻¹ M_unbal D`, `D = diag(κ^{1/4}, κ^{−1/4})`, hence equal traces.

## What is realized
* **Class of `u`.**  A continuous representative `u : ℝ → ℂ` (smooth profiles, or the continuous
  representative of an `H¹(𝕋_L)` profile, extended periodically).  This is the class on which the
  fundamental solution is a classical `C¹` solution and its uniqueness is a theorem
  (`IsFundamental.unique`, via `ODE_solution_unique_of_mem_Ioo`, the coefficient being bounded on compacts).
  For `u ∈ L² \ H¹` the solution is an absolutely continuous (Carathéodory) solution of the integral equation
  `M(x) = 1 + ∫₀ˣ A M`; that `L¹`-coefficient theory is **not** formalized here (gap, stated below).
* **Fundamental solution** `IsFundamental A M : M 0 = 1 ∧ ∀ x, HasDerivAt M (A x * M x) x` for
  `Mat2 = Matrix (Fin 2) (Fin 2) ℂ` with the `ℓ^∞`-operator norm; `coef p q u z` is
  `[[−iz/2, p ū],[q u, iz/2]]`, `balCoef` has `(p,q) = (√κ,√κ)`, `unbalCoef` has `(κ,1)`.
  `spatialTransfer κ u z` is the (unique, `IsFundamental.unique`) solution, chosen when it exists
  (`spatialTransfer_spec`); `discriminant L κ u z = trace M(L,z)` (`discriminant_eq_trace`).
* **Gauge identity (proved, part of the definition text).**  `Dinv_unbalCoef_Dm`:
  `D⁻¹ A_unbal D = A_bal`; `IsFundamental.gauge`; `bal_eq_gauge : M_bal = D⁻¹ M_unbal D`; and
  `trace_bal_eq_trace_unbal`: equal traces, for continuous `u`, `κ > 0`.
* **Boundary phase** `boundaryPhase L κ M z = L z/2 − κ G_M(z)`, *parametric in a finite positive measure
  `M`* (the DEF-010 full-mass limiting measure `M_{κ,u}`, named but not constructed in the source), with
  `G_M = EmpiricalRapidity.cauchyTransform` (DEF-010).  `im_boundaryPhase_pos`: for `L, κ > 0`, `M ≠ 0` finite
  and `Im z > 0`, `Im γ > 0`, *proved* from DEF-010's sign lemma `Im G_M < 0` (so it holds for every such
  `M`, not only the transfer-limit one).
* `QuantumTransferIdentity L κ u M z` is the *proposition* `2 cos γ_u = Δ_u`.  The ledger states it (and the
  positivity of `Im γ_u` for the true `M_{κ,u}`) as proved **from the quantum transfer limit**, i.e. a theorem
  elsewhere; it is neither assumed nor proved here.

## Gaps
* Existence of the fundamental solution is not proved here: for continuous `u` it is the classical Picard
  existence theorem for linear systems with continuous coefficients, not formalized (Mathlib's
  Picard–Lindelöf is local with a smallness condition `L·T ≤ r`, and no global linear-system existence
  theorem is available).  `spatialTransfer_spec` and `discriminant_eq_trace` therefore carry the explicit
  hypothesis that a solution exists; uniqueness, the gauge identity and the traces are unconditional on it
  (they are statements about any two solutions).
* `L¹`/`L²`-adapted absolutely continuous solutions: not formalized (above).
* The full-mass measure `M_{κ,u}` itself (DEF-010 limit) is a parameter.
-/

set_option autoImplicit false

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.SpatialTransfer

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Coefficient matrix `[[-iz/2, p ū(x)], [q u(x), iz/2]]`: balanced `(p,q) = (√κ,√κ)`, unbalanced
`(p,q) = (κ,1)`. -/
def coef (p q : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) : Mat2 :=
  !![-(Complex.I * z) / 2, (p : ℂ) * conj (u x); (q : ℂ) * u x, Complex.I * z / 2]

/-- Balanced coefficient (DEF-013 main convention). -/
def balCoef (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) : ℝ → Mat2 := coef (Real.sqrt κ) (Real.sqrt κ) u z

/-- Unbalanced coefficient (quantum-kernel convention: entries `κ ū`, `u`). -/
def unbalCoef (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) : ℝ → Mat2 := coef κ 1 u z

/-- `M` is a fundamental solution of `M_x = A(x) M`, `M(0) = 1` (classical, `C¹` solution). -/
def IsFundamental (A : ℝ → Mat2) (M : ℝ → Mat2) : Prop :=
  M 0 = 1 ∧ ∀ x, HasDerivAt M (A x * M x) x

theorem continuous_coef (p q : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (z : ℂ) :
    Continuous (coef p q u z) := by
  unfold coef
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- **Uniqueness of the fundamental solution** for continuous `u` (Gronwall / `ODE_solution_unique`). -/
theorem IsFundamental.unique {A : ℝ → Mat2} (hA : Continuous A) {M₁ M₂ : ℝ → Mat2}
    (h₁ : IsFundamental A M₁) (h₂ : IsFundamental A M₂) : M₁ = M₂ := by
  funext t
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s ∈ Set.Icc (-(|t| + 1)) (|t| + 1), ‖A s‖ ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_Icc (a := -(|t| + 1)) (b := |t| + 1)).exists_bound_of_continuousOn
      hA.continuousOn
    exact ⟨R, hR⟩
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0 ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩)
  have := ODE_solution_unique_of_mem_Ioo (v := fun s Y => A s * Y) (s := fun _ => Set.univ)
    (K := ⟨R, hR0⟩) (a := -(|t| + 1)) (b := |t| + 1) (t₀ := 0) (f := M₁) (g := M₂)
    (fun s hs => by
      refine LipschitzOnWith.of_dist_le_mul fun Y _ Y' _ => ?_
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
      calc ‖A s * (Y - Y')‖ ≤ ‖A s‖ * ‖Y - Y'‖ := norm_mul_le _ _
        _ ≤ R * ‖Y - Y'‖ := mul_le_mul_of_nonneg_right (hR s ⟨hs.1.le, hs.2.le⟩) (norm_nonneg _)
        _ = ((⟨R, hR0⟩ : NNReal) : ℝ) * ‖Y - Y'‖ := rfl)
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
    (fun s _ => ⟨h₁.2 s, trivial⟩) (fun s _ => ⟨h₂.2 s, trivial⟩) (by rw [h₁.1, h₂.1])
  exact this ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩


section Gauge

/-- `κ^{1/4}`. -/
def dq (κ : ℝ) : ℝ := κ ^ (1 / 4 : ℝ)

/-- `D = diag(κ^{1/4}, κ^{-1/4})`. -/
def Dm (κ : ℝ) : Mat2 := !![((dq κ : ℝ) : ℂ), 0; 0, (((dq κ)⁻¹ : ℝ) : ℂ)]

/-- `D⁻¹ = diag(κ^{-1/4}, κ^{1/4})`. -/
def Dinv (κ : ℝ) : Mat2 := !![(((dq κ)⁻¹ : ℝ) : ℂ), 0; 0, ((dq κ : ℝ) : ℂ)]

theorem dq_pos {κ : ℝ} (hκ : 0 < κ) : 0 < dq κ := Real.rpow_pos_of_pos hκ _

theorem dq_mul_dq {κ : ℝ} (hκ : 0 < κ) : dq κ * dq κ = Real.sqrt κ := by
  rw [dq, ← Real.rpow_add hκ, Real.sqrt_eq_rpow]; norm_num

theorem Dm_mul_Dinv {κ : ℝ} (hκ : 0 < κ) : Dm κ * Dinv κ = 1 := by
  have h : (dq κ : ℂ) ≠ 0 := by exact_mod_cast (dq_pos hκ).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dm, Dinv, Matrix.mul_apply, Fin.sum_univ_two, h]

theorem Dinv_mul_Dm {κ : ℝ} (hκ : 0 < κ) : Dinv κ * Dm κ = 1 := by
  have h : (dq κ : ℂ) ≠ 0 := by exact_mod_cast (dq_pos hκ).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dm, Dinv, Matrix.mul_apply, Fin.sum_univ_two, h]

/-- The gauge relation of the coefficient matrices: `D⁻¹ (unbalanced) D = (balanced)`. -/
theorem Dinv_unbalCoef_Dm {κ : ℝ} (hκ : 0 < κ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    Dinv κ * unbalCoef κ u z x * Dm κ = balCoef κ u z x := by
  have hd : (dq κ : ℂ) ≠ 0 := by exact_mod_cast (dq_pos hκ).ne'
  have hdd : (dq κ : ℂ) * (dq κ : ℂ) = ((Real.sqrt κ : ℝ) : ℂ) := by exact_mod_cast dq_mul_dq hκ
  have hss : ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hκ.le
  have hd2 : (dq κ : ℂ) ^ 2 = ((Real.sqrt κ : ℝ) : ℂ) := by rw [sq]; exact hdd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unbalCoef, balCoef, coef, Dm, Dinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    first | ring1 | (simp only [hd2]; ring1) | (simp only [hd2]; rw [← hss]; ring1)


/-- `D⁻¹ M_unbal D` solves the balanced equation. -/
theorem IsFundamental.gauge {κ : ℝ} (hκ : 0 < κ) {u : ℝ → ℂ} {z : ℂ} {Mu : ℝ → Mat2}
    (h : IsFundamental (unbalCoef κ u z) Mu) :
    IsFundamental (balCoef κ u z) (fun x => Dinv κ * Mu x * Dm κ) := by
  refine ⟨by simp [h.1, Dinv_mul_Dm hκ], fun x => ?_⟩
  have h1 := ((h.2 x).const_mul (Dinv κ)).mul_const (Dm κ)
  refine h1.congr_deriv ?_
  rw [← Dinv_unbalCoef_Dm hκ u z x]
  calc Dinv κ * (unbalCoef κ u z x * Mu x) * Dm κ
      = Dinv κ * unbalCoef κ u z x * (Dm κ * Dinv κ) * Mu x * Dm κ := by
        rw [Dm_mul_Dinv hκ]; simp [Matrix.mul_assoc]
    _ = (Dinv κ * unbalCoef κ u z x * Dm κ) * (Dinv κ * Mu x * Dm κ) := by
        simp [Matrix.mul_assoc]
    _ = _ := by rw [Dinv_unbalCoef_Dm hκ u z x]

/-- **`M_bal = D⁻¹ M_unbal D`** for the two fundamental solutions (continuous `u`). -/
theorem bal_eq_gauge {κ : ℝ} (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) {z : ℂ}
    {Mb Mu : ℝ → Mat2} (hb : IsFundamental (balCoef κ u z) Mb)
    (hu' : IsFundamental (unbalCoef κ u z) Mu) : Mb = fun x => Dinv κ * Mu x * Dm κ :=
  IsFundamental.unique (continuous_coef _ _ hu z) hb (hu'.gauge hκ)

/-- The two fundamental solutions have equal traces. -/
theorem trace_bal_eq_trace_unbal {κ : ℝ} (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) {z : ℂ}
    {Mb Mu : ℝ → Mat2} (hb : IsFundamental (balCoef κ u z) Mb)
    (hu' : IsFundamental (unbalCoef κ u z) Mu) (x : ℝ) :
    (Mb x).trace = (Mu x).trace := by
  rw [bal_eq_gauge hκ hu hb hu']
  show (Dinv κ * Mu x * Dm κ).trace = _
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Dm_mul_Dinv hκ, Matrix.one_mul]

open Classical in
/-- **DEF-013 spatial transfer matrix** `M(x, z)`: the fundamental solution of
`M_x = [[-iz/2, √κ ū],[√κ u, iz/2]] M`, `M(0) = 1`, for a continuous representative `u : ℝ → ℂ`
(smooth or `H¹` profiles on `𝕋_L`, extended periodically).  If no solution exists the junk value `0`
is returned; for continuous `u` a solution exists (classical linear ODE theory); uniqueness is
`IsFundamental.unique`. -/
def spatialTransfer (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) : ℝ → Mat2 :=
  if h : ∃ M, IsFundamental (balCoef κ u z) M then h.choose else 0

theorem spatialTransfer_spec {κ : ℝ} {u : ℝ → ℂ} {z : ℂ}
    (h : ∃ M, IsFundamental (balCoef κ u z) M) :
    IsFundamental (balCoef κ u z) (spatialTransfer κ u z) := by
  unfold spatialTransfer
  rw [dif_pos h]
  exact h.choose_spec

/-- `Δ_u(z) = trace M(L, z)`. -/
def discriminant (L κ : ℝ) (u : ℝ → ℂ) (z : ℂ) : ℂ := (spatialTransfer κ u z L).trace

theorem discriminant_eq_trace {L κ : ℝ} {u : ℝ → ℂ} {z : ℂ} {M : ℝ → Mat2}
    (hu : Continuous u) (h : IsFundamental (balCoef κ u z) M) :
    discriminant L κ u z = (M L).trace := by
  have hM : spatialTransfer κ u z = M :=
    IsFundamental.unique (continuous_coef _ _ hu z) (spatialTransfer_spec ⟨M, h⟩) h
  simp [discriminant, hM]

/-- **DEF-013 boundary phase** `γ_u(z) = L z/2 − κ G_M(z)` on the upper half-plane, parametric in the finite
positive full-mass measure `M = M_{κ,u}` (DEF-010; the limiting measure is named, not constructed, in
the source) and using DEF-010's `cauchyTransform`. -/
def boundaryPhase (L κ : ℝ) (M : Measure ℝ) (z : ℂ) : ℂ :=
  (L : ℂ) * z / 2 - (κ : ℂ) * QuantumNLS.EmpiricalRapidity.cauchyTransform M z

/-- **`Im γ > 0`** on the upper half-plane for `L, κ > 0` and a nonzero finite measure, from DEF-010's sign
lemma `Im G_M < 0` there.  (The ledger states positivity of `Im γ_u` as a consequence of the quantum
transfer limit; here it is *proved* for every nonzero finite `M`, not assumed.) -/
theorem im_boundaryPhase_pos {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (M : Measure ℝ) [IsFiniteMeasure M]
    (hM : M ≠ 0) {z : ℂ} (hz : 0 < z.im) : 0 < (boundaryPhase L κ M z).im := by
  have hG := QuantumNLS.EmpiricalRapidity.im_cauchyTransform_neg M hM z hz
  unfold boundaryPhase
  simp only [Complex.sub_im, Complex.mul_im, Complex.div_ofNat_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  have h1 : 0 < L * z.im / 2 := by positivity
  nlinarith [mul_pos hκ (neg_pos.mpr hG)]

/-- The identity `2 cos γ_u = Δ_u` of DEF-013 as a *proposition* (a theorem of the quantum transfer
limit elsewhere in the report; not assumed or proved here). -/
def QuantumTransferIdentity (L κ : ℝ) (u : ℝ → ℂ) (M : Measure ℝ) (z : ℂ) : Prop :=
  2 * Complex.cos (boundaryPhase L κ M z) = discriminant L κ u z

end Gauge

end QuantumNLS.SpatialTransfer

#print axioms QuantumNLS.SpatialTransfer.IsFundamental.unique
#print axioms QuantumNLS.SpatialTransfer.Dinv_unbalCoef_Dm
#print axioms QuantumNLS.SpatialTransfer.IsFundamental.gauge
#print axioms QuantumNLS.SpatialTransfer.bal_eq_gauge
#print axioms QuantumNLS.SpatialTransfer.trace_bal_eq_trace_unbal
#print axioms QuantumNLS.SpatialTransfer.spatialTransfer_spec
#print axioms QuantumNLS.SpatialTransfer.discriminant_eq_trace
#print axioms QuantumNLS.SpatialTransfer.im_boundaryPhase_pos
