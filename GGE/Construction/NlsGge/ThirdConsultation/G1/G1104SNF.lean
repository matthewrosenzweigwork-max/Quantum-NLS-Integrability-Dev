import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# G1-104 M5/M6 support: local Smith diagonal and nilpotent chain count

M5's full 2×2 local Smith reduction and its analytic-germ adapter remain open; this file proves
the diagonal determinant-order calculation used after such a reduction. M6 is proved for a
finite-dimensional vector space, conditional only at its Taylor-kernel interface on the M4
linear equivalence to the finite chain space below. No M2 or M4 declarations are copied here.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.G1.G1104SNF

/-! ## M5: diagonal determinant valuation -/

/-- The diagonal 2×2 matrix with diagonal entries `p` and `q`. -/
def diagonalTwo (p q : PowerSeries ℂ) : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then p else q)

/-- For a Smith diagonal, the determinant order is the sum of the two local orders.

This is the diagonal case of the M5 determinant count; it does not assert that a general
characteristic matrix has already been reduced to this form. -/
theorem diagonalTwo_det_order (p q : PowerSeries ℂ) :
    PowerSeries.order (diagonalTwo p q).det = PowerSeries.order p + PowerSeries.order q := by
  classical
  simp [diagonalTwo, Matrix.det_diagonal, Fin.prod_univ_two, PowerSeries.order_mul]

/-- Determinant order is invariant under invertible row and column changes in a Smith
factorization. The factorization itself is an explicit hypothesis; this theorem does not claim
that a given characteristic matrix has already been reduced. -/
theorem det_order_eq_of_smith_equiv
    (D U V : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (p q : PowerSeries ℂ)
    (hSmith : U * D * V = diagonalTwo p q)
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    PowerSeries.order D.det = PowerSeries.order p + PowerSeries.order q := by
  have hdet := congrArg Matrix.det hSmith
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hord := congrArg PowerSeries.order hdet
  rw [PowerSeries.order_mul, PowerSeries.order_mul,
    PowerSeries.order_zero_of_isUnit hU, PowerSeries.order_zero_of_isUnit hV,
    diagonalTwo_det_order] at hord
  simpa using hord

/-- Multiplying a formal germ by a unit does not change its local order. -/
theorem powerSeries_order_mul_unit (p : PowerSeries ℂ) (u : (PowerSeries ℂ)ˣ) :
    (p * (u : PowerSeries ℂ)).order = p.order := by
  simp only [PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit u.isUnit, add_zero]

/-- A nonzero constant factor does not change the analytic order of a scalar germ.

This is the scalar-order transfer needed with the nonzero constant in the M3 determinant identity.
-/
theorem analyticOrderAt_const_mul {f : ℂ → ℂ} (c z₀ : ℂ) (hc : c ≠ 0)
    (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt (fun z => c * f z) z₀ = analyticOrderAt f z₀ := by
  have hconstant : AnalyticAt ℂ (fun _ : ℂ => c) z₀ := analyticAt_const
  have hconstantOrder : analyticOrderAt (fun _ : ℂ => c) z₀ = 0 := by
    exact (analyticOrderAt_eq_zero (f := fun _ : ℂ => c) (z₀ := z₀)).2 (Or.inr hc)
  have hsmul : (fun z : ℂ => c * f z) = (fun _ : ℂ => c) • f := by
    funext z
    simp
  rw [hsmul, analyticOrderAt_smul hconstant hf, hconstantOrder, zero_add]

/-! ## M6: chains of a nilpotent endomorphism -/

/-- Length-`N` forward chains for `T`, with the terminal value `w_N = 0`.

The equations use the same forward orientation as `rootVector`: `T w_j = w_(j+1)`. Reversing
the Taylor chain `(W_j)` from M4 gives this orientation, with its top coefficient as `w_0`. -/
def chainSpace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (N : ℕ) : Submodule ℂ (Fin (N + 1) → V) where
  carrier := {w | w (Fin.last N) = 0 ∧
    ∀ j : Fin N, T (w j.castSucc) = w j.succ}
  zero_mem' := by simp
  add_mem' := by
    intro w v hw hv
    refine ⟨?_, ?_⟩
    · simp [hw.1, hv.1]
    · intro j
      simp only [Pi.add_apply, map_add, hw.2 j, hv.2 j]
  smul_mem' := by
    intro c w hw
    refine ⟨?_, ?_⟩
    · simp [hw.1]
    · intro j
      simp only [Pi.smul_apply, map_smul, hw.2 j]

/-- Build the unique chain whose first value is `v`, when `T^N = 0`. -/
def chainFromFirst {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (N : ℕ) (hT : T ^ N = 0) :
    V →ₗ[ℂ] chainSpace T N where
  toFun v := ⟨fun i => (T ^ i.val) v, by
    refine ⟨?_, ?_⟩
    · change (T ^ N) v = 0
      rw [hT]
      rfl
    · intro j
      change T ((T ^ j.val) v) = (T ^ (j.val + 1)) v
      simp [pow_succ']
  ⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    simp
  map_smul' c v := by
    apply Subtype.ext
    funext i
    simp

/-- Read the first chain entry. -/
def chainFirst {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (N : ℕ) : chainSpace T N →ₗ[ℂ] V where
  toFun w := w.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem chain_value_eq_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (N : ℕ) (w : chainSpace T N) (i : Fin (N + 1)) :
    w.1 i = (T ^ i.val) (w.1 0) := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    calc
      w.1 j.succ = T (w.1 j.castSucc) := (w.property.2 j).symm
      _ = T ((T ^ j.castSucc.val) (w.1 0)) := by rw [ih]
      _ = (T ^ j.succ.val) (w.1 0) := by
        simp [pow_succ']

/-- If `T^N = 0`, taking the first entry is a linear equivalence from chains to `V`. -/
noncomputable def chainSpaceEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (N : ℕ) (hT : T ^ N = 0) : chainSpace T N ≃ₗ[ℂ] V where
  toFun := chainFirst T N
  invFun := chainFromFirst T N hT
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    change (T ^ i.val) (w.1 0) = w.1 i
    exact (chain_value_eq_pow T N w i).symm
  right_inv := by
    intro v
    simp [chainFirst, chainFromFirst]
  map_add' := (chainFirst T N).map_add
  map_smul' := (chainFirst T N).map_smul

/-- The dimension of length-`N` chains equals the dimension of `V` once `T^N = 0`. -/
theorem chainSpace_finrank_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (N : ℕ) (hT : T ^ N = 0) :
    Module.finrank ℂ (chainSpace T N) = Module.finrank ℂ V :=
  (chainSpaceEquiv T N hT).finrank_eq

/-- M6 interface: if the M4 Taylor coefficient kernel is linearly equivalent to the operator
chain space, its dimension is the dimension of the finite-dimensional root space `V`.

The `hM4` premise is the unlanded M4 bridge, stated explicitly rather than copied or assumed
silently. It is not the G1-104 characteristic/order conclusion. -/
theorem taylorKernel_finrank_eq_of_m4_chainEquiv
    {W V : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (K : Submodule ℂ W) (T : V →ₗ[ℂ] V) (N : ℕ) (hT : T ^ N = 0)
    (hM4 : K ≃ₗ[ℂ] chainSpace T N) :
    Module.finrank ℂ K = Module.finrank ℂ V := by
  calc
    Module.finrank ℂ K = Module.finrank ℂ (chainSpace T N) :=
      LinearEquiv.finrank_eq hM4
    _ = Module.finrank ℂ V := chainSpace_finrank_eq T N hT

end NlsGge.ThirdConsultation.G1.G1104SNF

end
