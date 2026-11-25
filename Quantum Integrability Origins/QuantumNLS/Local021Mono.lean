import Mathlib
import QuantumNLS.ResetMoserField

/-!
# LOCAL-021, stage 1: unitary / antiunitary monomial operators on `K = ℓ²(ℤ;ℂ)`

Source: `local_covariance.tex:152-160` ("Each listed symmetry is a unitary or antiunitary monomial operator `U`: it permutes
coordinates, multiplies them by fixed unit complex numbers, and may conjugate them.  Write `ε = 1` in the unitary case and `-1` in
the antiunitary case.").  `Mono` is such an operator, `(U z)_n = c_n · s(z_{σ⁻¹ n})` with `s = id` or complex conjugation.

* `Mono.act` : the operator on `K` (`ℝ`-linear isometric equivalence `Mono.equiv`, inverse `Mono.inv`);
* `Mono.omega_act` : `ω(Uh, Uk) = ε ω(h,k)`; `Mono.act_I_smul` : `U(i z) = ε i U z`;
* `Mono.mem_ball`, `Mono.act_smul_real` etc.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

/-- A monomial operator on `ℓ²(ℤ;ℂ)`: permutation `σ`, unit multipliers `c`, optional conjugation. -/
structure Mono where
  σ : ℤ ≃ ℤ
  c : ℤ → ℂ
  hc : ∀ n, ‖c n‖ = 1
  anti : Bool

namespace Mono

variable (U : Mono)

/-- `ε = 1` (unitary) or `-1` (antiunitary). -/
def eps : ℝ := if U.anti then -1 else 1

/-- the conjugation-or-identity `s`. -/
def cj (w : ℂ) : ℂ := if U.anti then conj w else w

theorem norm_cj (w : ℂ) : ‖U.cj w‖ = ‖w‖ := by
  unfold cj; split_ifs <;> simp

theorem cj_cj (w : ℂ) : U.cj (U.cj w) = w := by
  unfold cj; split_ifs <;> simp

theorem cj_add (v w : ℂ) : U.cj (v + w) = U.cj v + U.cj w := by
  unfold cj; split_ifs <;> simp

theorem cj_mul (v w : ℂ) : U.cj (v * w) = U.cj v * U.cj w := by
  unfold cj; split_ifs <;> simp

theorem cj_real (a : ℝ) (w : ℂ) : U.cj ((a : ℂ) * w) = (a : ℂ) * U.cj w := by
  unfold cj; split_ifs <;> simp

theorem cj_I (w : ℂ) : U.cj (Complex.I * w) = (U.eps : ℂ) * Complex.I * U.cj w := by
  unfold cj eps; split_ifs <;> simp

theorem eps_sq : U.eps * U.eps = 1 := by unfold eps; split_ifs <;> norm_num

/-- the coordinate function of `U z`. -/
def fn (z : K) : ℤ → ℂ := fun n => U.c n * U.cj (z (U.σ.symm n))

theorem norm_fn (z : K) (n : ℤ) : ‖U.fn z n‖ = ‖z (U.σ.symm n)‖ := by
  simp [fn, U.hc, U.norm_cj]

theorem mem (z : K) : Memℓp (U.fn z) 2 := by
  refine memℓp_gen ?_
  have h1 : Summable fun n => ‖z n‖ ^ (2 : ℝ≥0∞).toReal := by
    have := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact this
  have h2 : Summable fun n => ‖z (U.σ.symm n)‖ ^ (2 : ℝ≥0∞).toReal := (U.σ.symm.summable_iff).2 h1
  refine h2.congr fun n => ?_
  rw [U.norm_fn]

/-- the operator. -/
def act (z : K) : K := ⟨U.fn z, U.mem z⟩

@[simp] theorem act_apply (z : K) (n : ℤ) : U.act z n = U.c n * U.cj (z (U.σ.symm n)) := rfl

theorem norm_act (z : K) : ‖U.act z‖ = ‖z‖ := by
  have h1 : ‖U.act z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_K (U.act z), norm_sq_K z]
    rw [← (U.σ.symm.tsum_eq (fun n => ‖z n‖ ^ 2))]
    refine tsum_congr fun n => ?_
    rw [act_apply, norm_mul, U.hc, one_mul, U.norm_cj]
  exact (sq_eq_sq₀ (norm_nonneg (U.act z)) (norm_nonneg z)).1 h1

theorem act_add (z w : K) : U.act (z + w) = U.act z + U.act w := by
  refine lp.ext (funext fun n => ?_)
  simp [act_apply, cj_add, mul_add]

theorem act_real_smul (a : ℝ) (z : K) : U.act ((a : ℂ) • z) = (a : ℂ) • U.act z := by
  refine lp.ext (funext fun n => ?_)
  simp only [act_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [U.cj_real]; ring

theorem act_I_smul (z : K) : U.act (Complex.I • z) = ((U.eps : ℂ) * Complex.I) • U.act z := by
  refine lp.ext (funext fun n => ?_)
  simp only [act_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [U.cj_I]; ring

/-- the inverse monomial operator. -/
def inv : Mono where
  σ := U.σ.symm
  c := fun m => U.cj (conj (U.c (U.σ m)))
  hc := fun m => by rw [U.norm_cj]; simp [U.hc]
  anti := U.anti

theorem unit_mul_conj (m : ℤ) : U.c m * conj (U.c m) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, U.hc]; simp

theorem inv_act_act (z : K) : U.inv.act (U.act z) = z := by
  refine lp.ext (funext fun m => ?_)
  show U.cj (conj (U.c (U.σ m))) * U.cj (U.c (U.σ m) * U.cj (z (U.σ.symm (U.σ m)))) = z m
  rw [Equiv.symm_apply_apply]
  have h := U.unit_mul_conj (U.σ m)
  unfold cj at *
  split_ifs <;> simp only [map_mul, Complex.conj_conj] <;> linear_combination (z m) * h

theorem act_inv_act (z : K) : U.act (U.inv.act z) = z := by
  refine lp.ext (funext fun m => ?_)
  show U.c m * U.cj (U.cj (conj (U.c (U.σ (U.σ.symm m)))) * U.cj (z (U.σ (U.σ.symm m)))) = z m
  rw [Equiv.apply_symm_apply]
  have h := U.unit_mul_conj m
  unfold cj at *
  split_ifs <;> simp only [map_mul, Complex.conj_conj] <;> linear_combination (z m) * h

/-- the operator as an `ℝ`-linear isometric equivalence. -/
def equiv : K ≃ₗᵢ[ℝ] K where
  toFun := U.act
  invFun := U.inv.act
  map_add' := U.act_add
  map_smul' := fun a z => by
    refine lp.ext (funext fun n => ?_)
    show U.c n * U.cj (a • z (U.σ.symm n)) = a • (U.c n * U.cj (z (U.σ.symm n)))
    rw [Complex.real_smul, Complex.real_smul, U.cj_real]; ring
  left_inv := U.inv_act_act
  right_inv := U.act_inv_act
  norm_map' := U.norm_act

theorem equiv_apply (z : K) : U.equiv z = U.act z := rfl

/-- the operator as a continuous linear equivalence over `ℝ`. -/
def cle : K ≃L[ℝ] K := U.equiv.toContinuousLinearEquiv

theorem cle_apply (z : K) : U.cle z = U.act z := rfl

theorem act_zero : U.act 0 = 0 := U.equiv.map_zero

theorem act_smul_real (a : ℝ) (z : K) : U.act (a • z) = a • U.act z := U.equiv.map_smul a z

theorem act_sub (z w : K) : U.act (z - w) = U.act z - U.act w := U.equiv.map_sub z w

theorem mem_ball {R : ℝ} {z : K} (hz : z ∈ ball (0 : K) R) : U.act z ∈ ball (0 : K) R := by
  rw [mem_ball_zero_iff] at *; rwa [U.norm_act]

theorem cj_conj_eq (w : ℂ) : conj (U.cj w) = U.cj (conj w) := by
  unfold cj; split_ifs <;> simp

/-- `⟨Uh, Uk⟩ = s(⟨h,k⟩)`. -/
theorem inner_act (h k : K) : inner ℂ (U.act h) (U.act k) = U.cj (inner ℂ h k) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have e1 : ∀ n, inner ℂ (U.act h n) (U.act k n) = U.cj (inner ℂ (h (U.σ.symm n)) (k (U.σ.symm n))) := by
    intro n
    rw [show U.act h n = U.c n * U.cj (h (U.σ.symm n)) from rfl,
      show U.act k n = U.c n * U.cj (k (U.σ.symm n)) from rfl]
    simp only [RCLike.inner_apply]
    have h1 := U.unit_mul_conj n
    set a := h (U.σ.symm n)
    set b := k (U.σ.symm n)
    cases hA : U.anti
    · simp only [cj, hA, map_mul, Bool.false_eq_true, ite_false]
      linear_combination (conj a * b) * h1
    · simp only [cj, hA, map_mul, Complex.conj_conj, ite_true]
      linear_combination (a * conj b) * h1
  rw [tsum_congr e1, U.σ.symm.tsum_eq (fun m => U.cj (inner ℂ (h m) (k m)))]
  unfold cj
  split_ifs
  · exact (RCLike.conj_tsum (fun m => inner ℂ (h m) (k m))).symm
  · rfl

/-- `ω(Uh, Uk) = ε ω(h,k)`. -/
theorem omega_act (h k : K) : omega (U.act h) (U.act k) = U.eps * omega h k := by
  unfold omega
  rw [U.inner_act]
  unfold cj eps
  split_ifs
  · rw [Complex.conj_im]; ring
  · ring

end Mono

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Mono.omega_act
#print axioms QuantumNLS.Local021.Mono.equiv
#print axioms QuantumNLS.Local021.Mono.act_I_smul
