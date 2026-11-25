import QuantumNLS.ResetMoserBounds
import QuantumNLS.ResetMoserCone

/-!
# `thm:reset-moser` (LOCAL-017): the hypotheses `Hyp` are satisfiable (non-vacuity witness)

The frozen structure `Hyp` (`ResetMoserHyp`, the printed hypotheses of `thm:reset-moser`, literally) is inhabited by the unperturbed datum: `Ω_z = ω` (constant), with the Hamiltonian flow of `q_n` the rotation
`rotN n t z = z + (e^{-it} − 1) z_n e_n` of the `n`th coordinate: the field of `q_n` for `Ω = ω` is `X_{q_n}(z) = −i z_n e_n` (`Xn_const`, from `omega_Xq_eq_fderiv` and `Jw`), the flow is `2π`-periodic and preserves
the norm, and the Poisson commutation `ω(X_{q_m}, X_{q_n}) = 0` holds.  `hypWitness : Hyp`.  (The theorem `reset_moser` for this datum is only the trivial `S = id` case; the point is that the hypotheses are consistent.)
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

/-- The rotation of the `n`th coordinate by the angle `−t`. -/
def rotN (n : ℤ) (t : ℝ) (z : K) : K :=
  z + lp.single 2 n ((Complex.exp (-(t : ℂ) * Complex.I) - 1) * z n)

theorem rotN_self (n : ℤ) (t : ℝ) (z : K) : rotN n t z n = Complex.exp (-(t : ℂ) * Complex.I) * z n := by
  simp [rotN]
  ring

theorem rotN_ne {n k : ℤ} (hk : k ≠ n) (t : ℝ) (z : K) : rotN n t z k = z k := by
  simp [rotN, lp.single_apply, hk]

theorem norm_rotN (n : ℤ) (t : ℝ) (z : K) : ‖rotN n t z‖ = ‖z‖ := by
  have h : ‖rotN n t z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [tsum_norm_sq, tsum_norm_sq]
    congr 1
    funext k
    by_cases hk : k = n
    · subst hk
      rw [rotN_self, norm_mul]
      have : ‖Complex.exp (-(t : ℂ) * Complex.I)‖ = 1 := by
        have := Complex.norm_exp_ofReal_mul_I (-t)
        simpa using this
      rw [this, one_mul]
    · rw [rotN_ne hk]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem Xn_const (n : ℤ) (z : K) : Xn (fun _ : K => omegaF) n z = Xq n z := by
  have hJ : Jw (Xq n z) = fderiv ℝ (q n) z :=
    ContinuousLinearMap.ext fun h => (Jw_apply _ _).trans (omega_Xq_eq_fderiv n z h)
  have h1 : Ycov (0 : Form) (-(fderiv ℝ (q n) z)) = Jw.symm (fderiv ℝ (q n) z) := by
    simp [Ycov, Nop]
  unfold Xn
  simp only [sub_self]
  rw [h1]
  exact (Jw.symm_apply_eq.2 hJ.symm)

theorem rotN_hasDerivAt (n : ℤ) (z : K) (t : ℝ) :
    HasDerivAt (fun s => rotN n s z) (Xq n (rotN n t z)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ) * Complex.I) (-Complex.I) t := by
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    simpa using h0.neg.mul_const Complex.I
  have h2 := h1.cexp
  have hc : HasDerivAt (fun s : ℝ => (Complex.exp (-(s : ℂ) * Complex.I) - 1) * z n)
      (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I) * z n) t :=
    (h2.sub_const 1).mul_const (z n)
  have hs := (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℂ) 2 n).hasFDerivAt.comp_hasDerivAt t hc
  have hs' := hs.const_add z
  refine hs'.congr_deriv ?_
  simp only [lp.singleContinuousLinearMap_apply, Xq, rotN_self]
  congr 1
  ring

theorem rotN_zero (n : ℤ) (z : K) : rotN n 0 z = z := by simp [rotN]

theorem rotN_period (n : ℤ) (z : K) : rotN n (2 * Real.pi) z = z := by
  have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  simp [rotN, hexp]

theorem poisson_const (m n : ℤ) (z : K) : omegaF (Xq m z) (Xq n z) = 0 := by
  rw [omegaF_apply, omega_Xq]
  by_cases h : m = n
  · subst h
    simp [Xq, Complex.mul_re, Complex.mul_im]
    ring
  · simp [Xq, lp.single_apply, h]

/-- The hypotheses of `thm:reset-moser` are satisfiable: `Ω = ω`, flows = coordinate rotations. -/
def hypWitness : Hyp where
  R := 1
  R_pos := one_pos
  Ω := fun _ => omegaF
  Ω_alt := fun _ v w => omegaF_alt v w
  Ω_analytic := fun _ _ => isRealAnalyticPoly_of_analyticAt analyticAt_const
  Ω_closed := fun _ _ a b c => by simp
  Ω_quad := ⟨0, fun z _ => by simp⟩
  Ω_lt := fun _ _ => by simp
  φ := rotN
  φ_zero := rotN_zero
  φ_mem := fun n z hz t => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_rotN]; exact hz
  φ_deriv := fun n z _ t => by
    rw [Xn_const]
    exact rotN_hasDerivAt n z t
  φ_period := fun n z _ => rotN_period n z
  poisson := fun m n z _ => by
    rw [Xn_const, Xn_const]
    exact poisson_const m n z

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Xn_const
#print axioms QuantumNLS.ResetMoser.rotN_hasDerivAt
#print axioms QuantumNLS.ResetMoser.hypWitness
