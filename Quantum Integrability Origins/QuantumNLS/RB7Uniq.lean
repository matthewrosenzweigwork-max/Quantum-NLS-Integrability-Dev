import Mathlib
import QuantumNLS.RB7Seq

/-!
# R-7B122087 `thm:hierarchy`, uniqueness in coordinates (abstract part)

Printed: "For another smooth solution ... All action moduli are therefore constant along that solution.  Its coordinate frequencies are the same constants,
so each coordinate satisfies the same scalar linear equation.  Injectivity proves uniqueness."

`unique_flow`: a curve `y` in `WSeq V` with `y 0 = z`, constant coordinate moduli, and coordinatewise Hamiltonian equation
`y_j' = -i Σ_r s_r ∇_j F_r(y)` equals the flow `flow (t • s) z`.  The constancy of the moduli along an arbitrary smooth solution (the
physical input: invariance of the actions `I_n`, i.e. `{I_n, I_{r+1}} = 0` from the smooth action rotations of R-F5355ABD) is a hypothesis here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

/-- Equal-modulus sequences differ by a unimodular multiplier. -/
theorem exists_rot_of_norm_eq {W : PosWeight} (y z : WSeq W) (h : ∀ j, ‖y.val j‖ = ‖z.val j‖) :
    ∃ u : ℤ → Circle, y = rot u z := by
  classical
  have hc : ∀ j, ∃ c : Circle, y.val j = (c : ℂ) * z.val j := by
    intro j
    by_cases hz : z.val j = 0
    · refine ⟨1, ?_⟩
      have : y.val j = 0 := by simpa [hz] using h j
      simp [this, hz]
    · have hn : ‖y.val j / z.val j‖ = 1 := by
        rw [norm_div, h j, div_self (norm_ne_zero_iff.2 hz)]
      refine ⟨⟨y.val j / z.val j, mem_sphere_zero_iff_norm.2 hn⟩, ?_⟩
      show y.val j = y.val j / z.val j * z.val j
      rw [div_mul_cancel₀ _ hz]
  choose u hu using hc
  exact ⟨u, WSeq.ext (funext fun j => hu j)⟩

namespace SeqData

variable {V : PosWeight} {ι : Type} [Fintype ι] (S : SeqData V ι)

theorem unique_flow (s : ι → ℝ) (z : WSeq V) (y : ℝ → WSeq V) (hy0 : y 0 = z)
    (hmod : ∀ t j, ‖(y t).val j‖ = ‖z.val j‖)
    (hder : ∀ (j : ℤ) (t : ℝ), HasDerivAt (fun t => (y t).val j)
      (-Complex.I * ∑ r, (s r : ℂ) * grad (fderiv ℝ (S.F r) (S.down r (y t))) j) t) (t : ℝ) :
    y t = flow S.D (t • s) z := by
  refine WSeq.ext (funext fun j => ?_)
  -- the frequencies along `y` are those of `z`
  have hΩ : ∀ τ r, S.D.Ω r (y τ) j = S.D.Ω r z j := by
    intro τ r
    obtain ⟨u, hu⟩ := exists_rot_of_norm_eq (y τ) z (hmod τ)
    rw [hu]; exact S.D.inv r u z j
  set ν : ℝ := S.nu s z j with hν
  have hg : ∀ τ, HasDerivAt (fun τ => (y τ).val j) (-Complex.I * (ν : ℂ) * (y τ).val j) τ := by
    intro τ
    have h := hder j τ
    have e : ∑ r, (s r : ℂ) * grad (fderiv ℝ (S.F r) (S.down r (y τ))) j = (ν : ℂ) * (y τ).val j := by
      simp only [S.grad_eq, hΩ, hν, SeqData.nu]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e] at h
    convert h using 1; ring
  -- `exp(iντ) y_j(τ)` is constant
  set k : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (ν : ℂ) * (τ : ℂ)) * (y τ).val j with hk
  have hkd : ∀ τ, HasDerivAt k 0 τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (ν : ℂ) * (τ : ℂ)))
        (Complex.exp (Complex.I * (ν : ℂ) * (τ : ℂ)) * (Complex.I * (ν : ℂ))) τ := by
      have := ((hasDerivAt_id' (τ : ℂ)).const_mul (Complex.I * (ν : ℂ))).cexp.comp_ofReal
      simpa using this
    have := h1.mul (hg τ)
    convert this using 1
    ring
  have hconst : k t = k 0 := is_const_of_deriv_eq_zero (fun τ => (hkd τ).differentiableAt)
    (fun τ => (hkd τ).deriv) t 0
  have h0 : k 0 = z.val j := by simp [hk, hy0]
  have hyt : (y t).val j = Complex.exp (-(Complex.I * (ν : ℂ) * (t : ℂ))) * z.val j := by
    have : (y t).val j = Complex.exp (-(Complex.I * (ν : ℂ) * (t : ℂ))) * k t := by
      simp only [hk]
      rw [← mul_assoc, ← Complex.exp_add]; simp
    rw [this, hconst, h0]
  rw [hyt, flow_val, SeqData.angle_smul]
  congr 2
  push_cast; ring

end SeqData

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.SeqData.unique_flow
