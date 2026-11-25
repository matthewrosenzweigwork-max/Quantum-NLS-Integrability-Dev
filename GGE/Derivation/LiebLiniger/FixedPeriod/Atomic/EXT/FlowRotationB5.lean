import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB4

/-! # The actual finite-plane Hamiltonian ODE

Real and imaginary coordinate tests of the symplectic pairing identify the
actual velocity with minus I/2 times the real coordinate gradient of HΛ.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

/-- Testing a finite symplectic sum against a single coordinate selects
exactly that coordinate, without any nonvanishing assumption. -/
theorem finitePlane_symplectic_single38 (Λ : Finset ℤ) (a : Λ → ℂ) (i : Λ) (c : ℂ) :
    (∑ j : Λ, (starRingEnd ℂ (a j) * (Pi.single i c : Λ → ℂ) j).im) =
      (starRingEnd ℂ (a i) * c).im := by
  classical
  calc
    (∑ j : Λ, (starRingEnd ℂ (a j) * (Pi.single i c : Λ → ℂ) j).im) =
        (starRingEnd ℂ (a i) * (Pi.single i c : Λ → ℂ) i).im :=
      Finset.sum_eq_single i
        (fun j _ hji => by simp [Pi.single_apply, hji])
        (fun hi => False.elim (hi (Finset.mem_univ i)))
    _ = (starRingEnd ℂ (a i) * c).im := by rw [Pi.single_eq_same]

set_option maxHeartbeats 400000 in
/-- The real differential of HΛ on the actual trajectory is represented by
twice the finite symplectic pairing with its time derivative. -/
theorem HΛ_fderiv_actual38 (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) (η : Λ → ℂ) :
    fderiv ℝ (HΛ Λ) (ZΛ Λ w t) η =
      2 * ∑ i : Λ, (starRingEnd ℂ ((deriv (ZΛ Λ w) t) i) * η i).im := by
  have hl := finitePlane_line_hasDerivAt38 Λ (ZΛ Λ w t) η 0
  have hF : HasFDerivAt (HΛ Λ) (fderiv ℝ (HΛ Λ) (ZΛ Λ w t))
      (fun i => ZΛ Λ w t i + (0 : ℂ) * η i) := by
    simpa only [zero_mul, add_zero] using
      (analytic_HLambda38 Λ (ZΛ Λ w t) (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hf := hF.comp_hasDerivAt 0 hl
  exact hf.unique (finiteGap_actualHamiltonian_pairing38 Λ w t η)

set_option maxHeartbeats 400000 in
/-- For every finite plane, every initial finite vector and every real time,
the actual finite-plane trajectory satisfies the vector field YΛ with exactly
the source normalization minus I/2. -/
theorem finiteGap_actualODE38 : ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ),
    HasDerivAt (ZΛ Λ w) (YΛ Λ (ZΛ Λ w t)) t := by
  intro Λ w t
  classical
  have hd : deriv (ZΛ Λ w) t = YΛ Λ (ZΛ Λ w t) := by
    funext i
    have ha := HΛ_fderiv_actual38 Λ w t (Pi.single i (1 : ℂ))
    have hb := HΛ_fderiv_actual38 Λ w t (Pi.single i Complex.I)
    have hA : fderiv ℝ (HΛ Λ) (ZΛ Λ w t) (Pi.single i (1 : ℂ)) =
        -(2 * ((deriv (ZΛ Λ w) t) i).im) := by
      rw [finitePlane_symplectic_single38] at ha
      simpa only [mul_one, Complex.conj_im, mul_neg] using ha
    have hB : fderiv ℝ (HΛ Λ) (ZΛ Λ w t) (Pi.single i Complex.I) =
        2 * ((deriv (ZΛ Λ w) t) i).re := by
      rw [finitePlane_symplectic_single38] at hb
      simpa only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] using hb
    apply Complex.ext <;>
      simp [YΛ, hA, hB, Complex.mul_re, Complex.mul_im] <;>
      ring
  exact (differentiable_ZΛ38 Λ w t).hasDerivAt.congr_deriv hd

end LiebLiniger.FixedPeriod.EXT
