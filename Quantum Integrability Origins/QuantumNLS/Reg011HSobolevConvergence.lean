import QuantumNLS.Reg011SequencesR48a

/-! REG-011 step 2 (haiku_inventory, module Reg011HSobolevConvergence).
Weighted Hilbert convergence in H^s from convergence of the L² classes, or of the Fourier
coordinates, together with convergence of the squared H^s norms. Read-only import of the
frozen `Reg011SequencesR48a` (`tendsto_of_coordinates_norm`) and of the `WField` coefficient
and norm API in `SobolevSpaces`. No REG-010 input and no review record unfrozen module. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
namespace QuantumNLS.Reg011HSobolevConvergence

variable {L : ℝ} [Fact (0 < L)]

/-- Each Fourier coefficient is a continuous functional on the L² class. -/
theorem coeff_continuous (n : ℤ) :
    Continuous (fun x : Lp ℂ 2 (volume : Measure (AddCircle L)) => fourierL2 L x n) :=
  (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := 2) n).continuous.comp
    (fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.continuous

/-- Convergence of L² classes gives convergence of every Fourier coefficient. -/
theorem coeff_tendsto_of_L2 {ι : Type*} {l : Filter ι} (x : ι → Lp ℂ 2 (volume : Measure (AddCircle L)))
    (y : Lp ℂ 2 (volume : Measure (AddCircle L))) (hx : Tendsto x l (𝓝 y)) (n : ℤ) :
    Tendsto (fun j => fourierL2 L (x j) n) l (𝓝 (fourierL2 L y n)) :=
  ((coeff_continuous (L := L) n).tendsto y).comp hx

/-- **H^s criterion.** A sequence in H^s converges to v as soon as its Fourier coefficients
converge pointwise to those of v and its squared H^s norms converge to ‖v‖². This is the
frozen `tendsto_of_coordinates_norm` read through the isometric coefficient map `toSeq`. -/
theorem H02_tendsto_of_coeff_norm {s : ℝ} (u : ℕ → H02 L s) (v : H02 L s)
    (hpt : ∀ n : ℤ, Tendsto (fun j => fourierL2 L (u j).val n) atTop
      (𝓝 (fourierL2 L v.val n)))
    (hn : Tendsto (fun j => ‖u j‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2))) :
    Tendsto u atTop (𝓝 v) := by
  have h := QuantumNLS.Reg011SequencesR48a.tendsto_of_coordinates_norm (def002 L s)
    (fun j => toSeq L (def002 L s) (u j)) (toSeq L (def002 L s) v)
    (fun n => by simpa only [toSeq_val] using hpt n)
    (by simpa only [WField.norm_def] using hn)
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  simpa only [← map_sub, ← WField.norm_def] using h

/-- **H^s convergence from L² convergence and norm convergence.** The inverse-direction
form used once the L² classes are known to converge. -/
theorem H02_tendsto_of_L2_and_norm {s : ℝ} (u : ℕ → H02 L s) (v : H02 L s)
    (hL2 : Tendsto (fun j => (u j).val) atTop (𝓝 v.val))
    (hn : Tendsto (fun j => ‖u j‖ ^ 2) atTop (𝓝 (‖v‖ ^ 2))) :
    Tendsto u atTop (𝓝 v) :=
  H02_tendsto_of_coeff_norm u v (fun n => coeff_tendsto_of_L2 (fun j => (u j).val) v.val hL2 n) hn

/-- The squared H^s norm, as the weighted Fourier sum. -/
theorem H02_norm_sq_eq_tsum {s : ℝ} (u : H02 L s) :
    ‖u‖ ^ 2 = ∑' n : ℤ, (def002 L s).w n * ‖fourierL2 L u.val n‖ ^ 2 :=
  WField.norm_sq_eq_tsum L u

#print axioms coeff_continuous
#print axioms coeff_tendsto_of_L2
#print axioms H02_tendsto_of_coeff_norm
#print axioms H02_tendsto_of_L2_and_norm
#print axioms H02_norm_sq_eq_tsum
end QuantumNLS.Reg011HSobolevConvergence
