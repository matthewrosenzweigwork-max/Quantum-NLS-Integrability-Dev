import Mathlib
import QuantumNLS.RiccatiPointwiseRep
import QuantumNLS.RiccatiL2Classical

/-!
# R-3FEAD88B step C4, stage RiccatiPointwiseDisc: L² discriminant from the Ell² fixed point

Physical-κ statement. Let `κ > 0` be the physical coupling and let `κ / L` be the model coupling
of `riccatiT` (so `κ_model · L = κ_phys`). For `u r : Ell2` with the fixed point
`riccatiT (κ/L) u (jEll u) r = r` (the conjugate profile is `v = jEll u`):

* `series_jEll`: the pointwise series of `toField (jEll u)` is the complex conjugate of the series
  of `toField u` (reindexing `k ↦ -k`, `pw_neg`);
* `physRep`: the physical representative `(√L)⁻¹ · series(toField ·)` of the field;
* `physRep_sup_bound`: sup bound `‖physRep r‖∞ ≤ (√L)⁻¹ Σ_k |c_k|` (the derived Rb);
* `physRep_periodic`, `physRep_continuous`, `physRep_ode`: periodicity, continuity of the
  representative of `fieldMap u`, and the pointwise physical Riccati ODE with coupling `κ`;
* `l2_discriminant_monodromy`: the `L²` discriminant of `fieldMap L a u` at `z` equals
  `ψ + ψ⁻¹` with `ψ = RiccatiMonodromy.psi κ (physRep u) (physRep r) z L`, by feeding
  `RiccatiL2Classical.discriminant_eq_monodromy`.

Scope: the coefficient-level Riccati fixed point is produced by C2/C3; no expansion at infinity,
no holomorphy, no uniformity (those are D1/D2). Standard axioms only; no sorry, admit,
native_decide.
-/

set_option autoImplicit false

noncomputable section

namespace QuantumNLS.RiccatiPointwiseDisc

open Complex ComplexConjugate MeasureTheory Set QuantumNLS.RiccatiPointwise
  QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseCoef QuantumNLS.RiccatiPointwiseRep
  QuantumNLS.RiccatiPicardBall QuantumNLS.ComplexifiedSobolevField

/-- Conjugation of the exponential: `conj(e_k(y)) = e_{-k}(y)`. -/
theorem conj_ex (L : ℝ) (k : ℤ) (y : ℝ) : conj (ex L k y) = ex L (-k) y := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_neg, map_intCast,
    map_ofNat]
  push_cast
  ring

/-- Coefficients of the conjugate field: `(toField (J x))_k = conj((toField x)_{-k})`. -/
theorem toField_jEll (L a : ℝ) (x : Ell2) (k : ℤ) :
    toField L a (jEll x) k = conj (toField L a x (-k)) := by
  unfold toField
  rw [jEll_apply, map_div₀, Complex.conj_ofReal, pw_neg]

/-- **Conjugate series.** `series(toField (J x))(y) = conj(series(toField x)(y))` for real `y`. -/
theorem series_jEll (L a : ℝ) (x : Ell2) (y : ℝ) :
    series L (toField L a (jEll x)) y = conj (series L (toField L a x) y) := by
  unfold series
  rw [RCLike.conj_tsum]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => conj (toField L a x k * ex L k y))]
  refine tsum_congr (fun k => ?_)
  show toField L a (jEll x) k * ex L k y = conj (toField L a x (-k) * ex L (-k) y)
  rw [toField_jEll, map_mul, conj_ex, neg_neg]

/-- The physical representative `(√L)⁻¹ · series(toField u)` of the profile of `u ∈ Ell2`. -/
def physRep (L a : ℝ) (u : Ell2) : ℝ → ℂ :=
  fun x => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a u) x

/-- **Derived sup bound.** `‖physRep r x‖ ≤ (√L)⁻¹ Σ_k |c_k|` with `c = toField r`, finite by
`ℓ¹` summability (`a > 1/2`). -/
theorem physRep_sup_bound {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r : Ell2) (x : ℝ) :
    ‖physRep L a r x‖ ≤ (Real.sqrt L)⁻¹ * ∑' k, ‖toField L a r k‖ := by
  simp only [physRep]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_series_le (summable_norm_toField hL ha r) x)
    (by positivity)

/-- Periodicity of the physical representative. -/
theorem physRep_periodic {L a : ℝ} (hL : 0 < L) (r : Ell2) :
    physRep L a r L = physRep L a r 0 := by
  have h := series_add_period (L := L) hL.ne' (toField L a r) 0
  rw [zero_add] at h
  simp only [physRep]
  rw [h]

/-- Continuity of the physical representative (from the continuous representative of
`fieldMap L a u`). -/
theorem physRep_continuous (L : ℝ) [Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a) (u : Ell2) :
    Continuous (physRep L a u) := by
  obtain ⟨G, hGc, -, hGpt, -⟩ := fieldMap_rep L ha u
  have hfun : physRep L a u = fun x : ℝ => G (x : AddCircle L) :=
    funext (fun x => (hGpt x).symm)
  rw [hfun]
  exact hGc.comp (AddCircle.continuous_mk' L)

/-- **Physical pointwise ODE.** For the fixed point `riccatiT (κ/L) u (jEll u) r = r`:
`d/dx physRep r = i z physRep r + physRep u - κ conj(physRep u) (physRep r)²`
with the physical coupling `κ`. -/
theorem physRep_ode (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} {u r : Ell2}
    (hr : riccatiT hLf.out ha hz (κ / L) u (jEll u) r = r) (x : ℝ) :
    HasDerivAt (physRep L a r)
      (Complex.I * z * physRep L a r x + physRep L a u x
        - (κ : ℂ) * conj (physRep L a u x) * physRep L a r x ^ 2) x := by
  have key := physical_rep_ode_sqrt hLf.out ha hz (κ / L) hr x
  have hV : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a (jEll u)) x
      = conj ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * series L (toField L a u) x) := by
    rw [series_jEll, map_mul, Complex.conj_ofReal]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hLf.out.ne'
  have hκ' : ((κ / L : ℝ) : ℂ) * (L : ℂ) = (κ : ℂ) := by
    rw [Complex.ofReal_div, div_mul_cancel₀ _ hL0]
  refine key.congr_deriv ?_
  simp only [physRep]
  rw [hV, hκ'] <;> ring

/-- **C4 statement (physical κ).** For `κ > 0`, the `L²` discriminant of the field `fieldMap u`
at `z` is `ψ + ψ⁻¹`, with `ψ = RiccatiMonodromy.psi κ (physRep u) (physRep r) z L`, for any `u, r`
with the fixed point `riccatiT (κ/L) u (jEll u) r = r`. -/
theorem l2_discriminant_monodromy (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a)
    {z : ℂ} (hz : 0 < z.im) {κ : ℝ} (hκ : 0 < κ) (u r : Ell2)
    (hr : riccatiT hLf.out ha hz (κ / L) u (jEll u) r = r) :
    QuantumNLS.L2SpatialTransfer.discriminant κ
        (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) z
      = QuantumNLS.RiccatiMonodromy.psi κ (physRep L a u) (physRep L a r) z L
        + (QuantumNLS.RiccatiMonodromy.psi κ (physRep L a u) (physRep L a r) z L)⁻¹ := by
  obtain ⟨G, -, hGae, hGpt, -⟩ := fieldMap_rep L ha u
  have hfun : (fun x : ℝ => G (x : AddCircle L)) = physRep L a u :=
    funext (fun x => hGpt x)
  have hae := (QuantumNLS.L2SpatialTransfer.profile_ae_of_representative
    (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) hGae.symm).symm
  rw [hfun] at hae
  exact QuantumNLS.RiccatiL2Classical.discriminant_eq_monodromy hκ
    (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) (physRep_continuous L ha u) hae
    (fun x => physRep_ode L ha hz hr x) (physRep_periodic (a := a) hLf.out r)

end QuantumNLS.RiccatiPointwiseDisc

#print axioms QuantumNLS.RiccatiPointwiseDisc.conj_ex
#print axioms QuantumNLS.RiccatiPointwiseDisc.toField_jEll
#print axioms QuantumNLS.RiccatiPointwiseDisc.series_jEll
#print axioms QuantumNLS.RiccatiPointwiseDisc.physRep_sup_bound
#print axioms QuantumNLS.RiccatiPointwiseDisc.physRep_periodic
#print axioms QuantumNLS.RiccatiPointwiseDisc.physRep_continuous
#print axioms QuantumNLS.RiccatiPointwiseDisc.physRep_ode
#print axioms QuantumNLS.RiccatiPointwiseDisc.l2_discriminant_monodromy
