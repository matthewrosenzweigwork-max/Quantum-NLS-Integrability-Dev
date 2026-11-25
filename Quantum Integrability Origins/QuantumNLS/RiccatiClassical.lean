import Mathlib
import QuantumNLS.RiccatiIndependentV
import QuantumNLS.RiccatiPointwiseRep
import QuantumNLS.RiccatiChargeIdent
import QuantumNLS.RiccatiPointwiseCoef
import QuantumNLS.RiccatiRemainder

/-!
# R-3FEAD88B stage C2: classical periodic solution and the discriminant bridge (`RiccatiClassical`)

Discharges the inputs `hr`, `hper` of `RiccatiIndependentV.cxDisc_eq_monodromy` for the Ell2 Riccati branch.

Proved here (all for `κ > 0` physical, model coupling `κ / L`, arbitrary Ell2 fields `u v`):
* `ropCLM_mem_dDom`: the resolvent `(∂x − i z)⁻¹` maps `Ell2` into `dDom L` (multiplier `|freq|/|freq − z| ≤ 1 + |z|/Im z`).
* `ropCLM_injective`: the resolvent is injective (coefficientwise division by a nonzero denominator).
* `riccati_classical_ode`: for a fixed point `riccatiT (κ/L) u v r = r`, the physical profile `physRep r` is
  differentiable everywhere with `(physRep r)' = i z physRep r + physRep u − κ physRep v (physRep r)²` (physical `κ`).
  Its periodicity `physRep r L = physRep r 0` is `physRep_periodic`; continuity is `physRep_continuous`.
* `cxDisc_eq_monodromy_ae`: the a.e.-on-`[0, L]` version of `cxDisc_eq_monodromy` (the complexified transfer
  depends on the profiles only a.e. on `[0, L]`, `L1SpatialTransfer.transfer_eq_of_ae`).
* `cxDisc_fieldMap_riccati`: for `u, v, r` as above, `cxDisc κ (fieldMap u) (fieldMap v) z = m + m⁻¹` with
  `m = psiV κ (physRep v) (physRep r) z L`. Here `fieldMap u` is an `L2T` element whose profile agrees a.e. on
  `[0, L]` with `physRep u` (`fieldMap_rep`, `profile_ae_of_representative`).

Not proved here: the Sobolev-embedding statement that a fixed point of the `H^S` Picard branch is `C¹` in the
classical sense beyond the ODE above (the ODE already gives `C¹` once `physRep v`, `physRep u` are continuous, which
holds for `a > 1/2`). The `H^S` branch enters only through the fixed point `r` (any fixed point).

No owner-held contract is used. No `sorry`, `admit`, or custom axioms.
-/

namespace QuantumNLS.RiccatiClassical

open Set Filter Topology MeasureTheory
open PhysicalTensor (L2T)
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwise
open QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiChargeIdent
open QuantumNLS.RiccatiDerivative
open QuantumNLS.RiccatiMonodromyV (psiV continuous_coefV)
open QuantumNLS.RiccatiIndependentV (trace_transfer_cxCoef)
open QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiSobolevE1 (freq)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Part A: the resolvent on `Ell2` -/

/-- Norm bound of one resolvent-times-derivative coefficient: `|freq| / |freq − z| ≤ 1 + |z| / Im z`. -/
theorem norm_dcoef_le (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : ℂ) (k : ℤ) :
    ‖dSymb L k * (x / (Complex.I * (((freq L k : ℝ) : ℂ) - z)))‖ ≤ (1 + ‖z‖ / z.im) * ‖x‖ := by
  have hd0 : (((freq L k : ℝ) : ℂ) - z) ≠ 0 := by
    have := ne_zero_I_mul L z hz k
    exact right_ne_zero_of_mul this
  have hdpos : 0 < ‖((freq L k : ℝ) : ℂ) - z‖ := norm_pos_iff.2 hd0
  have hdim : z.im ≤ ‖((freq L k : ℝ) : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm (((freq L k : ℝ) : ℂ) - z)
    have him : (((freq L k : ℝ) : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg, abs_of_pos hz] at h
    exact h
  have hfb : ‖((freq L k : ℝ) : ℂ)‖ ≤ ‖((freq L k : ℝ) : ℂ) - z‖ + ‖z‖ := by
    have h := norm_add_le (((freq L k : ℝ) : ℂ) - z) z
    rw [sub_add_cancel] at h
    exact h
  have hq : ‖z‖ ≤ ‖z‖ / z.im * ‖((freq L k : ℝ) : ℂ) - z‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hz]
    nlinarith [norm_nonneg z]
  have hratio : ‖((freq L k : ℝ) : ℂ)‖ / ‖((freq L k : ℝ) : ℂ) - z‖ ≤ 1 + ‖z‖ / z.im := by
    rw [div_le_iff₀ hdpos]
    have e : (1 + ‖z‖ / z.im) * ‖((freq L k : ℝ) : ℂ) - z‖
        = ‖((freq L k : ℝ) : ℂ) - z‖ + ‖z‖ / z.im * ‖((freq L k : ℝ) : ℂ) - z‖ := by ring
    linarith
  have hnum : ‖dSymb L k * (x / (Complex.I * (((freq L k : ℝ) : ℂ) - z)))‖
      = ‖((freq L k : ℝ) : ℂ)‖ / ‖((freq L k : ℝ) : ℂ) - z‖ * ‖x‖ := by
    unfold dSymb
    simp only [norm_mul, norm_div, Complex.norm_I, one_mul]
    ring
  rw [hnum]
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- The resolvent maps `Ell2` into the derivative domain `dDom L` (for `Im z > 0`). -/
theorem ropCLM_mem_dDom (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) :
    ropCLM L z hz x ∈ dDom L := by
  show Memℓp (fun k => dSymb L k * ((ropCLM L z hz x : Ell2) : ℤ → ℂ) k) 2
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((summable_sq x).mul_left ((1 + ‖z‖ / z.im) ^ 2))
  have h := norm_dcoef_le L z hz (x k) k
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  simp only [ropCLM_coord]
  exact h2

/-- The resolvent is injective on `Ell2`. -/
theorem ropCLM_injective (L : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (ropCLM L z hz) := by
  intro x y h
  apply lp.ext
  funext k
  have hk := congrArg (fun w : Ell2 => (w : ℤ → ℂ) k) h
  simp only [ropCLM_coord] at hk
  exact (div_left_inj' (ne_zero_I_mul L z hz k)).1 hk

/-! ### Part B: the classical ODE for a fixed point -/

theorem physRep_sub_apply {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) (t : ℝ) :
    physRep L a (x - y) t = physRep L a x t - physRep L a y t := by
  have h := congrFun (physRep_add hL ha (x - y) y) t
  rw [sub_add_cancel, Pi.add_apply] at h
  rw [h]
  ring

theorem physRep_smul_apply {L a : ℝ} (c : ℂ) (x : Ell2) (t : ℝ) :
    physRep L a (c • x) t = c * physRep L a x t := by
  rw [physRep_smul, Pi.smul_apply, smul_eq_mul]

theorem sqrt_sq_cast {L : ℝ} (hL : 0 < L) :
    ((Real.sqrt L : ℝ) : ℂ) * ((Real.sqrt L : ℝ) : ℂ) = (L : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hL.le]

/-- **Classical ODE of the Ell2 fixed point.** For `r = riccatiT (κ/L) u v r` (model coupling `κ/L`) the physical
profile `physRep r` solves `r' = i z r + u − κ v r²` pointwise on `ℝ`, with the physical `κ`. -/
theorem riccati_classical_ode {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) (κ : ℝ) (u v r : Ell2)
    (hr : riccatiT hL ha hz (κ / L) u v r = r) (t : ℝ) :
    HasDerivAt (physRep L a r)
      (Complex.I * z * physRep L a r t + physRep L a u t
        - (κ : ℂ) * physRep L a v t * physRep L a r t ^ 2) t := by
  set F : Ell2 := u - ((κ / L : ℝ) : ℂ) • mulBil hL ha v (mulBil hL ha r r) with hFdef
  have hF : ropCLM L z hz F = r := by
    rw [hFdef, map_sub, map_smul]
    exact hr
  have hy : r ∈ dDom L := by
    rw [← hF]
    exact ropCLM_mem_dDom L z hz F
  have h1 : ropCLM L z hz (dmulEll L ⟨r, hy⟩ - (Complex.I * z) • r) = r :=
    ropCLM_dmul_sub L z hz ⟨r, hy⟩
  have hid : dmulEll L ⟨r, hy⟩ - (Complex.I * z) • r = F := by
    apply ropCLM_injective L z hz
    exact h1.trans hF.symm
  have hD : dmulEll L ⟨r, hy⟩ = F + (Complex.I * z) • r := eq_add_of_sub_eq hid
  have hsq := sqrt_sq_cast hL
  have hkL : ((κ / L : ℝ) : ℂ) * (L : ℂ) = (κ : ℂ) := by
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  have hFt : physRep L a F t = physRep L a u t - (κ : ℂ) * physRep L a v t * physRep L a r t ^ 2 := by
    rw [hFdef, physRep_sub_apply hL ha, physRep_smul_apply]
    simp only [mulBil_apply, physRep_mulEll]
    linear_combination (-(((κ / L : ℝ) : ℂ) * physRep L a v t * physRep L a r t ^ 2)) * hsq
      + (-(physRep L a v t * physRep L a r t ^ 2)) * hkL
  have hsum : physRep L a (F + (Complex.I * z) • r) t
      = physRep L a F t + (Complex.I * z) * physRep L a r t := by
    rw [physRep_add hL ha, Pi.add_apply, physRep_smul_apply]
  have hder := physRep_hasDerivAt hL ha hy t
  rw [hD, hsum, hFt] at hder
  convert hder using 1
  ring

/-- Periodicity and continuity of the classical solution. -/
theorem riccati_classical_periodic {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a) (r : Ell2) :
    physRep L a r L = physRep L a r 0 :=
  physRep_periodic hL r

/-! ### Part C: the discriminant with a.e.-continuous profiles -/

/-- **Discriminant identity, a.e. form.** If the profiles agree a.e. on `[0, L]` with continuous `gu`, `gv`
and `r` is a `C¹` periodic solution with the fields `gu`, `gv`, then the complexified discriminant equals
`m + m⁻¹`, `m = ψ(L)` with the classical `gv`. -/
theorem cxDisc_eq_monodromy_ae {L κ : ℝ} [Fact (0 < L)] {u v : L2T L} {gu gv r : ℝ → ℂ} {z : ℂ}
    (hκ : 0 < κ) (hgu : Continuous gu) (hgv : Continuous gv)
    (hu : L2SpatialTransfer.profile u =ᵐ[volume.restrict (Icc 0 L)] gu)
    (hv : L2SpatialTransfer.profile v =ᵐ[volume.restrict (Icc 0 L)] gv)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + gu x - (κ : ℂ) * gv x * r x ^ 2) x)
    (hper : r L = r 0) :
    ComplexifiedDiscriminant.cxDisc κ u v z
      = psiV κ gv r z L + (psiV κ gv r z L)⁻¹ := by
  have hA : ComplexifiedDiscriminant.cxCoef κ (L2SpatialTransfer.profile u)
      (L2SpatialTransfer.profile v) z =ᵐ[volume.restrict (Icc 0 L)]
      ComplexifiedDiscriminant.cxCoef κ gu gv z := by
    filter_upwards [hu, hv] with x hxu hxv
    unfold ComplexifiedDiscriminant.cxCoef
    rw [hxu, hxv]
  have htr : ComplexifiedDiscriminant.cxDisc κ u v z
      = Matrix.trace (L1SpatialTransfer.transfer (ComplexifiedDiscriminant.cxCoef κ gu gv z) L) := by
    unfold ComplexifiedDiscriminant.cxDisc
    rw [L1SpatialTransfer.transfer_eq_of_ae (Fact.out : (0 : ℝ) < L).le hA
      (x := L) ⟨(Fact.out : (0 : ℝ) < L).le, le_rfl⟩]
  rw [htr]
  obtain ⟨Mu, hMu⟩ := LinearFundamental.exists_isFundamental (continuous_coefV κ hgu hgv z)
  exact trace_transfer_cxCoef (Fact.out : (0 : ℝ) < L) hκ hgu hgv hr hper hMu

/-! ### Part D: the Ell2 branch gives the discriminant identity -/

/-- **Stage C2 result.** For `r = riccatiT (κ/L) u v r` and the L2 profiles of the Ell2 fields `fieldMap u`, `fieldMap v`,
`cxDisc κ (fieldMap u) (fieldMap v) z = m + m⁻¹` with `m = ψ(L)` built from the classical solution `physRep r`. -/
theorem cxDisc_fieldMap_riccati {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (ha0 : (0 : ℝ) ≤ a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ) (hκ : 0 < κ) (u v r : Ell2)
    (hr : riccatiT hL ha hz (κ / L) u v r = r) :
    ComplexifiedDiscriminant.cxDisc κ (fieldMap L a ha0 u) (fieldMap L a ha0 v) z
      = psiV κ (physRep L a v) (physRep L a r) z L
        + (psiV κ (physRep L a v) (physRep L a r) z L)⁻¹ := by
  have hae : ∀ x : Ell2, physRep L a x =ᵐ[volume.restrict (Icc 0 L)]
      L2SpatialTransfer.profile (fieldMap L a ha0 x) := by
    intro x
    obtain ⟨g, -, hgae, hgpt, -⟩ := fieldMap_rep L ha x
    have h := L2SpatialTransfer.profile_ae_of_representative (fieldMap L a ha0 x) hgae.symm
    have hfun : physRep L a x = (fun y : ℝ => g (y : AddCircle L)) :=
      funext fun y => (hgpt y).symm
    rw [hfun]
    exact h
  exact cxDisc_eq_monodromy_ae hκ (physRep_continuous L ha u) (physRep_continuous L ha v)
    (hae u).symm (hae v).symm (fun x => riccati_classical_ode hL ha hz κ u v r hr x)
    (riccati_classical_periodic hL ha r)

end QuantumNLS.RiccatiClassical

#print axioms QuantumNLS.RiccatiClassical.norm_dcoef_le
#print axioms QuantumNLS.RiccatiClassical.ropCLM_mem_dDom
#print axioms QuantumNLS.RiccatiClassical.ropCLM_injective
#print axioms QuantumNLS.RiccatiClassical.riccati_classical_ode
#print axioms QuantumNLS.RiccatiClassical.cxDisc_eq_monodromy_ae
#print axioms QuantumNLS.RiccatiClassical.cxDisc_fieldMap_riccati
