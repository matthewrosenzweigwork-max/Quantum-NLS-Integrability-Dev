import Mathlib
import QuantumNLS.RiccatiExpansions
import QuantumNLS.RiccatiChargeLevels
import QuantumNLS.RiccatiDerivative
import QuantumNLS.RiccatiPointwise
import QuantumNLS.RiccatiPointwiseDisc
import QuantumNLS.RiccatiPointwiseRep

/-!
# E1 RiccatiChargeIdent (R-3FEAD88B, printed eq:charges)

Printed recursion (source-text model, eq:charges): `v_1 = u`, `v_{j+1} = -i ∂ v_j + κ v̄ Σ_{a=1}^{j-1} v_a v_{j-a}`,
`I_j = ∫ v̄ v_j`. For independent `u, v` the printed charges are `w_n[u,v]` with `φ = u`, `φ̄ = v`.

This module identifies the Ell2 recursion `wAbs` of `RiccatiChargeLevels` (weight `a`, level `S`, cut-off `M`,
model coupling `κ / L`) with the printed recursion at the level of the physical representation `physRep`.
In the physical normalisation the model coupling `κ / L` becomes the physical coupling `κ`, because
`physRep (x · y) = √L · physRep x · physRep y`. The second field is independent (`v` need not equal `ū`).
-/

noncomputable section

open Complex Finset

namespace QuantumNLS.RiccatiChargeIdent

open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiDerivative QuantumNLS.RiccatiSobolevS
open QuantumNLS.RiccatiPointwise QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPointwiseRep

/-- ℓ¹ summability of the Fourier-coefficient profile of an `Ell2` element at weight `a > 1/2`. -/
theorem summable_norm_toField' {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x : Ell2) :
    Summable (fun k => ‖toField L a x k‖) :=
  l1_summable hL ha (hsq_summable_eq (hsq_toField_ne_top L a x)).1

/-- Physical product rule: `physRep (x · y) = √L · physRep x · physRep y`. -/
theorem physRep_mulEll {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) (t : ℝ) :
    physRep L a (mulEll hL ha x y) t
      = ((Real.sqrt L : ℝ) : ℂ) * physRep L a x t * physRep L a y t := by
  have hs : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hL).ne'
  have key : ((Real.sqrt L : ℝ) : ℂ) * ((Real.sqrt L : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs
  simp only [physRep]
  rw [toField_mulEll hL ha x y,
    series_mul_convC L (summable_norm_toField' hL ha x) (summable_norm_toField' hL ha y) t]
  push_cast
  linear_combination (-(((Real.sqrt L : ℝ) : ℂ)⁻¹ * series L (toField L a x) t
    * series L (toField L a y) t)) * key

/-- The same product rule for the model product `mulLin`. -/
theorem physRep_mulLin {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) (t : ℝ) :
    physRep L a (mulLin hL ha x y) t
      = ((Real.sqrt L : ℝ) : ℂ) * physRep L a x t * physRep L a y t :=
  physRep_mulEll hL ha x y t

/-- Pointwise derivative of the physical representation on `dDom`: the derivative of
`physRep w` is `physRep (∂ w)`, with `∂` the multiplier `dSymb`. -/
theorem physRep_hasDerivAt {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {w : Ell2} (hw : w ∈ dDom L)
    (t : ℝ) :
    HasDerivAt (physRep L a w) (physRep L a (dmulEll L ⟨w, hw⟩) t) t := by
  have hc := summable_norm_toField' hL ha w
  have hd := summable_norm_toField' hL ha (dmulEll L ⟨w, hw⟩)
  have hdk : ∀ k : ℤ, toField L a (dmulEll L ⟨w, hw⟩) k
      = Complex.I * ((QuantumNLS.Fourier.freq L k : ℝ) : ℂ) * toField L a w k := by
    intro k
    rw [toField_dmulEll]
    rfl
  have hrec : ∀ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * toField L a w k
      = Complex.I * (0 : ℂ) * toField L a w k + toField L a (dmulEll L ⟨w, hw⟩) k := by
    intro k
    rw [hdk k]
    simp only [QuantumNLS.Fourier.freq]
    push_cast
    ring
  have h := ((series_hasDerivAt hc hd hrec t).const_mul (((Real.sqrt L)⁻¹ : ℝ) : ℂ))
  have e : physRep L a (dmulEll L ⟨w, hw⟩) t
      = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (Complex.I * 0 * series L (toField L a w) t
          + series L (toField L a (dmulEll L ⟨w, hw⟩)) t) := by
    simp [physRep]
  rw [e]
  exact h

/-- Model charge sequence: the Ell2 recursion `wAbs` with model coupling `κ / L`. -/
def Wc {L a : ℝ} (S : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ) (u v : Ell2) (D : Ell2 →ₗ[ℂ] Ell2)
    (N : ℕ) : Ell2 :=
  wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) ((κ / L : ℝ) : ℂ) N

/-- Algebraic cancellation `(κ/L) (√L V)(√L Σ) = κ V Σ`. -/
theorem aux_key (c V S' s LL : ℂ) (hLL : LL ≠ 0) (hs : s * s = LL) :
    c / LL * (s * V * (s * S')) = c * V * S' := by
  rw [show c / LL * (s * V * (s * S')) = c * V * S' * ((s * s) / LL) by ring, hs,
    div_self hLL, mul_one]

/-- **E1, printed recursion.** The physical functions `F_n = physRep (w_n)` of the Ell2 charge
recursion satisfy the printed recursion `v_1 = u`, `v_{n+2} = -i ∂ v_{n+1} + κ v Σ_{j=1}^{n} v_j v_{n+1-j}`
(independent `u`, `v`; physical coupling `κ`), for every `n` with `n + 2 ≤ M`. -/
theorem printed_recursion {L a : ℝ} {S : ℝ} {M : ℕ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y) :
    physRep L a (Wc S hL ha κ u v D 1) = physRep L a (lowT L a S u) ∧
    ∀ n : ℕ, n + 2 ≤ M → ∀ t : ℝ,
      physRep L a (Wc S hL ha κ u v D (n + 2)) t
        = -(Complex.I * deriv (physRep L a (Wc S hL ha κ u v D (n + 1))) t)
          + (κ : ℂ) * physRep L a (lowT L a S v) t
            * ∑ j ∈ Finset.Ico 1 (n + 1),
                physRep L a (Wc S hL ha κ u v D j) t
                  * physRep L a (Wc S hL ha κ u v D (n + 1 - j)) t := by
  have hW1 : ∀ N, 1 ≤ N → N ≤ M → Wc S hL ha κ u v D N
      = lowT L a (lv S M N) (chg L hL ha haS ((κ / L : ℝ) : ℂ) u v N) := fun N h1 hNM =>
    wAbs_identity L hL ha haS hM ((κ / L : ℝ) : ℂ) u v D hD N h1 hNM
  have hdom : ∀ N, 1 ≤ N → N ≤ M → Wc S hL ha κ u v D N ∈ dDom L := by
    intro N h1 hNM
    rw [hW1 N h1 hNM]
    exact lowT_mem_dDom (by linarith [lv_ge haS N] : a + 1 ≤ lv S M N) _
  have hDer : ∀ N, 1 ≤ N → N ≤ M → ∀ t : ℝ,
      deriv (physRep L a (Wc S hL ha κ u v D N)) t
        = physRep L a (D (Wc S hL ha κ u v D N)) t := by
    intro N h1 hNM t
    have hm := hdom N h1 hNM
    have e : D (Wc S hL ha κ u v D N) = dmulEll L ⟨_, hm⟩ := hD ⟨_, hm⟩
    rw [e]
    exact (physRep_hasDerivAt hL ha hm t).deriv
  have hLc : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsq : ((Real.sqrt L : ℝ) : ℂ) * ((Real.sqrt L : ℝ) : ℂ) = ((L : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hL.le]
  refine ⟨?_, ?_⟩
  · unfold Wc
    rw [wAbs_one]
  · intro n hn t
    have hN1 : 1 ≤ n + 1 := by omega
    have hNM : n + 1 ≤ M := by omega
    have hrec : Wc S hL ha κ u v D (n + 2)
        = -(Complex.I • D (Wc S hL ha κ u v D (n + 1)))
          + ((κ / L : ℝ) : ℂ) • mulLin hL ha (lowT L a S v)
              (∑ j ∈ Finset.Ico 1 (n + 1),
                mulLin hL ha (Wc S hL ha κ u v D j) (Wc S hL ha κ u v D (n + 1 - j))) := by
      unfold Wc
      exact wAbs_rec (mulLin hL ha) D (lowT L a S v) (lowT L a S u) ((κ / L : ℝ) : ℂ) n
    have hX : physRep L a (∑ j ∈ Finset.Ico 1 (n + 1),
          mulLin hL ha (Wc S hL ha κ u v D j) (Wc S hL ha κ u v D (n + 1 - j))) t
        = ((Real.sqrt L : ℝ) : ℂ) * ∑ j ∈ Finset.Ico 1 (n + 1),
            physRep L a (Wc S hL ha κ u v D j) t
              * physRep L a (Wc S hL ha κ u v D (n + 1 - j)) t := by
      have h := congrFun (physRep_sum hL ha (Finset.Ico 1 (n + 1))
        (fun j => mulLin hL ha (Wc S hL ha κ u v D j) (Wc S hL ha κ u v D (n + 1 - j)))) t
      simp only [Finset.sum_apply] at h
      rw [h, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [physRep_mulLin hL ha]
      ring
    rw [hrec, physRep_add hL ha, ← neg_smul, physRep_smul, physRep_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [physRep_mulLin hL ha, hX, ← hDer (n + 1) hN1 hNM t]
    push_cast
    rw [aux_key _ _ _ _ _ hLc hsq]
    ring

/-- **E1, charge integrals.** `I_N[u,v] = ∫ v w_N` is the mode coefficient of `v` against the
physical charge `physRep (w_N)` (definitional, by `modeCoef`). -/
theorem charge_integral {L a : ℝ} {S : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ)
    (u v : Ell2) (D : Ell2 →ₗ[ℂ] Ell2) (N : ℕ) :
    modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D N)
      = ∫ s in (0 : ℝ)..L, physRep L a (lowT L a S v) s * physRep L a (Wc S hL ha κ u v D N) s :=
  rfl

end QuantumNLS.RiccatiChargeIdent

#print axioms QuantumNLS.RiccatiChargeIdent.printed_recursion
#print axioms QuantumNLS.RiccatiChargeIdent.charge_integral
#print axioms QuantumNLS.RiccatiChargeIdent.physRep_hasDerivAt
#print axioms QuantumNLS.RiccatiChargeIdent.physRep_mulEll
#print axioms QuantumNLS.RiccatiChargeIdent.aux_key
