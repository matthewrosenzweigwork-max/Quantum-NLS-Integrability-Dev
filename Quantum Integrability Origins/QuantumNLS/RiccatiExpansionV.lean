import Mathlib
import QuantumNLS.RiccatiExpansions
import QuantumNLS.RiccatiChargeIdent
import QuantumNLS.RiccatiIndependentV

/-!
# R-3FEAD88B stage V1: independent-`v` expansion of the Floquet integral and of the log (`RiccatiExpansionV`)

Model coupling `κ / L` in the Ell2 Riccati equation, physical coupling `κ` in the log (`κ_phys = κ_model · L`),
exactly as in `RiccatiExpansions.log_expansion`. The Floquet integral is the independent-field one,
`J_v[r] = ∫₀ᴸ v r` (no conjugation), written as `modeCoef L a (lowT v) r`.

Frozen inputs (read only): `RiccatiExpansions` (`expansion_a`, `pointwise_expansion`, `logR`, `logC`, `logS`,
`physK`, `remR`, `remC`, `logB`, `physRep_*`), `RiccatiChargeIdent` (`Wc`, `printed_recursion`, `charge_integral`),
`RiccatiIndependentV` (`logS_sub_bound_gen`), `RiccatiFloquet` (`tail_exp_bound`), `RiccatiJBound` (`sector_smallness`).

Proved here:
* `norm_modeCoef_le`: `‖∫₀ᴸ f g‖ ≤ L · F · G` from sup bounds on `f`, `g` (no conjugation).
* `modeCoef_add`, `modeCoef_rMsum`: linearity and the `rMsum` identity for the unconjugated integral.
* `jv_expansion`: sup-norm expansion `‖J_v[r] − i Σ_{n=1}^M I_n z⁻ⁿ‖ ≤ E` with `I_n = modeCoef (lowT v) (Wc n)`
  and `E = L · (physK β) · (physK · remC · |z|^{-(M+1)})`, for an independent second field `v`.
* `logV_expansion`: `‖logS L κ z J_v − κ · (i Σ I_n z⁻ⁿ)‖ ≤ logC · |z|^{-(M+1)}`, combining `jv_expansion`,
  `logS_sub_bound_gen` and the exponential tail bound. The constant is the one of `RiccatiExpansions.logC`.

No owner-held contract is used. No `sorry`, `admit`, or custom axioms.
-/

namespace QuantumNLS.RiccatiExpansionV

open Set Filter Topology MeasureTheory
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2
open QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiSobolevE2bYoung
open QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwise
open QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiMonodromy
open QuantumNLS.RiccatiFloquet
open QuantumNLS.RiccatiJBound
open QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiChargeIdent
open QuantumNLS.RiccatiIndependentV (logS_sub_bound_gen)
open QuantumNLS.ComplexifiedSobolevField
open ComplexConjugate

/-! ### Part A: unconjugated Floquet integrals -/

/-- Sup-norm bound for the unconjugated integral `∫₀ᴸ f g` (from `norm_J_le` applied to `conj f`). -/
theorem norm_modeCoef_le {L : ℝ} (hL : 0 ≤ L) {f g : ℝ → ℂ} {F G : ℝ} (hF0 : 0 ≤ F)
    (hf : ∀ x ∈ Icc 0 L, ‖f x‖ ≤ F) (hg : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ G) :
    ‖∫ s in (0 : ℝ)..L, f s * g s‖ ≤ L * (F * G) := by
  have h := norm_J_le hL (f := fun s => (starRingEnd ℂ) (f s)) (r := g) hF0
    (fun x hx => by simpa only [Complex.norm_conj] using hf x hx) hg
  simpa only [Complex.conj_conj] using h

theorem modeCoef_add {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (f x y : Ell2) :
    modeCoef L a f (x + y) = modeCoef L a f x + modeCoef L a f y := by
  haveI : Fact (0 < L) := ⟨hL⟩
  unfold modeCoef
  have hc1 : Continuous (fun s : ℝ => physRep L a f s * physRep L a x s) :=
    (physRep_continuous L ha f).mul (physRep_continuous L ha x)
  have hc2 : Continuous (fun s : ℝ => physRep L a f s * physRep L a y s) :=
    (physRep_continuous L ha f).mul (physRep_continuous L ha y)
  rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [physRep_add hL ha, Pi.add_apply, mul_add]

theorem modeCoef_rMsum {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (f : Ell2) (w : ℕ → Ell2) (ζ : ℂ)
    (M : ℕ) :
    modeCoef L a f (rMsum w ζ M)
      = Complex.I * ∑ n ∈ Finset.Icc 1 M, modeCoef L a f (w n) * ζ ^ n := by
  haveI : Fact (0 < L) := ⟨hL⟩
  unfold modeCoef
  have hpt : ∀ s : ℝ, physRep L a f s * physRep L a (rMsum w ζ M) s
      = Complex.I * ∑ n ∈ Finset.Icc 1 M, ζ ^ n * (physRep L a f s * physRep L a (w n) s) := by
    intro s
    rw [physRep_rMsum hL ha]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hI := integral_finset_const_mul L (Finset.Icc 1 M) (fun n => ζ ^ n)
    (fun n s => physRep L a f s * physRep L a (w n) s)
    (fun n => (physRep_continuous L ha f).mul (physRep_continuous L ha (w n)))
  beta_reduce at hI
  rw [hI]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ### Part B: stage V1a, the sup-norm expansion of `J_v` -/

/-- **Independent-`v` Floquet expansion.** For `r` the bottom-level fixed point of `riccatiT` with fields
`(lowT u, lowT v)` and model coupling `κ / L`:
`‖J_v[r] − i Σ_{n=1}^M I_n z⁻ⁿ‖ ≤ L · (physK β) · (physK · remC · |z|^{-(M+1)})`, where
`J_v[r] = ∫₀ᴸ v r` and `I_n = ∫₀ᴸ v w_n` with `w_n = Wc n` (the printed `w_n[u,v]`). -/
theorem jv_expansion {a S : ℝ} {M : ℕ} (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2) (β : ℝ) (hβ : 0 < β)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : remR L a S M (κ / L) β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) :
    ‖modeCoef L a (lowT L a S v) r
        - Complex.I * ∑ n ∈ Finset.Icc 1 M,
            modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n‖
      ≤ L * (physK L a * β) * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹)) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have hrem := (expansion_a L hL ha haS hM (κ / L) u v β hβ hu hv D hD δ hδ z hz hsec hR).2 r hr hrn
  have hlv : ‖lowT L a S v‖ ≤ β := (norm_lowT_le L a S v).trans hv
  have hF : ∀ s : ℝ, ‖physRep L a (lowT L a S v) s‖ ≤ physK L a * β := fun s =>
    (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hlv (physK_nonneg ha0))
  set rM := rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) ((κ / L : ℝ) : ℂ)) (z⁻¹) M
    with hrM
  have hsplit : rM + (r - rM) = r := by abel
  have hJsplit : modeCoef L a (lowT L a S v) r
      = modeCoef L a (lowT L a S v) rM + modeCoef L a (lowT L a S v) (r - rM) := by
    rw [← modeCoef_add hL ha, hsplit]
  have hJM : modeCoef L a (lowT L a S v) rM = Complex.I * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n :=
    modeCoef_rMsum hL ha _ _ _ _
  have hJdiff : modeCoef L a (lowT L a S v) r - Complex.I * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n
      = modeCoef L a (lowT L a S v) (r - rM) := by
    rw [hJsplit, hJM]
    ring
  have hR' : ∀ s : ℝ, ‖physRep L a (r - rM) s‖
      ≤ physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹) := fun s =>
    (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hrem (physK_nonneg ha0))
  have hbound := norm_modeCoef_le hL.le (f := physRep L a (lowT L a S v))
    (g := physRep L a (r - rM)) (mul_nonneg (physK_nonneg ha0) hβ.le) (fun x _ => hF x)
    (fun x _ => hR' x)
  rw [hJdiff]
  unfold modeCoef
  exact hbound.trans (le_of_eq (by ring))

/-! ### Part C: stage V1b, the log expansion for independent `v` -/

/-- **Independent-`v` log expansion (bound).** With `J = J_v[r]`, `S = i Σ I_n z⁻ⁿ` and the physical `κ`:
`‖logS κ z J − κ · S‖ ≤ logC · |z|^{-(M+1)}`, the constant of `RiccatiExpansions.logC`. -/
theorem logV_expansion {a S : ℝ} {M : ℕ} (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2) (β : ℝ) (hβ : 0 < β)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) :
    ‖logS L κ z (modeCoef L a (lowT L a S v) r)
        - (κ : ℂ) * (Complex.I * ∑ n ∈ Finset.Icc 1 M,
            modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n)‖
      ≤ logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹ := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  unfold logR at hR
  have hz1 : 1 ≤ ‖z‖ := (le_max_of_le_right (le_max_left _ _)).trans hR
  have hRa : remR L a S M (κ / L) β δ ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hsm : (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L) ≤ ‖z‖ :=
    (le_max_of_le_right (le_max_right _ _)).trans hR
  have hlv : ‖lowT L a S v‖ ≤ β := (norm_lowT_le L a S v).trans hv
  have hδim : δ ≤ z.im := by nlinarith
  have hdiv : 2 * β / z.im ≤ 2 * β / δ :=
    div_le_div_of_nonneg_left (by linarith) hδ hδim
  have hF : ∀ s : ℝ, ‖physRep L a (lowT L a S v) s‖ ≤ physK L a * β := fun s =>
    (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hlv (physK_nonneg ha0))
  have hRb : ∀ s : ℝ, ‖physRep L a r s‖ ≤ physK L a * (2 * β / δ) := fun s =>
    (physRep_norm_le hL ha r s).trans
      (mul_le_mul_of_nonneg_left (hrn.trans hdiv) (physK_nonneg ha0))
  have hJB : ‖modeCoef L a (lowT L a S v) r‖ ≤ logB L a β δ := by
    unfold modeCoef logB
    have h := norm_modeCoef_le hL.le (f := physRep L a (lowT L a S v)) (g := physRep L a r)
      (mul_nonneg (physK_nonneg ha0) hβ.le) (fun x _ => hF x) (fun x _ => hRb x)
    exact h.trans (le_of_eq (by ring))
  have hsmall : Real.exp (2 * |κ| * logB L a β δ) * Real.exp (-(z.im * L)) ≤ 1 / 2 :=
    sector_smallness (L := L) (δ := δ) (Kb := |κ|) (B := logB L a β δ)
      (R := (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L)) (z := z) hL hδ le_rfl hsm hsec
  set J := modeCoef L a (lowT L a S v) r with hJ
  set Ssum := Complex.I * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n with hSsum
  -- the sup-norm expansion of `J - S`
  have hJS : ‖J - Ssum‖ ≤ L * (physK L a * β)
      * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹)) :=
    jv_expansion L hL ha haS hM κ u v β hβ hu hv D hD δ hδ z hz hsec hRa r hr hrn
  have hw : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖ ≤ 1 / 2 :=
    (tail_exp_bound L κ z J _ hJB).trans hsmall
  have hexpo : Real.exp (-(z.im * L))
      ≤ ((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹ := by
    have hx : 0 < δ * ‖z‖ * L := mul_pos (mul_pos hδ (by linarith)) hL
    have h1 : δ * ‖z‖ * L ≤ z.im * L := mul_le_mul_of_nonneg_right hsec hL.le
    have h2 : Real.exp (-(z.im * L)) ≤ Real.exp (-(δ * ‖z‖ * L)) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-(δ * ‖z‖ * L))
        ≤ (Nat.factorial (M + 1) : ℝ) / (δ * ‖z‖ * L) ^ (M + 1) := by
      rw [Real.exp_neg]
      have h4 := Real.pow_div_factorial_le_exp (δ * ‖z‖ * L) hx.le (M + 1)
      calc (Real.exp (δ * ‖z‖ * L))⁻¹
          ≤ ((δ * ‖z‖ * L) ^ (M + 1) / (Nat.factorial (M + 1) : ℝ))⁻¹ :=
            inv_anti₀ (div_pos (pow_pos hx _) (by positivity)) h4
        _ = (Nat.factorial (M + 1) : ℝ) / (δ * ‖z‖ * L) ^ (M + 1) := by rw [inv_div]
    have h5 : (Nat.factorial (M + 1) : ℝ) / (δ * ‖z‖ * L) ^ (M + 1)
        = ((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹ := by
      rw [show δ * ‖z‖ * L = (δ * L) * ‖z‖ by ring, mul_pow]
      ring
    exact h2.trans (h3.trans h5.le)
  have hw_bound : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖
      ≤ Real.exp (2 * |κ| * logB L a β δ)
        * (((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹) :=
    (tail_exp_bound L κ z J _ hJB).trans
      (mul_le_mul_of_nonneg_left hexpo (Real.exp_pos _).le)
  have key := logS_sub_bound_gen κ J Ssum
    (Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)) _ hJS hw
  have hkn : ‖(κ : ℂ)‖ = |κ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hgoal : logS L κ z J - (κ : ℂ) * Ssum
      = (κ : ℂ) * J + Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))
        - (κ : ℂ) * Ssum := rfl
  rw [hgoal]
  refine key.trans ?_
  rw [hkn]
  have hfin : |κ| * (L * (physK L a * β)
      * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹)))
      + 3 / 2 * (Real.exp (2 * |κ| * logB L a β δ)
        * (((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹))
      = logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹ := by
    unfold logC
    ring
  have hle : |κ| * (L * (physK L a * β)
      * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹)))
      + 3 / 2 * ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖
      ≤ |κ| * (L * (physK L a * β)
      * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹)))
      + 3 / 2 * (Real.exp (2 * |κ| * logB L a β δ)
        * (((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹)) := by
    have := hw_bound
    linarith
  linarith [hle, hfin]

end QuantumNLS.RiccatiExpansionV

#print axioms QuantumNLS.RiccatiExpansionV.norm_modeCoef_le
#print axioms QuantumNLS.RiccatiExpansionV.modeCoef_add
#print axioms QuantumNLS.RiccatiExpansionV.modeCoef_rMsum
#print axioms QuantumNLS.RiccatiExpansionV.jv_expansion
#print axioms QuantumNLS.RiccatiExpansionV.logV_expansion
