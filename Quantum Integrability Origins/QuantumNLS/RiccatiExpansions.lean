import Mathlib
import QuantumNLS.RiccatiRemainder
import QuantumNLS.RiccatiPointwiseDisc
import QuantumNLS.RiccatiPointwiseCoef
import QuantumNLS.RiccatiFloquet
import QuantumNLS.RiccatiJBound
import QuantumNLS.RiccatiSobolevE2bYoung
import QuantumNLS.RiccatiSobolevS
import QuantumNLS.ComplexifiedSobolevField

/-!
# R-3FEAD88B, stage D1: expansions of the Riccati branch (values:prop:riccati)

Model coupling `κ / L` in the Ell2 Riccati equation, physical coupling `κ` in the
log expansion (`κ_phys = κ_model · L`).

* (a) `expansion_a`: for a fixed point `r` of `riccatiT` on the bottom-level fields,
  `‖r - rMsum w_n z⁻¹ M‖ ≤ C ‖z‖^{-(M+1)}` with explicit `R`, `C` (from `remainder_bound`),
  and existence of such a fixed point (from `riccatiT_fixed_exists_unique`).
* (c) `pointwise_expansion`: the sup-norm version through `physRep_norm_le`.
* (b) `log_expansion`: the real-slice logarithm expansion from `l2_discriminant_monodromy`,
  the Floquet identity `trace_exp_identity` and `tail_log_bound`.

No owner-held contract is used. No `sorry`, `admit`, or custom axioms.
-/

namespace QuantumNLS.RiccatiExpansions

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
open QuantumNLS.ComplexifiedSobolevField
open ComplexConjugate

/-! ### Part A: `ℓ¹` control of Fourier coefficients by the `Ell2` norm -/

theorem l1_le_norm {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x : Ell2) :
    ∑' k : ℤ, ‖toField L a x k‖ ≤ ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2) * ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp [toField]
  have hs : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsum2 : ∑' k : ℤ, wt L a k * ‖toField L a x k‖ ^ 2 = ‖x‖ ^ 2 := by
    have h1 := (hsq_summable_eq (hsq_toField_ne_top L a x)).2
    rw [hsq_toField] at h1
    have h0 : 0 ≤ ∑' k : ℤ, wt L a k * ‖toField L a x k‖ ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (wt_pos (by linarith) k).le (sq_nonneg _)
    exact ((ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) h0).1 h1).symm
  have hA : Summable (fun k : ℤ => wt L a k * ‖toField L a x k‖ ^ 2) :=
    (hsq_summable_eq (hsq_toField_ne_top L a x)).1
  have hB : Summable (fun k : ℤ => (wt L a k)⁻¹) := summable_inv_wt hL ha
  set s := ‖x‖ with hs_def
  set t := s⁻¹ with ht_def
  have hterm : ∀ k : ℤ, ‖toField L a x k‖ ≤
      (1 / 2) * (t * (wt L a k * ‖toField L a x k‖ ^ 2) + s * (wt L a k)⁻¹) := by
    intro k
    have hw : 0 < t * wt L a k := mul_pos (inv_pos.mpr hs) (wt_pos (by linarith) k)
    have h := amgm_l1 (x := ‖toField L a x k‖) hw
    have e : (t * wt L a k)⁻¹ = s * (wt L a k)⁻¹ := by
      rw [mul_inv, ht_def, inv_inv]
    calc ‖toField L a x k‖
        ≤ (1 / 2) * ((t * wt L a k) * ‖toField L a x k‖ ^ 2 + (t * wt L a k)⁻¹) := h
      _ = (1 / 2) * (t * (wt L a k * ‖toField L a x k‖ ^ 2) + s * (wt L a k)⁻¹) := by
        rw [e]; ring
  have hsumm : Summable (fun k : ℤ =>
      (1 / 2) * (t * (wt L a k * ‖toField L a x k‖ ^ 2) + s * (wt L a k)⁻¹)) :=
    ((hA.mul_left t).add (hB.mul_left s)).mul_left (1 / 2)
  calc ∑' k : ℤ, ‖toField L a x k‖
      ≤ ∑' k : ℤ, (1 / 2) * (t * (wt L a k * ‖toField L a x k‖ ^ 2) + s * (wt L a k)⁻¹) :=
        Summable.tsum_le_tsum hterm (summable_norm_toField hL ha x) hsumm
    _ = (1 / 2) * (t * ∑' k : ℤ, wt L a k * ‖toField L a x k‖ ^ 2
          + s * ∑' k : ℤ, (wt L a k)⁻¹) := by
        rw [tsum_mul_left, Summable.tsum_add (hA.mul_left t) (hB.mul_left s)]
        simp only [tsum_mul_left]
    _ = ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2) * s := by
        rw [hsum2]
        have hts : t * s ^ 2 = s := by rw [ht_def]; field_simp
        linear_combination (1 / 2 : ℝ) * hts

/-! ### Part B: the physical representative is additive and finite-sum linear -/

theorem series_add_norm {L : ℝ} {c d : ℤ → ℂ} (hc : Summable (fun k => ‖c k‖))
    (hd : Summable (fun k => ‖d k‖)) (y : ℝ) :
    series L (fun k => c k + d k) y = series L c y + series L d y := by
  unfold series
  simp only [add_mul]
  exact Summable.tsum_add (summable_mul_ex hc y) (summable_mul_ex hd y)

theorem physRep_add {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    physRep L a (x + y) = physRep L a x + physRep L a y := by
  funext t
  simp only [physRep, Pi.add_apply]
  rw [toField_add, series_add_norm (summable_norm_toField hL ha x)
    (summable_norm_toField hL ha y), mul_add]

theorem physRep_zero {L a : ℝ} : physRep L a 0 = 0 := by
  funext t
  simp [physRep, toField, series]

theorem physRep_smul {L a : ℝ} (c : ℂ) (x : Ell2) :
    physRep L a (c • x) = c • physRep L a x := by
  funext t
  have hs : series L (toField L a (c • x)) t = c * series L (toField L a x) t := by
    rw [toField_smul]
    unfold series
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  simp only [physRep, Pi.smul_apply, smul_eq_mul]
  rw [hs]
  ring

theorem physRep_sum {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (s : Finset ℕ) (f : ℕ → Ell2) :
    physRep L a (∑ n ∈ s, f n) = ∑ n ∈ s, physRep L a (f n) := by
  induction s using Finset.induction_on with
  | empty => simp [physRep_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, physRep_add hL ha, ih]

theorem physRep_rMsum {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (w : ℕ → Ell2) (ζ : ℂ)
    (M : ℕ) (t : ℝ) :
    physRep L a (rMsum w ζ M) t
      = Complex.I * ∑ n ∈ Finset.Icc 1 M, ζ ^ n * physRep L a (w n) t := by
  unfold rMsum
  rw [physRep_smul, physRep_sum hL ha]
  simp only [physRep_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

theorem physRep_jEll (L a : ℝ) (x : Ell2) (s : ℝ) :
    physRep L a (jEll x) s = conj (physRep L a x s) := by
  simp only [physRep, series_jEll, map_mul, Complex.conj_ofReal]

/-! ### Part C: the sup bound -/

/-- Constant of the sup bound `‖physRep x t‖ ≤ physK · ‖x‖`. -/
noncomputable def physK (L a : ℝ) : ℝ :=
  (Real.sqrt L)⁻¹ * ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2)

theorem physK_nonneg {L a : ℝ} (ha : 0 ≤ a) : 0 ≤ physK L a := by
  have hS : 0 ≤ ∑' k : ℤ, (wt L a k)⁻¹ := tsum_nonneg fun k => (inv_pos.mpr (wt_pos ha k)).le
  unfold physK
  apply mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  linarith

theorem physRep_norm_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x : Ell2) (t : ℝ) :
    ‖physRep L a x t‖ ≤ physK L a * ‖x‖ := by
  unfold physK
  have h1 := physRep_sup_bound hL ha x t
  have h2 := l1_le_norm hL ha x
  have hpos : 0 ≤ (Real.sqrt L)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc ‖physRep L a x t‖ ≤ (Real.sqrt L)⁻¹ * ∑' k : ℤ, ‖toField L a x k‖ := h1
    _ ≤ (Real.sqrt L)⁻¹ * (((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h2 hpos
    _ = (Real.sqrt L)⁻¹ * ((1 + ∑' k : ℤ, (wt L a k)⁻¹) / 2) * ‖x‖ := by ring

/-! ### Part D: `lowT` commutes with the conjugation involution `jEll` -/

theorem lowT_jEll (L a S : ℝ) (x : Ell2) :
    lowT L a S (jEll x) = jEll (lowT L a S x) := by
  by_cases h : a ≤ S
  · unfold lowT
    rw [dif_pos h, dif_pos h]
    ext k
    show ((QuantumNLS.RiccatiSobolevS.incMult L a S k : ℝ) : ℂ) * conj (x (-k))
      = conj (((QuantumNLS.RiccatiSobolevS.incMult L a S (-k) : ℝ) : ℂ) * x (-k))
    unfold QuantumNLS.RiccatiSobolevS.incMult
    rw [pw_neg, pw_neg, map_mul, Complex.conj_ofReal]
  · unfold lowT
    rw [dif_neg h, dif_neg h]

/-! ### Part E: explicit constants and the Floquet objects -/

/-- The bracket `4|κ| C² β (2β/δ + Σ bnd)` of the smallness hypothesis of `remainder_bound`. -/
noncomputable def remH (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) : ℝ :=
  4 * |κ| * Cmul L a ^ 2 * β
    * (2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N)

/-- `16|κ| C² β²`, the discriminant-side smallness of `riccatiT_fixed_exists_unique`. -/
noncomputable def remQ (L a : ℝ) (κ β : ℝ) : ℝ := 16 * |κ| * Cmul L a ^ 2 * β ^ 2

/-- Radius `R` of the bottom-level expansion, `|z| ≥ R`. -/
noncomputable def remR (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) : ℝ :=
  max 1 (max (remH L a S M κ β δ / δ) (remQ L a κ β / δ ^ 2))

/-- Constant `C` of the bottom-level remainder bound, with `‖lowT v‖` replaced by `β`. -/
noncomputable def remC (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) : ℝ :=
  2 * (bnd L S M (κ : ℂ) β M + ‖(κ : ℂ)‖ * (Cmul L a * β)
    * ((M : ℝ) * ((M : ℝ) * (Cmul L a * (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2))))
    / δ

/-- The Floquet integral `J = ∫₀ᴸ conj(u) r` of the physical profiles. -/
noncomputable def floquetJ (L a : ℝ) (u r : Ell2) : ℂ :=
  ∫ s in (0 : ℝ)..L, (starRingEnd ℂ) (physRep L a u s) * physRep L a r s

/-- The mode coefficient `I_n = ∫₀ᴸ f w_n` of the physical profiles. -/
noncomputable def modeCoef (L a : ℝ) (f w : Ell2) : ℂ :=
  ∫ s in (0 : ℝ)..L, physRep L a f s * physRep L a w s

/-- The gauged log branch `κ J + log(1 + exp(izL - 2κJ))`. -/
noncomputable def logS (L κ : ℝ) (z J : ℂ) : ℂ :=
  (κ : ℂ) * J + Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))

/-- Bound on `|J|` in the sector, `|z| ≥ 1`. -/
noncomputable def logB (L a β δ : ℝ) : ℝ :=
  L * (physK L a * β) * (physK L a * (2 * β / δ))

/-- Radius of the log expansion (physical `κ`, model `κ / L`). -/
noncomputable def logR (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) : ℝ :=
  max (remR L a S M (κ / L) β δ) (max 1 ((2 * |κ| * logB L a β δ + Real.log 2) / (δ * L)))

/-- Constant of the log expansion. -/
noncomputable def logC (L a S : ℝ) (M : ℕ) (κ β δ : ℝ) : ℝ :=
  |κ| * L * (physK L a * β) * (physK L a * remC L a S M (κ / L) β δ)
    + 3 / 2 * Real.exp (2 * |κ| * logB L a β δ)
      * ((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1))

/-! ### Part F: stage (a), the bottom-level expansion -/

theorem expansion_a {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2) (β : ℝ) (hβ : 0 < β)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : remR L a S M κ β δ ≤ ‖z‖) :
    (∃ r : Ell2, riccatiT hL ha hz κ (lowT L a S u) (lowT L a S v) r = r ∧
        ‖r‖ ≤ 2 * β / z.im) ∧
    (∀ r : Ell2, riccatiT hL ha hz κ (lowT L a S u) (lowT L a S v) r = r →
        ‖r‖ ≤ 2 * β / z.im →
        ‖r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M‖
          ≤ remC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹) := by
  unfold remR at hR
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hA : remH L a S M κ β δ / δ ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hB : remQ L a κ β / δ ^ 2 ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hH : remH L a S M κ β δ ≤ δ * ‖z‖ := by
    have := (div_le_iff₀ hδ).1 hA
    linarith
  have hQ : remQ L a κ β ≤ z.im ^ 2 := by
    have h1 : remQ L a κ β ≤ ‖z‖ * δ ^ 2 := (div_le_iff₀ (pow_pos hδ 2)).1 hB
    have h2 : (δ * ‖z‖) ^ 2 ≤ z.im ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg z)) hsec 2
    have h3 : ‖z‖ * δ ^ 2 ≤ (δ * ‖z‖) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.2 hz1), norm_nonneg z]
    linarith
  have hβ' : 0 ≤ β := hβ.le
  constructor
  · obtain ⟨r, hrn, hrf, -⟩ := riccatiT_fixed_exists_unique hL ha hz κ β hβ hQ
      (lowT L a S u) (lowT L a S v) ((norm_lowT_le L a S u).trans hu)
      ((norm_lowT_le L a S v).trans hv)
    exact ⟨r, hrf, hrn⟩
  · intro r hrf hrn
    have key := remainder_bound L hL ha haS hM κ u v β hβ' hu hv D hD δ hδ z hz hz1 hsec hH r
      hrf hrn
    refine key.trans ?_
    have hlv : ‖lowT L a S v‖ ≤ β := (norm_lowT_le L a S v).trans hv
    have hC : 0 ≤ Cmul L a := Real.sqrt_nonneg _
    unfold remC
    gcongr
    all_goals first
      | exact hC
      | exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg hC (sq_nonneg _)))
      | positivity

/-! ### Part G: stage (c), the pointwise version -/

theorem pointwise_expansion {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2) (β : ℝ) (hβ : 0 < β)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : remR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hrf : riccatiT hL ha hz κ (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) (t : ℝ) :
    ‖physRep L a r t
        - Complex.I * ∑ n ∈ Finset.Icc 1 M,
            (z⁻¹) ^ n * physRep L a
              (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ) n) t‖
      ≤ physK L a * (remC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹) := by
  have hrem := (expansion_a L hL ha haS hM κ u v β hβ hu hv D hD δ hδ z hz hsec hR).2 r hrf hrn
  have hsplit : rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M
      + (r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M) = r := by
    abel
  have hdec : physRep L a r t
      = physRep L a (rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ))
          (z⁻¹) M) t
        + physRep L a (r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ))
          (z⁻¹) M) t := by
    have h1 := physRep_add hL ha
      (rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M)
      (r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M)
    rw [hsplit] at h1
    rw [h1, Pi.add_apply]
  have hkey : physRep L a r t
        - Complex.I * ∑ n ∈ Finset.Icc 1 M,
            (z⁻¹) ^ n * physRep L a
              (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ) n) t
      = physRep L a (r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ))
          (z⁻¹) M) t := by
    rw [hdec, physRep_rMsum hL ha]
    ring
  rw [hkey]
  exact (physRep_norm_le hL ha _ t).trans
    (mul_le_mul_of_nonneg_left hrem (physK_nonneg (by linarith)))

/-! ### Part H: Floquet bookkeeping -/

theorem floquetJ_split {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (u r1 r2 : Ell2) :
    floquetJ L a u (r1 + r2) = floquetJ L a u r1 + floquetJ L a u r2 := by
  haveI : Fact (0 < L) := ⟨hL⟩
  unfold floquetJ
  have hc1 : Continuous (fun s : ℝ => (starRingEnd ℂ) (physRep L a u s) * physRep L a r1 s) :=
    (Complex.continuous_conj.comp (physRep_continuous L ha u)).mul (physRep_continuous L ha r1)
  have hc2 : Continuous (fun s : ℝ => (starRingEnd ℂ) (physRep L a u s) * physRep L a r2 s) :=
    (Complex.continuous_conj.comp (physRep_continuous L ha u)).mul (physRep_continuous L ha r2)
  rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [physRep_add hL ha, Pi.add_apply, mul_add]

theorem integral_finset_const_mul (L : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ n, Continuous (f n)) :
    ∫ x in (0 : ℝ)..L, ∑ n ∈ s, c n * f n x = ∑ n ∈ s, c n * ∫ x in (0 : ℝ)..L, f n x := by
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
  · intro n _
    exact (continuous_const.mul (hf n)).intervalIntegrable _ _

theorem floquetJ_rMsum {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (u : Ell2) (w : ℕ → Ell2)
    (ζ : ℂ) (M : ℕ) :
    floquetJ L a u (rMsum w ζ M)
      = Complex.I * ∑ n ∈ Finset.Icc 1 M, modeCoef L a (jEll u) (w n) * ζ ^ n := by
  haveI : Fact (0 < L) := ⟨hL⟩
  unfold floquetJ
  have hpt : ∀ s : ℝ, (starRingEnd ℂ) (physRep L a u s) * physRep L a (rMsum w ζ M) s
      = Complex.I * ∑ n ∈ Finset.Icc 1 M,
          ζ ^ n * (physRep L a (jEll u) s * physRep L a (w n) s) := by
    intro s
    rw [← physRep_jEll, physRep_rMsum hL ha]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hI := integral_finset_const_mul L (Finset.Icc 1 M) (fun n => ζ ^ n)
    (fun n s => physRep L a (jEll u) s * physRep L a (w n) s)
    (fun n => (physRep_continuous L ha (jEll u)).mul (physRep_continuous L ha (w n)))
  beta_reduce at hI
  rw [hI]
  unfold modeCoef
  exact Finset.sum_congr rfl fun n _ => by ring

theorem psi_floquet {L a : ℝ} (κ : ℝ) (hL : 0 < L) (ha : 1 / 2 < a) (z : ℂ) (u r : Ell2) :
    QuantumNLS.RiccatiMonodromy.psi κ (physRep L a u) (physRep L a r) z L
      = Complex.exp (-(Complex.I * z * L / 2) + (κ : ℂ) * floquetJ L a u r) := by
  haveI : Fact (0 < L) := ⟨hL⟩
  unfold floquetJ
  exact psi_eq_exp L (physRep_continuous L ha u) (physRep_continuous L ha r)

/-! ### Part I: stage (b), the logarithm expansion on the real slice -/

theorem log_expansion {a S : ℝ} {M : ℕ} (L : ℝ) [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (hκ : 0 < κ) (u : Ell2) (β : ℝ)
    (hβ : 0 < β) (hu : ‖u‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u) (jEll (lowT L a S u)) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) :
    Complex.exp (logS L κ z (floquetJ L a (lowT L a S u) r))
        = Complex.exp (Complex.I * z * (L : ℂ) / 2)
          * QuantumNLS.L2SpatialTransfer.discriminant κ
              (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S u)) z ∧
    ‖logS L κ z (floquetJ L a (lowT L a S u) r)
        - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
            modeCoef L a (jEll (lowT L a S u))
              (wAbs (mulLin hL ha) D (jEll (lowT L a S u)) (lowT L a S u) ((κ / L : ℝ) : ℂ) n)
              * (z⁻¹) ^ n‖
      ≤ logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹ := by
  haveI : Fact (0 < L) := ⟨hL⟩
  have ha0 : (0 : ℝ) ≤ a := by linarith
  unfold logR at hR
  have hz1 : 1 ≤ ‖z‖ := (le_max_of_le_right (le_max_left _ _)).trans hR
  have hRa : remR L a S M (κ / L) β δ ≤ ‖z‖ := (le_max_left _ _).trans hR
  have hsm : (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L) ≤ ‖z‖ :=
    (le_max_of_le_right (le_max_right _ _)).trans hR
  have hua : ‖lowT L a S u‖ ≤ β := (norm_lowT_le L a S u).trans hu
  have hδim : δ ≤ z.im := by nlinarith
  have hdiv : 2 * β / z.im ≤ 2 * β / δ :=
    div_le_div_of_nonneg_left (by linarith) hδ hδim
  have hF : ∀ s : ℝ, ‖physRep L a (lowT L a S u) s‖ ≤ physK L a * β := fun s =>
    (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hua (physK_nonneg ha0))
  have hRb : ∀ s : ℝ, ‖physRep L a r s‖ ≤ physK L a * (2 * β / δ) := fun s =>
    (physRep_norm_le hL ha r s).trans
      (mul_le_mul_of_nonneg_left (hrn.trans hdiv) (physK_nonneg ha0))
  have hJB : ‖floquetJ L a (lowT L a S u) r‖ ≤ logB L a β δ := by
    unfold floquetJ logB
    have h := norm_J_le (f := physRep L a (lowT L a S u)) (r := physRep L a r) hL.le
      (mul_nonneg (physK_nonneg ha0) hβ.le) (fun x _ => hF x) (fun x _ => hRb x)
    exact h.trans (le_of_eq (by ring))
  have hsmall : Real.exp (2 * |κ| * logB L a β δ) * Real.exp (-(z.im * L)) ≤ 1 / 2 :=
    sector_smallness (L := L) (δ := δ) (Kb := |κ|) (B := logB L a β δ)
      (R := (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L)) (z := z) hL hδ le_rfl hsm hsec
  -- the expansion (a) for this fixed point, with the second field `v = jEll u`
  have hr' : riccatiT hL ha hz (κ / L) (lowT L a S u) (lowT L a S (jEll u)) r = r := by
    rw [lowT_jEll]; exact hr
  have hrem := (expansion_a L hL ha haS hM (κ / L) u (jEll u) β hβ hu
    (by rw [norm_jEll]; exact hu) D hD δ hδ z hz hsec hRa).2 r hr' hrn
  rw [lowT_jEll] at hrem
  -- the Floquet identity on the real slice
  have hdisc := l2_discriminant_monodromy L ha hz hκ (lowT L a S u) r hr
  rw [psi_floquet κ hL ha z (lowT L a S u) r] at hdisc
  set J := floquetJ L a (lowT L a S u) r with hJ
  have hJB' : ‖J‖ ≤ logB L a β δ := hJB
  have hw : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖ ≤ 1 / 2 :=
    (tail_exp_bound L κ z J _ hJB').trans hsmall
  have hne : (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)) ≠ 0 := by
    intro h
    have hw1 : Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) = -1 := by
      linear_combination h
    rw [hw1, norm_neg, norm_one] at hw
    norm_num at hw
  have hid := trace_exp_identity z (L : ℂ) (κ : ℂ) J
  have hpart1 : Complex.exp (logS L κ z J)
      = Complex.exp ((κ : ℂ) * J)
        * (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)) := by
    unfold logS
    rw [Complex.exp_add, Complex.exp_log hne]
  -- the mode split of J
  set rM := rMsum (wAbs (mulLin hL ha) D (jEll (lowT L a S u)) (lowT L a S u)
    ((κ / L : ℝ) : ℂ)) (z⁻¹) M with hrM
  have hsplit : rM + (r - rM) = r := by abel
  have hJsplit : J = floquetJ L a (lowT L a S u) rM + floquetJ L a (lowT L a S u) (r - rM) := by
    rw [← floquetJ_split hL ha, hsplit, hJ]
  have hJM : floquetJ L a (lowT L a S u) rM = Complex.I * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (jEll (lowT L a S u))
        (wAbs (mulLin hL ha) D (jEll (lowT L a S u)) (lowT L a S u) ((κ / L : ℝ) : ℂ) n)
        * (z⁻¹) ^ n :=
    floquetJ_rMsum hL ha _ _ _ _
  have hJdiff : J - Complex.I * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (jEll (lowT L a S u))
        (wAbs (mulLin hL ha) D (jEll (lowT L a S u)) (lowT L a S u) ((κ / L : ℝ) : ℂ) n)
        * (z⁻¹) ^ n
      = floquetJ L a (lowT L a S u) (r - rM) := by
    rw [hJsplit, hJM]
    ring
  have hcore : logS L κ z J - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (jEll (lowT L a S u))
        (wAbs (mulLin hL ha) D (jEll (lowT L a S u)) (lowT L a S u) ((κ / L : ℝ) : ℂ) n)
        * (z⁻¹) ^ n
      = (κ : ℂ) * floquetJ L a (lowT L a S u) (r - rM)
        + Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)) := by
    unfold logS
    linear_combination (κ : ℂ) * hJdiff
  -- the two bounds
  have hkn : ‖(κ : ℂ)‖ = |κ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hJR : ‖floquetJ L a (lowT L a S u) (r - rM)‖
      ≤ L * (physK L a * β * (physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹))) := by
    unfold floquetJ
    have hR' : ∀ s : ℝ, ‖physRep L a (r - rM) s‖
        ≤ physK L a * (remC L a S M (κ / L) β δ * (‖z‖ ^ (M + 1))⁻¹) := fun s =>
      (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hrem (physK_nonneg ha0))
    exact norm_J_le (f := physRep L a (lowT L a S u)) (r := physRep L a (r - rM)) hL.le
      (mul_nonneg (physK_nonneg ha0) hβ.le) (fun x _ => hF x) (fun x _ => hR' x)
  have htail := tail_log_bound L κ z J (logB L a β δ) hJB' hsmall
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
  have hb2 : Real.exp (2 * |κ| * logB L a β δ) * Real.exp (-(z.im * L))
      ≤ Real.exp (2 * |κ| * logB L a β δ)
        * (((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹) :=
    mul_le_mul_of_nonneg_left hexpo (Real.exp_pos _).le
  have hbound2 : ‖Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))‖
      ≤ 3 / 2 * (Real.exp (2 * |κ| * logB L a β δ)
        * (((Nat.factorial (M + 1) : ℝ) / (δ * L) ^ (M + 1)) * (‖z‖ ^ (M + 1))⁻¹)) :=
    htail.trans (mul_le_mul_of_nonneg_left hb2 (by norm_num))
  have hbound1 : ‖(κ : ℂ) * floquetJ L a (lowT L a S u) (r - rM)‖
      ≤ |κ| * (L * (physK L a * β * (physK L a * (remC L a S M (κ / L) β δ
          * (‖z‖ ^ (M + 1))⁻¹)))) := by
    rw [norm_mul, hkn]
    exact mul_le_mul_of_nonneg_left hJR (abs_nonneg κ)
  constructor
  · rw [hpart1, hdisc]
    exact hid.symm
  · rw [hcore]
    calc _ ≤ ‖(κ : ℂ) * floquetJ L a (lowT L a S u) (r - rM)‖
          + ‖Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))‖ :=
          norm_add_le _ _
      _ ≤ _ := add_le_add hbound1 hbound2
      _ = logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹ := by unfold logC; ring

end QuantumNLS.RiccatiExpansions

#print axioms QuantumNLS.RiccatiExpansions.l1_le_norm
#print axioms QuantumNLS.RiccatiExpansions.lowT_jEll
#print axioms QuantumNLS.RiccatiExpansions.expansion_a
#print axioms QuantumNLS.RiccatiExpansions.pointwise_expansion
#print axioms QuantumNLS.RiccatiExpansions.log_expansion
