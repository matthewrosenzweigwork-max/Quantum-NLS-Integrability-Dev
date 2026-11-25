import Mathlib
import QuantumNLS.RiccatiPicardBranch
import QuantumNLS.RiccatiAbsorb
import QuantumNLS.RiccatiCharges
import QuantumNLS.RiccatiChargeLevels

/-!
# E4 remainder (R-3FEAD88B, prop:riccati)

Stage (b): the resolvent identity `(∂x - i z) (ropCLM x) = x` coefficientwise,
where `ropCLM L z hz = R_z = (∂x - i z)^{-1}` on the periodic `Ell2` space, and
`∂x` acts on the Fourier coefficient `k` by the symbol `dSymb L k = i * freq L k`.

Also the commutativity of the algebra product `mulEll`, needed to write
`r^2 - rM^2 = (r + rM) (r - rM)`.

No sorry, admit, native_decide or axioms are used.
-/

open Complex
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiDerivative QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiAbsorb
open QuantumNLS.RiccatiCharges

namespace QuantumNLS.RiccatiRemainder

/-- Coefficient formula for the resolvent `R_z = ropCLM`. -/
theorem ropCLM_apply (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) (k : ℤ) :
    (ropCLM L z hz x : ℤ → ℂ) k
      = (x : ℤ → ℂ) k / (Complex.I * (((freq L k : ℝ) : ℂ) - z)) := rfl

/-- The symbol `i (freq - z)` never vanishes when `Im z > 0`. -/
theorem freq_sub_ne_zero (L : ℝ) (z : ℂ) (hz : 0 < z.im) (k : ℤ) :
    ((freq L k : ℝ) : ℂ) - z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- Stage (b), scalar form: `(∂x - i z)(R_z x) = x` coefficientwise. -/
theorem resolvent_identity (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) (k : ℤ) :
    dSymb L k * (ropCLM L z hz x : ℤ → ℂ) k - Complex.I * z * (ropCLM L z hz x : ℤ → ℂ) k
      = (x : ℤ → ℂ) k := by
  have hne : Complex.I * (((freq L k : ℝ) : ℂ) - z) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (freq_sub_ne_zero L z hz k)
  have key : (x : ℤ → ℂ) k / (Complex.I * (((freq L k : ℝ) : ℂ) - z))
      * (Complex.I * (((freq L k : ℝ) : ℂ) - z)) = (x : ℤ → ℂ) k :=
    div_mul_cancel₀ _ hne
  rw [ropCLM_apply]
  unfold dSymb
  linear_combination key

/-- Stage (b), Ell2 form on the domain of the derivative: for `y` in `dDom`,
`R_z ((∂x - i z) y) = y`, where `∂x y` is `dmulEll L y`. -/
theorem ropCLM_dmul_sub (L : ℝ) (z : ℂ) (hz : 0 < z.im) (y : dDom L) :
    ropCLM L z hz (dmulEll L y - (Complex.I * z) • (y : Ell2)) = (y : Ell2) := by
  apply lp.ext
  funext k
  have hc : ((dmulEll L y - (Complex.I * z) • (y : Ell2) : Ell2) : ℤ → ℂ) k
      = dSymb L k * ((y : Ell2) : ℤ → ℂ) k - Complex.I * z * ((y : Ell2) : ℤ → ℂ) k := rfl
  have hne : Complex.I * (((freq L k : ℝ) : ℂ) - z) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (freq_sub_ne_zero L z hz k)
  rw [ropCLM_apply, hc, div_eq_iff hne]
  unfold dSymb
  ring

/-- Commutativity of the discrete convolution. -/
theorem convC_comm (c d : ℤ → ℂ) (k : ℤ) : convC c d k = convC d c k := by
  unfold convC
  have h := (Equiv.subLeft k).tsum_eq (fun j => d j * c (k - j))
  simp only [Equiv.subLeft_apply, sub_sub_cancel] at h
  rw [← h]
  exact tsum_congr fun j => by ring

/-- Commutativity of the algebra product on the periodic `H^a` space. -/
theorem mulEll_comm {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    mulEll hL ha x y = mulEll hL ha y x := by
  apply lp.ext
  funext k
  rw [mulEll_apply, mulEll_apply, convC_comm (toField L a x) (toField L a y) k]

/-- Stage (b) scalar form of commutativity for the bilinear map used in `absorb_sector`. -/
theorem mulBil_comm {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    mulBil hL ha x y = mulBil hL ha y x := by
  rw [mulBil_apply, mulBil_apply, mulEll_comm hL ha x y]

/-! ### Stage (c): the r_M identity -/

/-- The truncated Riccati sum `r_M = i ∑_{n=1}^M ζ^n w_n` (tex: `r_M = i ∑ w_n z^{-n}`, `ζ = 1/z`). -/
noncomputable def rMsum (w : ℕ → Ell2) (ζ : ℂ) (M : ℕ) : Ell2 :=
  Complex.I • ∑ n ∈ Finset.Icc 1 M, ζ ^ n • w n

/-- The residual of the truncated sum is the defect `(∂x - i z) r_M - u + κ v r_M^2`.
This is the algebraic identity behind `E_M` in the tex (`r'-izr-u+κvr^2`). -/
theorem rMsum_residual {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ z ζ : ℂ) (w : ℕ → Ell2) (M : ℕ) :
    resid (mulLin hL ha) D vb ub κ z ζ w M
      = (D (rMsum w ζ M) - (Complex.I * z) • rMsum w ζ M) - ub
        + κ • mulLin hL ha vb (mulLin hL ha (rMsum w ζ M) (rMsum w ζ M)) := by
  unfold resid rMsum
  set X : Ell2 := ∑ n ∈ Finset.Icc 1 M, ζ ^ n • w n with hXdef
  have h1 : D (Complex.I • X) = ∑ n ∈ Finset.Icc 1 M, (Complex.I * ζ ^ n) • D (w n) := by
    rw [hXdef, map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, smul_smul]
  have hc : Complex.I * z * Complex.I = -z := by
    linear_combination z * Complex.I_mul_I
  have h2 : (Complex.I * z) • (Complex.I • X)
      = -∑ n ∈ Finset.Icc 1 M, (z * ζ ^ n) • w n := by
    calc (Complex.I * z) • (Complex.I • X) = (-z) • X := by rw [smul_smul, hc]
      _ = -(z • X) := neg_smul _ _
      _ = -∑ n ∈ Finset.Icc 1 M, (z * ζ ^ n) • w n := by
          rw [hXdef, Finset.smul_sum]
          simp only [smul_smul]
  have hT : mulLin hL ha X X
      = ∑ b ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 M,
          (ζ ^ (b + d)) • mulLin hL ha (w b) (w d) := by
    rw [hXdef]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul, pow_add]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    rw [mul_comm]
  have h3 : mulLin hL ha (Complex.I • X) (Complex.I • X)
      = -∑ b ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 M,
          (ζ ^ (b + d)) • mulLin hL ha (w b) (w d) := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.I_mul_I, neg_one_smul, hT]
  rw [h1, h2, h3]
  simp only [map_neg, smul_neg, sub_neg_eq_add]
  abel

/-- The tail form of the residual of the bottom-level family `wAbs`, from `resid_formula`. -/
theorem resid_wAbs_tail {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (D : Ell2 →ₗ[ℂ] Ell2) (vb ub : Ell2) (κ z ζ : ℂ) (hzζ : z * ζ = 1) (M : ℕ) (hM : 1 ≤ M) :
    resid (mulLin hL ha) D vb ub κ z ζ (wAbs (mulLin hL ha) D vb ub κ) M
      = (Complex.I * ζ ^ M) • D (wAbs (mulLin hL ha) D vb ub κ M)
        - κ • mulLin hL ha vb (tailT (mulLin hL ha) ζ (wAbs (mulLin hL ha) D vb ub κ) M) := by
  refine resid_formula (mulLin hL ha) D vb ub κ z ζ (wAbs (mulLin hL ha) D vb ub κ) hzζ
    (wAbs_one (mulLin hL ha) D vb ub κ) ?_ M hM
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact wAbs_rec (mulLin hL ha) D vb ub κ n'

/-! ### Stage (d): the remainder bound `‖r - r_M‖ ≤ C' |z|^{-M-1}` -/

theorem mulBil_eq_mulLin {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    mulBil hL ha x y = mulLin hL ha x y := by
  rw [mulBil_apply]
  rfl

theorem mulLin_comm' {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    mulLin hL ha x y = mulLin hL ha y x := by
  rw [← mulBil_eq_mulLin, ← mulBil_eq_mulLin]
  exact mulBil_comm hL ha x y

/-- Remainder bound for the fixed point `r` of `riccatiT` on the bottom-level fields
`lowT u`, `lowT v` (the `H^S -> H^a` inclusion). The truncated sum `r_M` is
`i ∑_{n=1}^M z^{-n} w_n` with `w_n = wAbs`. -/
theorem remainder_bound {a S : ℝ} {M : ℕ} (L : ℝ) (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u v : Ell2) (β : ℝ) (hβ : 0 ≤ β)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hz1 : 1 ≤ ‖z‖) (hsec : δ * ‖z‖ ≤ z.im)
    (hκ : 4 * |κ| * Cmul L a ^ 2 * β
        * (2 * β / δ + ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ≤ δ * ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz κ (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) :
    ‖r - rMsum (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) (z⁻¹) M‖
      ≤ 2 * (bnd L S M (κ : ℂ) β M + ‖(κ : ℂ)‖ * (Cmul L a * ‖lowT L a S v‖)
          * ((M : ℝ) * ((M : ℝ) * (Cmul L a
              * (∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N) ^ 2))))
        / δ * (‖z‖ ^ (M + 1))⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hzζ : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hζ1 : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz1
  have hζn : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
  have hδz : δ ≤ z.im := le_trans (le_mul_of_one_le_right hδ.le hz1) hsec
  have hK0 : 0 ≤ ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N :=
    Finset.sum_nonneg fun N _ => (bnd_props L hL ha haS (κ : ℂ) u v β hβ hu hv N).1
  have hcl := charge_levels_main L hL ha haS hM (κ : ℂ) u v β hβ hu hv
  have hE := resid_bottom L hL ha haS hM (κ : ℂ) u v β hβ hu hv D hD z z⁻¹ hzζ hζ1
  have hwmem : ∀ n, 1 ≤ n → n ≤ M →
      wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ) n ∈ dDom L := by
    intro n h1 hnM
    rw [(hcl.2 D hD).1 n h1 hnM]
    exact lowT_mem_dDom (L := L) (a := a) (p := lv S M n) (by linarith [lv_ge haS n]) _
  have hEq := rMsum_residual hL ha D (lowT L a S v) (lowT L a S u) (κ : ℂ) z z⁻¹
    (wAbs (mulLin hL ha) D (lowT L a S v) (lowT L a S u) (κ : ℂ)) M
  set uB := lowT L a S u with huB
  set vB := lowT L a S v with hvB
  set w := wAbs (mulLin hL ha) D vB uB (κ : ℂ) with hw
  set ζ := z⁻¹ with hζdef
  set K := ∑ N ∈ Finset.range (M + 1), bnd L S M (κ : ℂ) β N with hKdef
  set E := resid (mulLin hL ha) D vB uB (κ : ℂ) z ζ w M with hEdef
  have hrM_mem : rMsum w ζ M ∈ dDom L := by
    unfold rMsum
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun n hn =>
      Submodule.smul_mem _ _ (hwmem n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2))
  have hrM_inv : ropCLM L z hz (D (rMsum w ζ M) - (Complex.I * z) • rMsum w ζ M)
      = rMsum w ζ M := by
    rw [show D (rMsum w ζ M) = dmulEll L ⟨rMsum w ζ M, hrM_mem⟩ from
      hD ⟨rMsum w ζ M, hrM_mem⟩]
    exact ropCLM_dmul_sub L z hz ⟨rMsum w ζ M, hrM_mem⟩
  have h4 : D (rMsum w ζ M) - (Complex.I * z) • rMsum w ζ M
      = E + uB - (κ : ℂ) • mulLin hL ha vB (mulLin hL ha (rMsum w ζ M) (rMsum w ζ M)) := by
    rw [hEdef, rMsum_residual hL ha D vB uB (κ : ℂ) z ζ w M]
    abel
  have hrM_eq : rMsum w ζ M = ropCLM L z hz E + ropCLM L z hz uB
      - (κ : ℂ) • ropCLM L z hz (mulLin hL ha vB (mulLin hL ha (rMsum w ζ M) (rMsum w ζ M))) := by
    calc rMsum w ζ M
        = ropCLM L z hz (D (rMsum w ζ M) - (Complex.I * z) • rMsum w ζ M) := hrM_inv.symm
      _ = ropCLM L z hz (E + uB - (κ : ℂ) • mulLin hL ha vB
            (mulLin hL ha (rMsum w ζ M) (rMsum w ζ M))) := by rw [h4]
      _ = ropCLM L z hz E + ropCLM L z hz uB - (κ : ℂ) • ropCLM L z hz
            (mulLin hL ha vB (mulLin hL ha (rMsum w ζ M) (rMsum w ζ M))) := by
          rw [map_sub, map_add, map_smul]
  have hr' : r = ropCLM L z hz uB
      - (κ : ℂ) • ropCLM L z hz (mulLin hL ha vB (mulLin hL ha r r)) := by
    have h := hr
    unfold riccatiT at h
    simp only [mulBil_eq_mulLin] at h
    exact h.symm
  have hsq : mulLin hL ha (r + rMsum w ζ M) (r - rMsum w ζ M)
      = mulLin hL ha r r - mulLin hL ha (rMsum w ζ M) (rMsum w ζ M) := by
    simp only [map_add, map_sub, LinearMap.add_apply,
      mulLin_comm' hL ha r (rMsum w ζ M)]
    abel
  have hd : r - rMsum w ζ M
      = -ropCLM L z hz (E + (κ : ℂ) • mulLin hL ha vB
          (mulLin hL ha (r + rMsum w ζ M) (r - rMsum w ζ M))) := by
    rw [map_add (ropCLM L z hz) E, map_smul, hsq]
    simp only [map_sub]
    linear_combination (norm := module) hr' - hrM_eq
  have hv' : ‖vB‖ ≤ β := (norm_lowT_le L a S v).trans hv
  have hr_le : ‖r‖ ≤ 2 * β / δ + K := by
    have h2 : 2 * β / z.im ≤ 2 * β / δ :=
      div_le_div_of_nonneg_left (by linarith) hδ hδz
    linarith [hrn, h2, hK0]
  have hrM_le : ‖rMsum w ζ M‖ ≤ 2 * β / δ + K := by
    have hpos : 0 ≤ 2 * β / δ := by positivity
    have hsum : ‖∑ n ∈ Finset.Icc 1 M, ζ ^ n • w n‖
        ≤ ∑ n ∈ Finset.Icc 1 M, bnd L S M (κ : ℂ) β n := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have h1 := (Finset.mem_Icc.1 hn).1
      have h2 := (Finset.mem_Icc.1 hn).2
      rw [norm_smul, norm_pow]
      calc ‖ζ‖ ^ n * ‖w n‖ ≤ 1 * ‖w n‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hζ1) (norm_nonneg _)
        _ ≤ bnd L S M (κ : ℂ) β n := by
          rw [one_mul]
          have e := (hcl.2 D hD).1 n h1 h2
          show ‖wAbs (mulLin hL ha) D vB uB (κ : ℂ) n‖ ≤ _
          rw [e]
          exact (norm_lowT_le _ _ _ _).trans (hcl.1 n h1 h2)
    have hsub : ∑ n ∈ Finset.Icc 1 M, bnd L S M (κ : ℂ) β n ≤ K :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega)
        (fun n _ _ => (bnd_props L hL ha haS (κ : ℂ) u v β hβ hu hv n).1)
    have hnorm : ‖rMsum w ζ M‖ = ‖∑ n ∈ Finset.Icc 1 M, ζ ^ n • w n‖ := by
      unfold rMsum
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [hnorm]
    linarith [hsum, hsub]
  have habs := absorb_sector hL ha hz κ hδ hsec hv' hr_le hrM_le hE hκ hd
  refine habs.trans (le_of_eq ?_)
  have hzn0 : ‖z‖ ≠ 0 := hnz.ne'
  have hδ0 : δ ≠ 0 := hδ.ne'
  rw [hζn, inv_pow]
  field_simp
  ring

end QuantumNLS.RiccatiRemainder

#print axioms QuantumNLS.RiccatiRemainder.resolvent_identity
#print axioms QuantumNLS.RiccatiRemainder.ropCLM_dmul_sub
#print axioms QuantumNLS.RiccatiRemainder.mulEll_comm
#print axioms QuantumNLS.RiccatiRemainder.mulBil_comm
#print axioms QuantumNLS.RiccatiRemainder.rMsum_residual
#print axioms QuantumNLS.RiccatiRemainder.resid_wAbs_tail
#print axioms QuantumNLS.RiccatiRemainder.remainder_bound
#print axioms QuantumNLS.RiccatiRemainder.mulLin_comm'
