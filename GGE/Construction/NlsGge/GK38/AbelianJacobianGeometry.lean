import NlsGge.GK38.AbelianJacobianNumerator

/-! Original full-family geometry for the actual Jacobian columns.
UNCOMPILED source preparation; no spectral denominator is divided before nonzero. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section
namespace P3JacobianColumns

theorem full_eq_extend_restrict_add_single (n : ℤ) (s : Lib.L2Seq) :
    p2Extend38 n (p2Restrict38 n s) + s n • lp.single 2 n (1 : ℂ) = s := by
  apply Subtype.ext
  funext m
  change p2Extend38 n (p2Restrict38 n s) m +
    (s n • lp.single 2 n (1 : ℂ) : Lib.L2Seq) m = s m
  by_cases hm : m = n
  · subst m
    simp only [p2Extend_self38, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, lp.single_apply_self, mul_one, zero_add]
  · rw [p2Extend_at38 n (p2Restrict38 n s) ⟨m,hm⟩, p2Restrict_apply38]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) hm, mul_zero, add_zero]

theorem column_add_omitted_single (n r : ℤ) (s : Lib.L2Seq) (z t : ℂ) :
    p3NumeratorColumn38 n r (s + t • lp.single 2 n (1 : ℂ)) z =
      p3NumeratorColumn38 n r s z := by
  unfold p3NumeratorColumn38
  rw [Lib.sOmit_add_single]

theorem column_extend_restrict (n r : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    p3NumeratorColumn38 n r (p2Extend38 n (p2Restrict38 n s)) z =
      p3NumeratorColumn38 n r s z := by
  have h := column_add_omitted_single n r (p2Extend38 n (p2Restrict38 n s)) z (s n)
  rw [full_eq_extend_restrict_add_single n s] at h
  exact h.symm

/-- Original full-family separation excludes every other numerator zero. -/
theorem omittedRatio_ne_zero (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (m : ℤ) (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    p2OmittedRatio38 m ((φ,s),z) ≠ 0 := by
  have hp := a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m z hz
  have hD := a5OmittedRoot_ne_zero38 m (φ,z) hp
  have hO : Lib.omitProd m s z ≠ 0 := by
    intro ho
    obtain ⟨k,hkm,hk⟩ := (Lib.omitProd_eq_zero_iff m s z).mp ho
    obtain ⟨c,N,hgeom,_hspec⟩ := hfam
    have hd := (p2OwnSigma_denominator38 C R c N hgeom k m hkm s (hσ k) z hz).1
    exact hd (sub_eq_zero.mpr hk)
  exact div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m)) hO) hD

/-- Only real parameters/points are used in this realness statement. -/
theorem omittedRatio_real (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im = 0) (m : ℤ) (x : ℝ)
    (hp : (realSlice u,(x : ℂ)) ∈ a5OmittedRootDomain38 m) :
    (p2OmittedRatio38 m ((realSlice u,s),(x : ℂ))).im = 0 := by
  have hN := p2FullNumerator_real38 m s hs x
  have hO : (Lib.omitProd m s (x : ℂ)).im = 0 := by
    norm_num [p2FullNumerator38, Complex.mul_im] at hN
    linarith
  have hD := p2OmittedRoot_real38 m u x hp
  unfold p2OmittedRatio38
  simp only [Complex.div_im, Complex.mul_im, Complex.ofReal_im, hO, hD,
    zero_mul, mul_zero, add_zero, sub_zero, zero_div]

end P3JacobianColumns

/-- The source diagonal factor has no imaginary prefactor. -/
def p3DiagonalFactor38 (n m : ℤ) (φ : PotPair) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  (((n-m : ℤ) : ℂ)) * p2OmittedRatio38 m ((φ,s),z) / (Lib.sigmaOf s n-z)

namespace P3JacobianColumns

theorem diagonalFactor_analytic (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    AnalyticOnNhd ℂ (p3DiagonalFactor38 n m φ s) (closedBall (C m) (R m)) := by
  have hd : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 := by
    obtain ⟨c,N,hgeom,_hspec⟩ := hfam
    intro z hz
    exact (p2OwnSigma_denominator38 C R c N hgeom n m hnm s hσ z hz).1
  exact (analyticOnNhd_const.mul
    (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s)).div
    (analyticOnNhd_const.sub analyticOnNhd_id) hd

theorem diagonalFactor_ne_zero (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (n m : ℤ) (hnm : n ≠ m) (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    p3DiagonalFactor38 n m φ s z ≠ 0 := by
  have hi : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hnm
  have hR := omittedRatio_ne_zero φ hφ C R hfam s hσ m z hz
  obtain ⟨c,N,hgeom,_hspec⟩ := hfam
  have hd := (p2OwnSigma_denominator38 C R c N hgeom n m hnm s (hσ n) z hz).1
  exact div_ne_zero (mul_ne_zero hi hR) hd

end P3JacobianColumns
end
end NlsGge.GK38
