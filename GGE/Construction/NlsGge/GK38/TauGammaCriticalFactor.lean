import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.TauGammaCriticalMoments

/-! The source critical-factor equation includes complex collapsed gaps. No gap quotient is used. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem perChar_deriv_discrim38 (φ : PotPair) (z : ℂ) :
    deriv (perChar φ) z = 2 * discrim φ z * deriv (discrim φ) z := by
  have hd := (analyticOnNhd_discrim_z φ z (mem_univ _)).differentiableAt.hasDerivAt
  have he : perChar φ = fun w => discrim φ w ^ 2 - 4 := rfl
  rw [he]
  simpa only [Pi.pow_apply, show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat]
    using ((hd.pow 2).sub_const 4).deriv

theorem perChar_deriv_exterior38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ) :
    deriv (perChar φ) z = -4 * (2 * (z - tauN38 C R φ n) * exteriorFactor38 φ n z +
      ((z - tauN38 C R φ n) ^ 2 - gamma2N38 C R φ n / 4) *
        deriv (exteriorFactor38 φ n) z) := by
  have hQ := (exterior_entire38 φ n z (mem_univ _)).differentiableAt.hasDerivAt
  have hP := (((hasDerivAt_const z (tauN38 C R φ n)).sub (hasDerivAt_id z)).pow 2).sub_const
    (gamma2N38 C R φ n / 4)
  have hD := (hasDerivAt_const z (-4 : ℂ)).mul (hP.mul hQ)
  have he : perChar φ = fun w => (-4 : ℂ) *
      (((tauN38 C R φ n - w) ^ 2 - gamma2N38 C R φ n / 4) * exteriorFactor38 φ n w) := by
    funext w
    rw [exterior_perChar_factor38 φ n w]
    calc
      _ = -4 * ((lamPlus φ n - w) * (lamMinus φ n - w)) * exteriorFactor38 φ n w := by ring
      _ = -4 * ((tauN38 C R φ n - w) ^ 2 - gamma2N38 C R φ n / 4) * exteriorFactor38 φ n w := by
        rw [pair_polynomial_identity38 C R hsel φ hφ n w]
      _ = _ := by ring
  have hD' : HasDerivAt (fun w => (-4 : ℂ) *
      (((tauN38 C R φ n - w) ^ 2 - gamma2N38 C R φ n / 4) * exteriorFactor38 φ n w))
      (-4 * (2 * (z - tauN38 C R φ n) * exteriorFactor38 φ n z +
        ((z - tauN38 C R φ n) ^ 2 - gamma2N38 C R φ n / 4) *
          deriv (exteriorFactor38 φ n) z)) z := by
    convert hD using 1
    · funext w
      rfl
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq,
        Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  rw [he]
  exact hD'.deriv

theorem gamma2_zero_critical_eq_tau38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hcollapse : gamma2N38 C R φ n = 0) : lamDot φ n = tauN38 C R φ n := by
  have hgap : lamPlus φ n = lamMinus φ n := by
    rw [gamma2_pair_gap38 C R hsel φ hφ n] at hcollapse
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hcollapse)
  have hmean : tauN38 C R φ n = lamPlus φ n := by
    rw [tau_pair_mean38 C R hsel φ hφ n, ← hgap]
    ring
  have hchar : perChar φ (lamPlus φ n) = 0 := by
    rw [exterior_perChar_factor38 φ n (lamPlus φ n), sub_self]
    simp
  have hdchar : deriv (perChar φ) (lamPlus φ n) = 0 := by
    rw [perChar_deriv_exterior38 C R hsel φ hφ n, hmean, hcollapse]
    simp
  have hDelta : discrim φ (lamPlus φ n) ≠ 0 := by
    intro he
    rw [perChar_eq, he] at hchar
    norm_num at hchar
  have hd : deriv (discrim φ) (lamPlus φ n) = 0 := by
    rw [perChar_deriv_discrim38] at hdchar
    exact (mul_eq_zero.mp hdchar).resolve_left (mul_ne_zero (by norm_num) hDelta)
  obtain ⟨m, hm⟩ := ((lamDot_enumeration38 φ).2.1 (lamPlus φ n)).mp hd
  obtain ⟨c, N, hg, hs⟩ := hsel φ hφ
  have hcrit : lamDot φ m ∈ ball (C φ m) (R φ m) := (hs.1 m).2.2.2.1
  have hplus : lamPlus φ n ∈ ball (C φ n) (R φ n) :=
    (hs.1 n).1 (right_mem_segment ℝ _ _)
  have hmn : m = n := by
    by_contra hne
    exact (Set.disjoint_left.mp (isolating_geometry_disjoint38 _ _ c N hg hne))
      (hm ▸ hcrit) hplus
  subst m
  exact hm.trans hmean.symm

theorem critical_factor_equation38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    let d := lamDot φ n - tauN38 C R φ n
    let q := exteriorFactor38 φ n (lamDot φ n)
    let qp := deriv (exteriorFactor38 φ n) (lamDot φ n)
    2 * d * q + (d ^ 2 - gamma2N38 C R φ n / 4) * qp = 0 := by
  have hroot : deriv (discrim φ) (lamDot φ n) = 0 :=
    ((lamDot_enumeration38 φ).2.1 (lamDot φ n)).mpr ⟨n, rfl⟩
  have hchar : deriv (perChar φ) (lamDot φ n) = 0 := by
    rw [perChar_deriv_discrim38, hroot, mul_zero]
  rw [perChar_deriv_exterior38 C R hsel φ hφ n] at hchar
  exact (mul_eq_zero.mp hchar).resolve_left (by norm_num)

end
end NlsGge.GK38
