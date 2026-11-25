import NlsGge.GK38.AngleGlobalLocalQuadraticMass
import NlsGge.GK38.PeriodicAsymptotics

/-!
# Uniform endpoint placement for the supplied normalized family

Working proof code for GK Lemma 15.1. It extracts the root-placement constant
needed by the quadratic terminal-magnitude estimate from the already proved
quadratic quotient square-mass bound and periodic endpoint l2 control.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_quadratic_root_endpoint_bound38
    (a b sigma A : ℂ) (G Q : ℝ)
    (hG : 0 <= G) (_hQ : 0 <= Q)
    (hgap : ‖a - b‖ <= G) (hA : ‖A‖ <= Real.sqrt Q)
    (hsigma : sigma = (a + b) / 2 + (b - a)^2 * A) :
    ‖sigma - a‖ <= (1 / 2 + G * Real.sqrt Q) * ‖a - b‖ ∧
    ‖sigma - b‖ <= (1 / 2 + G * Real.sqrt Q) * ‖a - b‖ := by
  have hxy : ‖a - b‖ * ‖A‖ <= G * Real.sqrt Q :=
    mul_le_mul hgap hA (norm_nonneg _) hG
  have hquad :
      ‖a - b‖^2 * ‖A‖ <=
        ‖a - b‖ * (G * Real.sqrt Q) := by
    calc
      ‖a - b‖^2 * ‖A‖ =
          ‖a - b‖ * (‖a - b‖ * ‖A‖) := by ring
      _ <= ‖a - b‖ * (G * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
  have hpert :
      ‖(b - a)^2 * A‖ <=
        ‖a - b‖ * (G * Real.sqrt Q) := by
    rw [norm_mul, norm_pow, norm_sub_rev]
    exact hquad
  constructor
  · rw [hsigma]
    have htri :
        ‖(a + b) / 2 + (b - a)^2 * A - a‖ <=
          ‖(b - a) / 2‖ + ‖(b - a)^2 * A‖ := by
      have he :
          (a + b) / 2 + (b - a)^2 * A - a =
            (b - a) / 2 + (b - a)^2 * A := by ring
      rw [he]
      exact norm_add_le _ _
    calc
      _ <= ‖(b - a) / 2‖ + ‖(b - a)^2 * A‖ := htri
      _ <= ‖a - b‖ / 2 + ‖a - b‖ * (G * Real.sqrt Q) := by
        rw [norm_div, Complex.norm_ofNat, norm_sub_rev]
        exact add_le_add le_rfl hpert
      _ = (1 / 2 + G * Real.sqrt Q) * ‖a - b‖ := by ring
  · rw [hsigma]
    have htri :
        ‖(a + b) / 2 + (b - a)^2 * A - b‖ <=
          ‖(a - b) / 2‖ + ‖(b - a)^2 * A‖ := by
      have he :
          (a + b) / 2 + (b - a)^2 * A - b =
            (a - b) / 2 + (b - a)^2 * A := by ring
      rw [he]
      exact norm_add_le _ _
    calc
      _ <= ‖(a - b) / 2‖ + ‖(b - a)^2 * A‖ := htri
      _ <= ‖a - b‖ / 2 + ‖a - b‖ * (G * Real.sqrt Q) := by
        rw [norm_div, Complex.norm_ofNat]
        exact add_le_add le_rfl hpert
      _ = (1 / 2 + G * Real.sqrt Q) * ‖a - b‖ := by ring

/-- Around each real base point, the same supplied normalized family has one
endpoint-placement constant before all signed off-diagonal pairs. -/
theorem gk151_same_family_endpoint_placement38
    (W : Set PotPair) (hWopen : IsOpen W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFspec : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0 ∧
        (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi, y))
          (F n phi)).IsInvertible)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (u : PhysicalL2) (huW : realSlice u ∈ W) :
    ∃ rho L : ℝ, 0 < rho ∧ 0 <= L ∧ ball (realSlice u) rho ⊆ W ∧
      ∀ phi ∈ ball (realSlice u) rho, ∀ n m : ℤ, ∀ hmn : m ≠ n,
        ‖countingCenter38 m + F n phi ⟨m, hmn⟩ - lamMinus phi m‖ <=
            L * ‖lamPlus phi m - lamMinus phi m‖ ∧
        ‖countingCenter38 m + F n phi ⟨m, hmn⟩ - lamPlus phi m‖ <=
            L * ‖lamPlus phi m - lamMinus phi m‖ := by
  obtain ⟨Ciso, Riso, hfam⟩ :=
    exists_isolating_family38 (realSlice u) (hWgk huW)
  obtain ⟨rq, Bq, hrq, hBq, hrqW, hquot⟩ :=
    angleGlobal_normalized_local_quadratic_quotient_lp38
      W hWopen hWgk F hFanalytic hFspec hFreal
      u huW Ciso Riso hfam
  obtain ⟨Up, hUp, Cp, hCp, hp⟩ :=
    periodic_l2_summable38 (realSlice u)
  obtain ⟨rp, hrp, hrpU⟩ := Metric.mem_nhds_iff.mp hUp
  let rho : ℝ := min rq rp
  let G : ℝ := Real.sqrt (2 * Cp)
  let L : ℝ := 1 / 2 + G * Real.sqrt Bq
  have hrho : 0 < rho := lt_min hrq hrp
  have hsubq : ball (realSlice u) rho ⊆ ball (realSlice u) rq :=
    ball_subset_ball (min_le_left _ _)
  have hsubp : ball (realSlice u) rho ⊆ Up :=
    (ball_subset_ball (min_le_right _ _)).trans hrpU
  have hG0 : 0 <= G := Real.sqrt_nonneg _
  have hL0 : 0 <= L := by
    dsimp [L]
    positivity
  refine ⟨rho, L, hrho, hL0, hsubq.trans hrqW, ?_⟩
  intro phi hphi n m hmn
  obtain ⟨A, hAcoord, hAsum, hAB, hAroot⟩ :=
    hquot n phi (hsubq hphi)
  let mi : P2Index38 n := ⟨m, hmn⟩
  have htermA : ‖A mi‖^2 <= ∑' k : P2Index38 n, ‖A k‖^2 := by
    simpa only [Finset.sum_singleton] using
      hAsum.sum_le_tsum ({mi} : Finset (P2Index38 n))
        (fun _ _ => sq_nonneg _)
  have hApoint2 : ‖A mi‖^2 <= Bq := htermA.trans hAB
  have hApoint : ‖A mi‖ <= Real.sqrt Bq := by
    nlinarith [Real.sq_sqrt hBq.le, Real.sqrt_nonneg Bq]
  obtain ⟨hpsum, hpB⟩ := hp phi (hsubp hphi)
  have hpterm :
      ‖lamMinus phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 +
        ‖lamPlus phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 <=
          ∑' k : ℤ,
            (‖lamMinus phi k - (k : ℂ) * (Real.pi : ℂ)‖^2 +
             ‖lamPlus phi k - (k : ℂ) * (Real.pi : ℂ)‖^2) := by
    simpa only [Finset.sum_singleton] using
      hpsum.sum_le_tsum ({m} : Finset ℤ)
        (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hgapSq :
      ‖lamPlus phi m - lamMinus phi m‖^2 <= 2 * Cp := by
    calc
      _ <= 2 *
          (‖lamMinus phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 +
           ‖lamPlus phi m - (m : ℂ) * (Real.pi : ℂ)‖^2) :=
        (pair_value_square_bounds38
          (lamPlus phi m) (lamMinus phi m)
          ((m : ℂ) * (Real.pi : ℂ))).2
      _ <= 2 * (∑' k : ℤ,
            (‖lamMinus phi k - (k : ℂ) * (Real.pi : ℂ)‖^2 +
             ‖lamPlus phi k - (k : ℂ) * (Real.pi : ℂ)‖^2)) :=
        mul_le_mul_of_nonneg_left hpterm (by norm_num)
      _ <= 2 * Cp := mul_le_mul_of_nonneg_left hpB (by norm_num)
  have h2Cp : 0 <= 2 * Cp := by positivity
  have hgap : ‖lamPlus phi m - lamMinus phi m‖ <= G := by
    dsimp [G]
    nlinarith [Real.sq_sqrt h2Cp, Real.sqrt_nonneg (2 * Cp)]
  have hsigma :
      countingCenter38 m + F n phi mi =
        (lamMinus phi m + lamPlus phi m) / 2 +
          (lamPlus phi m - lamMinus phi m)^2 * A mi := by
    rw [hAroot mi, tauN_value38 phi (hWgk (hrqW (hsubq hphi))) m,
      gamma2_value38 phi (hWgk (hrqW (hsubq hphi))) m]
    ring
  have hb := gk151_quadratic_root_endpoint_bound38
    (lamMinus phi m) (lamPlus phi m)
    (countingCenter38 m + F n phi mi) (A mi) G Bq
    hG0 hBq.le
    (by simpa only [norm_sub_rev] using hgap)
    hApoint hsigma
  simpa only [mi, L, norm_sub_rev (lamMinus phi m) (lamPlus phi m)] using hb

end
end NlsGge.GK38
