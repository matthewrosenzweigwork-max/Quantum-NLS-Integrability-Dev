import Armstrong.Work.RawBetaSourceSum
import Armstrong.Frozen.RawBetaMagnitude.gkSourceBeta_inverseDistance_bound38
import Mathlib.Analysis.Complex.Exponential

/-!
# Local bounds for the literal source-beta sums and their exponential factors

SPECULATIVE_PARENT_UNACCEPTED: this file consumes the separately reviewed A8
source-sum transport. The original W and F are unchanged. Independent series
and inverse-estimate witnesses are intersected, then the concrete spectral
square-mass bound and Cauchy–Schwarz give one local bound for every signed mode.
The two exponential factors share that bound. No outer-index beta square
summability, real-trace, full Theorem 15.3, or Cartesian-map theorem is claimed.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_source_beta_local_uniform_bound38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      ∀ phi0 : PotPair, phi0 ∈ Wbeta →
        ∃ V : Set PotPair, ∃ B : ℝ,
          IsOpen V ∧ phi0 ∈ V ∧ V ⊆ Wbeta ∧ 0 ≤ B ∧
          ∀ phi : {psi : PotPair // psi ∈ W}, phi.1 ∈ V →
            ∀ n : ℤ,
              ‖∑' m : P2Index38 n,
                gkSourceBeta38 W hWopen hreal hWgk F
                  hFanalytic hFn hperiod n m.1 m.2 phi‖ ≤ B := by
  obtain ⟨Ws, hWs, hrealS, hWsW, hsum, _hunif, _hanalytic, _hdecay⟩ :=
    gk151_source_beta_series38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  obtain ⟨Wi, hWi, hrealI, _hWiW, hinv⟩ :=
    gkSourceBeta_inverseDistance_bound38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  refine ⟨Ws ∩ Wi, hWs.inter hWi, fun x hx => ⟨hrealS hx, hrealI hx⟩,
    fun x hx => hWsW hx.1, ?_⟩
  intro phi0 hphi0
  obtain ⟨Vb, C, hVb, hphi0Vb, hVbWi, hC, hbound⟩ := hinv phi0 hphi0.2
  obtain ⟨Us, hUs, _hUsGK, M, _hM, hmass⟩ :=
    gk151BetaMass_local_l2_38 phi0 (hWgk (hWsW hphi0.1))
  refine ⟨(Vb ∩ Ws) ∩ interior Us, C * Real.sqrt M * Real.sqrt Lib.invSqSum,
    (hVb.inter hWs).inter isOpen_interior,
    ⟨⟨hphi0Vb, hphi0.1⟩, mem_interior_iff_mem_nhds.mpr hUs⟩,
    fun y hy => ⟨hy.1.2, hVbWi hy.1.1⟩,
    mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg M))
      (Real.sqrt_nonneg Lib.invSqSum), ?_⟩
  intro phi hphi n
  obtain ⟨hmassSum, hmassBound⟩ := hmass phi.1 (interior_subset hphi.2)
  have hrow := hsum n phi hphi.1.2
  obtain ⟨hcsSum, hcsBound⟩ := Lib.c3_cs hmassSum n
  have hmajor : Summable (fun m : ℤ =>
      C * (‖gk151BetaMass38 phi.1 m‖ * Lib.c3w n m)) := hcsSum.mul_left C
  have hpoint (m : P2Index38 n) :
      ‖gkSourceBeta38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod n m.1 m.2 phi‖ ≤
        C * (‖gk151BetaMass38 phi.1 m.1‖ * Lib.c3w n m.1) := by
    simpa only [norm_gk151BetaMass38, mul_assoc] using
      hbound phi hphi.1.1 n m.1 m.2
  calc
    ‖∑' m : P2Index38 n,
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖ ≤
        ∑' m : P2Index38 n,
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi‖ :=
      norm_tsum_le_tsum_norm hrow
    _ ≤ ∑' m : P2Index38 n,
        C * (‖gk151BetaMass38 phi.1 m.1‖ * Lib.c3w n m.1) :=
      hrow.tsum_le_tsum hpoint (hmajor.subtype (fun m : ℤ => m ≠ n))
    _ ≤ ∑' m : ℤ,
        C * (‖gk151BetaMass38 phi.1 m‖ * Lib.c3w n m) :=
      Summable.tsum_subtype_le
        (fun m : ℤ => C * (‖gk151BetaMass38 phi.1 m‖ * Lib.c3w n m))
        {m : ℤ | m ≠ n}
        (fun m => mul_nonneg hC.le
          (mul_nonneg (norm_nonneg _) (Lib.c3w_nonneg n m))) hmajor
    _ = C * (∑' m : ℤ, ‖gk151BetaMass38 phi.1 m‖ * Lib.c3w n m) :=
      tsum_mul_left
    _ ≤ C * (Real.sqrt (∑' m : ℤ, ‖gk151BetaMass38 phi.1 m‖ ^ 2) *
        Real.sqrt Lib.invSqSum) :=
      mul_le_mul_of_nonneg_left hcsBound hC.le
    _ ≤ C * (Real.sqrt M * Real.sqrt Lib.invSqSum) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmassBound)
          (Real.sqrt_nonneg Lib.invSqSum)) hC.le
    _ = C * Real.sqrt M * Real.sqrt Lib.invSqSum := (mul_assoc _ _ _).symm

theorem gk151_source_beta_exponential_local_bound38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t) :
    ∃ Wbeta : Set PotPair,
      IsOpen Wbeta ∧ range realSlice ⊆ Wbeta ∧ Wbeta ⊆ W ∧
      ∀ phi0 : PotPair, phi0 ∈ Wbeta →
        ∃ V : Set PotPair, ∃ B : ℝ,
          IsOpen V ∧ phi0 ∈ V ∧ V ⊆ Wbeta ∧ 0 ≤ B ∧
          ∀ phi : {psi : PotPair // psi ∈ W}, phi.1 ∈ V →
            ∀ n : ℤ,
              (‖Complex.exp (Complex.I *
                (∑' m : P2Index38 n,
                  gkSourceBeta38 W hWopen hreal hWgk F
                    hFanalytic hFn hperiod n m.1 m.2 phi))‖ ≤ Real.exp B) ∧
              (‖Complex.exp (-Complex.I *
                (∑' m : P2Index38 n,
                  gkSourceBeta38 W hWopen hreal hWgk F
                    hFanalytic hFn hperiod n m.1 m.2 phi))‖ ≤ Real.exp B) := by
  obtain ⟨Wbeta, hWbeta, hrealBeta, hbetaW, hlocal⟩ :=
    gk151_source_beta_local_uniform_bound38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  refine ⟨Wbeta, hWbeta, hrealBeta, hbetaW, ?_⟩
  intro phi0 hphi0
  obtain ⟨V, B, hV, hphi0V, hVWbeta, hB, hbound⟩ := hlocal phi0 hphi0
  refine ⟨V, B, hV, hphi0V, hVWbeta, hB, ?_⟩
  intro phi hphi n
  let z : ℂ := ∑' m : P2Index38 n,
    gkSourceBeta38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m.1 m.2 phi
  have hz : ‖z‖ ≤ B := hbound phi hphi n
  change (‖Complex.exp (Complex.I * z)‖ ≤ Real.exp B) ∧
    (‖Complex.exp (-Complex.I * z)‖ ≤ Real.exp B)
  constructor
  · calc
      ‖Complex.exp (Complex.I * z)‖ ≤ Real.exp ‖Complex.I * z‖ :=
        Complex.norm_exp_le_exp_norm _
      _ = Real.exp ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ Real.exp B := Real.exp_le_exp.mpr hz
  · calc
      ‖Complex.exp (-Complex.I * z)‖ ≤ Real.exp ‖-Complex.I * z‖ :=
        Complex.norm_exp_le_exp_norm _
      _ = Real.exp ‖z‖ := by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      _ ≤ Real.exp B := Real.exp_le_exp.mpr hz

end
end NlsGge.GK38
