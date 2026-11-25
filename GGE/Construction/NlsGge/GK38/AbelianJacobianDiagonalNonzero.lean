import NlsGge.GK38.AbelianJacobianDiagonalMean
import NlsGge.GK38.AbelianJacobianPeriods
import NlsGge.GK38.AbelianRealJacobian

/-! Diagonal nonvanishing for the actual complex and real Hilbert derivatives.
UNCOMPILED source preparation. Full original s, rather than its zero extension,
supplies every spectral placement used by the mean and nonzero proofs. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem actual_complex_diagonal_ne_zero (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (n : ℤ) (m : P2Index38 n) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p2Restrict38 n s)) (lp.single 2 m (1 : ℂ)) m ≠ 0 := by
  rw [matrix_coordinate n m m (realSlice u) (realSlice_mem_gkW u)]
  have hcol : p3NumeratorColumn38 n m.1 (p2Extend38 n (p2Restrict38 n s)) =
      p3NumeratorColumn38 n m.1 s :=
    funext (column_extend_restrict n m.1 s)
  rw [hcol]
  exact diagonal_period_ne_zero u C R hfam s hs hσ n m.1 m.2

theorem actual_real_diagonal_ne_zero (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : Lib.L2Seq) (hs : ∀ k : ℤ, (s k).im = 0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (n : ℤ) (m : P2Index38 n) :
    (fderiv ℝ (p3RealFn38 n u) (p3RealPart38 n (p2Restrict38 n s)))
      (lp.single 2 m (1 : ℝ)) m ≠ 0 := by
  let t : P3RealSpace38 n := p3RealPart38 n (p2Restrict38 n s)
  have hre : p2RealSeq38 n (p2Restrict38 n s) := by
    intro k
    simpa only [p2Restrict_apply38] using hs k.1
  have hinc : p3RealInclude38 n t = p2Restrict38 n s :=
    p3RealInclude_realPart38 n (p2Restrict38 n s) hre
  have hb := p3RealFn_fderiv_include38 n u t
  have he := congrArg
    (fun T : P3RealSpace38 n →L[ℝ] P2Space38 n => T (lp.single 2 m (1 : ℝ)) m) hb
  have hJ : p3RealIncludeCLM38 n (lp.single 2 m (1 : ℝ)) =
      lp.single 2 m (1 : ℂ) := p3RealInclude_single38 n m
  simp only [ContinuousLinearMap.comp_apply,hJ] at he
  change (((fderiv ℝ (p3RealFn38 n u) t) (lp.single 2 m (1 : ℝ)) m : ℝ) : ℂ) =
    (fderiv ℂ (fun v : P2Space38 n => p2Fn38 n (realSlice u,v))
      (p3RealInclude38 n t)) (lp.single 2 m (1 : ℂ)) m at he
  rw [hinc] at he
  intro hz
  have hz' : (fderiv ℝ (p3RealFn38 n u) t) (lp.single 2 m (1 : ℝ)) m = 0 := hz
  rw [hz',Complex.ofReal_zero] at he
  exact actual_complex_diagonal_ne_zero u C R hfam s hs hσ n m he.symm

end
end NlsGge.GK38.P3JacobianColumns
