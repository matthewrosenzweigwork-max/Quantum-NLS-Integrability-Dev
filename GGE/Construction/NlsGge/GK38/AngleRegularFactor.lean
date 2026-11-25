import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.AbelianDenominator

/-! Uncompiled source-only ACTUAL regular factor for an arbitrary genuine lp2
input. Its joint analyticity across the own cut is earned from existing omitted
products. An actual normalized P7 input family is still a separate dependency. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def angleRegularFactor38 (n m : ℤ) (p : (PotPair × Lib.L2Seq) × ℂ) : ℂ :=
  Complex.I * p2OmittedRatio38 m p / (Lib.sigmaOf p.1.2 n - p.2)

/-- The full joint potential/input/spectral derivative exists on the entire
ORIGINAL m-th filled disc, including its own cut. The nth input belongs to its
own ORIGINAL disc before the denominator is proved nonzero. -/
theorem angleRegularFactor_joint_own_disc38 (n m : ℤ) (hnm : n ≠ m)
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hs : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    AnalyticAt ℂ (angleRegularFactor38 n m) ((φ, s), z) := by
  have hp := a5OwnClosedBall_omittedDomain38 φ hφ C R hfam m z hz
  have hratio := p2OmittedRatio_analytic38 m ((φ, s), z) hp
  have hsA : AnalyticAt ℂ (fun p : (PotPair × Lib.L2Seq) × ℂ => p.1.2) ((φ, s), z) :=
    AnalyticAt.comp (g := fun q : PotPair × Lib.L2Seq => q.2)
      (f := fun q : (PotPair × Lib.L2Seq) × ℂ => q.1) analyticAt_snd analyticAt_fst
  have hev : AnalyticAt ℂ
      (fun p : (PotPair × Lib.L2Seq) × ℂ => p.1.2 n) ((φ, s), z) :=
    AnalyticAt.comp (g := fun q : Lib.L2Seq => q n)
      (f := fun p : (PotPair × Lib.L2Seq) × ℂ => p.1.2)
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt s) hsA
  have hσ : AnalyticAt ℂ
      (fun p : (PotPair × Lib.L2Seq) × ℂ => Lib.sigmaOf p.1.2 n) ((φ, s), z) :=
    analyticAt_const.add hev
  obtain ⟨c, N, hg, _hsp⟩ := hfam
  have hden := (p2OwnSigma_denominator38 C R c N hg n m hnm s hs z hz).1
  exact (analyticAt_const.mul hratio).div (hσ.sub analyticAt_snd) hden

/-- Exact normalization, including the factor I, is checked against the actual
existing canonical product on its genuine cut-complement domain. No value on
the cut is assigned to the canonical root by this identity. -/
theorem angleRegularFactor_factorization38 (n m : ℤ) (s : Lib.L2Seq)
    (φ : PotPair) (z : ℂ) (hp : (φ, z) ∈ rootDomain38)
    (hden : Lib.sigmaOf s n - z ≠ 0) :
    p2FullNumerator38 n s z / canonRoot38 φ z =
      ((Lib.sigmaOf s m - z) / stdRoot38 (tauN φ m) (gamma2 φ m) z) *
        angleRegularFactor38 n m ((φ, s), z) := by
  rw [p2FullNumerator_div_root38 n m s φ z hp hden]
  unfold angleRegularFactor38
  ring

end
end NlsGge.GK38
