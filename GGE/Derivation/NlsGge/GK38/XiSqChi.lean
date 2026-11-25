import NlsGge.GK38.XiSqOmittedRoot

set_option autoImplicit false
open Set Metric Filter Topology SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- A Hilbert-valued realization of the already proved actual critical spectral shift. -/
def a5CriticalShift38 : PotPair → Lib.L2Z := Classical.choose critical_l2_realization38

theorem a5CriticalShift_value38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    a5CriticalShift38 φ m = lamDot φ m - (m : ℂ) * (Real.pi : ℂ) :=
  (Classical.choose_spec critical_l2_realization38).1 φ hφ m

theorem a5CriticalShift_analytic38 : AnalyticOnNhd ℂ a5CriticalShift38 gkW :=
  (Classical.choose_spec critical_l2_realization38).2

theorem a5CriticalShift_sigma38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Lib.sigmaOf (a5CriticalShift38 φ) = lamDot φ := by
  funext m
  dsimp [Lib.sigmaOf]
  rw [a5CriticalShift_value38 φ hφ m]
  ring

/-- Lib.omitProd includes an EXTRA inverse piN factor; remove precisely that factor here. -/
def a5CriticalNumerator38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  (Lib.piN n : ℂ) * Lib.omitProd n (a5CriticalShift38 p.1) p.2

theorem a5CriticalNumerator_analyticAt38 (n : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW) : AnalyticAt ℂ (a5CriticalNumerator38 n) p := by
  have ha : AnalyticAt ℂ (fun q : PotPair × ℂ => (q.2, a5CriticalShift38 q.1)) p :=
    analyticAt_snd.prod ((a5CriticalShift_analytic38 p.1 hW).comp analyticAt_fst)
  have houter : AnalyticAt ℂ (fun q : ℂ × Lib.L2Z => Lib.omitProd n q.2 q.1)
      (p.2, a5CriticalShift38 p.1) := Lib.analyticOnNhd_omitProd n _ trivial
  have hcomp : AnalyticAt ℂ
      (fun q : PotPair × ℂ => Lib.omitProd n (a5CriticalShift38 q.1) q.2) p :=
    AnalyticAt.comp (g := fun q : ℂ × Lib.L2Z => Lib.omitProd n q.2 q.1)
      (f := fun q : PotPair × ℂ => (q.2, a5CriticalShift38 q.1)) houter ha
  change AnalyticAt ℂ (fun q : PotPair × ℂ =>
    (Lib.piN n : ℂ) * Lib.omitProd n (a5CriticalShift38 q.1) q.2) p
  exact analyticAt_const.mul hcomp

/-- The actual symmetric derivative product with its nth normalized factor separated. -/
theorem a5DiscrimDeriv_omitted38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW) :
    deriv (discrim p.1) p.2 =
      2 * ((lamDot p.1 n - p.2) / (Lib.piN n : ℂ)) * a5CriticalNumerator38 n p := by
  have he := Lib.entProd_eq_mul_omitProd n (a5CriticalShift38 p.1) p.2
  rw [a5CriticalShift_sigma38 p.1 hW] at he
  calc
    deriv (discrim p.1) p.2 =
        2 * ((lamDot p.1 n - p.2) * Lib.omitProd n (a5CriticalShift38 p.1) p.2) := by
      rw [discrimDeriv_product]
      exact congrArg (fun w : ℂ => 2 * w) he
    _ = _ := by
      dsimp [a5CriticalNumerator38]
      have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
      field_simp

/-- Actual omitted critical/root ratio; no analyticity of this function is assumed. -/
def a5Chi38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  a5CriticalNumerator38 n p / a5OmittedRootProduct38 n p

theorem a5Chi_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5Chi38 n) (a5OmittedRootDomain38 n) := by
  intro p hp
  exact (a5CriticalNumerator_analyticAt38 n p hp.1).div
    (a5OmittedRoot_analytic38 n p hp) (a5OmittedRoot_ne_zero38 n p hp)

/-- The actual logarithmic-derivative factorization with its exact i and normalized nth root. -/
theorem a5Chi_discrimDeriv_ratio38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    deriv (discrim p.1) p.2 / canonRoot38 p.1 p.2 =
      (lamDot p.1 n - p.2) /
        (Complex.I * stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2) * a5Chi38 n p := by
  have hp' : p ∈ a5OmittedRootDomain38 n :=
    ⟨hp.1, fun m _ => rootDomain_avoids38 hp m⟩
  have hprod := a5OmittedRoot_ne_zero38 n p hp'
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  have hstd : stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2 ≠ 0 := by
    intro he
    exact rootFactor_ne_zero38 n p hp (by simp [rootFactor38, he])
  rw [a5DiscrimDeriv_omitted38 n p hp.1, a5CanonRoot_omitted_factorization38 n p hp]
  dsimp [a5Chi38, rootFactor38]
  field_simp

/-- Actual critical omitted factors converge in the original symmetric convention. -/
theorem a5CriticalNumerator_multipliable38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW) :
    Multipliable (fun m : ℤ => if m = n then 1 else
      (lamDot p.1 m - p.2) / (Lib.piN m : ℂ)) (symmetricIcc ℤ) := by
  simpa only [a5CriticalShift_sigma38 p.1 hW, Lib.prodFactor] using
    Lib.multipliable_omit n (a5CriticalShift38 p.1) p.2

/-- Its exact actual product representation has no extra piN factor left over. -/
theorem a5CriticalNumerator_product38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW) :
    a5CriticalNumerator38 n p = ∏'[symmetricIcc ℤ] m : ℤ,
      if m = n then 1 else (lamDot p.1 m - p.2) / (Lib.piN m : ℂ) := by
  have _convergence := a5CriticalNumerator_multipliable38 n p hW
  unfold a5CriticalNumerator38 Lib.omitProd
  rw [← mul_assoc]
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  rw [mul_one_div_cancel hpi, one_mul]
  congr 1
  funext m
  simp only [a5CriticalShift_sigma38 p.1 hW, Lib.prodFactor]

/-- The two actual omitted products agree at the free potential, even on the nth slit. -/
theorem a5CriticalNumerator_free38 (n : ℤ) (z : ℂ) :
    a5CriticalNumerator38 n ((0 : PotPair), z) =
      a5OmittedRootProduct38 n ((0 : PotPair), z) := by
  have hW : (0 : PotPair) ∈ gkW := by
    simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)
  calc
    a5CriticalNumerator38 n ((0 : PotPair), z) =
        ∏'[symmetricIcc ℤ] m : ℤ, if m = n then 1 else
          (lamDot 0 m - z) / (Lib.piN m : ℂ) :=
      a5CriticalNumerator_product38 n ((0 : PotPair), z) hW
    _ = a5OmittedRootProduct38 n ((0 : PotPair), z) := by
      unfold a5OmittedRootProduct38
      apply tprod_congr
      intro m
      by_cases hmn : m = n
      · simp [a5OmittedRootFactor38, hmn]
      · simp only [a5OmittedRootFactor38, ite_eq_right hmn]
        rw [lamDot_zero38, rootFactor_free38]
        rfl

/-- Exact free chi normalization on its actual enlarged domain. -/
theorem a5Chi_free38 (n : ℤ) (z : ℂ)
    (hp : ((0 : PotPair), z) ∈ a5OmittedRootDomain38 n) :
    a5Chi38 n ((0 : PotPair), z) = 1 := by
  dsimp [a5Chi38]
  rw [a5CriticalNumerator_free38]
  exact div_self (a5OmittedRoot_ne_zero38 n _ hp)

/-- Every actual free collapsed centre has analytic normalized chi value one. -/
theorem a5Chi_free_center_probe38 (n : ℤ) :
    AnalyticAt ℂ (a5Chi38 n) ((0 : PotPair), countingCenter38 n) ∧
      a5Chi38 n ((0 : PotPair), countingCenter38 n) = 1 := by
  have hp := a5OmittedRoot_free_center_mem38 n
  exact ⟨a5Chi_analytic38 n _ hp, a5Chi_free38 n _ hp⟩

end
end NlsGge.GK38
