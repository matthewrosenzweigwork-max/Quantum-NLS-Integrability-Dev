import NlsGge.GK38.XiSqChiSequenceInputs

set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

/-- Choice of an already-proved ACTUAL analytic Hilbert realization, not a target extension. -/
def a5TauShift38 : PotPair → Lib.L2Z := Classical.choose rootTau_l2_analytic38

theorem a5TauShift_value38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    a5TauShift38 φ m = tauN φ m - (m : ℂ) * (Real.pi : ℂ) :=
  (Classical.choose_spec rootTau_l2_analytic38).1 φ hφ m

theorem a5TauShift_analytic38 : AnalyticOnNhd ℂ a5TauShift38 gkW :=
  (Classical.choose_spec rootTau_l2_analytic38).2

theorem a5TauShift_sigma38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Lib.sigmaOf (a5TauShift38 φ) = tauN φ := by
  funext m
  dsimp [Lib.sigmaOf]
  rw [a5TauShift_value38 φ hφ m]
  ring

/-- Linear omitted mean product; the library's extra inverse piN is removed exactly. -/
def a5TauNumerator38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  (Lib.piN n : ℂ) * Lib.omitProd n (a5TauShift38 p.1) p.2

theorem a5TauNumerator_analyticAt38 (n : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW) : AnalyticAt ℂ (a5TauNumerator38 n) p := by
  have ha : AnalyticAt ℂ (fun q : PotPair × ℂ => (q.2, a5TauShift38 q.1)) p :=
    analyticAt_snd.prod ((a5TauShift_analytic38 p.1 hW).comp analyticAt_fst)
  have houter : AnalyticAt ℂ (fun q : ℂ × Lib.L2Z => Lib.omitProd n q.2 q.1)
      (p.2, a5TauShift38 p.1) := Lib.analyticOnNhd_omitProd n _ trivial
  have hcomp : AnalyticAt ℂ
      (fun q : PotPair × ℂ => Lib.omitProd n (a5TauShift38 q.1) q.2) p :=
    AnalyticAt.comp (g := fun q : ℂ × Lib.L2Z => Lib.omitProd n q.2 q.1)
      (f := fun q : PotPair × ℂ => (q.2, a5TauShift38 q.1)) houter ha
  exact analyticAt_const.mul hcomp

theorem a5TauNumerator_multipliable38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW) :
    Multipliable (fun m : ℤ => if m = n then 1 else
      (tauN p.1 m - p.2) / (Lib.piN m : ℂ)) (symmetricIcc ℤ) := by
  simpa only [a5TauShift_sigma38 p.1 hW, Lib.prodFactor] using
    Lib.multipliable_omit n (a5TauShift38 p.1) p.2

theorem a5TauNumerator_product38 (n : ℤ) (p : PotPair × ℂ) (hW : p.1 ∈ gkW) :
    a5TauNumerator38 n p = ∏'[symmetricIcc ℤ] m : ℤ,
      if m = n then 1 else (tauN p.1 m - p.2) / (Lib.piN m : ℂ) := by
  have _convergence := a5TauNumerator_multipliable38 n p hW
  unfold a5TauNumerator38 Lib.omitProd
  rw [← mul_assoc]
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  rw [mul_one_div_cancel hpi, one_mul]
  congr 1
  funext m
  simp only [a5TauShift_sigma38 p.1 hW, Lib.prodFactor]

theorem a5TauNumerator_ne_zero38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) : a5TauNumerator38 n p ≠ 0 := by
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n))
  intro he
  obtain ⟨m, hmn, hm⟩ := (Lib.omitProd_eq_zero_iff n (a5TauShift38 p.1) p.2).mp he
  rw [a5TauShift_sigma38 p.1 hp.1] at hm
  apply hp.2 m hmn
  rw [← hm]
  exact a5Tau_mem_segment38 p.1 hp.1 m

/-- Actual critical/mean ratio identity, with genuine ratio convergence as an ordinary input. -/
theorem a5CriticalTau_ratio_product38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n)
    (hprod : Multipliable (Lib.ratioFam (lamDot p.1) (tauN p.1) n p.2) (symmetricIcc ℤ)) :
    a5CriticalNumerator38 n p =
      a5TauNumerator38 n p * Lib.ratioProd (lamDot p.1) (tauN p.1) n p.2 := by
  have hτ := a5TauNumerator_multipliable38 n p hp.1
  have hfactor (m : ℤ) :
      (if m = n then 1 else (tauN p.1 m - p.2) / (Lib.piN m : ℂ)) *
        Lib.ratioFam (lamDot p.1) (tauN p.1) n p.2 m =
      (if m = n then 1 else (lamDot p.1 m - p.2) / (Lib.piN m : ℂ)) := by
    by_cases hm : m = n
    · simp [hm, Lib.ratioFam]
    · have hne : tauN p.1 m - p.2 ≠ 0 := by
        intro he
        apply hp.2 m hm
        rw [← sub_eq_zero.mp he]
        exact a5Tau_mem_segment38 p.1 hp.1 m
      simp only [hm, ite_false, Lib.ratioFam]
      field_simp
  rw [a5CriticalNumerator_product38 n p hp.1, a5TauNumerator_product38 n p hp.1]
  unfold Lib.ratioProd
  rw [← hτ.tprod_mul hprod]
  exact tprod_congr (fun m => (hfactor m).symm)

end
end NlsGge.GK38
