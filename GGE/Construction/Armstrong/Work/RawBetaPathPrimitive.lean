import Armstrong.Work.RawBetaRootDerivative
import Armstrong.Work.RawBetaSpectralInput
import Armstrong.Work.RawBetaCompactIntegrability
import Armstrong.Work.RawBetaRootedPath
import Armstrong.Work.RawBetaEndpointZero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! REVIEW_ONLY: conditional integration of the analytic coefficient route.
The coefficient R is an explicit prerequisite, not a realized source input.
Compact FTC and the literal joins give one common genuine joint limit.
-/

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory

namespace NlsGge.GK38
noncomputable section

private def rawBetaArcPrimitive38 (φ : GKPotential38) (m : ℤ)
    (R : ℂ → ℂ) (a : GKRootedC1Arc38 φ m) (t : ℝ) : ℂ :=
  GKArcSheet38 a t * R (GKArcCurve38 a t)

private theorem rawBetaArcPrimitiveContinuous38 (φ : GKPotential38) (m : ℤ)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (a : GKRootedC1Arc38 φ m) :
    ContinuousOn (rawBetaArcPrimitive38 φ m R a) (Icc (0 : ℝ) 1) := by
  exact a.2.2.2.1.mul
    (hR.continuousOn.comp a.2.1 (fun t ht => a.2.2.2.2.2.1 t ht))

private theorem rawBetaArcPrimitiveHasDeriv38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rawBetaArcPrimitive38 φ m R a)
      (GKRootedArcIntegrand38 n m F φ a t) t := by
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have htn : Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hγd : DifferentiableAt ℝ (GKArcCurve38 a) t :=
    (a.2.2.1.differentiableOn (by norm_num) t htc).differentiableAt htn
  have hsc : ContinuousAt (GKArcSheet38 a) t := a.2.2.2.1.continuousAt htn
  have hsn : GKArcSheet38 a t ≠ 0 := by
    intro hz
    apply rawBetaPerCharNonzeroOnSlit38 φ m (GKArcCurve38 a t)
      (a.2.2.2.2.2.2 t ht)
    have hsq : GKArcSheet38 a t ^ 2 =
        perChar φ.1 (GKArcCurve38 a t) := a.2.2.2.2.1 t htc
    simpa only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq.symm
  have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[nhds t]
      perChar φ.1 ∘ GKArcCurve38 a := by
    filter_upwards [htn] with u hu
    exact a.2.2.2.2.1 u hu
  exact rawBetaSheetPrimitiveHasDerivAt38 hγd.hasDerivAt
    ((analyticOnNhd_perChar_z φ.1) _ (mem_univ _)).differentiableAt.hasDerivAt
    (hR _ (a.2.2.2.2.2.1 t htc)).differentiableAt.hasDerivAt
    hsc hsn he (hODE _ (a.2.2.2.2.2.2 t ht))

private theorem rawBetaArcIntegralOfPrimitive38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (u v : ℝ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hi : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume u v) :
    (∫ t in u..v, GKRootedArcIntegrand38 n m F φ a t) =
      rawBetaArcPrimitive38 φ m R a v - rawBetaArcPrimitive38 φ m R a u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((rawBetaArcPrimitiveContinuous38 φ m R hR a).mono
      (fun t ht => ⟨hu.trans ht.1, ht.2.trans hv⟩))
    (fun t ht => rawBetaArcPrimitiveHasDeriv38 n m F φ R hR hODE a t
      ⟨hu.trans_lt ht.1, ht.2.trans_le hv⟩) hi

private theorem rawBetaPrimitiveJoin38 (φ : GKPotential38) (m : ℤ)
    (R : ℂ → ℂ) (a b : GKRootedC1Arc38 φ m)
    (h : GKRootedArcJoin38 φ m a b) :
    rawBetaArcPrimitive38 φ m R a 1 = rawBetaArcPrimitive38 φ m R b 0 := by
  simp only [rawBetaArcPrimitive38, h.1, h.2.1]

private theorem rawBetaMiddlePrimitiveTelescopes38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (arcs : List (GKRootedC1Arc38 φ m)) :
    ∀ (a b : GKRootedC1Arc38 φ m),
      GKRootedArcChain38 φ m (a :: (arcs ++ [b])) →
      (∀ d ∈ arcs, (∫ t in (0 : ℝ)..1, GKRootedArcIntegrand38 n m F φ d t) =
        rawBetaArcPrimitive38 φ m R d 1 - rawBetaArcPrimitive38 φ m R d 0) →
      rawBetaArcPrimitive38 φ m R a 1 + GKPathMiddleIntegral38 n m F φ arcs =
        rawBetaArcPrimitive38 φ m R b 0 := by
  induction arcs with
  | nil =>
      intro a b hc hi
      simpa only [GKPathMiddleIntegral38, add_zero] using
        rawBetaPrimitiveJoin38 φ m R a b hc.1
  | cons d tail ih =>
      intro a b hc hi
      have hjoin := rawBetaPrimitiveJoin38 φ m R a d hc.1
      have hd := hi d List.mem_cons_self
      have htail := ih d b hc.2 (fun e he => hi e (List.mem_cons_of_mem _ he))
      calc
        rawBetaArcPrimitive38 φ m R a 1 +
            GKPathMiddleIntegral38 n m F φ (d :: tail)
            = rawBetaArcPrimitive38 φ m R d 1 +
                GKPathMiddleIntegral38 n m F φ tail := by
                  rw [GKPathMiddleIntegral38, hjoin, hd]
                  ring
        _ = rawBetaArcPrimitive38 φ m R b 0 := htail

private theorem rawBetaTruncatedPrimitive38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (p : GKRootedPiecewisePath38 φ m) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) (hs : ε + η < 1) :
    GKPathTruncatedIntegral38 n m F φ p ε η =
      rawBetaArcPrimitive38 φ m R (GKPathLast38 p) (1 - η) -
        rawBetaArcPrimitive38 φ m R (GKPathFirst38 p) ε := by
  obtain ⟨hif, him, hil⟩ := rawBetaPathCompactIntegrable38 n m F φ p ε η hε hη hs
  have hf := rawBetaArcIntegralOfPrimitive38 n m F φ R hR hODE
    (GKPathFirst38 p) ε 1 hε.le (by linarith) le_rfl hif
  have hl := rawBetaArcIntegralOfPrimitive38 n m F φ R hR hODE
    (GKPathLast38 p) 0 (1 - η) le_rfl (by linarith) (by linarith) hil
  have hm := rawBetaMiddlePrimitiveTelescopes38 n m F φ R (GKPathMiddle38 p)
    (GKPathFirst38 p) (GKPathLast38 p) p.2.2.1
    (fun d hd => rawBetaArcIntegralOfPrimitive38 n m F φ R hR hODE d 0 1
      le_rfl zero_le_one le_rfl (him d hd))
  rw [GKPathTruncatedIntegral38, hf, hl]
  calc
    _ = (rawBetaArcPrimitive38 φ m R (GKPathLast38 p) (1 - η) -
        rawBetaArcPrimitive38 φ m R (GKPathFirst38 p) ε) +
        (rawBetaArcPrimitive38 φ m R (GKPathFirst38 p) 1 +
          GKPathMiddleIntegral38 n m F φ (GKPathMiddle38 p) -
          rawBetaArcPrimitive38 φ m R (GKPathLast38 p) 0) := by ring
    _ = _ := by rw [hm, sub_self, add_zero]

private theorem rawBetaPathPrimitiveEndpoints38
    (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ)
    (p : GKRootedPiecewisePath38 φ m) :
    rawBetaArcPrimitive38 φ m R (GKPathFirst38 p) 0 = 0 ∧
      rawBetaArcPrimitive38 φ m R (GKPathLast38 p) 1 =
        antiDiscrim φ.1 (muSeq φ.1 m) * R (muSeq φ.1 m) := by
  have hfirst : GKArcSheet38 (GKPathFirst38 p) 0 = 0 := by
    apply sq_eq_zero_iff.mp
    have hsq : GKArcSheet38 (GKPathFirst38 p) 0 ^ 2 =
        perChar φ.1 (GKArcCurve38 (GKPathFirst38 p) 0) :=
      (GKPathFirst38 p).2.2.2.2.1 0 ⟨le_rfl, zero_le_one⟩
    have hcurve : GKArcCurve38 (GKPathFirst38 p) 0 = lamMinus φ.1 m := p.2.2.2.1
    rw [hsq, hcurve]
    exact rawBetaPerCharLowerTipZero38 φ m
  have hlastCurve : GKArcCurve38 (GKPathLast38 p) 1 = muSeq φ.1 m := p.2.2.2.2.1
  have hlast : GKArcSheet38 (GKPathLast38 p) 1 =
      antiDiscrim φ.1 (muSeq φ.1 m) := by
    by_cases ht : muSeq φ.1 m = lamMinus φ.1 m ∨ muSeq φ.1 m = lamPlus φ.1 m
    · have hball : muSeq φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) := by
        rw [← p.2.2.2.2.1]
        exact (GKPathLast38 p).2.2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
      have hPzero := (rawBetaPerCharZeroInDiscIff38 φ m (muSeq φ.1 m) hball).mpr ht
      have hs0 : GKArcSheet38 (GKPathLast38 p) 1 = 0 := by
        apply sq_eq_zero_iff.mp
        have hsq : GKArcSheet38 (GKPathLast38 p) 1 ^ 2 =
            perChar φ.1 (GKArcCurve38 (GKPathLast38 p) 1) :=
          (GKPathLast38 p).2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
        rw [hsq, hlastCurve, hPzero]
      have hδ0 : antiDiscrim φ.1 (muSeq φ.1 m) = 0 :=
        sq_eq_zero_iff.mp ((rawBetaDirichletTerminalSquare38 φ m).trans hPzero)
      rw [hs0, hδ0]
    · exact p.2.2.2.2.2 (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))
  constructor
  · simp only [rawBetaArcPrimitive38, hfirst, zero_mul]
  · simp only [rawBetaArcPrimitive38, hlast, hlastCurve]

/-- Conditional on an analytic coefficient, every literal rooted path has
the same genuine joint limit. Coefficient realization is not assumed by the
frozen source theorem and must be supplied before this helper is consumed. -/
theorem rawBetaAllPathsOfPrimitiveCoefficient38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (p : GKRootedPiecewisePath38 φ m) :
    HasGKImproperPathIntegral38 n m F φ p
      (antiDiscrim φ.1 (muSeq φ.1 m) * R (muSeq φ.1 m)) := by
  refine ⟨rawBetaPathCompactIntegrable38 n m F φ p, ?_⟩
  let L := nhdsWithin ((0 : ℝ), (0 : ℝ))
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}
  have hfst : Tendsto (fun q : ℝ × ℝ => q.1) L (nhdsWithin 0 (Icc (0 : ℝ) 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact ⟨hq.1.le, by linarith [hq.2.1, hq.2.2]⟩
  have hlast : Tendsto (fun q : ℝ × ℝ => 1 - q.2) L
      (nhdsWithin 1 (Icc (0 : ℝ) 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) L (nhds (0 : ℝ)) :=
        continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [sub_zero] using (tendsto_const_nhds.sub hsnd :
        Tendsto (fun q : ℝ × ℝ => (1 : ℝ) - q.2) L (nhds (1 - 0)))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      constructor <;> linarith [hq.1, hq.2.1, hq.2.2]
  have hgfirst := (rawBetaArcPrimitiveContinuous38 φ m R hR (GKPathFirst38 p)
    0 ⟨le_rfl, zero_le_one⟩).tendsto.comp hfst
  have hglast := (rawBetaArcPrimitiveContinuous38 φ m R hR (GKPathLast38 p)
    1 ⟨zero_le_one, le_rfl⟩).tendsto.comp hlast
  have hend := rawBetaPathPrimitiveEndpoints38 φ m R p
  have hlim := hglast.sub hgfirst
  rw [hend.1, hend.2, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (rawBetaTruncatedPrimitive38 n m F φ R hR hODE p q.1 q.2
    hq.1 hq.2.1 hq.2.2).symm

theorem rawBetaUniqueSourceValueOfPrimitiveCoefficient38
    (n m : ℤ) (hmn : m ≠ n) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z) :
    ∃! β : ℂ, GKSourceBetaValue38 n m hmn F φ β := by
  obtain ⟨p⟩ := rawBetaRootedPiecewisePathExists38 φ m
  let β := antiDiscrim φ.1 (muSeq φ.1 m) * R (muSeq φ.1 m)
  have hall := rawBetaAllPathsOfPrimitiveCoefficient38 n m F φ R hR hODE
  refine ⟨β, ⟨p, hall p, hall⟩, ?_⟩
  intro β' hβ'
  let : NeBot (nhdsWithin ((0 : ℝ), (0 : ℝ))
    {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}) :=
    rawBetaImproperApproachNeBot38
  obtain ⟨q, hq, hqall⟩ := hβ'
  exact tendsto_nhds_unique (hqall p).2 (hall p).2

#print axioms rawBetaAllPathsOfPrimitiveCoefficient38
#print axioms rawBetaUniqueSourceValueOfPrimitiveCoefficient38

end
end NlsGge.GK38
