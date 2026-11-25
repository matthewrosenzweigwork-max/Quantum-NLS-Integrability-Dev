import Armstrong.Frozen.RawBeta.GKSourceBetaValue38
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The source beta value at a terminal spectral tip.

At a terminal tip the frozen conditional sheet normalization is vacuous.
Negating every sheet therefore gives another permitted rooted path, and
negates each truncated integral. The all-path clause in the source-value
predicate then forces the joint improper limit to equal its own negative.
This file proves that consequence only; it does not assert existence of a
source value or agreement of arbitrary path integrals.
-/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral

namespace NlsGge.GK38
noncomputable section

/-- The literal joint approach filter in the frozen improper-integral
definition is nontrivial. -/
theorem rawBetaImproperApproachNeBot38 :
    NeBot (nhdsWithin ((0 : ℝ), (0 : ℝ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
    self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hdiag : Tendsto (fun t : ℝ => (t, t)) (𝓝[>] (0 : ℝ))
      (nhdsWithin ((0 : ℝ), (0 : ℝ))
        {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hid.prodMk_nhds hid, ?_⟩
    apply (hpositive.and hsmall).mono
    intro t ht
    refine ⟨ht.1, ht.1, ?_⟩
    linarith [ht.2]
  exact hdiag.neBot

private def rawBetaNegateArc38
    (φ : GKPotential38) (m : ℤ) (a : GKRootedC1Arc38 φ m) :
    GKRootedC1Arc38 φ m := by
  refine ⟨(GKArcCurve38 a, fun t => -GKArcSheet38 a t),
    a.2.1, a.2.2.1, a.2.2.2.1.neg, ?_,
    a.2.2.2.2.2.1, a.2.2.2.2.2.2⟩
  intro t ht
  simpa only [GKArcSheet38, GKArcCurve38, neg_sq] using a.2.2.2.2.1 t ht

private theorem rawBetaNegateArcCurve38
    (φ : GKPotential38) (m : ℤ) (a : GKRootedC1Arc38 φ m) :
    GKArcCurve38 (rawBetaNegateArc38 φ m a) = GKArcCurve38 a := rfl

private theorem rawBetaNegateArcSheet38
    (φ : GKPotential38) (m : ℤ) (a : GKRootedC1Arc38 φ m) (t : ℝ) :
    GKArcSheet38 (rawBetaNegateArc38 φ m a) t = -GKArcSheet38 a t := rfl

private theorem rawBetaNegateJoin38
    (φ : GKPotential38) (m : ℤ) (a b : GKRootedC1Arc38 φ m)
    (h : GKRootedArcJoin38 φ m a b) :
    GKRootedArcJoin38 φ m (rawBetaNegateArc38 φ m a)
      (rawBetaNegateArc38 φ m b) := by
  refine ⟨h.1, ?_, h.2.2⟩
  exact congrArg (fun z : ℂ => -z) h.2.1

private theorem rawBetaNegateChain38
    (φ : GKPotential38) (m : ℤ) (arcs : List (GKRootedC1Arc38 φ m)) :
    GKRootedArcChain38 φ m arcs →
      GKRootedArcChain38 φ m (arcs.map (rawBetaNegateArc38 φ m)) := by
  induction arcs with
  | nil =>
      intro h
      exact False.elim h
  | cons a tail ih =>
      intro h
      cases tail with
      | nil => trivial
      | cons b rest =>
          change GKRootedArcJoin38 φ m a b ∧
            GKRootedArcChain38 φ m (b :: rest) at h
          change GKRootedArcJoin38 φ m (rawBetaNegateArc38 φ m a)
            (rawBetaNegateArc38 φ m b) ∧
            GKRootedArcChain38 φ m ((b :: rest).map (rawBetaNegateArc38 φ m))
          exact ⟨rawBetaNegateJoin38 φ m a b h.1, ih h.2⟩

private def rawBetaNegatePathAtTip38
    (φ : GKPotential38) (m : ℤ)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m)
    (p : GKRootedPiecewisePath38 φ m) : GKRootedPiecewisePath38 φ m := by
  refine ⟨(rawBetaNegateArc38 φ m (GKPathFirst38 p),
    ((GKPathMiddle38 p).map (rawBetaNegateArc38 φ m),
      rawBetaNegateArc38 φ m (GKPathLast38 p))),
    p.2.1, ?_, p.2.2.2.1, p.2.2.2.2.1, ?_⟩
  · have hchain := rawBetaNegateChain38 φ m
      (GKPathFirst38 p :: (GKPathMiddle38 p ++ [GKPathLast38 p])) p.2.2.1
    simpa only [List.map_cons, List.map_append, List.map_nil] using hchain
  · intro hminus hplus
    rcases htip with htip | htip
    · exact False.elim (hminus htip)
    · exact False.elim (hplus htip)

private theorem rawBetaNegatePathFirst38
    (φ : GKPotential38) (m : ℤ)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m)
    (p : GKRootedPiecewisePath38 φ m) :
    GKPathFirst38 (rawBetaNegatePathAtTip38 φ m htip p) =
      rawBetaNegateArc38 φ m (GKPathFirst38 p) := rfl

private theorem rawBetaNegatePathMiddle38
    (φ : GKPotential38) (m : ℤ)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m)
    (p : GKRootedPiecewisePath38 φ m) :
    GKPathMiddle38 (rawBetaNegatePathAtTip38 φ m htip p) =
      (GKPathMiddle38 p).map (rawBetaNegateArc38 φ m) := rfl

private theorem rawBetaNegatePathLast38
    (φ : GKPotential38) (m : ℤ)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m)
    (p : GKRootedPiecewisePath38 φ m) :
    GKPathLast38 (rawBetaNegatePathAtTip38 φ m htip p) =
      rawBetaNegateArc38 φ m (GKPathLast38 p) := rfl

private theorem rawBetaNegateArcIntegrand38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (a : GKRootedC1Arc38 φ m) (t : ℝ) :
    GKRootedArcIntegrand38 n m F φ (rawBetaNegateArc38 φ m a) t =
      -GKRootedArcIntegrand38 n m F φ a t := by
  simp only [GKRootedArcIntegrand38, rawBetaNegateArcCurve38,
    rawBetaNegateArcSheet38, div_neg, neg_mul]

private theorem rawBetaNegateMiddleIntegral38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (arcs : List (GKRootedC1Arc38 φ m)) :
    GKPathMiddleIntegral38 n m F φ (arcs.map (rawBetaNegateArc38 φ m)) =
      -GKPathMiddleIntegral38 n m F φ arcs := by
  induction arcs with
  | nil => simp only [List.map_nil, GKPathMiddleIntegral38, neg_zero]
  | cons a tail ih =>
      simp only [List.map_cons, GKPathMiddleIntegral38,
        rawBetaNegateArcIntegrand38, intervalIntegral.integral_neg, ih, neg_add]

private theorem rawBetaNegateTruncatedIntegral38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m)
    (p : GKRootedPiecewisePath38 φ m) (ε η : ℝ) :
    GKPathTruncatedIntegral38 n m F φ
        (rawBetaNegatePathAtTip38 φ m htip p) ε η =
      -GKPathTruncatedIntegral38 n m F φ p ε η := by
  simp only [GKPathTruncatedIntegral38, rawBetaNegatePathFirst38,
    rawBetaNegatePathMiddle38, rawBetaNegatePathLast38,
    rawBetaNegateArcIntegrand38, intervalIntegral.integral_neg,
    rawBetaNegateMiddleIntegral38, neg_add]

/-- The terminal-tip zero clause follows from the literal all-path source
value predicate. Existence and all-path agreement are not asserted here. -/
theorem rawBetaSourceValueEqZeroAtTip38
    (n m : ℤ) (hmn : m ≠ n)
    (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (β : ℂ)
    (hβ : GKSourceBetaValue38 n m hmn F φ β)
    (htip : muSeq φ.1 m = lamMinus φ.1 m ∨
      muSeq φ.1 m = lamPlus φ.1 m) : β = 0 := by
  obtain ⟨p, hp, hall⟩ := hβ
  have hnegPath := hall (rawBetaNegatePathAtTip38 φ m htip p)
  have hnegative : Tendsto
      (fun q : ℝ × ℝ => GKPathTruncatedIntegral38 n m F φ
        (rawBetaNegatePathAtTip38 φ m htip p) q.1 q.2)
      (nhdsWithin ((0 : ℝ), (0 : ℝ))
        {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1})
      (nhds (-β)) := by
    simpa only [rawBetaNegateTruncatedIntegral38] using hp.2.neg
  letI : NeBot (nhdsWithin ((0 : ℝ), (0 : ℝ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}) :=
    rawBetaImproperApproachNeBot38
  have heq : β = -β := tendsto_nhds_unique hnegPath.2 hnegative
  have hdouble : β + β = 0 := by
    calc
      β + β = β + -β := congrArg (fun z : ℂ => β + z) heq
      _ = 0 := add_neg_cancel β
  have hmul : (2 : ℂ) * β = 0 := by simpa only [two_mul] using hdouble
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

end
end NlsGge.GK38
