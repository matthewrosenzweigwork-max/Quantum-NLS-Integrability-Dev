import Armstrong.Work.RawBetaFixedCoefficient
import Armstrong.Work.RawBetaNestedCauchy

/-! Actual joint parameter/spectral analyticity of the literal fixed-circle
coefficient. The SAME supplied numerator family is retained. All circle
branches are the actual canonical and symmetric standard branches. No
analytic dependence of individually labelled endpoints is assumed. -/

set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology

namespace NlsGge.GK38
noncomputable section

/-- The actual symmetric standard root is analytic near a certified fixed
boundary. This follows from the actual normalized root factor, with its
piN normalization restored linearly, not by choosing a square-root sign. -/
theorem rawBetaFixedStandardRoot_analytic38
    (V : Set PotPair) (hVg : V ⊆ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C ρ) (m : ℤ) :
    AnalyticOnNhd ℂ
      (fun q : PotPair × ℂ => stdRoot38 (tauN q.1 m) (gamma2 q.1 m) q.2)
      (V ×ˢ sphere (C m) (ρ m)) := by
  have hpi : (Lib.piN m : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m)
  have he :
      (fun q : PotPair × ℂ => rootFactor38 m q * (Lib.piN m : ℂ)) =
      (fun q : PotPair × ℂ => stdRoot38 (tauN q.1 m) (gamma2 q.1 m) q.2) := by
    funext q
    dsimp only [rootFactor38]
    exact div_mul_cancel₀ _ hpi
  intro q hq
  have hoff : q.2 ∉ segment ℝ (lamMinus q.1 m) (lamPlus q.1 m) := by
    have hp : (q.1,q.2) ∈ rootDomain38 :=
      ⟨hVg hq.1,fixed_sphere_subset q.1 C ρ (hfamily q.1 hq.1) m hq.2⟩
    exact rootDomain_avoids38 hp m
  have ha : AnalyticAt ℂ
      (fun p : PotPair × ℂ => rootFactor38 m p * (Lib.piN m : ℂ)) q :=
    (a5RootFactor_analyticAt38 m q (hVg hq.1) hoff).mul analyticAt_const
  rw [he] at ha
  exact ha

/-- Joint analyticity on the open fixed filled-disc product. Normalized
periods are unnecessary for this analytic lemma; they are consumed by the
separate literal-coefficient ODE realization. -/
theorem rawBetaFixedCoefficient_joint_analytic38
    (V : Set PotPair) (hV : IsOpen V) (hVg : V ⊆ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C ρ)
    (n m : ℤ) (F : PotPair → P2Space38 n)
    (hF : AnalyticOnNhd ℂ F V) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => rawBetaFixedCoefficient38 n m F p.1 (C m) (ρ m) p.2)
      (V ×ˢ ball (C m) (ρ m)) := by
  intro p hp
  have hρ : 0 < ρ m := isolating_radius_pos38 (hfamily p.1 hp.1) m
  let U : Set (PotPair × ℂ) := V ×ˢ ball (C m) (ρ m)
  have hU : IsOpen U := hV.prod isOpen_ball
  let A : (PotPair × ℂ) → ℂ → ℂ := fun x w =>
    ((w-C m)*Complex.I) * p6PsiNumerator38 n F x.1 w / canonRoot38 x.1 w
  let B : (PotPair × ℂ) → ℂ → ℂ := fun x w =>
    ((w-C m)*Complex.I) /
      (stdRoot38 (tauN x.1 m) (gamma2 x.1 m) w * (w-x.2))
  have hJ : ∀ q : (PotPair × ℂ) × ℂ,
      AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) q := by
    intro q
    have hφ : AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => y.1.1) q :=
      AnalyticAt.comp (g := fun x : PotPair × ℂ => x.1)
        (f := fun y : (PotPair × ℂ) × ℂ => y.1)
        analyticAt_fst analyticAt_fst
    exact hφ.prod analyticAt_snd
  have hA : AnalyticOnNhd ℂ (Function.uncurry A)
      (U ×ˢ sphere (C m) (ρ m)) := by
    intro q hq
    have hφ : q.1.1 ∈ gkW := hVg hq.1.1
    have hfam := hfamily q.1.1 hq.1.1
    have hroot : (q.1.1,q.2) ∈ rootDomain38 :=
      ⟨hφ,fixed_sphere_subset q.1.1 C ρ hfam m hq.2⟩
    have hnum : AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ => p6PsiNumerator38 n F y.1.1 y.2) q :=
      AnalyticAt.comp
        (g := fun s : PotPair × ℂ => p6PsiNumerator38 n F s.1 s.2)
        (f := fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) (x := q)
        (p6PsiNumerator_joint_analytic38 n V F hF
          (q.1.1,q.2) ⟨hq.1.1,mem_univ _⟩) (hJ q)
    have hcanon : AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ => canonRoot38 y.1.1 y.2) q :=
      AnalyticAt.comp
        (g := fun s : PotPair × ℂ => canonRoot38 s.1 s.2)
        (f := fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) (x := q)
        (canonRoot_analytic38 (q.1.1,q.2) hroot) (hJ q)
    have hfactor : AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ => (y.2-C m)*Complex.I) q :=
      (analyticAt_snd.sub analyticAt_const).mul analyticAt_const
    exact (hfactor.mul hnum).div hcanon
      (canonRoot_ne_zero38 q.1.1 hφ q.2 hroot.2)
  have hS := rawBetaFixedStandardRoot_analytic38 V hVg C ρ hfamily m
  have hB : AnalyticOnNhd ℂ (Function.uncurry B)
      (U ×ˢ sphere (C m) (ρ m)) := by
    intro q hq
    have hfam := hfamily q.1.1 hq.1.1
    have hSn := ((rawBetaFixedBoundaryRoot38 q.1.1 (hVg hq.1.1)
      C ρ hfam m).2.2 q.2 hq.2).1
    have hden : q.2-q.1.2 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      have hs := mem_sphere.mp hq.2
      rw [he] at hs
      exact (not_lt.mpr hs.ge) (mem_ball.mp hq.1.2)
    have hSa : AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ =>
          stdRoot38 (tauN y.1.1 m) (gamma2 y.1.1 m) y.2) q :=
      AnalyticAt.comp
        (g := fun s : PotPair × ℂ => stdRoot38 (tauN s.1 m) (gamma2 s.1 m) s.2)
        (f := fun y : (PotPair × ℂ) × ℂ => (y.1.1,y.2)) (x := q)
        (hS (q.1.1,q.2) ⟨hq.1.1,hq.2⟩) (hJ q)
    have hz : AnalyticAt ℂ (fun y : (PotPair × ℂ) × ℂ => y.1.2) q :=
      AnalyticAt.comp (g := fun x : PotPair × ℂ => x.2)
        (f := fun y : (PotPair × ℂ) × ℂ => y.1)
        analyticAt_snd analyticAt_fst
    have hfactor : AnalyticAt ℂ
        (fun y : (PotPair × ℂ) × ℂ => (y.2-C m)*Complex.I) q :=
      (analyticAt_snd.sub analyticAt_const).mul analyticAt_const
    exact hfactor.div (hSa.mul (analyticAt_snd.sub hz)) (mul_ne_zero hSn hden)
  have hNested := Lib.parametricNestedCircle_analytic38
    hU hρ hA hB (0:ℝ) (0:ℝ) (2*Real.pi)
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : PotPair × ℂ → ℂ := fun x => a5OmittedRootProduct38 m (x.1,x.2)
  let E : PotPair × ℂ → ℂ := fun x =>
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ θ in (0:ℝ)..2*Real.pi,
        (∫ t in (0:ℝ)..θ, A x (circleMap (C m) (ρ m) t)) *
          B x (circleMap (C m) (ρ m) θ))) / (K*D x)
  have hK : K ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m))
  have hD : AnalyticOnNhd ℂ D U := by
    intro x hx
    exact a5OmittedRoot_analytic38 m x
      (a5OwnClosedBall_omittedDomain38 x.1 (hVg hx.1) C ρ
        (hfamily x.1 hx.1) m x.2 (ball_subset_closedBall hx.2))
  have hDn : ∀ x ∈ U, D x ≠ 0 := by
    intro x hx
    exact a5OmittedRoot_ne_zero38 m x
      (a5OwnClosedBall_omittedDomain38 x.1 (hVg hx.1) C ρ
        (hfamily x.1 hx.1) m x.2 (ball_subset_closedBall hx.2))
  have hE : AnalyticOnNhd ℂ E U :=
    (analyticOnNhd_const.mul hNested).div (analyticOnNhd_const.mul hD)
      (fun x hx => mul_ne_zero hK (hDn x hx))
  have hγd (t : ℝ) : deriv (circleMap (C m) (ρ m)) t =
      (circleMap (C m) (ρ m) t-C m)*Complex.I := by
    rw [deriv_circleMap,circleMap_sub_center]
  have hEqual : EqOn E
      (fun x : PotPair × ℂ => rawBetaFixedCoefficient38 n m F x.1 (C m) (ρ m) x.2) U := by
    intro x hx
    have hInner :
        (fun t : ℝ => A x (circleMap (C m) (ρ m) t)) =
        (fun t : ℝ => deriv (circleMap (C m) (ρ m)) t *
          (p6PsiNumerator38 n F x.1 (circleMap (C m) (ρ m) t) /
            canonRoot38 x.1 (circleMap (C m) (ρ m) t))) := by
      funext t
      dsimp only [A]
      rw [hγd t]
      ring
    have hOuter :
        (fun θ : ℝ => (∫ t in (0:ℝ)..θ, A x (circleMap (C m) (ρ m) t)) *
          B x (circleMap (C m) (ρ m) θ)) =
        (fun θ : ℝ =>
          (rawBetaFixedBoundaryPrimitive38 n m F x.1 (C m) (ρ m) θ /
            stdRoot38 (tauN x.1 m) (gamma2 x.1 m) (circleMap (C m) (ρ m) θ)) *
              deriv (circleMap (C m) (ρ m)) θ /
                (circleMap (C m) (ρ m) θ-x.2)) := by
      funext θ
      have hSn := ((rawBetaFixedBoundaryRoot38 x.1 (hVg hx.1)
        C ρ (hfamily x.1 hx.1) m).2.2
          (circleMap (C m) (ρ m) θ) (circleMap_mem_sphere (C m) hρ.le θ)).1
      have hden : circleMap (C m) (ρ m) θ-x.2 ≠ 0 :=
        sub_ne_zero.mpr (circleMap_ne_mem_ball hx.2 θ)
      dsimp only [B,rawBetaFixedBoundaryPrimitive38]
      rw [hInner,hγd θ]
      field_simp [hSn,hden] <;> ring
    change ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ θ in (0:ℝ)..2*Real.pi,
        (∫ t in (0:ℝ)..θ, A x (circleMap (C m) (ρ m) t)) *
          B x (circleMap (C m) (ρ m) θ))) / (K*D x) = _
    rw [hOuter]
    rfl
  exact (AnalyticOnNhd.congr hU hE hEqual) p hp

/-- Restrict the SAME supplied family from W to an earned local V. Neither
the original W nor the numerator witness is replaced in the source use. -/
theorem rawBetaFixedCoefficient_same_family_joint_analytic38
    (W V : Set PotPair) (hV : IsOpen V) (hVW : V ⊆ W) (hWg : W ⊆ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C ρ)
    (F : (k : ℤ) → PotPair → P2Space38 k)
    (hF : ∀ k : ℤ, AnalyticOnNhd ℂ (F k) W) (n m : ℤ) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => rawBetaFixedCoefficient38 n m (F n) p.1 (C m) (ρ m) p.2)
      (V ×ˢ ball (C m) (ρ m)) :=
  rawBetaFixedCoefficient_joint_analytic38 V hV (hVW.trans hWg)
    C ρ hfamily n m (F n) ((hF n).mono hVW)

end
end NlsGge.GK38
