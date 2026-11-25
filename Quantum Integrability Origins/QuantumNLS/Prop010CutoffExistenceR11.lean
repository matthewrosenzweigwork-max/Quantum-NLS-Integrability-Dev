import QuantumNLS.Prop010ContourBindingR11
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory Function
open scoped ContDiff InnerProductSpace BigOperators
namespace QuantumNLS.Prop010CutoffExistenceR11
open Prop010ContourBindingR11 PeriodReconstructionCore PeriodReconstruction

/-- A literal analytic germ on a compact set admits a smooth compact
extension agreeing on one open neighborhood of that set. -/
theorem compact_analytic_extension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (K : Set X) (hK : IsCompact K) (f : X → ℂ)
    (ha : ∀ x ∈ K,AnalyticAt ℝ f x) :
    ∃ F : X → ℂ,ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∃ W : Set X,IsOpen W ∧ K ⊆ W ∧ EqOn F f W := by
  let U := {x | AnalyticAt ℝ f x}
  have hU : IsOpen U := isOpen_analyticAt ℝ f
  obtain ⟨V,hV,hKV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hK hU ha
  obtain ⟨W,hW,hKW,hWV,_hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨φ,hφ,_hr,hφsupport,hφone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) hV isClosed_closure hWV
  let F : X → ℂ := fun x => φ x • f x
  have hφt : tsupport φ ⊆ U := by rw [tsupport,hφsupport]; exact hVU
  have hφc : HasCompactSupport φ := by rw [HasCompactSupport,tsupport,hφsupport]; exact hVc
  have hFc : HasCompactSupport F := hφc.smul_right
  have hFd : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hφ.contDiffAt.smul ((show AnalyticAt ℝ f x from hx).contDiffAt)
    · have hxt : x ∉ tsupport φ := fun h => hx (hφt h)
      have hn : (tsupport φ)ᶜ ∈ 𝓝 x := (isClosed_closure : IsClosed (tsupport φ)).isOpen_compl.mem_nhds hxt
      have he : F =ᶠ[𝓝 x] fun _ => (0:ℂ) := by
        filter_upwards [hn] with y hy
        change φ y • f y=0
        rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨F,hFd,hFc,W,hW,hKW,?_⟩
  intro x hx
  change φ x • f x=f x
  rw [(hφone x).mp (subset_closure hx),one_smul]

section LocalAnalytic
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
variable {L κ : ℝ} [Fact (0<L)]

lemma analytic_G (hκ : 0<κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    AnalyticAt ℝ (fun w : ℂ => G hκ w u) z := by
  exact (RootCauchyJointR9.analyticAt_joint_regular hκ (u,z) hz).comp
    (analyticAt_const.prod analyticAt_id)

lemma ef_exp (L : ℝ) (z : ℂ) : ef L z=RootScalarPeriodR10.exponential L z := by
  unfold ef RootScalarPeriodR10.exponential
  congr 1
  ring

lemma D_ne (hκ : 0<κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    Df L κ (fun w => G hκ w u) z≠0 := by
  have hd := RootScalarPeriodR10.difference_ne hκ u z hz
  simpa only [Df,Af,ScalarLogBranchR10.difference,RootScalarPeriodR10.exponent,← ef_exp] using hd

lemma root_background (κ L : ℝ) (G : ℂ → ℂ) (z : ℂ) :
    localRoot L κ G z (sf L κ G z)=Af κ G z := by
  simp only [localRoot,sub_self,zero_div,add_zero,one_cpow,mul_one,sf,Df]
  ring

lemma root_difference_background (κ L : ℝ) (G : ℂ → ℂ) (z : ℂ) :
    2*localRoot L κ G z (sf L κ G z)-sf L κ G z=Df L κ G z := by
  rw [root_background]
  unfold sf Df
  ring

lemma analytic_root (hκ : 0<κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    AnalyticAt ℝ (fun p : ℂ × ℂ => localRoot L κ (fun w => G hκ w u) p.1 p.2)
      (z,sf L κ (fun w => G hκ w u) z) := by
  let G0 : ℂ → ℂ := fun w => G hκ w u
  let p := (z,sf L κ G0 z)
  have hG := analytic_G hκ u z hz
  have hA : AnalyticAt ℝ (Af κ G0) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul hG)
  have he : AnalyticAt ℝ (ef L) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul analyticAt_id)
  have hAn : Af κ G0 z≠0 := Complex.exp_ne_zero _
  have hs : AnalyticAt ℝ (sf L κ G0) z := hA.add (he.div hA hAn)
  have hd : AnalyticAt ℝ (Df L κ G0) z := hA.sub (he.div hA hAn)
  have hdn := D_ne hκ u z hz
  have hd1 := hd.comp (analyticAt_fst (p := p))
  have hs1 := hs.comp (analyticAt_fst (p := p))
  have hv : AnalyticAt ℝ (fun q : ℂ × ℂ => 1+(q.2^2-sf L κ G0 q.1^2)/Df L κ G0 q.1^2) p :=
    analyticAt_const.add (((analyticAt_snd.pow 2).sub (hs1.pow 2)).div (hd1.pow 2) (pow_ne_zero 2 hdn))
  have hp : AnalyticAt ℝ (fun q : ℂ × ℂ =>
      (1+(q.2^2-sf L κ G0 q.1^2)/Df L κ G0 q.1^2)^((2:ℂ)⁻¹)) p := by
    have hc : AnalyticAt ℂ (fun w : ℂ => w^((2:ℂ)⁻¹)) (1:ℂ) :=
      analyticAt_id.cpow analyticAt_const (by simp [Complex.slitPlane])
    have hval : 1+(p.2^2-sf L κ G0 p.1^2)/Df L κ G0 p.1^2=1 := by dsimp [p]; simp
    exact (hc.restrictScalars (𝕜 := ℝ)).comp_of_eq hv hval
  exact ((analyticAt_snd.add (hd1.mul hp)).div analyticAt_const (by norm_num))

lemma analytic_log (hκ : 0<κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    AnalyticAt ℝ (fun p : ℂ × ℂ => localLog L κ (fun w => G hκ w u) p.1 p.2)
      (z,sf L κ (fun w => G hκ w u) z) := by
  let G0 : ℂ → ℂ := fun w => G hκ w u
  let p := (z,sf L κ G0 z)
  have hG := analytic_G hκ u z hz
  have hA : AnalyticAt ℝ (Af κ G0) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul hG)
  have hAn : Af κ G0 z≠0 := Complex.exp_ne_zero _
  have hroot : AnalyticAt ℝ (fun q : ℂ × ℂ => localRoot L κ G0 q.1 q.2) p := analytic_root hκ u z hz
  have hA1 : AnalyticAt ℝ (fun q : ℂ × ℂ => Af κ G0 q.1) p :=
    hA.comp_of_eq analyticAt_fst rfl
  have hratio : AnalyticAt ℝ (fun q : ℂ × ℂ => localRoot L κ G0 q.1 q.2/Af κ G0 q.1) p :=
    hroot.div hA1 hAn
  have hval : localRoot L κ G0 z (sf L κ G0 z)/Af κ G0 z=1 := by rw [root_background,div_self hAn]
  have hl : AnalyticAt ℂ Complex.log (localRoot L κ G0 z (sf L κ G0 z)/Af κ G0 z) :=
    analyticAt_clog (by rw [hval]; simp [Complex.slitPlane])
  exact ((analyticAt_const.mul analyticAt_const).mul (hG.comp (analyticAt_fst (p := p)))).add
    ((hl.restrictScalars (𝕜 := ℝ)).comp_of_eq hratio rfl)

lemma analytic_correction (hκ : 0<κ) (u : L2T L) (z v : ℂ) (hz : Regular κ (u,z)) :
    AnalyticAt ℝ (fun p : ℂ × (ℂ × ℂ) => localCorrection L κ (fun w => G hκ w u) p.1 p.2.1 p.2.2)
      (z,(sf L κ (fun w => G hκ w u) z,v)) := by
  let G0 : ℂ → ℂ := fun w => G hκ w u
  let p := (z,(sf L κ G0 z,v))
  have hroot : AnalyticAt ℝ (fun q : ℂ × (ℂ × ℂ) => localRoot L κ G0 q.1 q.2.1) p :=
    (analytic_root hκ u z hz).comp_of_eq
      ((analyticAt_fst (p := p)).prod (analyticAt_fst.comp analyticAt_snd)) rfl
  have he : AnalyticAt ℝ (ef L) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul analyticAt_id)
  have he1 := he.comp (analyticAt_fst (p := p))
  have hv : AnalyticAt ℝ (fun q : ℂ × (ℂ × ℂ) => q.2.2) p := analyticAt_snd.comp analyticAt_snd
  have hw : AnalyticAt ℝ (fun q : ℂ × (ℂ × ℂ) => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have ha : localRoot L κ G0 z (sf L κ G0 z)≠0 := by rw [root_background]; exact Complex.exp_ne_zero _
  have hd : 2*localRoot L κ G0 z (sf L κ G0 z)-sf L κ G0 z≠0 := by
    rw [root_difference_background]
    exact D_ne hκ u z hz
  exact (he1.mul ((hroot.mul hv).sub ((analyticAt_const.mul analyticAt_const).mul he1))).div
    ((hroot.pow 2).mul ((analyticAt_const.mul hroot).sub hw |>.pow 2))
    (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hd))
end LocalAnalytic

section Existence
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

lemma rectangle_regular (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h)
    {z : ℂ} (hz : z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h) :
    Regular κ (u,z) := by
  rcases Gam_im_ne_zero_or hh hz with hi | he
  · exact Or.inl hi
  · rcases he with rfl | rfl
    · exact Or.inr ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).separator_in_band (n-1))
    · exact Or.inr ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).separator_in_band n)

lemma analytic_background (hκ : 0<κ) (u : L2T L) (z : ℂ) (hz : Regular κ (u,z)) :
    AnalyticAt ℝ (sf L κ (fun w => G hκ w u)) z := by
  let G0 := fun w => G hκ w u
  have hG := analytic_G hκ u z hz
  have hA : AnalyticAt ℝ (Af κ G0) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul hG)
  have he : AnalyticAt ℝ (ef L) z :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((analyticAt_const.mul analyticAt_const).mul analyticAt_id)
  exact hA.add (he.div hA (Complex.exp_ne_zero _))

/-- The actual scalar-background functions have smooth compact extensions
on a common positive-radius tube; the correction includes its derivative cutoff. -/
theorem source_extensions (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∃ r>0,∃ F : ℂ × ℂ → ℂ,∃ H : ℂ × (ℂ × ℂ) → ℂ,
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
        ∀ w,‖w-sf L κ (fun z => G hκ z u) z‖<r →
          F (z,w)=localLog L κ (fun z => G hκ z u) z w) ∧
      (∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
        ∀ w v,‖w-sf L κ (fun z => G hκ z u) z‖<r →
        ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
          H (z,(w,v))=localCorrection L κ (fun z => G hκ z u) z w v) := by
  let Γ := Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h
  let s := sf L κ (fun z => G hκ z u)
  let V := MixedQuadratures.Rbd L κ (h+1)
  have hΓ : IsCompact Γ := isCompact_Gam _ _ _
  have hsc : ContinuousOn s Γ := fun z hz =>
    (analytic_background L hκ u z (rectangle_regular L hκ u n hh hz)).continuousAt.continuousWithinAt
  let KF : Set (ℂ × ℂ) := (fun z => (z,s z)) '' Γ
  have hKF : IsCompact KF := hΓ.image_of_continuousOn (continuousOn_id.prodMk hsc)
  have hFA : ∀ p ∈ KF,AnalyticAt ℝ
      (fun q : ℂ × ℂ => localLog L κ (fun z => G hκ z u) q.1 q.2) p := by
    rintro _ ⟨z,hz,rfl⟩
    exact analytic_log hκ u z (rectangle_regular L hκ u n hh hz)
  obtain ⟨F,hF,hFc,WF,hWF,hKWF,hFE⟩ := compact_analytic_extension KF hKF _ hFA
  obtain ⟨rF,hrF,hthF⟩ := hKF.exists_thickening_subset_open hWF hKWF
  let KH : Set (ℂ × (ℂ × ℂ)) := (fun p : ℂ × ℂ => (p.1,(s p.1,p.2))) ''
    (Γ ×ˢ Metric.closedBall (0:ℂ) V)
  have hKH : IsCompact KH := (hΓ.prod (isCompact_closedBall (0:ℂ) V)).image_of_continuousOn
    ((continuousOn_fst).prodMk ((hsc.comp continuousOn_fst (fun _ hp => hp.1)).prodMk continuousOn_snd))
  have hHA : ∀ p ∈ KH,AnalyticAt ℝ
      (fun q : ℂ × (ℂ × ℂ) => localCorrection L κ (fun z => G hκ z u) q.1 q.2.1 q.2.2) p := by
    rintro _ ⟨⟨z,v⟩,hp,rfl⟩
    exact analytic_correction hκ u z v (rectangle_regular L hκ u n hh hp.1)
  obtain ⟨H,hH,hHc,WH,hWH,hKWH,hHE⟩ := compact_analytic_extension KH hKH _ hHA
  obtain ⟨rH,hrH,hthH⟩ := hKH.exists_thickening_subset_open hWH hKWH
  refine ⟨min rF rH,lt_min hrF hrH,F,H,hF,hFc,hH,hHc,?_,?_⟩
  · intro z hz w hw
    apply hFE
    apply hthF
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(z,s z),⟨z,hz,rfl⟩,?_⟩
    simpa [Prod.dist_eq,dist_eq_norm] using hw.trans_le (min_le_left rF rH)
  · intro z hz w v hw hv
    apply hHE
    apply hthH
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(z,(s z,v)),⟨(z,v),⟨hz,by simpa [Metric.mem_closedBall,dist_eq_norm] using hv⟩,rfl⟩,?_⟩
    simpa [Prod.dist_eq,dist_eq_norm] using hw.trans_le (min_le_right rF rH)

/-- PROP-010 norm clause, including construction of the smooth scalar
extensions, the particular norm-integral C_N and the actual occupation B_N.
Its printed hypotheses are positive L/kappa, a unit profile, n and h>0. -/
theorem condensate_reconstruction (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h : ℝ} (hh : 0<h) :
    ∃ F : ℂ × ℂ → ℂ,∃ H : ℂ × (ℂ × ℂ) → ℂ,
    ∃ hF : ContDiff ℝ ∞ F,∃ hFc : HasCompactSupport F,
    ∃ hH : ContDiff ℝ ∞ H,∃ hHc : HasCompactSupport H,
    ∃ r>0,
      (∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
        ∀ w,‖w-sf L κ (fun z => G hκ z u) z‖<r →
          F (z,w)=localLog L κ (fun z => G hκ z u) z w) ∧
      (∀ z ∈ Gam (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h,
        ∀ w v,‖w-sf L κ (fun z => G hκ z u) z‖<r →
        ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
          H (z,(w,v))=localCorrection L κ (fun z => G hκ z u) z w v) ∧
      let f := Extension.ofSmooth F hF hFc
      let g := Extension.ofSmooth H hH hHc
      ∃ D≥0,∃ N₀ : ℕ,∀ (N : ℕ) (hN : 0<N),N₀≤N →
        IsSelfAdjoint (C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h) ∧
        ‖C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h‖≤
          K κ (RootScalarPeriodR8.cut hκ u (n-1)) (RootScalarPeriodR8.cut hκ u n) h f g ∧
        ‖(B L hκ hN n-C L hκ hN f g (RootScalarPeriodR8.cut hκ u (n-1))
          (RootScalarPeriodR8.cut hκ u n) h) (HighMomentsOps.wvec N u)‖≤D*((N:ℝ)⁻¹)^2 := by
  obtain ⟨r,hr,F,H,hF,hFc,hH,hHc,hf,hg⟩ := source_extensions L hκ u n hh
  refine ⟨F,H,hF,hFc,hH,hHc,r,hr,hf,hg,?_⟩
  exact Prop010ContourBindingR11.condensate_reconstruction_smooth L hκ u hu n hh hr F H hF hFc hH hHc hf hg
end Existence
end QuantumNLS.Prop010CutoffExistenceR11


#print axioms QuantumNLS.Prop010CutoffExistenceR11.condensate_reconstruction
#print axioms QuantumNLS.Prop010CutoffExistenceR11.source_extensions
#check @QuantumNLS.Prop010CutoffExistenceR11.condensate_reconstruction
#check @QuantumNLS.Prop010CutoffExistenceR11.source_extensions
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop010CutoffExistenceR11." ||
        n.toString.startsWith "_private.QuantumNLS.Prop010CutoffExistenceR11." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Prop010CutoffExistenceR11 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
