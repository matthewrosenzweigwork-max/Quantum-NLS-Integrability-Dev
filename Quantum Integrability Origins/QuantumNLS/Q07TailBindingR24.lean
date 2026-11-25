import QuantumNLS.Q07SobolevModelR24
import QuantumNLS.Q07ChargeHessiansR24
import QuantumNLS.Q07TailValuesR24
import QuantumNLS.Q07BUniformCutsR16
import QuantumNLS.R275Unconditional

/-! The physical tail: exact printed charges minus the full-mass contour. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07TailBindingR24
open RiccatiSobolevBanach ComplexifiedSobolevField ClassicalCharges
open Q07ChargeLevelsR24 Q07ChargeBoundsR24 Q07ChargeHessiansR24 Q07SobolevModelR24
open RiccatiPointwiseDisc RiccatiExpansions SmoothScalarMomentsPhysical
open Q07IntegratedHessiansR16 PROP017UniformN Q07RealCalculusR24
variable {L κ : ℝ} [Fact (0 < L)]

def regularity (r : ℕ) : ℝ := (2*r+4 : ℕ)
def order (r : ℕ) : ℕ := 2*r+3
lemma sharp (r : ℕ) : 1+(order r : ℝ) ≤ regularity r := by
  dsimp [order,regularity]; push_cast; linarith
lemma regularity_pos (r : ℕ) : 0 < regularity r := by dsimp [regularity]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]

def field (r : ℕ) : Ell2 →L[ℂ] PhysicalTensor.L2T L :=
  fieldMap L (regularity r) (regularity_pos r).le

def tail (hκ : 0 < κ) (r : ℕ) (h : ℝ) (l : ℕ) (x : Ell2) : ℝ :=
  realCharge (L := L) (sharp r) κ (r+1) x -
    windowContour hκ r (cutSeq L l) h (field (L := L) r x)

omit [Fact (0 < L)] in
lemma physical_rep (r : ℕ) (x : Ell2) :
    physRep L 1 (lowT L 1 (regularity r) x) = physRep L (regularity r) x := by
  funext t
  unfold physRep
  rw [toField_lowT (by dsimp [regularity]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r] : (1 : ℝ) ≤ regularity r)]

lemma physical_tail (hκ : 0 < κ) (r l : ℕ) (h : ℝ) (x : Ell2) :
    tail (L := L) hκ r h l x =
      (charge L κ (physRep L (regularity r) x) (r+1)).re -
        windowContour hκ r (cutSeq L l) h (field (L := L) r x) := by
  rw [tail,physical_charge (sharp r) (by dsimp [order]; omega) κ (r+1)
    (by omega) (by dsimp [order]; omega) x (physical_rep (L := L) r x)]

lemma smooth_value (hκ : 0 < κ) (r l : ℕ) (h B : ℝ) (x : Ell2)
    (hx : ‖x‖ ≤ B+2) (hf : SmoothPeriodic L (physRep L (regularity r) x))
    (ha : 0 < cutSeq L l)
    (hw : windowContour hκ r (cutSeq L l) h (field (L := L) r x) =
      ∫ t in Ioo (-cutSeq L l) (cutSeq L l), t^r ∂FullMass.Mmeas κ (field (L := L) r x)) :
    |tail (L := L) hκ r h l x| ≤
      majorant (L := L) (regularity r) (order r) κ (|B|+8) (order r) / (cutSeq L l)^(r+2) := by
  have hs : (1 : ℝ)/2 < regularity r := by dsimp [regularity]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have he := fieldMap_eq_smooth hs hf x rfl
  change field (L := L) r x = smoothL2 hf at he
  obtain ⟨-,hm⟩ := R275Unconditional.R_275B7656 κ hκ hf
  have hir := (hm r).1
  have hiq := (hm (2*r+2)).1
  have hr := congrArg Complex.re (hm r).2
  have hq := congrArg Complex.re (hm (2*r+2)).2
  simp only [Complex.ofReal_re] at hr hq
  rw [← he] at hir hiq hr hq
  have hp := physical_charge (L := L) (sharp r) (by dsimp [order]; omega) κ
    (order r) (by dsimp [order]; omega) le_rfl x (physical_rep (L := L) r x)
  have hK : (∫ t : ℝ, t^(2*r+2) ∂FullMass.Mmeas κ (field (L := L) r x)) ≤
      majorant (L := L) (regularity r) (order r) κ (|B|+8) (order r) := by
    rw [hq]
    change (charge L κ (physRep L (regularity r) x) (order r)).re ≤ _
    rw [← hp]
    apply (Complex.re_le_norm _).trans
    apply cxCharge_bound (sharp r) κ (by positivity) (order r) (by dsimp [order]; omega)
    simpa only [norm_slice] using hx.trans (by linarith [le_abs_self B] : B+2 ≤ |B|+8)
  rw [physical_tail,hw,← hr]
  exact Q07TailValuesR24.tail_value _ r ha hir hiq hK

theorem window_data (hκ : 0 < κ) (r : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧
      ∀ x : Ell2, ‖x‖ ≤ B+2 →
        windowContour hκ r (cutSeq L l) h (field (L := L) r x) =
          (∫ t in Ioo (-cutSeq L l) (cutSeq L l), t^r ∂FullMass.Mmeas κ (field (L := L) r x)) ∧
        DifferentiableAt ℝ (fun y => windowContour hκ r (cutSeq L l) h (field (L := L) r y)) x ∧
        DifferentiableAt ℝ (fderiv ℝ (fun y => windowContour hκ r (cutSeq L l) h (field (L := L) r y))) x ∧
        ∀ v w : Ell2,
          |fderiv ℝ (fderiv ℝ (fun y => windowContour hκ r (cutSeq L l) h (field (L := L) r y))) x v w| ≤
            C*(cutSeq L l)^(r+1)*‖v‖*‖w‖ := by
  obtain ⟨-,η,hη,l0,C,hC,hd⟩ := Q07BUniformCutsR16.q07Buniformcuts (L := L)
    hκ (regularity_pos r) (B+2) hh r
  refine ⟨l0,C,hC,?_⟩
  intro l hl
  obtain ⟨ha,hall⟩ := hd l hl
  refine ⟨ha,?_⟩
  intro x hx
  have hc := class_mem (L := L) (regularity_pos r).le x hx
  have hpoint := hall (field (L := L) r x) hc (field (L := L) r x) (by simpa using hη)
  obtain ⟨-,hvalue,h1,h2,hbound⟩ := hpoint
  let A := (field (L := L) r).restrictScalars ℝ
  have hnear : ∀ v ∈ ball (field (L := L) r x) η,
      DifferentiableAt ℝ (windowContour hκ r (cutSeq L l) h) v := by
    intro v hv
    exact (hall (field (L := L) r x) hc v (by simpa only [mem_ball,dist_eq_norm] using hv)).2.2.1
  obtain ⟨hd1,hd2,he⟩ := linear_twice A (ContinuousLinearMap.id ℝ ℝ)
    isOpen_ball (mem_ball_self hη) hnear h2
  refine ⟨hvalue,hd1,hd2,?_⟩
  intro v w
  change |fderiv ℝ (fderiv ℝ (fun y => (ContinuousLinearMap.id ℝ ℝ)
    (windowContour hκ r (cutSeq L l) h (A y)))) x v w| ≤ _
  rw [he]
  refine (hbound (A v) (A w)).trans ?_
  have hA : ‖A‖ ≤ 1 := by
    simpa only [A,field,ContinuousLinearMap.norm_restrictScalars] using
      norm_fieldMap_le L (regularity r) (regularity_pos r).le
  have hv : ‖A v‖ ≤ ‖v‖ := by simpa only [one_mul] using A.le_of_opNorm_le hA v
  have hw : ‖A w‖ ≤ ‖w‖ := by simpa only [one_mul] using A.le_of_opNorm_le hA w
  change C*(cutSeq L l)^(r+1)*‖A v‖*‖A w‖ ≤ _
  have ha0 : 0 ≤ cutSeq L l := zero_le_one.trans ha
  gcongr

theorem tail_data (hκ : 0 < κ) (r : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ K H : ℝ, 0 ≤ K ∧ 0 ≤ H ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      1 ≤ cutSeq L l ∧
      (∀ x : Ell2, ‖x‖ < B+2 → DifferentiableAt ℝ (tail (L := L) hκ r h l) x ∧
        DifferentiableAt ℝ (fderiv ℝ (tail (L := L) hκ r h l)) x ∧
        ∀ v w : Ell2, |fderiv ℝ (fderiv ℝ (tail (L := L) hκ r h l)) x v w| ≤
          H*(cutSeq L l)^(r+1)*‖v‖*‖w‖) ∧
      ∀ x : Ell2, ‖x‖ ≤ B+1 → |tail (L := L) hκ r h l x| ≤ K/(cutSeq L l)^(r+2) := by
  obtain ⟨l0,CW,hCW,hwindow⟩ := window_data (L := L) hκ r B hh
  obtain ⟨CQ,hCQ,hcharge⟩ := charge_hessians (L := L) (sharp r)
    (by dsimp [order]; omega) κ (r+1) (by omega) B
  let K := majorant (L := L) (regularity r) (order r) κ (|B|+8) (order r)
  have hK : 0 ≤ K := majorant_nonneg (sharp r) κ (by positivity) (order r)
  have hCD := realCharge_contDiff (L := L) (sharp r) (by dsimp [order]; omega) κ (r+1) (by omega)
  have hD1 : ∀ x : Ell2, DifferentiableAt ℝ (realCharge (L := L) (sharp r) κ (r+1)) x :=
    fun x => (hCD.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hD2 : ∀ x : Ell2,
      DifferentiableAt ℝ (fderiv ℝ (realCharge (L := L) (sharp r) κ (r+1))) x :=
    fun x => ((hCD.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨K,CQ+CW,hK,add_nonneg hCQ hCW,l0,?_⟩
  intro l hl
  obtain ⟨ha,hw⟩ := hwindow l hl
  have ha0 : 0 < cutSeq L l := zero_lt_one.trans_le ha
  have hp : 1 ≤ (cutSeq L l)^(r+1) := one_le_pow₀ ha
  have hdiff : ∀ x : Ell2, ‖x‖ < B+2 → DifferentiableAt ℝ (tail (L := L) hκ r h l) x := by
    intro x hx
    exact (hD1 x).sub (hw x hx.le).2.1
  refine ⟨ha,?_,?_⟩
  · intro x hx
    have he : fderiv ℝ (tail (L := L) hκ r h l) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ (realCharge (L := L) (sharp r) κ (r+1)) y -
          fderiv ℝ (fun z => windowContour hκ r (cutSeq L l) h (field (L := L) r z)) y) := by
      filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball 0 (B+2) by simpa using hx)] with y hy
      exact fderiv_sub (hD1 y) (hw y (by simpa using (mem_ball_zero_iff.mp hy).le)).2.1
    have hd := ((hD2 x).hasFDerivAt.sub (hw x hx.le).2.2.1.hasFDerivAt).congr_of_eventuallyEq he
    refine ⟨hdiff x hx,hd.differentiableAt,?_⟩
    intro v w
    rw [hd.fderiv]
    simp only [sub_apply]
    calc |fderiv ℝ (fderiv ℝ (realCharge (L := L) (sharp r) κ (r+1))) x v w -
        fderiv ℝ (fderiv ℝ (fun z => windowContour hκ r (cutSeq L l) h (field (L := L) r z))) x v w|
        ≤ |fderiv ℝ (fderiv ℝ (realCharge (L := L) (sharp r) κ (r+1))) x v w| +
          |fderiv ℝ (fderiv ℝ (fun z => windowContour hκ r (cutSeq L l) h (field (L := L) r z))) x v w| := abs_sub _ _
      _ ≤ CQ*‖v‖*‖w‖+CW*(cutSeq L l)^(r+1)*‖v‖*‖w‖ :=
        add_le_add (hcharge x hx.le v w) ((hw x hx.le).2.2.2 v w)
      _ ≤ (CQ+CW)*(cutSeq L l)^(r+1)*‖v‖*‖w‖ := by
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hCQ) (mul_nonneg (norm_nonneg v) (norm_nonneg w))
        nlinarith
  · intro x hx
    have hxc : ‖x‖ < B+2 := by linarith
    have hc := (hdiff x hxc).continuousAt
    have ht : Tendsto (fun J : Finset ℤ => |tail (L := L) hκ r h l (approx x J)|) atTop
        (𝓝 |tail (L := L) hκ r h l x|) := (continuous_abs.continuousAt.comp hc).tendsto.comp (approx_tendsto x)
    apply le_of_tendsto ht
    apply Eventually.of_forall
    intro J
    have hJ : ‖approx x J‖ ≤ B+2 := (approx_norm_le x J).trans (by linarith)
    exact smooth_value (L := L) hκ r l h B (approx x J) hJ (approx_smooth (L := L) (S := regularity r) x J) ha0 (hw (approx x J) hJ).1

end QuantumNLS.Q07TailBindingR24
