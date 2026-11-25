import QuantumNLS.Ext025A4BanachComplexification
import QuantumNLS.Ext025A4CompactAssembly
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal ENNReal
namespace QuantumNLS.Ext025A4BanachSeries
open QuantumNLS.Ext025A4BanachComplexification
universe u v
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
section Lin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]

theorem ofReal_smul' (x : ℝ) (w : W) : (x : ℂ) • w = x • w := by
  show (algebraMap ℝ ℂ x) • w = x • w
  exact algebraMap_smul ℂ x w

omit [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] in
theorem I_smul_I_smul (w : W) : Complex.I • Complex.I • w = -w := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- Complexification of a continuous real-linear map `A : F →L[ℝ] W` into a complex normed space:
`Ã z = A (re z) + i A (im z)`. -/
def cxLin (A : F →L[ℝ] W) : Cx F →L[ℂ] W :=
  LinearMap.mkContinuous
    { toFun := fun z => A (Cx.re z) + Complex.I • A (Cx.im z)
      map_add' := fun z w => by
        simp only [Cx.re_add, Cx.im_add, map_add, smul_add]
        abel
      map_smul' := fun c z => by
        simp only [Cx.re_smul, Cx.im_smul, map_sub, map_add, map_smul, RingHom.id_apply]
        rw [← ofReal_smul' c.re (A (Cx.re z)), ← ofReal_smul' c.im (A (Cx.im z)),
          ← ofReal_smul' c.re (A (Cx.im z)), ← ofReal_smul' c.im (A (Cx.re z))]
        conv_rhs => rw [← Complex.re_add_im c]
        simp only [add_smul, smul_add, mul_smul, I_smul_I_smul, smul_neg]
        rw [smul_comm Complex.I (c.re : ℂ), smul_comm Complex.I (c.im : ℂ)]
        abel }
    (2 * ‖A‖) (fun z => by
      show ‖A (Cx.re z) + Complex.I • A (Cx.im z)‖ ≤ 2 * ‖A‖ * ‖z‖
      calc ‖A (Cx.re z) + Complex.I • A (Cx.im z)‖
          ≤ ‖A (Cx.re z)‖ + ‖Complex.I • A (Cx.im z)‖ := norm_add_le _ _
        _ = ‖A (Cx.re z)‖ + ‖A (Cx.im z)‖ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ ‖A‖ * ‖Cx.re z‖ + ‖A‖ * ‖Cx.im z‖ := add_le_add (A.le_opNorm _) (A.le_opNorm _)
        _ ≤ 2 * ‖A‖ * ‖z‖ := by
          nlinarith [Cx.norm_re_le z, Cx.norm_im_le z, norm_nonneg A, norm_nonneg z])

theorem cxLin_apply (A : F →L[ℝ] W) (z : Cx F) : cxLin A z = A (Cx.re z) + Complex.I • A (Cx.im z) := rfl

theorem norm_cxLin_le (A : F →L[ℝ] W) : ‖cxLin A‖ ≤ 2 * ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end Lin

theorem curryLeft_add_apply {n : ℕ} (p q : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) G) (x : F) :
    (p + q).curryLeft x = p.curryLeft x + q.curryLeft x := by
  ext m
  simp

theorem curryLeft_smul_apply {n : ℕ} (c : ℝ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) G)
    (x : F) : (c • p).curryLeft x = c • p.curryLeft x := by
  ext m
  simp

variable (F G) in
/-- **Complexification of continuous real multilinear maps** `F^n → F`, by currying. -/
def cxML : (n : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => F) G →L[ℝ]
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Cx F) (Cx G)
  | 0 => LinearMap.mkContinuous
      { toFun := fun p => ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0))
        map_add' := fun p q => by
          apply ContinuousMultilinearMap.ext
          intro v
          simp [Cx.ι_add]
        map_smul' := fun c p => by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [ContinuousMultilinearMap.constOfIsEmpty_apply, _root_.smul_apply, RingHom.id_apply, Cx.ι_smul, ← Cx.ofReal_smul] }
      1 (fun p => by
        show ‖ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0))‖ ≤ 1 * ‖p‖
        rw [ContinuousMultilinearMap.norm_constOfIsEmpty, Cx.norm_ι, one_mul]
        exact (p.le_opNorm 0).trans (by simp))
  | n + 1 => LinearMap.mkContinuous
      { toFun := fun p => (cxLin ((cxML n).comp p.curryLeft)).uncurryLeft
        map_add' := fun p q => by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_add_apply, map_add, _root_.add_apply, smul_add]
          abel
        map_smul' := fun c p => by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_smul_apply, map_smul, _root_.smul_apply, RingHom.id_apply]
          rw [smul_comm Complex.I c]
          rw [← smul_add]; rfl }
      (2 * ‖cxML n‖) (fun p => by
        refine (ContinuousLinearMap.uncurryLeft_norm (Ei := fun _ : Fin (n + 1) => Cx F)
          (cxLin ((cxML n).comp p.curryLeft))).le.trans ?_
        calc ‖cxLin ((cxML n).comp p.curryLeft)‖ ≤ 2 * ‖(cxML n).comp p.curryLeft‖ := norm_cxLin_le _
          _ ≤ 2 * (‖cxML n‖ * ‖p.curryLeft‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
          _ = 2 * ‖cxML n‖ * ‖p‖ := by rw [ContinuousMultilinearMap.curryLeft_norm, mul_assoc])

theorem cxML_zero_eq (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) G) :
    cxML F G 0 p = ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0)) := by
  rfl

theorem cxML_succ_eq {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) G) :
    cxML F G (n + 1) p = (cxLin ((cxML F G n).comp p.curryLeft)).uncurryLeft := by
  rfl

theorem cxML_zero_apply (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) G) (v : Fin 0 → Cx F) :
    cxML F G 0 p v = Cx.ι (p 0) := by
  rw [cxML_zero_eq, ContinuousMultilinearMap.constOfIsEmpty_apply]

theorem cxML_succ_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) G)
    (v : Fin (n + 1) → Cx F) :
    cxML F G (n + 1) p v = cxML F G n (p.curryLeft (Cx.re (v 0))) (Fin.tail v) +
      Complex.I • cxML F G n (p.curryLeft (Cx.im (v 0))) (Fin.tail v) := by
  rw [cxML_succ_eq, ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply]

/-- `‖cxML F G n‖ ≤ 2ⁿ`. -/
theorem norm_cxML_le : ∀ n : ℕ, ‖cxML F G n‖ ≤ 2 ^ n
  | 0 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxML_zero_eq, ContinuousMultilinearMap.norm_constOfIsEmpty, Cx.norm_ι, pow_zero, one_mul]
    exact (p.le_opNorm 0).trans (by simp)
  | n + 1 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxML_succ_eq, ContinuousLinearMap.uncurryLeft_norm]
    calc ‖cxLin ((cxML F G n).comp p.curryLeft)‖ ≤ 2 * ‖(cxML F G n).comp p.curryLeft‖ := norm_cxLin_le _
      _ ≤ 2 * (‖cxML F G n‖ * ‖p.curryLeft‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (2 ^ n * ‖p‖) := by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        gcongr
        exact norm_cxML_le n
      _ = 2 ^ (n + 1) * ‖p‖ := by ring

/-- `‖q_n‖ ≤ 2ⁿ ‖p_n‖`. -/
theorem norm_cxML_apply_le {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => F) G) :
    ‖cxML F G n p‖ ≤ 2 ^ n * ‖p‖ :=
  ((cxML F G n).le_opNorm p).trans (mul_le_mul_of_nonneg_right (norm_cxML_le n) (norm_nonneg _))

/-- **Agreement at real points**: `q_n (ι a₁, …, ι aₙ) = ι (p_n (a₁, …, aₙ))`. -/
theorem cxML_ι : ∀ (n : ℕ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => F) G) (a : Fin n → F),
    cxML F G n p (fun i => Cx.ι (a i)) = Cx.ι (p a)
  | 0, p, a => by
    rw [cxML_zero_apply, Subsingleton.elim a 0]
  | n + 1, p, a => by
    rw [cxML_succ_apply]
    simp only [Cx.re_ι, Cx.im_ι, map_zero, zero_apply, smul_zero, add_zero]
    have h := cxML_ι n (p.curryLeft (a 0)) (Fin.tail a)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Termwise complexification of a real formal multilinear series. -/
def cxSeries (p : FormalMultilinearSeries ℝ F G) : FormalMultilinearSeries ℂ (Cx F) (Cx G) :=
  fun n => cxML F G n (p n)

theorem norm_cxSeries_le (p : FormalMultilinearSeries ℝ F G) (n : ℕ) : ‖cxSeries p n‖ ≤ 2 ^ n * ‖p n‖ :=
  norm_cxML_apply_le (p n)

theorem cxSeries_ι (p : FormalMultilinearSeries ℝ F G) (n : ℕ) (y : F) :
    cxSeries p n (fun _ => Cx.ι y) = Cx.ι (p n (fun _ => y)) :=
  cxML_ι n (p n) (fun _ => y)


variable [CompleteSpace G]
theorem cxSeries_bound (p : FormalMultilinearSeries ℝ F G) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) (n : ℕ) : ‖cxSeries p n‖ * (r / 2) ^ n ≤ C := by
  have e : (2 : ℝ) ^ n * (r / 2) ^ n = r ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc ‖cxSeries p n‖ * (r / 2) ^ n ≤ (2 ^ n * ‖p n‖) * (r / 2) ^ n :=
        mul_le_mul_of_nonneg_right (norm_cxSeries_le p n) (by positivity)
    _ = ‖p n‖ * r ^ n := by rw [← e]; ring
    _ ≤ C := hC n

theorem radius_cxSeries (p : FormalMultilinearSeries ℝ F G) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) : ENNReal.ofReal (r / 2) ≤ (cxSeries p).radius := by
  have h := (cxSeries p).le_radius_of_bound C (r := (r / 2).toNNReal) (fun n => by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact cxSeries_bound p hr hC n)
  exact h

/-- `T̃` has the power series `q = cxSeries p` at `ι u` on the complex ball of radius `r/2`. -/
theorem series_sum_hasSeries (p : FormalMultilinearSeries ℝ F G) (u : F) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) :
    HasFPowerSeriesOnBall ((fun z => (cxSeries p).sum (z - Cx.ι u))) (cxSeries p) (Cx.ι u) (ENNReal.ofReal (r / 2)) := by
  have hrad := radius_cxSeries p hr hC
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have H0 := ((cxSeries p).hasFPowerSeriesOnBall (hpos.trans_le hrad)).mono hpos hrad
  have H1 := H0.comp_sub (Cx.ι u)
  rw [zero_add] at H1
  exact H1

/-- `T̃` is bounded by `2C` on the complex ball of radius `r/4`. -/
theorem series_sum_bound (p : FormalMultilinearSeries ℝ F G) (u : F) {r C : ℝ}
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) (z : Cx F) (hz : z ∈ ball (Cx.ι u) (r / 4)) : ‖(fun z => (cxSeries p).sum (z - Cx.ι u)) z‖ ≤ 2 * C := by
  have hy : ‖z - Cx.ι u‖ < r / 4 := mem_ball_iff_norm.1 hz
  have hb : ∀ n : ℕ, ‖cxSeries p n (fun _ => z - Cx.ι u)‖ ≤ C * (1 / 2) ^ n := fun n => by
    have e : (2 : ℝ) ^ n * (r / 4) ^ n = r ^ n * (1 / 2) ^ n := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
    calc ‖cxSeries p n (fun _ => z - Cx.ι u)‖ ≤ ‖cxSeries p n‖ * ∏ _i : Fin n, ‖z - Cx.ι u‖ :=
          (cxSeries p n).le_opNorm _
      _ = ‖cxSeries p n‖ * ‖z - Cx.ι u‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 ^ n * ‖p n‖) * (r / 4) ^ n :=
          mul_le_mul (norm_cxSeries_le p n) (pow_le_pow_left₀ (norm_nonneg _) hy.le n)
            (by positivity) (by positivity)
      _ = (‖p n‖ * r ^ n) * (1 / 2) ^ n := by
          rw [show (2 : ℝ) ^ n * ‖p n‖ * (r / 4) ^ n = ‖p n‖ * (2 ^ n * (r / 4) ^ n) by ring, e]
          ring
      _ ≤ C * (1 / 2) ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
  have h := tsum_of_norm_bounded (hasSum_geometric_two.mul_left C) hb
  calc ‖(fun z => (cxSeries p).sum (z - Cx.ι u)) z‖ = ‖∑' n, cxSeries p n (fun _ => z - Cx.ι u)‖ := rfl
    _ ≤ C * 2 := h
    _ = 2 * C := mul_comm _ _

/-- `T̃` extends `T`: `T̃ (ι x) = ι (T x)` on the real ball of radius `r`. -/
theorem series_sum_real {T : F → G} {p : FormalMultilinearSeries ℝ F G} {u : F} {r : ℝ}
    (hT : HasFPowerSeriesOnBall T p u (ENNReal.ofReal r)) (x : F) (hx : x ∈ ball u r) :
    (fun z => (cxSeries p).sum (z - Cx.ι u)) (Cx.ι x) = Cx.ι (T x) := by
  have hy : x - u ∈ Metric.eball (0 : F) (ENNReal.ofReal r) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff, ← dist_eq_norm]
    exact hx
  have h2 := ContinuousLinearMap.hasSum (Cx.ιL : G →L[ℝ] Cx G) (hT.hasSum hy)
  have hux : u + (x - u) = x := by abel
  rw [hux] at h2
  have e : (fun n => cxSeries p n (fun _ => Cx.ι x - Cx.ι u)) = fun n => Cx.ι (p n (fun _ => x - u)) := by
    funext n
    rw [← Cx.ι_sub, cxSeries_ι]
  have h3 : HasSum (fun n => cxSeries p n (fun _ => Cx.ι x - Cx.ι u)) (Cx.ι (T x)) := by
    rw [e]
    exact h2
  exact h3.tsum_eq


end QuantumNLS.Ext025A4BanachSeries

#print axioms QuantumNLS.Ext025A4BanachSeries.ofReal_smul'
#print axioms QuantumNLS.Ext025A4BanachSeries.I_smul_I_smul
#print axioms QuantumNLS.Ext025A4BanachSeries.cxLin
#print axioms QuantumNLS.Ext025A4BanachSeries.cxLin_apply
#print axioms QuantumNLS.Ext025A4BanachSeries.norm_cxLin_le
#print axioms QuantumNLS.Ext025A4BanachSeries.curryLeft_add_apply
#print axioms QuantumNLS.Ext025A4BanachSeries.curryLeft_smul_apply
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML_zero_eq
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML_succ_eq
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML_zero_apply
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML_succ_apply
#print axioms QuantumNLS.Ext025A4BanachSeries.norm_cxML_le
#print axioms QuantumNLS.Ext025A4BanachSeries.norm_cxML_apply_le
#print axioms QuantumNLS.Ext025A4BanachSeries.cxML_ι
#print axioms QuantumNLS.Ext025A4BanachSeries.cxSeries
#print axioms QuantumNLS.Ext025A4BanachSeries.norm_cxSeries_le
#print axioms QuantumNLS.Ext025A4BanachSeries.cxSeries_ι
#print axioms QuantumNLS.Ext025A4BanachSeries.cxSeries_bound
#print axioms QuantumNLS.Ext025A4BanachSeries.radius_cxSeries
#print axioms QuantumNLS.Ext025A4BanachSeries.series_sum_hasSeries
#print axioms QuantumNLS.Ext025A4BanachSeries.series_sum_bound
#print axioms QuantumNLS.Ext025A4BanachSeries.series_sum_real
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4BanachSeries" then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
