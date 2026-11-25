import Mathlib

/- G6040 SUP1 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6040Sup1Core.lean, namespace NlsGge.ThirdConsultation.G6040S.  SUPPORT (no packet
   increment): complexification_of = the body of Pro's retained leaf exists_local_complexification
   (followup14 PRO_DEFINITION_RESPONSE_FP80_16.md §Q3, "Complete construction", L803-877; head unchanged).
   Route exactly as Pro:  R z, J z = components of c.symm z (‖·‖ ≤ ‖c.symm‖);  z = j(Rz) + i j(Jz),
   R(iz) = -Jz, J(iz) = Rz (from hc);  A_ℂ(v) = Σ_{S ⊆ Fin n} i^|S| A(v^S) (cval), complex multilinear (additive,
   real homogeneous, and i-equivariant by the involution S ↦ S Δ {slot}), ‖A_ℂ‖ ≤ (2‖c.symm‖)^n ‖A‖ (Pro's corrected
   bound with the inverse-chart norm), A_ℂ(j h) = A h;  q n = (p n)_ℂ, K = max 1 ‖c.symm‖, r = ρ/(4K), q.radius ≥ 2r,
   G z = q.sum (z - c(a,0)) (totalized; analytic on ball (c(a,0)) r by Mathlib's series lemmas); for c(x,0) in that
   ball ‖x - a‖ < ρ/4 and the real series represents F x.
   Mathlib names verified in this repo's pinned tree (.lake/packages/mathlib @ d13f23b7), incl. Pro's L919 list. -/
set_option autoImplicit false

open Set Function
open scoped BigOperators NNReal ENNReal

namespace NlsGge.ThirdConsultation.G6040S
noncomputable section

section Coords
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  (c : (H × H) ≃L[ℝ] E)

def Rm : E →L[ℝ] H := (ContinuousLinearMap.fst ℝ H H).comp c.symm.toContinuousLinearMap
def Jm : E →L[ℝ] H := (ContinuousLinearMap.snd ℝ H H).comp c.symm.toContinuousLinearMap

theorem Rm_apply (z : E) : Rm c z = (c.symm z).1 := rfl
theorem Jm_apply (z : E) : Jm c z = (c.symm z).2 := rfl

theorem decomp (z : E) : c (Rm c z, Jm c z) = z := by
  rw [Rm_apply, Jm_apply, Prod.mk.eta]; exact c.apply_symm_apply z

theorem norm_Rm_le (z : E) : ‖Rm c z‖ ≤ ‖c.symm.toContinuousLinearMap‖ * ‖z‖ :=
  (norm_fst_le (c.symm z)).trans (c.symm.toContinuousLinearMap.le_opNorm z)

theorem norm_Jm_le (z : E) : ‖Jm c z‖ ≤ ‖c.symm.toContinuousLinearMap‖ * ‖z‖ :=
  (norm_snd_le (c.symm z)).trans (c.symm.toContinuousLinearMap.le_opNorm z)

theorem Rm_real (x : H) : Rm c (c (x, 0)) = x := by rw [Rm_apply, c.symm_apply_apply]
theorem Jm_real (x : H) : Jm c (c (x, 0)) = 0 := by rw [Jm_apply, c.symm_apply_apply]

variable (hc : ∀ x y : H, c (x, y) = c (x, 0) + Complex.I • c (y, 0))
include hc

theorem neg_swap (x y : H) : c (-y, x) = Complex.I • c (x, y) := by
  have h1 : c (-y, 0) = -c (y, 0) := by
    rw [← map_neg]; congr 1; ext <;> simp
  rw [hc (-y) x, hc x y, h1, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem symm_I (z : E) : c.symm (Complex.I • z) = (-(Jm c z), Rm c z) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, neg_swap c hc (Rm c z) (Jm c z), decomp]

theorem Rm_I (z : E) : Rm c (Complex.I • z) = -(Jm c z) := by rw [Rm_apply, symm_I c hc]
theorem Jm_I (z : E) : Jm c (Complex.I • z) = Rm c z := by rw [Jm_apply, symm_I c hc]

end Coords

section Multi
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  (c : (H × H) ≃L[ℝ] E) {n : ℕ}

def wS (S : Finset (Fin n)) (v : Fin n → E) : Fin n → H :=
  fun j => if j ∈ S then Jm c (v j) else Rm c (v j)

/-- Pro's finite subset-sum body of the complexified coefficient. -/
def cval (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) (v : Fin n → E) : ℂ :=
  ∑ S : Finset (Fin n), Complex.I ^ S.card * ((A (wS c S v) : ℝ) : ℂ)

theorem wS_update [DecidableEq (Fin n)] (S : Finset (Fin n)) (v : Fin n → E) (i : Fin n) (x : E) :
    wS c S (update v i x) = update (wS c S v) i (if i ∈ S then Jm c x else Rm c x) := by
  funext j
  by_cases h : j = i
  · subst h; simp [wS]
  · simp [wS, h]

theorem cval_add [DecidableEq (Fin n)] (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ)
    (v : Fin n → E) (i : Fin n) (x y : E) :
    cval c A (update v i (x + y)) = cval c A (update v i x) + cval c A (update v i y) := by
  unfold cval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [wS_update, wS_update, wS_update]
  split_ifs with h
  · rw [map_add, A.map_update_add]; push_cast; ring
  · rw [map_add, A.map_update_add]; push_cast; ring

theorem cval_smul_real [DecidableEq (Fin n)] (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ)
    (v : Fin n → E) (i : Fin n) (a : ℝ) (x : E) :
    cval c A (update v i (a • x)) = (a : ℂ) * cval c A (update v i x) := by
  unfold cval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [wS_update, wS_update]
  split_ifs with h
  · rw [map_smul, A.map_update_smul, smul_eq_mul]; push_cast; ring
  · rw [map_smul, A.map_update_smul, smul_eq_mul]; push_cast; ring

def flipS [DecidableEq (Fin n)] (i : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if i ∈ S then S.erase i else insert i S

theorem flipS_invol [DecidableEq (Fin n)] (i : Fin n) : Function.Involutive (flipS i) := by
  intro S
  unfold flipS
  by_cases h : i ∈ S
  · rw [if_pos h, if_neg (Finset.notMem_erase i S), Finset.insert_erase h]
  · rw [if_neg h, if_pos (Finset.mem_insert_self i S), Finset.erase_insert h]

theorem I_mul_pow_succ (k : ℕ) : Complex.I * Complex.I ^ (k + 1) = -Complex.I ^ k := by
  rw [pow_succ, ← mul_assoc, mul_comm Complex.I, mul_assoc, Complex.I_mul_I, mul_neg_one]

variable (hc : ∀ x y : H, c (x, y) = c (x, 0) + Complex.I • c (y, 0))
include hc

theorem term_I [DecidableEq (Fin n)] (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ)
    (v : Fin n → E) (i : Fin n) (x : E) (S : Finset (Fin n)) :
    Complex.I ^ S.card * ((A (wS c S (update v i (Complex.I • x))) : ℝ) : ℂ) =
      Complex.I * (Complex.I ^ (flipS i S).card * ((A (wS c (flipS i S) (update v i x)) : ℝ) : ℂ)) := by
  unfold flipS
  by_cases h : i ∈ S
  · rw [if_pos h]
    have hw : wS c S (update v i (Complex.I • x)) = wS c (S.erase i) (update v i x) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [wS, h, Jm_I c hc]
      · simp [wS, hj, Finset.mem_erase]
    have hk : S.card = (S.erase i).card + 1 := by
      rw [Finset.card_erase_of_mem h]; have := Finset.card_pos.2 ⟨i, h⟩; omega
    rw [hw, hk, pow_succ]; ring
  · rw [if_neg h]
    set u := wS c (insert i S) (update v i x) with hu
    have hw : wS c S (update v i (Complex.I • x)) = update u i (-(u i)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hu, wS, h, Rm_I c hc]
      · simp [hu, wS, hj]
    have hA : A (update u i (-(u i))) = -A u := by
      have := A.map_update_smul u i (-1 : ℝ) (u i)
      rwa [neg_one_smul, update_eq_self, neg_one_smul] at this
    have hk : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem h
    rw [hw, hA, hk, ← mul_assoc, I_mul_pow_succ]
    push_cast; ring

theorem cval_I [DecidableEq (Fin n)] (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ)
    (v : Fin n → E) (i : Fin n) (x : E) :
    cval c A (update v i (Complex.I • x)) = Complex.I * cval c A (update v i x) := by
  unfold cval
  rw [Finset.mul_sum]
  simp_rw [term_I c hc A v i x]
  exact Equiv.sum_comp (Function.Involutive.toPerm (flipS i) (flipS_invol i))
    (fun S => Complex.I * (Complex.I ^ S.card * ((A (wS c S (update v i x)) : ℝ) : ℂ)))

theorem cval_smul [DecidableEq (Fin n)] (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ)
    (v : Fin n → E) (i : Fin n) (z : ℂ) (x : E) :
    cval c A (update v i (z • x)) = z * cval c A (update v i x) := by
  have hz : z • x = (z.re : ℝ) • x + (z.im : ℝ) • (Complex.I • x) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  rw [hz, cval_add, cval_smul_real, cval_smul_real, cval_I c hc]
  have := Complex.re_add_im z
  linear_combination (cval c A (update v i x)) * this

def cmult (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) :
    MultilinearMap ℂ (fun _ : Fin n => E) ℂ where
  toFun := cval c A
  map_update_add' := fun v i x y => cval_add c A v i x y
  map_update_smul' := fun v i z x => by rw [smul_eq_mul]; exact cval_smul c hc A v i z x

omit hc in
theorem norm_cval_le (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) (v : Fin n → E) :
    ‖cval c A v‖ ≤ (2 * ‖c.symm.toContinuousLinearMap‖) ^ n * ‖A‖ * ∏ j, ‖v j‖ := by
  set K := ‖c.symm.toContinuousLinearMap‖ with hK
  have hterm : ∀ S : Finset (Fin n),
      ‖Complex.I ^ S.card * ((A (wS c S v) : ℝ) : ℂ)‖ ≤ ‖A‖ * ∏ j, (K * ‖v j‖) := by
    intro S
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real]
    refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)) (norm_nonneg _))
    unfold wS
    split_ifs
    · exact norm_Jm_le c _
    · exact norm_Rm_le c _
  unfold cval
  calc ‖∑ S : Finset (Fin n), Complex.I ^ S.card * ((A (wS c S v) : ℝ) : ℂ)‖
      ≤ ∑ S : Finset (Fin n), ‖A‖ * ∏ j, (K * ‖v j‖) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => hterm S)
    _ = (2 * K) ^ n * ‖A‖ * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- The complexified continuous multilinear coefficient. -/
def cCML (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
  (cmult c hc A).mkContinuous ((2 * ‖c.symm.toContinuousLinearMap‖) ^ n * ‖A‖) (norm_cval_le c A)

theorem cCML_apply (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) (v : Fin n → E) :
    cCML c hc A v = cval c A v := rfl

theorem norm_cCML_le (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) :
    ‖cCML c hc A‖ ≤ (2 * ‖c.symm.toContinuousLinearMap‖) ^ n * ‖A‖ :=
  MultilinearMap.mkContinuous_norm_le _ (by positivity) _

theorem cCML_real (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ) (h : Fin n → H) :
    cCML c hc A (fun j => c (h j, 0)) = ((A h : ℝ) : ℂ) := by
  rw [cCML_apply]
  unfold cval
  rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
  · have hw0 : wS c (∅ : Finset (Fin n)) (fun j => c (h j, 0)) = h := by
      funext j; simp [wS, Rm_real]
    rw [hw0]; simp
  · intro S _ hS
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hS
    rw [A.map_coord_zero j (by simp [wS, hj, Jm_real])]
    simp
  · intro h0; exact absurd (Finset.mem_univ _) h0

end Multi

/-! ### The series step -/

theorem complexification_of
    {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (c : (H × H) ≃L[ℝ] E)
    (hc : ∀ x y : H, c (x, y) = c (x, 0) + Complex.I • c (y, 0))
    (F : H → ℝ) (a : H) (hF : AnalyticAt ℝ F a) :
  ∃ (r : ℝ) (G : E → ℂ), 0 < r ∧
    AnalyticOnNhd ℂ G (Metric.ball (c (a, 0)) r) ∧
    ∀ x : H, c (x, 0) ∈ Metric.ball (c (a, 0)) r →
      G (c (x, 0)) = (F x : ℂ) := by
  obtain ⟨p, ρ₀, hp⟩ := hF
  obtain ⟨ρ, hρ0, hρρ₀⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast ENNReal.coe_pos.1 hρ0
  have hsumm : Summable fun n => ‖p n‖ * (ρ : ℝ) ^ n :=
    p.summable_norm_mul_pow (lt_of_lt_of_le hρρ₀ hp.r_le)
  set K' : ℝ := ‖c.symm.toContinuousLinearMap‖ with hK'
  set K : ℝ := max 1 K' with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK'K : K' ≤ K := le_max_right _ _
  have hK'0 : 0 ≤ K' := norm_nonneg c.symm.toContinuousLinearMap
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  set r : ℝ := ρ / (4 * K) with hr
  have hrpos : 0 < r := div_pos hρpos (by positivity)
  have h4Kr : 4 * K * r = ρ := by rw [hr]; field_simp
  let q : FormalMultilinearSeries ℂ E ℂ := fun n => cCML c hc (p n)
  let r2 : ℝ≥0 := ⟨2 * r, by positivity⟩
  have hr2 : ((r2 : ℝ≥0) : ℝ) = 2 * r := rfl
  have hq : (r2 : ℝ≥0∞) ≤ q.radius := by
    refine q.le_radius_of_summable (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsumm)
    rw [hr2]
    calc ‖q n‖ * (2 * r) ^ n ≤ ((2 * K') ^ n * ‖p n‖) * (2 * r) ^ n :=
          mul_le_mul_of_nonneg_right (norm_cCML_le c hc (p n)) (by positivity)
      _ = ‖p n‖ * (4 * K' * r) ^ n := by
          have e : (4 * K' * r) ^ n = (2 * K') ^ n * (2 * r) ^ n := by
            rw [← mul_pow]; congr 1; ring
          rw [e]; ring
      _ ≤ ‖p n‖ * (4 * K * r) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by nlinarith) n) (norm_nonneg _)
      _ = ‖p n‖ * (ρ : ℝ) ^ n := by rw [h4Kr]
  have hr2pos : (0 : ℝ≥0) < r2 := NNReal.coe_pos.1 (by rw [hr2]; positivity)
  have hrad : 0 < q.radius := lt_of_lt_of_le (by exact_mod_cast hr2pos) hq
  have hG := (q.hasFPowerSeriesOnBall hrad).comp_sub (c (a, 0))
  rw [zero_add] at hG
  have hball : ∀ z : E, ‖z‖ < r → z ∈ Metric.eball (0 : E) q.radius := by
    intro z hz
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    have h1 : ENNReal.ofReal ‖z‖ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hz
    refine lt_of_lt_of_le h1 (le_trans ?_ hq)
    rw [show ((r2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 * r) by rw [← hr2, ENNReal.ofReal_coe_nnreal]]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨r, fun z => q.sum (z - c (a, 0)), hrpos, ?_, ?_⟩
  · intro z hz
    refine hG.analyticOnNhd z ?_
    rw [Metric.mem_eball, edist_dist]
    have hz' : dist z (c (a, 0)) < r := hz
    have : ENNReal.ofReal (dist z (c (a, 0))) < ENNReal.ofReal (2 * r) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    refine lt_of_lt_of_le this (le_trans ?_ hq)
    rw [← hr2, ENNReal.ofReal_coe_nnreal]
  · intro x hx
    have hxa : c (x, 0) - c (a, 0) = c (x - a, 0) := by
      rw [← map_sub, Prod.mk_sub_mk, sub_zero]
    have hxr : ‖c (x, 0) - c (a, 0)‖ < r := by rw [← dist_eq_norm]; exact hx
    have hnorm : ‖x - a‖ ≤ K' * ‖c (x, 0) - c (a, 0)‖ := by
      have h1 : (x - a, (0 : H)) = c.symm (c (x, 0) - c (a, 0)) := by rw [hxa, c.symm_apply_apply]
      calc ‖x - a‖ ≤ ‖((x - a, (0 : H)) : H × H)‖ := norm_fst_le ((x - a, (0 : H)) : H × H)
        _ = ‖c.symm (c (x, 0) - c (a, 0))‖ := by rw [h1]
        _ ≤ K' * ‖c (x, 0) - c (a, 0)‖ := c.symm.toContinuousLinearMap.le_opNorm _
    have hxa_lt : ‖x - a‖ < ρ := by
      have : K' * ‖c (x, 0) - c (a, 0)‖ ≤ K * r :=
        mul_le_mul hK'K hxr.le (norm_nonneg _) hKpos.le
      nlinarith
    have hmemF : x ∈ Metric.eball a ρ₀ := by
      rw [Metric.mem_eball, edist_dist, dist_eq_norm]
      refine lt_of_lt_of_le ?_ hρρ₀.le
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff hρpos).2 hxa_lt
    have hsF := Complex.ofRealCLM.hasSum (hp.hasSum_sub hmemF)
    have hsG := q.hasSum (hball _ hxr)
    have hterms : (fun n : ℕ => q n fun _ => c (x, 0) - c (a, 0)) =
        fun n => Complex.ofRealCLM (p n fun _ => x - a) := by
      funext n
      rw [hxa, Complex.ofRealCLM_apply]
      exact cCML_real c hc (p n) (fun _ => x - a)
    rw [hterms] at hsG
    rw [Complex.ofRealCLM_apply] at hsF
    exact hsG.unique hsF

end
end NlsGge.ThirdConsultation.G6040S
