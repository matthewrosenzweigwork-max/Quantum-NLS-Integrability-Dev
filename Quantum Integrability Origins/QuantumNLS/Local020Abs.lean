import Mathlib

/-! LOCAL-020 stage S0: abstract intertwining lemma for resolvents and contour integrals.

For a relation `G ⊆ H × H` (the graph of an operator) we define the resolvent `res G z` (junk value `0`
when no bounded two-sided inverse exists), exactly as `LocalSpectralOperator.resolvent`.  If a unitary
`W : H ≃ₗᵢ[ℂ] H` carries `G` to `G'` by `(f, φ) ↦ (W f, ε W φ + c W f)` with `ε² = 1`, then
`res G' (c + ε z) = ε • (W (res G z) W⁻¹)`.  Contour integrals are transported accordingly
(`ε = ±1`, translation and rotation by `π` of the circle). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section
open Filter Topology Set MeasureTheory

namespace QuantumNLS.Local020Abs

section Res

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- `R` is a two-sided bounded resolvent at `z` for the graph `G` (same shape as `IsResolvent`). -/
def IsRes (G : Set (H × H)) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ, (R φ, z • R φ - φ) ∈ G) ∧ ∀ p ∈ G, R (z • p.1 - p.2) = p.1

theorem IsRes.unique {G : Set (H × H)} {z : ℂ} {R R' : H →L[ℂ] H} (h : IsRes G z R)
    (h' : IsRes G z R') : R = R' := by
  ext φ : 1
  have := h.2 (R' φ, z • R' φ - φ) (h'.1 φ)
  simpa using this

open Classical in
/-- The resolvent (junk value `0` outside the resolvent set). -/
def res (G : Set (H × H)) (z : ℂ) : H →L[ℂ] H :=
  if h : ∃ R, IsRes G z R then h.choose else 0

theorem res_eq {G : Set (H × H)} {z : ℂ} {R : H →L[ℂ] H} (h : IsRes G z R) : res G z = R := by
  have hex : ∃ R, IsRes G z R := ⟨R, h⟩
  unfold res
  rw [dif_pos hex]
  exact IsRes.unique hex.choose_spec h

theorem res_eq_zero {G : Set (H × H)} {z : ℂ} (h : ¬ ∃ R, IsRes G z R) : res G z = 0 := by
  unfold res
  rw [dif_neg h]

/-- The intertwining relation `G' = {(W f, ε W φ + c W f)}`. -/
structure Inter (G G' : Set (H × H)) (W : H ≃ₗᵢ[ℂ] H) (ε c : ℂ) : Prop where
  eps : ε * ε = 1
  iff : ∀ f φ, (f, φ) ∈ G ↔ (W f, ε • W φ + c • W f) ∈ G'
  neg : ∀ f φ, (f, φ) ∈ G' → (ε • f, ε • φ) ∈ G'

theorem Inter.symm {G G' : Set (H × H)} {W : H ≃ₗᵢ[ℂ] H} {ε c : ℂ} (h : Inter G G' W ε c) :
    Inter G' G W.symm ε (-(ε * c)) := by
  refine ⟨h.eps, fun f' φ' => ?_, fun f φ hfφ => ?_⟩
  · rw [h.iff]
    have e1 : W (W.symm f') = f' := W.apply_symm_apply f'
    have e2 : W (ε • W.symm φ' + (-(ε * c)) • W.symm f') = ε • φ' + (-(ε * c)) • f' := by
      rw [map_add, map_smul, map_smul, e1, W.apply_symm_apply]
    rw [e1, e2]
    have e3 : ε • (ε • φ' + (-(ε * c)) • f') + c • f' = φ' := by
      simp only [smul_add, smul_smul, h.eps, one_smul, neg_mul, mul_neg]
      have : ε * (ε * c) = c := by rw [← mul_assoc, h.eps, one_mul]
      rw [this, neg_smul]; abel
    rw [e3]
  · have h1 := h.neg _ _ ((h.iff _ _).1 hfφ)
    rw [h.iff]
    have e1 : W (ε • f) = ε • W f := map_smul _ _ _
    have e2 : ε • W (ε • φ) + c • W (ε • f) = ε • (ε • W φ + c • W f) := by
      rw [map_smul, map_smul]
      simp only [smul_add, smul_smul, mul_comm c ε]
    rw [e2, e1]
    exact h1

/-- Conjugation of an operator by `W`: `A ↦ W A W⁻¹`, as a continuous linear equivalence. -/
def cjE {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (W : X ≃ₗᵢ[ℂ] X) :
    (X →L[ℂ] X) ≃L[ℂ] (X →L[ℂ] X) :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.mulLeftRight ℂ (X →L[ℂ] X) (W.toContinuousLinearEquiv : X →L[ℂ] X)
      (W.symm.toContinuousLinearEquiv : X →L[ℂ] X))
    (ContinuousLinearMap.mulLeftRight ℂ (X →L[ℂ] X) (W.symm.toContinuousLinearEquiv : X →L[ℂ] X)
      (W.toContinuousLinearEquiv : X →L[ℂ] X))
    (fun A => by
      ext x
      simp [ContinuousLinearMap.mulLeftRight_apply])
    (fun A => by
      ext x
      simp [ContinuousLinearMap.mulLeftRight_apply])

theorem cjE_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (W : X ≃ₗᵢ[ℂ] X) (A : X →L[ℂ] X) (x : X) : cjE W A x = W (A (W.symm x)) := rfl

theorem cjE_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (W : X ≃ₗᵢ[ℂ] X) (A B : X →L[ℂ] X) : cjE W (A * B) = cjE W A * cjE W B := by
  ext x
  simp [cjE_apply]

theorem cjE_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (W : X ≃ₗᵢ[ℂ] X) : cjE W 1 = 1 := by
  ext x
  simp [cjE_apply]

variable {G G' : Set (H × H)} {W : H ≃ₗᵢ[ℂ] H} {ε c : ℂ}

theorem alg1 (heps : ε * ε = 1) (a ψ : H) (z : ℂ) :
    ε • (ε • (z • a - ψ) + c • a) = (c + ε * z) • (ε • a) - ψ := by
  have : ε • (ε • (z • a - ψ) + c • a) - ((c + ε * z) • (ε • a) - ψ) = (ε * ε - 1) • (-ψ) := by module
  rw [heps, sub_self, zero_smul] at this
  exact sub_eq_zero.mp this

theorem alg2 (heps : ε * ε = 1) (x y : H) (z : ℂ) :
    W.symm ((c + ε * z) • x - y) = ε • (z • W.symm x - (ε • W.symm y + (-(ε * c)) • W.symm x)) := by
  rw [map_sub, map_smul]
  have : (c + ε * z) • W.symm x - W.symm y - ε • (z • W.symm x - (ε • W.symm y + (-(ε * c)) • W.symm x)) =
      (ε * ε - 1) • (W.symm y - c • W.symm x) := by
    module
  rw [heps, sub_self, zero_smul] at this
  exact sub_eq_zero.mp this

/-- Forward transport of a resolvent. -/
theorem IsRes.transport (h : Inter G G' W ε c) {z : ℂ} {R : H →L[ℂ] H} (hR : IsRes G z R) :
    IsRes G' (c + ε * z) (ε • cjE W R) := by
  refine ⟨fun ψ => ?_, fun p hp => ?_⟩
  · simp only [ContinuousLinearMap.smul_apply, cjE_apply]
    have h1 := (h.iff _ _).1 (hR.1 (W.symm ψ))
    have h2 := h.neg _ _ h1
    rw [map_sub, map_smul, W.apply_symm_apply] at h2
    have e := alg1 (c := c) h.eps (W (R (W.symm ψ))) ψ z
    rw [← e]
    exact h2
  · simp only [ContinuousLinearMap.smul_apply, cjE_apply]
    have hq := (h.symm.iff p.1 p.2).1 hp
    have h3 : R (z • W.symm p.1 - (ε • W.symm p.2 + (-(ε * c)) • W.symm p.1)) = W.symm p.1 :=
      hR.2 _ hq
    rw [alg2 h.eps, map_smul, h3, map_smul, W.apply_symm_apply, smul_smul, h.eps, one_smul]

theorem res_transport (h : Inter G G' W ε c) (z : ℂ) :
    res G' (c + ε * z) = ε • cjE W (res G z) := by
  by_cases hex : ∃ R, IsRes G z R
  · obtain ⟨R, hR⟩ := hex
    rw [res_eq hR, res_eq (hR.transport h)]
  · rw [res_eq_zero hex]
    have : ¬ ∃ R', IsRes G' (c + ε * z) R' := by
      rintro ⟨R', hR'⟩
      have h4 := hR'.transport h.symm
      have e : -(ε * c) + ε * (c + ε * z) = z := by
        have : ε * (ε * z) = z := by rw [← mul_assoc, h.eps, one_mul]
        linear_combination this
      rw [e] at h4
      exact hex ⟨_, h4⟩
    rw [res_eq_zero this]
    simp

end Res

/-! ### Contour integrals -/

section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_equiv {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']
    (e : E ≃L[ℂ] E') (F : ℂ → E) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => e (F z)) c r = e (circleIntegral F c r) := by
  unfold circleIntegral
  have h0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h0,
    ← ContinuousLinearEquiv.integral_comp_comm]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_smul]

theorem circle_transport (F : ℂ → E) (c c0 ε : ℂ) (r : ℝ) (hε : ε = 1 ∨ ε = -1) :
    circleIntegral (fun z' => F (ε * (z' - c))) (c + ε * c0) r = ε • circleIntegral F c0 r := by
  have hc : ∀ (c : ℂ) (θ : ℝ), circleMap c r θ = c + circleMap 0 r θ := by
    intro c θ; simp [circleMap]
  rcases hε with rfl | rfl
  · unfold circleIntegral
    rw [one_smul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [one_mul, deriv_circleMap]
    have e : circleMap (c + c0) r θ - c = circleMap c0 r θ := by simp [circleMap]; ring
    rw [e]
  · unfold circleIntegral
    have hpi : ∀ θ : ℝ, circleMap 0 r (θ + Real.pi) = - circleMap 0 r θ := by
      intro θ
      rw [circleMap_zero, circleMap_zero]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    set f : ℝ → E := fun θ => deriv (circleMap c0 r) θ • F (circleMap c0 r θ) with hf
    have key : ∀ θ : ℝ, deriv (circleMap (c + -1 * c0) r) θ •
        F (-1 * (circleMap (c + -1 * c0) r θ - c)) = -(f (θ + Real.pi)) := by
      intro θ
      simp only [hf, deriv_circleMap, hpi θ, hc c0 (θ + Real.pi), hc (c + -1 * c0) θ]
      rw [neg_mul (circleMap 0 r θ) Complex.I, neg_smul, neg_neg]
      congr 2
      ring
    have hper : Function.Periodic f (2 * Real.pi) := by
      intro θ
      simp only [hf, deriv_circleMap, periodic_circleMap 0 r θ, periodic_circleMap c0 r θ]
    simp only [key]
    have hP := hper.intervalIntegral_add_eq Real.pi 0
    rw [zero_add] at hP
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_add_right f Real.pi,
      zero_add, show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, hP]
    simp

end Circle

section Contour

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G G' : Set (H × H)} {W : H ≃ₗᵢ[ℂ] H} {ε c : ℂ}

theorem res_transport' (h : Inter G G' W ε c) (z' : ℂ) :
    res G' z' = ε • cjE W (res G (ε * (z' - c))) := by
  have := res_transport h (ε * (z' - c))
  have e : c + ε * (ε * (z' - c)) = z' := by
    have : ε * (ε * (z' - c)) = z' - c := by rw [← mul_assoc, h.eps, one_mul]
    rw [this]; ring
  rwa [e] at this

/-- Transport of the Riesz integral `∮ (z - 𝓛)⁻¹ dz`. -/
theorem riesz_transport (h : Inter G G' W ε c) (hε : ε = 1 ∨ ε = -1) (p0 : ℂ) (r : ℝ) :
    circleIntegral (fun z => res G' z) (c + ε * p0) r =
      cjE W (circleIntegral (fun z => res G z) p0 r) := by
  have e1 : (fun z => res G' z) =
      fun z' => (fun w => ε • cjE W (res G w)) (ε * (z' - c)) := funext (res_transport' h)
  rw [e1, circle_transport (fun w => ε • cjE W (res G w)) c p0 ε r hε,
    circleIntegral.integral_smul ε, circleIntegral_equiv (cjE W) (fun w => res G w), smul_smul,
    h.eps, one_smul]

/-- Transport of the dressed integral `∮ (z - p) (z - 𝓛)⁻¹ dz`; note the factor `ε`. -/
theorem dressed_transport (h : Inter G G' W ε c) (hε : ε = 1 ∨ ε = -1) (p0 : ℂ) (r : ℝ) :
    circleIntegral (fun z => (z - (c + ε * p0)) • res G' z) (c + ε * p0) r =
      ε • cjE W (circleIntegral (fun z => (z - p0) • res G z) p0 r) := by
  have e1 : (fun z => (z - (c + ε * p0)) • res G' z) =
      fun z' => (fun w => cjE W ((w - p0) • res G w)) (ε * (z' - c)) := by
    funext z'
    rw [res_transport' h z']
    have hw : ε * (ε * (z' - c)) = z' - c := by rw [← mul_assoc, h.eps, one_mul]
    have hz : z' - (c + ε * p0) = ε * (ε * (z' - c) - p0) := by
      rw [mul_sub, hw]; ring
    simp only [hz, map_smul, smul_smul]
    rw [show ε * (ε * (z' - c) - p0) * ε = ε * ε * (ε * (z' - c) - p0) by ring, h.eps, one_mul]
  rw [e1, circle_transport (fun w => cjE W ((w - p0) • res G w)) c p0 ε r hε,
    circleIntegral_equiv (cjE W) (fun w => (w - p0) • res G w)]

end Contour

/-! ### The reduction pipeline `E ↦ C ↦ C^{-1/2} ↦ U ↦ B` and its transport -/

section Pipe

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A unitary as a continuous linear map. -/
def ic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (M : X ≃ₗᵢ[ℂ] X) : X →L[ℂ] X :=
  (M.toContinuousLinearEquiv : X →L[ℂ] X)

@[simp] theorem ic_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (M : X ≃ₗᵢ[ℂ] X)
    (x : X) : ic M x = M x := rfl

theorem adjoint_ic {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) : ContinuousLinearMap.adjoint (ic M) = ic M.symm := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [ic_apply]
  exact (M.symm.inner_map_eq_flip x y).trans (by simp)

/-- The series `∑ cf k (T - 1)^k` (the inverse square root with `cf k = binom(-1/2,k)`). -/
def isqs {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (cf : ℕ → ℂ) (T : X →L[ℂ] X) :
    X →L[ℂ] X := ∑' k : ℕ, cf k • (T - 1) ^ k

theorem cjE_pow {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) (T : X →L[ℂ] X) (k : ℕ) : cjE M (T ^ k) = (cjE M T) ^ k := by
  induction k with
  | zero => simpa using cjE_one M
  | succ k ih => rw [pow_succ, cjE_mul, ih, pow_succ]

theorem cjE_isqs {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) (cf : ℕ → ℂ) (T : X →L[ℂ] X) : cjE M (isqs cf T) = isqs cf (cjE M T) := by
  unfold isqs
  rw [ContinuousLinearEquiv.map_tsum]
  refine tsum_congr fun k => ?_
  rw [map_smul, cjE_pow, map_sub, cjE_one]

theorem cjE_symm_cjE {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) (A : X →L[ℂ] X) : cjE M.symm (cjE M A) = A := by
  ext x
  simp [cjE_apply]

theorem norm_cjE_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) (A : X →L[ℂ] X) : ‖cjE M A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [cjE_apply, M.norm_map]
  exact (A.le_opNorm _).trans (by rw [M.symm.norm_map])

theorem norm_cjE {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (M : X ≃ₗᵢ[ℂ] X) (A : X →L[ℂ] X) : ‖cjE M A‖ = ‖A‖ := by
  refine le_antisymm (norm_cjE_le M A) ?_
  have := norm_cjE_le M.symm (cjE M A)
  rwa [cjE_symm_cjE] at this

/-- The compression `E* P E`. -/
def cmpM (P : H →L[ℂ] H) (E : K →L[ℂ] H) : K →L[ℂ] K :=
  (ContinuousLinearMap.adjoint E) ∘L P ∘L E

/-- The normalized isometry `U = P E C^{-1/2}`. -/
def isoU (cf : ℕ → ℂ) (P : H →L[ℂ] H) (E : K →L[ℂ] H) : K →L[ℂ] H :=
  P ∘L E ∘L isqs cf (cmpM P E)

/-- The reduced matrix `p 1 + U* D U`. -/
def redM (cf : ℕ → ℂ) (p : ℂ) (P D : H →L[ℂ] H) (E : K →L[ℂ] H) : K →L[ℂ] K :=
  p • ContinuousLinearMap.id ℂ K +
    (ContinuousLinearMap.adjoint (isoU cf P E)) ∘L D ∘L (isoU cf P E)

variable (W : H ≃ₗᵢ[ℂ] H) (M : K ≃ₗᵢ[ℂ] K) (P D : H →L[ℂ] H) (E E' : K →L[ℂ] H)

theorem E'_apply (hE : E' ∘L ic M = ic W ∘L E) (x : K) : E' x = W (E (M.symm x)) := by
  have := congrArg (fun T : K →L[ℂ] H => T (M.symm x)) hE
  simpa using this

theorem adjoint_E' (hE : E' ∘L ic M = ic W ∘L E) :
    ContinuousLinearMap.adjoint E' = ic M ∘L ContinuousLinearMap.adjoint E ∘L ic W.symm := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [ContinuousLinearMap.comp_apply, ic_apply]
  rw [E'_apply W M E E' hE, M.inner_map_eq_flip, ContinuousLinearMap.adjoint_inner_left,
    W.symm.inner_map_eq_flip]
  simp

theorem cmpM_transport (hE : E' ∘L ic M = ic W ∘L E) :
    cmpM (cjE W P) E' = cjE M (cmpM P E) := by
  ext x
  rw [cmpM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adjoint_E' W M E E' hE]
  simp only [ContinuousLinearMap.comp_apply, ic_apply, cjE_apply, cmpM, E'_apply W M E E' hE]
  simp

theorem isoU_transport (cf : ℕ → ℂ) (hE : E' ∘L ic M = ic W ∘L E) :
    isoU cf (cjE W P) E' = ic W ∘L isoU cf P E ∘L ic M.symm := by
  ext x
  have hc : isqs cf (cmpM (cjE W P) E') = cjE M (isqs cf (cmpM P E)) := by
    rw [cmpM_transport W M P E E' hE, cjE_isqs]
  simp only [isoU, hc, ContinuousLinearMap.comp_apply, cjE_apply, ic_apply, E'_apply W M E E' hE]
  simp

theorem redM_transport (cf : ℕ → ℂ) (ε p p' : ℂ) (hE : E' ∘L ic M = ic W ∘L E) (heps : ε * ε = 1) :
    redM cf p' (cjE W P) (ε • cjE W D) E' = p' • ContinuousLinearMap.id ℂ K +
      ε • cjE M (redM cf p P D E - p • ContinuousLinearMap.id ℂ K) := by
  have hU := isoU_transport W M P E E' cf hE
  have hadj : ContinuousLinearMap.adjoint (isoU cf (cjE W P) E') =
      ic M ∘L ContinuousLinearMap.adjoint (isoU cf P E) ∘L ic W.symm := by
    rw [hU, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_ic, adjoint_ic]
    ext x
    simp
  unfold redM
  rw [hadj, hU]
  ext x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ic_apply, cjE_apply, add_sub_cancel_left, map_smul, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]

end Pipe

end QuantumNLS.Local020Abs

#print axioms QuantumNLS.Local020Abs.res_transport
#print axioms QuantumNLS.Local020Abs.riesz_transport
#print axioms QuantumNLS.Local020Abs.dressed_transport
#print axioms QuantumNLS.Local020Abs.cmpM_transport
#print axioms QuantumNLS.Local020Abs.isoU_transport
#print axioms QuantumNLS.Local020Abs.redM_transport
#print axioms QuantumNLS.Local020Abs.circle_transport
