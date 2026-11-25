import QuantumNLS.Q07TailBindingR24
import QuantumNLS.RiccatiFourierBase

/-! R-C5645D32 / prop:Q07Bgradientremoval, at the exact printed regularity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Metric Filter Topology
namespace QuantumNLS.Q07GradientRemovalR24
open RiccatiSobolevBanach Q07TailBindingR24 Q07SobolevModelR24 Q07RealCalculusR24
open Q07ChargeLevelsR24 ClassicalCharges SmoothScalarMomentsPhysical
open ComplexifiedSobolevField RiccatiPointwiseDisc PROP017UniformN
variable {L κ : ℝ} [Fact (0 < L)]

def T (hκ : 0 < κ) (r : ℕ) (h : ℝ) (l : ℕ)
    (u : Sobolev.H02 L (regularity r)) : ℝ :=
  tail (L := L) hκ r h l (coordinates (regularity_pos r).le u)

def smoothBall (r : ℕ) (B : ℝ) : Set (Sobolev.H02 L (regularity r)) :=
  {u | ‖u‖ ≤ B ∧ ∃ f : ℝ → ℂ, ∃ hf : SmoothPeriodic L f, u.val = smoothL2 hf}

/-- The function differentiated below is exactly the printed difference at
all smooth profiles, with the full-mass window contour. -/
theorem T_eq_printed (hκ : 0 < κ) (r l : ℕ) (h : ℝ)
    (u : Sobolev.H02 L (regularity r)) {f : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hu : u.val = smoothL2 hf) :
    T (L := L) hκ r h l u = (charge L κ f (r+1)).re -
      Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) h u.val := by
  obtain ⟨x,hx⟩ := RiccatiFourierBase.riccati_fourier_base (Fact.out : 0 < L)
    (a := (1 : ℝ)) (S := regularity r) (by norm_num)
    (by dsimp [regularity]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]) hf
  have hrep : physRep L (regularity r) x = f := (physical_rep (L := L) r x).symm.trans hx
  have hs : (1 : ℝ)/2 < regularity r := by dsimp [regularity]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have he := fieldMap_eq_smooth hs hf x hrep
  have hc : coordinates (regularity_pos r).le u = x := by
    apply toField_inj
    funext k
    rw [toField_coordinates, ← coeff_fieldMap L (regularity r) (regularity_pos r).le x k,he,hu]
  unfold T
  rw [hc,physical_tail,hrep]
  change _ - Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) h
    (fieldMap L (regularity r) (regularity_pos r).le x) = _
  rw [he,hu]

lemma scale_identity (r : ℕ) {a K H : ℝ} (ha : 1 ≤ a) :
    let ε := (a^(r+1)*Real.sqrt a)⁻¹
    0 < ε ∧ ε ≤ 1 ∧
      2*(K/a^(r+2))/ε+(H*a^(r+1))*ε = (2*K+H)*a^(-(1/2 : ℝ)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hp : 0 < a^(r+1) := pow_pos ha0 _
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hs1 : 1 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) ha0.le).mpr (by simpa using ha)
  have hp1 : 1 ≤ a^(r+1) := one_le_pow₀ ha
  have hprod : 1 ≤ a^(r+1)*Real.sqrt a := by
    simpa only [one_mul] using mul_le_mul hp1 hs1 zero_le_one hp.le
  dsimp only
  refine ⟨inv_pos.mpr (mul_pos hp hs),inv_le_one_of_one_le₀ hprod,?_⟩
  rw [Real.rpow_neg ha0.le,← Real.sqrt_eq_rpow]
  rw [show r+2 = (r+1)+1 by omega,pow_succ]
  field_simp
  rw [Real.sq_sqrt ha0.le]
  ring

/-- The numerical argument applies on the entire real Sobolev ball. -/
lemma model_bound (hκ : 0 < κ) (r : ℕ) (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ x : Ell2, ‖x‖ ≤ B →
      DifferentiableAt ℝ (tail (L := L) hκ r h l) x ∧
      ‖fderiv ℝ (tail (L := L) hκ r h l) x‖ ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨K,H,hK,hH,l0,hd⟩ := tail_data (L := L) hκ r B hh
  refine ⟨2*K+H,by positivity,l0,?_⟩
  intro l hl x hx
  obtain ⟨ha,hD,hV⟩ := hd l hl
  obtain ⟨hε,hε1,he⟩ := scale_identity r (K := K) (H := H) ha
  have ha0 : 0 < cutSeq L l := zero_lt_one.trans_le ha
  have hb := derivative_bound (div_nonneg hK (pow_nonneg ha0.le _))
    (mul_nonneg hH (pow_nonneg ha0.le _)) hε hε1
    (fun y hy => (hD y hy).1) (fun y hy => (hD y hy).2.1)
    (fun y hy v w => (hD y hy).2.2 v w) hV x hx
  rw [he] at hb
  exact ⟨(hD x (by linarith)).1,hb⟩

/-- R-C5645D32: the full real H^s dual norm, with s=2r+4, uniformly over
all smooth profiles of norm at most B. Radial/mass variations are included. -/
theorem «prop:Q07Bgradientremoval» (hκ : 0 < κ) (r : ℕ) (_hr : 2 ≤ r)
    (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      (∀ u : Sobolev.H02 L (regularity r), ‖u‖ ≤ B → DifferentiableAt ℝ (T (L := L) hκ r h l) u) ∧
      sSup ((fun u : Sobolev.H02 L (regularity r) => ‖fderiv ℝ (T (L := L) hκ r h l) u‖) '' smoothBall (L := L) r B)
        ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨C,hC,l0,hbound⟩ := model_bound (L := L) hκ r B hh
  refine ⟨C,hC,l0,?_⟩
  intro l hl
  have ha0 : 0 ≤ cutSeq L l := by
    unfold cutSeq
    exact div_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (Fact.out : 0 < L).le
  let A := ((coordinates (L := L) (regularity_pos r).le).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hall : ∀ u : Sobolev.H02 L (regularity r), ‖u‖ ≤ B →
      DifferentiableAt ℝ (T (L := L) hκ r h l) u ∧
        ‖fderiv ℝ (T (L := L) hκ r h l) u‖ ≤ C*(cutSeq L l)^(-(1/2 : ℝ)) := by
    intro u hu
    have hn : ‖A u‖ = ‖u‖ := (coordinates (regularity_pos r).le).norm_map u
    obtain ⟨hD,hb⟩ := hbound l hl (A u) (by simpa only [hn] using hu)
    have hd := hD.hasFDerivAt.comp u A.hasFDerivAt
    refine ⟨hd.differentiableAt,?_⟩
    change ‖fderiv ℝ (tail (L := L) hκ r h l ∘ A) u‖ ≤ _
    rw [hd.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Real.rpow_nonneg ha0 _))
    intro v
    calc ‖(fderiv ℝ (tail (L := L) hκ r h l) (A u)).comp A v‖
        ≤ ‖fderiv ℝ (tail (L := L) hκ r h l) (A u)‖*‖A v‖ := by
          change ‖fderiv ℝ (tail (L := L) hκ r h l) (A u) (A v)‖ ≤ _
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C*(cutSeq L l)^(-(1/2 : ℝ)))*‖v‖ := by
        rw [show ‖A v‖ = ‖v‖ from (coordinates (regularity_pos r).le).norm_map v]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  refine ⟨fun u hu => (hall u hu).1,?_⟩
  by_cases hs : (((fun u : Sobolev.H02 L (regularity r) => ‖fderiv ℝ (T (L := L) hκ r h l) u‖) '' smoothBall (L := L) r B) : Set ℝ).Nonempty
  · apply csSup_le hs
    rintro b ⟨u,hu,rfl⟩
    exact (hall u hu.1).2
  · rw [not_nonempty_iff_eq_empty.mp hs,Real.sSup_empty]
    exact mul_nonneg hC (Real.rpow_nonneg ha0 _)

end QuantumNLS.Q07GradientRemovalR24
