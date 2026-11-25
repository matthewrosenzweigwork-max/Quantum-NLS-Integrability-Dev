import Mathlib
import QuantumNLS.RB7FinalAll
import QuantumNLS.RB7Jet
import QuantumNLS.HierarchyInputR25m

/-!
# R-7B122087 shared-input bridge, part 1: the two smooth topologies coincide (RB7BindTopology)

`HierarchyInputR25m.HierarchyConclusion` (clauses (4), (5) of `thm:hierarchy`) is stated for the topology of
`Def033HierarchyR24m.Smooth L`, induced by the sup norms on `[0, L]` of every spatial derivative
(`Def033HierarchyR24m.smoothTopology`).  The frozen RB7 interface (`RB7FinalAll.OrbitCompactInput`,
`JointContInput`) is stated for `RB7.SmoothProf L`, induced by the product of all `H^k` embeddings (`RB7.jetOf`).

This module proves, for every `L > 0` and with no further input, that

* `smoothHomeo : Smooth L ≃ₜ SmoothProf L` is a homeomorphism (the identity on profiles);
  - `continuous_toSmooth` (`H^{k+1}` bounds the sup norm of the `k`-th derivative: `RB7.jet`, the F04 `eq:l1` embedding),
  - `continuous_toProf` (the `H^k` norm of a smooth difference is bounded by `L²` norms of the difference and of its
    `k`-th derivative, hence by sup norms on `[0, L]`: Parseval and `cof_iterated`);
* `jointSmooth_val`: the value of `Def033HierarchyR24m.jointSmooth` is `jointClassicalFlow`;
* `isClosed_range_jetOf`: the jets of smooth profiles form a closed subset of `∏_k H^k` (a limit of jets is a compatible
  family, hence the class of an `L²` function lying in all `H^s`, hence smooth by `RB7.smooth_of_memHs`);
* `isCompact_closure_of`: relative compactness in the ambient product (the frozen form of clause (4)) gives relative
  compactness of the same set in `SmoothProf L`.

No sorry, no new axiom, no new hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
noncomputable section

open scoped ComplexConjugate Topology NNReal ENNReal
open MeasureTheory Filter

namespace QuantumNLS.RB7BindTopology

open QuantumNLS.RB7 QuantumNLS.Sobolev QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m (Smooth smoothStep jointSmooth)

variable {L : ℝ} [Fact (0 < L)]

/-- A smooth profile as an element of `SmoothProf`. -/
def toProf (u : Smooth L) : SmoothProf L := ⟨u.val, u.property⟩

/-- An element of `SmoothProf` as a smooth profile. -/
def toSmooth (f : SmoothProf L) : Smooth L := ⟨f.val, f.smooth⟩

/-- The `H^k` class of a smooth periodic profile. -/
def jk {g : ℝ → ℂ} (hg : SmoothPeriodic L g) (k : ℕ) : H02 L (k : ℝ) :=
  WField.mk (smoothL2 hg) (memHs_of_smooth hg (k : ℝ))

theorem jetOf_eq {g : ℝ → ℂ} (hg : SmoothPeriodic L g) (k : ℕ) :
    (jetOf (L := L) g k) = jk hg k := by
  unfold jetOf jk
  exact dif_pos hg

/-! ## Direction 1: `SmoothProf → Smooth` is continuous -/

/-- The inclusion of `[0, L]` into the circle. -/
def evalCirc : C(Set.Icc (0 : ℝ) L, AddCircle L) :=
  ⟨fun x => ((x : ℝ) : AddCircle L), (AddCircle.continuous_mk' L).comp continuous_subtype_val⟩

theorem continuous_jet_toSmooth (a : ℕ) :
    Continuous fun f : SmoothProf L => Def033HierarchyR24m.jet L (toSmooth f) a := by
  have h0 : Continuous (fun f : SmoothProf L => (jetOf (L := L) f.val : ∀ k : ℕ, H02 L (k : ℝ))) :=
    continuous_induced_dom
  have h1 : Continuous fun f : SmoothProf L => (jetOf (L := L) f.val (a + 1) : H02 L (((a + 1 : ℕ)) : ℝ)) :=
    (continuous_apply (a + 1)).comp h0
  have hh : (a : ℝ) + 1 ≤ (((a + 1 : ℕ)) : ℝ) := by push_cast; exact le_rfl
  have h2 := (ContinuousMap.compRightContinuousMap ℂ (evalCirc (L := L))).continuous.comp
    ((RB7.jet (L := L) hh).continuous.comp h1)
  refine h2.congr (fun f => ?_)
  ext x
  dsimp only [Function.comp_apply]
  rw [jetOf_eq f.smooth]
  have := jet_smooth (L := L) hh f.smooth (memHs_of_smooth f.smooth (((a + 1 : ℕ)) : ℝ)) (x : ℝ)
  exact this

theorem continuous_toSmooth : Continuous (toSmooth (L := L)) :=
  continuous_induced_rng.2 (continuous_pi fun a => continuous_jet_toSmooth a)

/-! ## Direction 2: `Smooth → SmoothProf` is continuous -/

theorem bound_of_Icc {F : ℝ → ℂ} (hp : Function.Periodic F L) {A : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) L, ‖F x‖ ≤ A) (t : ℝ) : ‖F t‖ ≤ A := by
  obtain ⟨y, hy, hFy⟩ := hp.exists_mem_Ico₀ (Fact.out : 0 < L) t
  rw [hFy]
  exact h y ⟨hy.1, hy.2.le⟩

/-- `L²` bound for a continuous function on the circle. -/
theorem sq_norm_toLp_le (G : C(AddCircle L, ℂ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖G x‖ ≤ M) :
    ‖ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ G‖ ^ 2 ≤ L * M ^ 2 := by
  have hL : 0 < L := Fact.out
  have hG : ‖G‖ ≤ M := (ContinuousMap.norm_le _ hM0).2 hM
  have h1 := ContinuousMap.toLp_norm_le (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ)
    (volume : Measure (AddCircle L))
  have h2 := (ContinuousLinearMap.le_opNorm
    (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) (volume : Measure (AddCircle L)) ℂ) G)
  have hmeas : ((MeasureTheory.measureUnivNNReal (volume : Measure (AddCircle L)) : ℝ≥0) : ℝ) = L := by
    unfold MeasureTheory.measureUnivNNReal
    rw [AddCircle.measure_univ, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hL.le]
  have h1' : ‖(ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) (volume : Measure (AddCircle L)) ℂ :
      C(AddCircle L, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)))‖ ≤ L ^ ((2 : ℝ)⁻¹) := by
    have := h1
    have e : (((MeasureTheory.measureUnivNNReal (volume : Measure (AddCircle L)) ^
        (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0)) : ℝ) = L ^ ((2 : ℝ)⁻¹) := by
      rw [NNReal.coe_rpow, hmeas]
      simp
    rw [← e]
    exact_mod_cast this
  have hLp : L ^ ((2 : ℝ)⁻¹) ≥ 0 := Real.rpow_nonneg hL.le _
  have h3 : ‖ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ G‖ ≤ L ^ ((2 : ℝ)⁻¹) * M :=
    h2.trans (mul_le_mul h1' hG (norm_nonneg _) hLp)
  have h4 : (L ^ ((2 : ℝ)⁻¹)) ^ 2 = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  calc ‖ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ G‖ ^ 2
      ≤ (L ^ ((2 : ℝ)⁻¹) * M) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = L * M ^ 2 := by rw [mul_pow, h4]

/-- `L²` bound on the difference of two smooth periodic profiles from a sup bound on `[0, L]`. -/
theorem sq_norm_smoothL2_sub_le {F G : ℝ → ℂ} (hF : SmoothPeriodic L F) (hG : SmoothPeriodic L G) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ Set.Icc (0 : ℝ) L, ‖F x - G x‖ ≤ M) :
    ‖smoothL2 hF - smoothL2 hG‖ ^ 2 ≤ L * M ^ 2 := by
  have hsub : smoothL2 hF - smoothL2 hG = ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
      (liftC hF.smooth.continuous hF.periodic - liftC hG.smooth.continuous hG.periodic) := by
    rw [map_sub]; rfl
  rw [hsub]
  refine sq_norm_toLp_le _ hM0 (fun x => ?_)
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    have hp : Function.Periodic (fun s : ℝ => F s - G s) L := fun s => by
      simp only [hF.periodic s, hG.periodic s]
    have := bound_of_Icc (L := L) hp hM t
    simpa [liftC_coe] using this

/-- Parseval for the orthonormal coefficients. -/
theorem hasSum_sq_fourierL2 (u : L2T L) : HasSum (fun n : ℤ => ‖fourierL2 L u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) (fourierL2 L u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rwa [norm_fourierL2] at h

theorem norm_ikn_sq (n : ℤ) (a : ℕ) : ‖ikn L n ^ a‖ ^ 2 = freq L n ^ (2 * a) := by
  have hn : ‖ikn L n‖ = |freq L n| := by simp [ikn]
  rw [norm_pow, hn, ← pow_mul, mul_comm a 2, pow_mul, sq_abs, pow_mul]

theorem fourierL2_deriv_sub {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) (a : ℕ) (n : ℤ) :
    fourierL2 L (smoothL2 (smooth_iter hf a) - smoothL2 (smooth_iter hg a)) n =
      ikn L n ^ a * fourierL2 L (smoothL2 hf - smoothL2 hg) n := by
  simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, fourierL2_smoothL2]
  rw [cof_iterated hf a n, cof_iterated hg a n]
  ring

/-- Core `H^k` estimate in abstract form. -/
theorem sq_norm_core (d Dk : L2T L) (k : ℕ) {A B : ℝ}
    (hrel : ∀ n : ℤ, ‖fourierL2 L Dk n‖ ^ 2 = freq L n ^ (2 * k) * ‖fourierL2 L d n‖ ^ 2)
    (hnd : ‖d‖ ^ 2 ≤ L * A ^ 2) (hnk : ‖Dk‖ ^ 2 ≤ L * B ^ 2)
    (X : H02 L (k : ℝ)) (hX : X.val = d) :
    ‖X‖ ^ 2 ≤ 2 ^ (2 * k - 1) * (L * (A ^ 2 + B ^ 2)) := by
  have hS0 : HasSum (fun n : ℤ => ‖fourierL2 L d n‖ ^ 2) (‖d‖ ^ 2) := hasSum_sq_fourierL2 d
  have hSk : HasSum (fun n : ℤ => ‖fourierL2 L Dk n‖ ^ 2) (‖Dk‖ ^ 2) := hasSum_sq_fourierL2 Dk
  have hnorm : ‖X‖ ^ 2 = ∑' n : ℤ, sobolevWeight L (k : ℝ) n * ‖fourierL2 L d n‖ ^ 2 := by
    have := WField.norm_sq_eq_tsum L X
    rw [hX] at this
    exact this
  have hsumX : Summable fun n : ℤ => sobolevWeight L (k : ℝ) n * ‖fourierL2 L d n‖ ^ 2 := by
    have := WField.summable X
    rw [hX] at this
    exact this
  have hw : ∀ n : ℤ, sobolevWeight L (k : ℝ) n * ‖fourierL2 L d n‖ ^ 2 ≤
      2 ^ (2 * k - 1) * (‖fourierL2 L d n‖ ^ 2 + ‖fourierL2 L Dk n‖ ^ 2) := by
    intro n
    have hx : 1 ≤ 1 + |freq L n| := by linarith [abs_nonneg (freq L n)]
    have h1 : sobolevWeight L (k : ℝ) n ≤ (1 + |freq L n|) ^ (2 * k) := by
      unfold sobolevWeight
      have : (1 + |2 * Real.pi * (n : ℝ) / L|) = 1 + |freq L n| := rfl
      rw [this, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
    have h2 : (1 + |freq L n|) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (1 + freq L n ^ (2 * k)) := by
      have := add_pow_le (zero_le_one' ℝ) (abs_nonneg (freq L n)) (2 * k)
      have e : |freq L n| ^ (2 * k) = freq L n ^ (2 * k) := by
        rw [pow_mul, pow_mul, sq_abs]
      rw [e] at this
      simpa using this
    rw [hrel n]
    calc sobolevWeight L (k : ℝ) n * ‖fourierL2 L d n‖ ^ 2
        ≤ (2 ^ (2 * k - 1) * (1 + freq L n ^ (2 * k))) * ‖fourierL2 L d n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
      _ = 2 ^ (2 * k - 1) * (‖fourierL2 L d n‖ ^ 2 + freq L n ^ (2 * k) * ‖fourierL2 L d n‖ ^ 2) := by ring
  have hsumR : Summable fun n : ℤ => 2 ^ (2 * k - 1) * (‖fourierL2 L d n‖ ^ 2 + ‖fourierL2 L Dk n‖ ^ 2) :=
    (hS0.summable.add hSk.summable).mul_left _
  rw [hnorm]
  calc ∑' n : ℤ, sobolevWeight L (k : ℝ) n * ‖fourierL2 L d n‖ ^ 2
      ≤ ∑' n : ℤ, 2 ^ (2 * k - 1) * (‖fourierL2 L d n‖ ^ 2 + ‖fourierL2 L Dk n‖ ^ 2) :=
        Summable.tsum_le_tsum hw hsumX hsumR
    _ = 2 ^ (2 * k - 1) * (‖d‖ ^ 2 + ‖Dk‖ ^ 2) := by
        rw [tsum_mul_left, hS0.summable.tsum_add hSk.summable, hS0.tsum_eq, hSk.tsum_eq]
    _ ≤ 2 ^ (2 * k - 1) * (L * A ^ 2 + L * B ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hnd hnk) (by positivity)
    _ = 2 ^ (2 * k - 1) * (L * (A ^ 2 + B ^ 2)) := by ring

/-- **The `H^k` estimate**: the distance of two smooth profiles in `H^k` is controlled by sup norms on `[0, L]` of the
difference and of its `k`-th derivative. -/
theorem sq_norm_jet_sub_le {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) (k : ℕ)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ x ∈ Set.Icc (0 : ℝ) L, ‖f x - g x‖ ≤ A)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) L, ‖iteratedDeriv k f x - iteratedDeriv k g x‖ ≤ B) :
    ‖jk hf k - jk hg k‖ ^ 2 ≤
      2 ^ (2 * k - 1) * (L * (A ^ 2 + B ^ 2)) := by
  refine sq_norm_core (smoothL2 hf - smoothL2 hg)
    (smoothL2 (smooth_iter hf k) - smoothL2 (smooth_iter hg k)) k (fun n => ?_)
    (sq_norm_smoothL2_sub_le hf hg hA0 hA)
    (sq_norm_smoothL2_sub_le (smooth_iter hf k) (smooth_iter hg k) hB0 hB) _ rfl
  rw [fourierL2_deriv_sub hf hg k n, norm_mul, mul_pow, norm_ikn_sq]

theorem continuous_jetOf_toProf (k : ℕ) :
    Continuous fun u : Smooth L => (jetOf (L := L) u.val k : H02 L (k : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro u0
  have hj0 : Continuous (fun v : Smooth L => (fun a : ℕ => Def033HierarchyR24m.jet L v a)) :=
    continuous_induced_dom
  have hjc : ∀ a : ℕ, Continuous fun v : Smooth L => Def033HierarchyR24m.jet L v a := fun a =>
    (continuous_apply a).comp hj0
  have hA : Tendsto (fun v : Smooth L => ‖Def033HierarchyR24m.jet L v 0 - Def033HierarchyR24m.jet L u0 0‖)
      (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((hjc 0).tendsto u0)
  have hB : Tendsto (fun v : Smooth L => ‖Def033HierarchyR24m.jet L v k - Def033HierarchyR24m.jet L u0 k‖)
      (𝓝 u0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((hjc k).tendsto u0)
  have h1 := ((hA.pow 2).add (hB.pow 2)).const_mul (2 ^ (2 * k - 1) * L)
  have h2 : Tendsto (fun v : Smooth L => Real.sqrt ((2 ^ (2 * k - 1) * L) *
      (‖Def033HierarchyR24m.jet L v 0 - Def033HierarchyR24m.jet L u0 0‖ ^ 2 +
        ‖Def033HierarchyR24m.jet L v k - Def033HierarchyR24m.jet L u0 k‖ ^ 2))) (𝓝 u0)
      (𝓝 (Real.sqrt ((2 ^ (2 * k - 1) * L) * ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2)))) :=
    (Real.continuous_sqrt.tendsto _).comp h1
  rw [show (2 ^ (2 * k - 1) * L) * ((0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 0 by ring, Real.sqrt_zero] at h2
  show Tendsto (fun u : Smooth L => (jetOf (L := L) u.val k : H02 L (k : ℝ))) (𝓝 u0)
    (𝓝 (jetOf (L := L) u0.val k))
  apply tendsto_iff_dist_tendsto_zero.2
  refine squeeze_zero (fun _ => dist_nonneg) (fun v => ?_) h2
  show dist (jetOf (L := L) v.val k) (jetOf (L := L) u0.val k) ≤ _
  rw [dist_eq_norm, jetOf_eq v.property, jetOf_eq u0.property]
  have hmain := sq_norm_jet_sub_le v.property u0.property k (norm_nonneg _) (norm_nonneg _)
    (A := ‖Def033HierarchyR24m.jet L v 0 - Def033HierarchyR24m.jet L u0 0‖)
    (B := ‖Def033HierarchyR24m.jet L v k - Def033HierarchyR24m.jet L u0 k‖)
    (fun x hx => by
      have h := ContinuousMap.norm_coe_le_norm
        (Def033HierarchyR24m.jet L v 0 - Def033HierarchyR24m.jet L u0 0) ⟨x, hx⟩
      have e : (Def033HierarchyR24m.jet L v 0 - Def033HierarchyR24m.jet L u0 0) ⟨x, hx⟩ =
          v.val x - u0.val x := by
        show iteratedDeriv 0 v.val x - iteratedDeriv 0 u0.val x = _
        simp
      rw [e] at h
      exact h)
    (fun x hx => by
      have h := ContinuousMap.norm_coe_le_norm
        (Def033HierarchyR24m.jet L v k - Def033HierarchyR24m.jet L u0 k) ⟨x, hx⟩
      exact h)
  exact (le_abs_self _).trans (Real.abs_le_sqrt (hmain.trans_eq (by ring)))

theorem continuous_toProf : Continuous (toProf (L := L)) :=
  continuous_induced_rng.2 (continuous_pi fun k => continuous_jetOf_toProf k)

/-- **The two smooth topologies coincide**: the identity on smooth periodic profiles is a homeomorphism between the
sup-norm-of-all-derivatives topology (`Def033HierarchyR24m.Smooth`) and the `∏_k H^k` topology (`RB7.SmoothProf`). -/
def smoothHomeo : Smooth L ≃ₜ SmoothProf L where
  toFun := toProf
  invFun := toSmooth
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toProf
  continuous_invFun := continuous_toSmooth

theorem smoothHomeo_apply (u : Smooth L) : smoothHomeo u = ⟨u.val, u.property⟩ := rfl

theorem smoothHomeo_symm_apply (f : SmoothProf L) : smoothHomeo.symm f = ⟨f.val, f.smooth⟩ := rfl

/-! ## The value of the smooth joint flow -/

theorem foldr_val {κ : ℝ} {R : Finset ℕ} (F : HamFlows L κ R) (t : ℕ → ℝ) :
    ∀ (l : List ℕ), (∀ r ∈ l, r ∈ R) → ∀ u : Smooth L,
      (l.foldr (fun r v => smoothStep F r (t r) v) u).val =
        ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u.val := by
  intro l
  induction l with
  | nil => intro _ u; rfl
  | cons r l ih =>
    intro hl u
    have hr : r ∈ R := hl r (by simp)
    have hl' : ∀ r' ∈ l, r' ∈ R := fun r' hr' => hl r' (by simp [hr'])
    simp only [List.foldr_cons, List.map_cons, Function.comp_apply]
    unfold smoothStep
    rw [dif_pos hr]
    show F.Φ r (t r) ((l.foldr (fun r v => smoothStep F r (t r) v) u).val) = _
    rw [ih hl' u]

/-- The value of `jointSmooth` is `jointClassicalFlow`. -/
theorem jointSmooth_val {κ : ℝ} {R : Finset ℕ} (F : HamFlows L κ R) (t : ℕ → ℝ) (u : Smooth L) :
    (jointSmooth F t u).val = jointClassicalFlow F t u.val :=
  foldr_val F t (R.sort (· ≤ ·)) (fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr) u

/-! ## Closedness of the jets of smooth profiles in `∏_k H^k` -/

/-- The jet map of `SmoothProf`. -/
def J (f : SmoothProf L) : ∀ k : ℕ, H02 L (k : ℝ) := fun k => jetOf (L := L) f.val k

theorem isInducing_J : Topology.IsInducing (J (L := L)) := ⟨rfl⟩

theorem J_val (f : SmoothProf L) (k : ℕ) : (J f k).val = smoothL2 f.smooth := by
  show (jetOf (L := L) f.val k).val = _
  rw [jetOf_eq f.smooth]
  rfl

theorem continuous_val_apply (k : ℕ) :
    Continuous fun y : (∀ k : ℕ, H02 L (k : ℝ)) => (y k).val := by
  have h : Continuous fun y : (∀ k : ℕ, H02 L (k : ℝ)) => H02.toL2 (Nat.cast_nonneg k) (y k) :=
    (H02.toL2 (L := L) (Nat.cast_nonneg k)).continuous.comp (continuous_apply k)
  exact h

theorem isClosed_range_J : IsClosed (Set.range (J (L := L))) := by
  have hE : ∀ k : ℕ, IsClosed {y : (∀ k : ℕ, H02 L (k : ℝ)) | (y k).val = (y 0).val} := fun k =>
    isClosed_eq (continuous_val_apply k) (continuous_val_apply 0)
  have hsub : Set.range (J (L := L)) ⊆ ⋂ k : ℕ, {y : (∀ k : ℕ, H02 L (k : ℝ)) | (y k).val = (y 0).val} := by
    rintro _ ⟨f, rfl⟩
    refine Set.mem_iInter.2 (fun k => ?_)
    show (J f k).val = (J f 0).val
    rw [J_val, J_val]
  have hcl : IsClosed (⋂ k : ℕ, {y : (∀ k : ℕ, H02 L (k : ℝ)) | (y k).val = (y 0).val}) :=
    isClosed_iInter hE
  have hsup : ⋂ k : ℕ, {y : (∀ k : ℕ, H02 L (k : ℝ)) | (y k).val = (y 0).val} ⊆ Set.range (J (L := L)) := by
    intro y hy
    have hy' : ∀ k : ℕ, (y k).val = (y 0).val := fun k => Set.mem_iInter.1 hy k
    have hmem : ∀ s : ℝ, MemHsLp L s (y 0).val := by
      intro s
      obtain ⟨K, hK⟩ := exists_nat_ge s
      have hs := (y K).summable
      rw [hy' K] at hs
      unfold MemHsLp MemHs
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
      · exact mul_nonneg (sobolevWeight_pos L s n).le (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (sobolevWeight_mono L hK n) (sq_nonneg _)
    obtain ⟨f, hf, hfeq⟩ := smooth_of_memHs (y 0).val hmem
    refine ⟨⟨f, hf⟩, ?_⟩
    funext k
    apply WField.ext
    rw [J_val, hy' k]
    exact hfeq
  have : Set.range (J (L := L)) = ⋂ k : ℕ, {y : (∀ k : ℕ, H02 L (k : ℝ)) | (y k).val = (y 0).val} :=
    Set.Subset.antisymm hsub hsup
  rw [this]
  exact hcl

/-- **Relative compactness in the ambient product gives relative compactness in `SmoothProf`.** -/
theorem isCompact_closure_of {S : Set (SmoothProf L)}
    (h : IsCompact (closure (J '' S))) : IsCompact (closure S) := by
  have hsub : closure (J '' S) ⊆ Set.range (J (L := L)) :=
    closure_minimal (Set.image_subset_range J S) isClosed_range_J
  rw [isInducing_J.closure_eq_preimage_closure_image, isInducing_J.isCompact_iff,
    Set.image_preimage_eq_of_subset hsub]
  exact h

end QuantumNLS.RB7BindTopology

#print axioms QuantumNLS.RB7BindTopology.continuous_toSmooth
#print axioms QuantumNLS.RB7BindTopology.sq_norm_jet_sub_le
#print axioms QuantumNLS.RB7BindTopology.continuous_toProf
#print axioms QuantumNLS.RB7BindTopology.smoothHomeo
#print axioms QuantumNLS.RB7BindTopology.jointSmooth_val
#print axioms QuantumNLS.RB7BindTopology.isClosed_range_J
#print axioms QuantumNLS.RB7BindTopology.isCompact_closure_of
