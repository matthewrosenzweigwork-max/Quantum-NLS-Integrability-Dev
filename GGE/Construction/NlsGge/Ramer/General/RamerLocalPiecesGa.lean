import Mathlib
import NlsGge.Ramer.General.RamerLocalToolsG
import NlsGge.Ramer.General.RamerStep4LocalG
import NlsGge.Ramer.General.LinearSmallJacobiLocalG
import NlsGge.Ramer.RamerStep7
import NlsGge.Ramer.General.RamerStep8aG
import NlsGge.Ramer.General.FibreBridgeGa
import NlsGge.Ramer.General.FibreBridgeGb
import NlsGge.Ramer.General.PatchingPrereqsG
import NlsGge.Ramer.General.RamerStep5G

/-!
# R10-P3, part a: local pieces of the Ramer assembly over a `RamerSetting` (GE7a)

Adapted from the first half of `NlsGge/Ramer/RamerLocalPieces.lean`.  Dictionary:
`c, s, hs ↦ S`, `FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE c s hs ↦ S.incl`,
`headProj c n ↦ S.headProj n`, `tailProj c n ↦ S.tailProj n`, `TM c s hs ↦ S.TM`,
`fullWeightedSequenceGaussian c s ↦ S.γE`.

Anisotropy check (the `Step8Hyp` derivation): the old proof is a norm / triangle-inequality
argument about `incl h - incl (P_m h)`; the R5 tail bound enters only through `TailSmall`, which
is supplied by `Gen.exists_tail_small` (i.e. `S.tail_bound`).  No isotropy of `E` and no bound on
`‖incl‖` is used, so all constants (`1/8`, `1/2`, `2`, `ε₀/8`) are unchanged.

Contents: `TailSmall`, `LocalField`, `step8Hyp_tailField`, `localPieces_i`, and the generic
inverse lemmas (`gl_facts`, `sinv_local`, `isUnit_of_local`, `isUnit_G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

/-! ### Smoothness and derivative of `S⁻¹` (generic `E`, `H`) -/

namespace NlsGge.Ramer.Gen

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer

section GenericInverse

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- `gl_transfer` with the identity `Tt.symm (i h) = i (Q h)`, `Q = (I + A i)⁻¹`. -/
theorem gl_facts (i : H →L[ℝ] E) (A : E →L[ℝ] H) (hA : ‖A.comp i‖ ≤ 1 / 2) :
    ∃ (Tt : E ≃L[ℝ] E) (Q : H →L[ℝ] H), (∀ y, Tt y = y + i (A y)) ∧
      Q * (1 + A.comp i) = 1 ∧ (1 + A.comp i) * Q = 1 ∧ ∀ h, Tt.symm (i h) = i (Q h) := by
  have hU : IsUnit (1 + A.comp i) := isUnit_one_add_of_norm_le _ hA
  obtain ⟨Tt, B, h1, h2, h3, h4⟩ := gl_transfer i A hU
  have hQ1 : (↑hU.unit⁻¹ : H →L[ℝ] H) * (1 + A.comp i) = 1 := by
    have h := hU.unit.inv_mul
    rw [hU.unit_spec] at h; exact h
  have hQ2 : (1 + A.comp i) * (↑hU.unit⁻¹ : H →L[ℝ] H) = 1 := by
    have h := hU.unit.mul_inv
    rw [hU.unit_spec] at h; exact h
  refine ⟨Tt, ↑hU.unit⁻¹, h1, hQ1, hQ2, fun h => ?_⟩
  have hQ' : ∀ h, (↑hU.unit⁻¹ : H →L[ℝ] H) h + (↑hU.unit⁻¹ : H →L[ℝ] H) (A (i h)) = h := fun h => by
    have := congrArg (fun F : H →L[ℝ] H => F h) hQ1
    exact (map_add (↑hU.unit⁻¹ : H →L[ℝ] H) h (A (i h))).symm.trans this
  have e : (↑hU.unit⁻¹ : H →L[ℝ] H) h = h - (↑hU.unit⁻¹ : H →L[ℝ] H) (A (i h)) :=
    eq_sub_of_add_eq (hQ' h)
  rw [h2, h4, map_neg, e, map_sub]
  abel

theorem sinv_local (i : H →L[ℝ] E) (L : E → H) (ε₀ : ℝ) (hL : ContDiff ℝ 2 L)
    (hy : Step7Hyp i L ε₀) {z : E} (hz : z ∈ ball (0 : E) (ε₀ / 2)) :
    ContDiffAt ℝ 2 (Sinv i L ε₀) z ∧
    ∃ D : E →L[ℝ] E, HasFDerivAt (Sinv i L ε₀) D z ∧
      ∃ Q : H →L[ℝ] H,
        Q * (1 + (fderiv ℝ L (Sinv i L ε₀ z)).comp i) = 1 ∧
        (1 + (fderiv ℝ L (Sinv i L ε₀ z)).comp i) * Q = 1 ∧
        ∀ h, D (i h) = i (Q h) := by
  have hx := Sinv_spec hy hz
  set x := Sinv i L ε₀ z with hxdef
  have hLd : Differentiable ℝ L := hL.differentiable (by norm_num)
  obtain ⟨Tt, Q, h1, hQ1, hQ2, hTQ⟩ := gl_facts i (fderiv ℝ L x) (hy.contr x hx.1)
  set f : E → E := fun y => y + i (L y) with hf
  have hfc : ContDiff ℝ 2 f := contDiff_id.add (i.contDiff.comp hL)
  have hfd : HasFDerivAt f (Tt : E →L[ℝ] E) x := by
    have := (hasFDerivAt_id x).add (i.hasFDerivAt.comp x (hLd x).hasFDerivAt)
    have e : (Tt : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + i.comp (fderiv ℝ L x) := by
      ext y; simp [h1]
    rw [e]; exact this
  have hSc : ContinuousAt (Sinv i L ε₀) z :=
    (continuousOn_Sinv hy).continuousAt (isOpen_ball.mem_nhds hz)
  have hfg : ∀ᶠ y in 𝓝 z, f (Sinv i L ε₀ y) = y := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy'
    exact (Sinv_spec hy hy').2
  refine ⟨?_, (Tt.symm : E →L[ℝ] E), HasFDerivAt.of_local_left_inverse hSc hfd hfg, Q, hQ1, hQ2,
    hTQ⟩
  have hfca : ContDiffAt ℝ 2 f x := hfc.contDiffAt
  have hg := (hfca.to_localInverse hfd (by norm_num))
  have hzf : f x = z := hx.2
  rw [hzf] at hg
  have hev : ∀ᶠ y in 𝓝 x, (hfca.localInverse hfd (by norm_num)) (f y) = y :=
    (hfca.hasStrictFDerivAt' hfd (by norm_num)).eventually_left_inverse
  have hev' := hSc.eventually hev
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [hev', hfg] with y h1' h2'
  rw [h2'] at h1'
  exact h1'.symm

/-- The unit property of `I + D G(z) ∘ i` for `G = R ∘ K ∘ S⁻¹`. -/
theorem isUnit_of_local (i : H →L[ℝ] E) (R : H →L[ℝ] H) (DK : E →L[ℝ] H) (D : E →L[ℝ] E)
    (Q : H →L[ℝ] H) (hA : ‖DK.comp i‖ ≤ 1 / 2)
    (hQ1 : Q * (1 + (DK.comp i - R.comp (DK.comp i))) = 1)
    (hQ2 : (1 + (DK.comp i - R.comp (DK.comp i))) * Q = 1) (hD : ∀ h, D (i h) = i (Q h)) :
    IsUnit (1 + ((R.comp (DK.comp D)).comp i)) := by
  have hQ : (R.comp (DK.comp D)).comp i = R.comp (DK.comp i) * Q := by
    ext h
    simp [hD]
  have hU : IsUnit (1 + DK.comp i) := isUnit_one_add_of_norm_le _ hA
  have hQu : IsUnit Q := isUnit_iff_exists.2 ⟨_, hQ1, hQ2⟩
  have hprod : 1 + R.comp (DK.comp i) * Q = (1 + DK.comp i) * Q := by
    have : (1 + DK.comp i) * Q = (1 + (DK.comp i - R.comp (DK.comp i))) * Q +
        R.comp (DK.comp i) * Q := by
      rw [← add_mul]; congr 1; abel
    rw [this, hQ2]
  rw [hQ, hprod]
  exact hU.mul hQu

theorem fderiv_apply_eq_of_hasFDerivAt {F : E → H} {f' : E →L[ℝ] H} {z : E}
    (h : HasFDerivAt F f' z) (v : E) : fderiv ℝ F z v = f' v := by rw [h.fderiv]

theorem isUnit_G (i : H →L[ℝ] E) (R : H →L[ℝ] H) (K L : E → H)
    (hL : ∀ y, L y = K y - R (K y)) (x : E) (hKx : DifferentiableAt ℝ K x)
    (D : E →L[ℝ] E) (Q : H →L[ℝ] H) (hA : ∀ h, ‖fderiv ℝ K x (i h)‖ ≤ 1 / 2 * ‖h‖)
    (hQ1 : Q * (1 + (fderiv ℝ L x).comp i) = 1) (hQ2 : (1 + (fderiv ℝ L x).comp i) * Q = 1)
    (hDQ : ∀ h, D (i h) = i (Q h)) :
    IsUnit (1 + ((R.comp ((fderiv ℝ K x).comp D)).comp i)) := by
  have hLe : L = fun y => K y - R (K y) := funext hL
  have hfL : fderiv ℝ L x = fderiv ℝ K x - R.comp (fderiv ℝ K x) := by
    rw [hLe]
    exact (hKx.hasFDerivAt.sub (R.hasFDerivAt.comp x hKx.hasFDerivAt)).fderiv
  have hN : (fderiv ℝ L x).comp i = (fderiv ℝ K x).comp i - R.comp ((fderiv ℝ K x).comp i) := by
    rw [hfL]; ext w; rfl
  rw [hN] at hQ1 hQ2
  refine isUnit_of_local i R (fderiv ℝ K x) D Q ?_ hQ1 hQ2 hDQ
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hA

end GenericInverse

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- `P_{n'} P_k = P_{min}`, in the form needed for `stepP`.
(Old: `headProj_headProj_of_ge`.) -/
theorem headProj_headProj_of_ge {k n : ℕ} (hkn : n ≤ k) (w : S.H) :
    S.headProj n (S.headProj k w) = S.headProj n w := by
  apply S.hcoord_ext
  intro m
  rw [S.hcoord_headProj, S.hcoord_headProj, S.hcoord_headProj]
  split_ifs with h1 h2 <;>
    first | rfl | exact absurd (symmetricModes_mono hkn h1) h2

/-- (Old: `headProj_tailProj_self`.) -/
theorem headProj_tailProj_self (n : ℕ) (w : S.H) : S.headProj n (S.tailProj n w) = 0 :=
  S.headProj_tailProj_of_le le_rfl w

/-- The tail field `(I - P_n) K`. (Old: `tailField`.) -/
def tailField (n : ℕ) (K : S.E → S.H) : S.E → S.H := fun y => K y - S.headProj n (K y)

/-- The R5 tail smallness needed (`D = 2 d`, threshold `ε₀/8`). (Old: `TailSmall`.) -/
def TailSmall (d ε₀ : ℝ) (n : ℕ) : Prop :=
  ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 2 * d →
    ‖S.incl h - S.incl (S.headProj m h)‖ < ε₀ / 8

/-- (Old: `exists_tailSmall`.) -/
theorem exists_tailSmall (d ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, S.TailSmall d ε₀ n := by
  obtain ⟨n₀, hn₀⟩ := Gen.exists_tail_small S (2 * d) (ε₀ / 4) (by linarith)
  refine ⟨n₀, fun n hn m hm h hh => ?_⟩
  have := hn₀ m (hn.trans hm) h hh
  linarith

/-- Hypotheses on the local field `K` (Step 4 output): `C²`, bounded by `d` and with
`‖DK(y) ∘ i‖ ≤ 1/8` on `‖y‖ < ε`. (Old: `LocalField`.) -/
structure LocalField (K : S.E → S.H) (ε d : ℝ) : Prop where
  smooth : ContDiff ℝ 2 K
  bound : ∀ y : S.E, ‖y‖ < ε → ‖K y‖ < d
  contr : ∀ y : S.E, ‖y‖ < ε → ∀ h : S.H,
    ‖fderiv ℝ K y (S.incl h)‖ ≤ 1 / 8 * ‖h‖

variable {S} {K : S.E → S.H} {ε d ε₀ : ℝ}

theorem LocalField.diff (hK : S.LocalField K ε d) (y : S.E) :
    DifferentiableAt ℝ K y :=
  (hK.smooth.differentiable (by norm_num)) y

/-- `Step7Hyp` for `W ∘ K`, `W` a bounded (by 2) endomorphism of `H` with the smallness property.
(Old: `step7Hyp_comp`.) -/
theorem step7Hyp_comp (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε)
    (W : S.H →L[ℝ] S.H) (hW : ∀ w, ‖W w‖ ≤ 2 * ‖w‖)
    (hsm : ∀ y : S.E, ‖y‖ ≤ ε₀ → ‖S.incl (W (K y))‖ < ε₀ / 2) :
    Step7Hyp S.incl (fun y => W (K y)) ε₀ := by
  have hm : ∀ y : S.E, y ∈ closedBall (0 : S.E) ε₀ → ‖y‖ < ε := fun y hy => by
    rw [mem_closedBall, dist_zero_right] at hy; linarith
  refine ⟨hε₀, fun y hy => W.differentiableAt.comp y (hK.diff y), fun y hy => ?_,
    fun y hy => ?_⟩
  · exact hsm y (by rwa [mem_closedBall, dist_zero_right] at hy)
  · have hd : fderiv ℝ (fun y => W (K y)) y = W.comp (fderiv ℝ K y) :=
      (W.hasFDerivAt.comp y (hK.diff y).hasFDerivAt).fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => W (K y)) y (S.incl h)‖ ≤ _
    rw [hd]
    calc _ ≤ 2 * ‖fderiv ℝ K y (S.incl h)‖ := hW _
      _ ≤ 2 * (1 / 8 * ‖h‖) := by
        gcongr; exact hK.contr y (hm y hy) h
      _ ≤ 1 / 2 * ‖h‖ := by nlinarith [norm_nonneg h]

/-- Uniform smallness for the truncations of the tail field. (Old: `small_tailField`.) -/
theorem small_tailField (hK : S.LocalField K ε d) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) {y : S.E} (hy : ‖y‖ ≤ ε₀) :
    ‖S.incl (S.tailProj n (K y))‖ < ε₀ / 4 ∧
      ∀ k : ℕ, ‖S.incl (S.headProj k (S.tailProj n (K y)))‖ < ε₀ / 4 := by
  have hKy : ‖K y‖ < d := hK.bound y (lt_of_le_of_lt hy hlt)
  refine S.small_of_tail (ε₀ / 2) (2 * d) n ?_ (S.tailProj n (K y))
    (S.headProj_tailProj_self n _) ?_ |> fun h => ⟨by linarith [h.1], fun k => by linarith [h.2 k]⟩
  · intro m hm h hh
    have := hn m hm h hh
    linarith
  · calc _ ≤ 2 * ‖K y‖ := S.norm_tailProj_le n _
      _ < 2 * d := by linarith

/-- `Step8Hyp` for `(I - P_n) K`. (Old: `step8Hyp_tailField`.) -/
theorem step8Hyp_tailField (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) : S.Step8Hyp (S.tailField n K) ε₀ := by
  refine ⟨hK.smooth.sub ((S.headProj n).contDiff.comp hK.smooth), ?_, fun n' => ?_⟩
  · exact S.step7Hyp_comp hK hε₀ hlt (S.tailProj n) (fun w => S.norm_tailProj_le n w)
      (fun y hy => lt_of_lt_of_le (S.small_tailField hK hlt n hn hy).1 (by linarith))
  · exact S.step7Hyp_comp hK hε₀ hlt ((S.headProj n').comp (S.tailProj n))
      (fun w => (S.norm_headProj_le n' _).trans (S.norm_tailProj_le n w))
      (fun y hy => lt_of_lt_of_le ((S.small_tailField hK hlt n hn hy).2 n') (by linarith))

/-- `Step8Hyp` for `P_k (I - P_n) K`. (Old: `step8Hyp_projTailField`.) -/
theorem step8Hyp_projTailField (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε)
    (n k : ℕ) (hn : S.TailSmall d ε₀ n) :
    S.Step8Hyp (S.projField k (S.tailField n K)) ε₀ := by
  refine ⟨S.contDiff_projField k _ (hK.smooth.sub ((S.headProj n).contDiff.comp hK.smooth)), ?_,
    fun n' => ?_⟩
  · exact S.step7Hyp_comp hK hε₀ hlt ((S.headProj k).comp (S.tailProj n))
      (fun w => (S.norm_headProj_le k _).trans (S.norm_tailProj_le n w))
      (fun y hy => lt_of_lt_of_le ((S.small_tailField hK hlt n hn hy).2 k) (by linarith))
  · have key : ∀ w : S.H, S.headProj n' (S.headProj k (S.tailProj n w)) =
        S.headProj (min n' k) (S.tailProj n w) := by
      intro w
      rcases le_total n' k with h | h
      · rw [min_eq_left h]; exact S.headProj_headProj_of_ge h _
      · rw [min_eq_right h]; exact S.headProj_headProj_of_le h _
    refine S.step7Hyp_comp hK hε₀ hlt (((S.headProj n').comp (S.headProj k)).comp (S.tailProj n))
      (fun w => ((S.norm_headProj_le n' _).trans ((S.norm_headProj_le k _))).trans
        (S.norm_tailProj_le n w))
      (fun y hy => ?_)
    show ‖S.incl (S.headProj n' (S.headProj k (S.tailProj n (K y))))‖ < ε₀ / 2
    rw [key]
    exact lt_of_lt_of_le ((S.small_tailField hK hlt n hn hy).2 _) (by linarith)

variable (S) in
/-- Null-set preservation of `TM M` on `U` (class N hypotheses `hT`/`hTk` of R9c').
(Old: `NullPresOn`.) -/
def NullPresOn (M : S.E → S.H) (U : Set S.E) : Prop :=
  ∀ N : Set S.E, S.γE N = 0 → S.γE (U ∩ S.TM M ⁻¹' N) = 0

/-- **(i)** The tail field `L = (I - P_n) K` is in class N2: `Step8Hyp`, `Step8Concl`, null
preservation on `U_S` and, together with every `P_k L`, on every `U ⊆ ball 0 (ε₀/4)`.
(Old: `localPieces_i`.) -/
theorem localPieces_i (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) :
    S.Step8Hyp (S.tailField n K) ε₀ ∧ S.Step8Concl (S.tailField n K) ε₀ ∧
    (∀ U : Set S.E,
      U ⊆ closedBall (0 : S.E) ε₀ ∩
        S.TM (S.tailField n K) ⁻¹' ball (0 : S.E) (ε₀ / 2) →
      S.NullPresOn (S.tailField n K) U) ∧
    (∀ U : Set S.E, U ⊆ ball (0 : S.E) (ε₀ / 4) →
      S.NullPresOn (S.tailField n K) U ∧
      ∀ k : ℕ, S.NullPresOn (S.projField k (S.tailField n K)) U) := by
  have h0 := S.step8Hyp_tailField hK hε₀ hlt n hn
  have hc0 := S.step8Concl_of_hyp _ h0
  refine ⟨h0, hc0, fun U hU => ?_, fun U hU => ?_⟩
  · exact S.nullPres_of_concl _ hc0 U (fun x hx => (hU hx).1) (fun x hx => (hU hx).2)
  have hUb : U ⊆ closedBall (0 : S.E) ε₀ := fun x hx => by
    have := hU hx
    rw [mem_ball, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]; linarith
  have hUZ : ∀ (M : S.E → S.H), (∀ y : S.E,
      ‖y‖ ≤ ε₀ → ‖S.incl (M y)‖ < ε₀ / 4) → ∀ x ∈ U,
      x + S.incl (M x) ∈ ball (0 : S.E) (ε₀ / 2) := by
    intro M hM x hx
    have h1 := hU hx
    rw [mem_ball, dist_zero_right] at h1
    have h2 := hM x (by linarith)
    rw [mem_ball, dist_zero_right]
    calc _ ≤ ‖x‖ + ‖S.incl (M x)‖ := norm_add_le _ _
      _ < ε₀ / 2 := by linarith
  refine ⟨S.nullPres_of_concl _ hc0 U hUb
    (hUZ _ (fun y hy => (S.small_tailField hK hlt n hn hy).1)), fun k => ?_⟩
  exact S.nullPres_of_concl _ (S.step8Concl_of_hyp _
    (S.step8Hyp_projTailField hK hε₀ hlt n k hn)) U hUb
    (hUZ _ (fun y hy => (S.small_tailField hK hlt n hn hy).2 k))

end NlsGge.Ramer.General.RamerSetting
