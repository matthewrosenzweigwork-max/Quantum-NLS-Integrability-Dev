import NlsGge.Ramer.RamerLocalTools
import NlsGge.Ramer.RamerStep4Local
import NlsGge.Ramer.LinearSmallJacobiLocal
import NlsGge.Ramer.RamerStep7
import NlsGge.Ramer.RamerStep8a
import NlsGge.Ramer.FibreBridge
import NlsGge.Ramer.PatchingPrereqs

/-!
# R10-P3: local pieces of the Ramer assembly (setting of Step 8 for the tail field of `K2`)

Setting: `K : E_s → H` is `C²` with the Step-4 bounds on `‖y‖ < ε`; `L := (I - P_n) K`.
Part (i): `Step8Hyp`/`Step8Concl` for `L` and every `P_k L`, class N2 on `ball 0 (ε₀/4)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- `P_{n'} P_k = P_{min}`, in the form needed for `stepP`. -/
theorem headProj_headProj_of_ge {k n : ℕ} (hkn : n ≤ k) (w : ActualCM c) :
    headProj c n (headProj c k w) = headProj c n w := by
  apply cmCoord_ext
  intro m
  simp only [headProj_apply, cmCoord_cmTrunc]
  split_ifs with h1 h2 <;>
    first | rfl | exact absurd (symmetricModes_mono hkn h1) h2

theorem headProj_tailProj_self (n : ℕ) (w : ActualCM c) : headProj c n (tailProj c n w) = 0 := by
  rw [tailProj_apply, map_sub, headProj_idem, sub_self]

/-- The tail field `(I - P_n) K`. -/
def tailField (n : ℕ) (K : FullWeightedHilbert c s → ActualCM c) :
    FullWeightedHilbert c s → ActualCM c := fun y => K y - headProj c n (K y)

/-- The R5 tail smallness needed (`D = 2 d`, threshold `ε₀/8`). -/
def TailSmall (hs : (1 : ℝ) / 2 < s) (d ε₀ : ℝ) (n : ℕ) : Prop :=
  ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 2 * d →
    ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
      cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
        ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < ε₀ / 8

theorem exists_tailSmall (hs : (1 : ℝ) / 2 < s) (d ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, TailSmall c s hs d ε₀ n := by
  obtain ⟨n₀, hn₀⟩ := exists_tail_small c s (by linarith : 0 < s) (2 * d) (ε₀ / 4) (by linarith)
  refine ⟨n₀, fun n hn m hm h hh => ?_⟩
  have := hn₀ m (hn.trans hm) h hh
  linarith

section Setting

variable {c s}

/-- Hypotheses on the local field `K` (Step 4 output): `C²`, bounded by `d` and with
`‖DK(y) ∘ i‖ ≤ 1/8` on `‖y‖ < ε`. -/
structure LocalField (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (ε d : ℝ) : Prop where
  smooth : ContDiff ℝ 2 K
  bound : ∀ y : FullWeightedHilbert c s, ‖y‖ < ε → ‖K y‖ < d
  contr : ∀ y : FullWeightedHilbert c s, ‖y‖ < ε → ∀ h : ActualCM c,
    ‖fderiv ℝ K y (inclE c s hs h)‖ ≤ 1 / 8 * ‖h‖

variable {hs : (1 : ℝ) / 2 < s} {K : FullWeightedHilbert c s → ActualCM c} {ε d ε₀ : ℝ}

theorem LocalField.diff (hK : LocalField hs K ε d) (y : FullWeightedHilbert c s) :
    DifferentiableAt ℝ K y :=
  (hK.smooth.differentiable (by norm_num)) y

/-- `Step7Hyp` for `W ∘ K`, `W` a bounded (by 2) endomorphism of `H` with the smallness property. -/
theorem step7Hyp_comp (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε)
    (W : ActualCM c →L[ℝ] ActualCM c) (hW : ∀ w, ‖W w‖ ≤ 2 * ‖w‖)
    (hsm : ∀ y : FullWeightedHilbert c s, ‖y‖ ≤ ε₀ → ‖inclE c s hs (W (K y))‖ < ε₀ / 2) :
    Step7Hyp (inclE c s hs) (fun y => W (K y)) ε₀ := by
  have hm : ∀ y : FullWeightedHilbert c s, y ∈ closedBall (0 : FullWeightedHilbert c s) ε₀ →
      ‖y‖ < ε := fun y hy => by
    rw [mem_closedBall, dist_zero_right] at hy; linarith
  refine ⟨hε₀, fun y hy => W.differentiableAt.comp y (hK.diff y), fun y hy => ?_,
    fun y hy => ?_⟩
  · exact hsm y (by rwa [mem_closedBall, dist_zero_right] at hy)
  · have hd : fderiv ℝ (fun y => W (K y)) y = W.comp (fderiv ℝ K y) :=
      (W.hasFDerivAt.comp y (hK.diff y).hasFDerivAt).fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => W (K y)) y (inclE c s hs h)‖ ≤ _
    rw [hd]
    calc _ ≤ 2 * ‖fderiv ℝ K y (inclE c s hs h)‖ := hW _
      _ ≤ 2 * (1 / 8 * ‖h‖) := by
        gcongr; exact hK.contr y (hm y hy) h
      _ ≤ 1 / 2 * ‖h‖ := by nlinarith [norm_nonneg h]

theorem norm_tailProj_comp_le (n : ℕ) (w : ActualCM c) : ‖tailProj c n w‖ ≤ 2 * ‖w‖ :=
  norm_tailProj_le c n w

/-- Uniform smallness for the truncations of the tail field. -/
theorem small_tailField (hK : LocalField hs K ε d) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) {y : FullWeightedHilbert c s} (hy : ‖y‖ ≤ ε₀) :
    ‖inclE c s hs (tailProj c n (K y))‖ < ε₀ / 4 ∧
      ∀ k : ℕ, ‖inclE c s hs (headProj c k (tailProj c n (K y)))‖ < ε₀ / 4 := by
  have hKy : ‖K y‖ < d := hK.bound y (lt_of_le_of_lt hy hlt)
  refine small_of_tail c s hs (ε₀ / 2) (2 * d) n ?_ (tailProj c n (K y))
    (headProj_tailProj_self c n _) ?_ |> fun h => ⟨by linarith [h.1], fun k => by linarith [h.2 k]⟩
  · intro m hm h hh
    have := hn m hm h hh
    linarith
  · calc _ ≤ 2 * ‖K y‖ := norm_tailProj_le c n _
      _ < 2 * d := by linarith

/-- `Step8Hyp` for `(P_k) (I - P_n) K` (`k = none` : no projection) -/
theorem step8Hyp_tailField (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) : Step8Hyp c s hs (tailField c s n K) ε₀ := by
  have hW : ∀ (a b : ℕ) (w : ActualCM c),
      ‖headProj c a (headProj c b (tailProj c n w))‖ ≤ 2 * ‖w‖ := fun a b w =>
    ((norm_headProj_le c a _).trans (norm_headProj_le c b _)).trans (norm_tailProj_le c n w)
  refine ⟨hK.smooth.sub ((headProj c n).contDiff.comp hK.smooth), ?_, fun n' => ?_⟩
  · exact step7Hyp_comp hK hε₀ hlt (tailProj c n) (fun w => norm_tailProj_le c n w)
      (fun y hy => lt_of_lt_of_le (small_tailField hK hlt n hn hy).1 (by linarith))
  · exact step7Hyp_comp hK hε₀ hlt ((headProj c n').comp (tailProj c n))
      (fun w => (norm_headProj_le c n' _).trans (norm_tailProj_le c n w))
      (fun y hy => lt_of_lt_of_le ((small_tailField hK hlt n hn hy).2 n') (by linarith))

theorem step8Hyp_projTailField (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n k : ℕ)
    (hn : TailSmall c s hs d ε₀ n) :
    Step8Hyp c s hs (projField k (tailField c s n K)) ε₀ := by
  refine ⟨contDiff_projField k _ (hK.smooth.sub ((headProj c n).contDiff.comp hK.smooth)), ?_,
    fun n' => ?_⟩
  · exact step7Hyp_comp hK hε₀ hlt ((headProj c k).comp (tailProj c n))
      (fun w => (norm_headProj_le c k _).trans (norm_tailProj_le c n w))
      (fun y hy => lt_of_lt_of_le ((small_tailField hK hlt n hn hy).2 k) (by linarith))
  · have key : ∀ w : ActualCM c, headProj c n' (headProj c k (tailProj c n w)) =
        headProj c (min n' k) (tailProj c n w) := by
      intro w
      rcases le_total n' k with h | h
      · rw [min_eq_left h]; exact headProj_headProj_of_ge c h _
      · rw [min_eq_right h]; exact headProj_headProj_of_le c h _
    refine step7Hyp_comp hK hε₀ hlt (((headProj c n').comp (headProj c k)).comp (tailProj c n))
      (fun w => ((norm_headProj_le c n' _).trans ((norm_headProj_le c k _))).trans
        (norm_tailProj_le c n w))
      (fun y hy => ?_)
    show ‖inclE c s hs (headProj c n' (headProj c k (tailProj c n (K y))))‖ < ε₀ / 2
    rw [key]
    exact lt_of_lt_of_le ((small_tailField hK hlt n hn hy).2 _) (by linarith)

variable (c s) in
/-- Null-set preservation of `TM M` on `U` (class N hypotheses `hT`/`hTk` of R9c'). -/
def NullPresOn (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (U : Set (FullWeightedHilbert c s)) : Prop :=
  ∀ N : Set (FullWeightedHilbert c s), NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
    NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs M ⁻¹' N) = 0

/-- **(i)** The tail field `L = (I - P_n) K` is in class N2: `Step8Hyp`, `Step8Concl`, null
preservation on `U_S` and, together with every `P_k L`, on every `U ⊆ ball 0 (ε₀/4)`. -/
theorem localPieces_i (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) :
    Step8Hyp c s hs (tailField c s n K) ε₀ ∧ Step8Concl c s hs (tailField c s n K) ε₀ ∧
    (∀ U : Set (FullWeightedHilbert c s),
      U ⊆ closedBall (0 : FullWeightedHilbert c s) ε₀ ∩
        TM c s hs (tailField c s n K) ⁻¹' ball (0 : FullWeightedHilbert c s) (ε₀ / 2) →
      NullPresOn c s hs (tailField c s n K) U) ∧
    (∀ U : Set (FullWeightedHilbert c s), U ⊆ ball (0 : FullWeightedHilbert c s) (ε₀ / 4) →
      NullPresOn c s hs (tailField c s n K) U ∧
      ∀ k : ℕ, NullPresOn c s hs (projField k (tailField c s n K)) U) := by
  have h0 := step8Hyp_tailField hK hε₀ hlt n hn
  have hc0 := step8Concl_of_hyp c s hs _ h0
  refine ⟨h0, hc0, fun U hU => ?_, fun U hU => ?_⟩
  · exact nullPres_of_concl c s hs _ hc0 U (fun x hx => (hU hx).1) (fun x hx => (hU hx).2)
  have hUb : U ⊆ closedBall (0 : FullWeightedHilbert c s) ε₀ := fun x hx => by
    have := hU hx
    rw [mem_ball, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]; linarith
  have hUZ : ∀ (M : FullWeightedHilbert c s → ActualCM c), (∀ y : FullWeightedHilbert c s,
      ‖y‖ ≤ ε₀ → ‖inclE c s hs (M y)‖ < ε₀ / 4) → ∀ x ∈ U,
      x + inclE c s hs (M x) ∈ ball (0 : FullWeightedHilbert c s) (ε₀ / 2) := by
    intro M hM x hx
    have h1 := hU hx
    rw [mem_ball, dist_zero_right] at h1
    have h2 := hM x (by linarith)
    rw [mem_ball, dist_zero_right]
    calc _ ≤ ‖x‖ + ‖inclE c s hs (M x)‖ := norm_add_le _ _
      _ < ε₀ / 2 := by linarith
  refine ⟨nullPres_of_concl c s hs _ hc0 U hUb
    (hUZ _ (fun y hy => (small_tailField hK hlt n hn hy).1)), fun k => ?_⟩
  exact nullPres_of_concl c s hs _ (step8Concl_of_hyp c s hs _
    (step8Hyp_projTailField hK hε₀ hlt n k hn)) U hUb
    (hUZ _ (fun y hy => (small_tailField hK hlt n hn hy).2 k))

end Setting

/-! ### Smoothness and derivative of `S⁻¹` (generic `E`, `H`) -/

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

/-! ### The head-valued field `G_Π` -/

section GPi

variable {c s}
variable {hs : (1 : ℝ) / 2 < s} {K : FullWeightedHilbert c s → ActualCM c} {ε d ε₀ : ℝ}

/-- `Π' = PiMap` for the tail field of `K` (radius `ε₀`). -/
abbrev PiOf (hs : (1 : ℝ) / 2 < s) (n : ℕ) (K : FullWeightedHilbert c s → ActualCM c) (ε₀ : ℝ) :
    FullWeightedHilbert c s → FullWeightedHilbert c s :=
  PiMap (inclE c s hs) (tailField c s n K) K ε₀

/-- **`G_Π`**: a globally `C²`, `V_n`-valued field with `I + i G_Π = Π'` on `ball 0 r`, and
`I + D_H G_Π(z)` invertible there. -/
theorem exists_headField (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) {r : ℝ} (hr : 0 < r) (hr4 : 4 * r < ε₀) :
    ∃ G : FullWeightedHilbert c s → ActualCM c, ContDiff ℝ 2 G ∧
      (∀ z, headProj c n (G z) = G z) ∧
      (∀ z ∈ ball (0 : FullWeightedHilbert c s) r, TM c s hs G z = PiOf hs n K ε₀ z) ∧
      (∀ z ∈ ball (0 : FullWeightedHilbert c s) r,
        IsUnit (1 + (hsDerivH c s hs G z).toCLM)) := by
  have h8 := step8Hyp_tailField hK hε₀ hlt n hn
  have hy := h8.step
  set Sv := Sinv (inclE c s hs) (tailField c s n K) ε₀ with hSv
  obtain ⟨ρ, hρd, -, -, hρin, hρout, -⟩ := exists_bump_generic (0 : FullWeightedHilbert c s) hr
  set G : FullWeightedHilbert c s → ActualCM c := fun z => ρ z • headProj c n (K (Sv z)) with hG
  have hr2 : ∀ z : FullWeightedHilbert c s, z ∈ ball (0 : FullWeightedHilbert c s) r →
      z ∈ ball (0 : FullWeightedHilbert c s) (ε₀ / 2) := fun z hz =>
    ball_subset_ball (by linarith) hz
  have hGsmooth : ContDiff ℝ 2 G := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ ball (0 : FullWeightedHilbert c s) (ε₀ / 2)
    · have hS := (sinv_local (inclE c s hs) (tailField c s n K) ε₀ h8.smooth hy hz).1
      exact hρd.contDiffAt.smul ((headProj c n).contDiff.contDiffAt.comp z
        (hK.smooth.contDiffAt.comp z hS))
    · have hz' : 2 * r < ‖z‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hz; linarith
      have hev : ∀ᶠ y in 𝓝 z, 2 * r < ‖y‖ :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hz'
      refine (contDiffAt_const (c := (0 : ActualCM c))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy'
      have : y ∉ ball (0 : FullWeightedHilbert c s) (2 * r) := by
        rw [mem_ball, dist_zero_right, not_lt]; exact hy'.le
      simp [hG, hρout y this]
  refine ⟨G, hGsmooth, fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simp only [hG, map_smul, headProj_idem]
  · have hz2 := hr2 z hz
    have h1 := PiMap_sub (K := K) (R := headProj c n) (i := inclE c s hs) (ε := ε₀) hy hz2
    show z + inclE c s hs (G z) = _
    have e : G z = headProj c n (K (Sv z)) := by simp [hG, hρin z hz]
    rw [e]
    show _ = PiMap (inclE c s hs) (fun y => K y - headProj c n (K y)) K ε₀ z
    exact add_eq_of_eq_sub' h1.symm
  · have hz2 := hr2 z hz
    obtain ⟨-, D, hD, Q, hQ1, hQ2, hDQ⟩ :=
      sinv_local (inclE c s hs) (tailField c s n K) ε₀ h8.smooth hy hz2
    have hx := Sinv_spec hy hz2
    have hxlt : ‖Sv z‖ < ε := by
      have := hx.1
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have hKx := hK.diff (Sv z)
    have hG0 : HasFDerivAt G ((headProj c n).comp ((fderiv ℝ K (Sv z)).comp D)) z := by
      have hev : G =ᶠ[𝓝 z] fun y => headProj c n (K (Sv y)) := by
        filter_upwards [isOpen_ball.mem_nhds hz] with y hy'
        simp [hG, hρin y hy']
      exact ((headProj c n).hasFDerivAt.comp z (hKx.hasFDerivAt.comp z hD)).congr_of_eventuallyEq hev
    have hA : ∀ h : ActualCM c, ‖fderiv ℝ K (Sv z) (inclE c s hs h)‖ ≤ 1 / 2 * ‖h‖ := fun h => by
      have := hK.contr _ hxlt h
      nlinarith [norm_nonneg h]
    have hU := isUnit_G (inclE c s hs) (headProj c n) K (tailField c s n K) (fun y => rfl)
      (Sv z) hKx D Q hA hQ1 hQ2 hDQ
    convert hU using 2
    ext h
    have := congrArg (fun f => f h) (hsDerivH_toCLM c s hs G z)
    refine this.trans ?_
    exact fderiv_apply_eq_of_hasFDerivAt hG0 _

/-- Injectivity of `Π'` on `ball 0 (ε₀/2)`: R6 for `T'` and R7b. -/
theorem injOn_PiOf (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) :
    InjOn (PiOf hs n K ε₀) (ball (0 : FullWeightedHilbert c s) (ε₀ / 2)) :=
  injOn_PiMap (step8Hyp_tailField hK hε₀ hlt n hn).step
    (injOn_T'_local_generic (inclE c s hs) K hlt (fun y _ => hK.diff y) hK.contr)

/-- **(ii)** the change-of-variables identity for `Π'` on `ball 0 r`, with density
`ramerJac G` (`G` head-valued `C²` with `TM G = Π'` there), and measurability of the image. -/
theorem localPieces_ii (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) {r : ℝ} (hr4 : 4 * r < ε₀) (hr : 0 < r)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (hGh : ∀ z, headProj c n (G z) = G z)
    (hGPi : ∀ z ∈ ball (0 : FullWeightedHilbert c s) r, TM c s hs G z = PiOf hs n K ε₀ z) :
    MeasurableSet (PiOf hs n K ε₀ '' ball (0 : FullWeightedHilbert c s) r) ∧
    ∀ f : FullWeightedHilbert c s → ℝ≥0∞, Measurable f →
      ∫⁻ y in PiOf hs n K ε₀ '' ball (0 : FullWeightedHilbert c s) r, f y
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
        ∫⁻ x in ball (0 : FullWeightedHilbert c s) r, f (PiOf hs n K ε₀ x) *
          ENNReal.ofReal (ramerJac c s hs G x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hGd : Differentiable ℝ G := hG1.differentiable one_ne_zero
  have hSnTM : Sn c s hs n G = TM c s hs G := Sn_eq_TM c s hs G hGh
  have hSc : Continuous (Sn c s hs n G) := continuous_Sn c s hs n G hG1.continuous
  set A : Set (FullWeightedHilbert c s) := ball (0 : FullWeightedHilbert c s) r with hA
  have hAZ : A ⊆ ball (0 : FullWeightedHilbert c s) (ε₀ / 2) :=
    ball_subset_ball (by linarith)
  have hSP : ∀ z ∈ A, Sn c s hs n G z = PiOf hs n K ε₀ z := fun z hz => by
    rw [hSnTM]; exact hGPi z hz
  have hinj : InjOn (Sn c s hs n G) A := fun a ha b hb hab => by
    rw [hSP a ha, hSP b hb] at hab
    exact injOn_PiOf hK hε₀ hlt n hn (hAZ ha) (hAZ hb) hab
  have himg : Sn c s hs n G '' A = PiOf hs n K ε₀ '' A := image_congr hSP
  have hmeas : MeasurableSet (Sn c s hs n G '' A) :=
    measurableSet_ball.image_of_continuousOn_injOn hSc.continuousOn hinj
  rw [← himg]
  refine ⟨hmeas, fun f hf => ?_⟩
  have h := lintegral_image_eq_fibre c s n hs (Sn c s hs n G) hSc.measurable
    (sameTail_Sn c s hs n G) (measurable_fibreJ_Sn c s n hs G hG1) A measurableSet_ball hmeas hinj
    (fun t v _ _ => differentiable_fibreMapOf_Sn c s n hs G hGd t v) f hf
  rw [h]
  have hae := ramerJac_ae_eq_fibreJ c s hs G hG hGh
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [hae] with x hx hxA
  rw [hx, hSnTM, hGPi x hxA]

/-- `projField k G = G` for a `V_n`-valued `G` and `k ≥ n`. -/
theorem projField_eq_of_headValued {n k : ℕ} (hkn : n ≤ k)
    (G : FullWeightedHilbert c s → ActualCM c) (hGh : ∀ z, headProj c n (G z) = G z) :
    projField k G = G := by
  funext z
  show headProj c k (G z) = G z
  rw [← hGh z, headProj_headProj_of_le c hkn, hGh z]

/-- **(iii)** null preservation of `TM G = Π'` on every `U ⊆ ball 0 r`, from (ii) and
positivity of `ramerJac G`. -/
theorem localPieces_iii (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : TailSmall c s hs d ε₀ n) {r : ℝ} (hr4 : 4 * r < ε₀) (hr : 0 < r)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (hGh : ∀ z, headProj c n (G z) = G z)
    (hGPi : ∀ z ∈ ball (0 : FullWeightedHilbert c s) r, TM c s hs G z = PiOf hs n K ε₀ z)
    (hGU : ∀ z ∈ ball (0 : FullWeightedHilbert c s) r,
        IsUnit (1 + (hsDerivH c s hs G z).toCLM)) :
    (∀ z ∈ ball (0 : FullWeightedHilbert c s) r, 0 < ramerJac c s hs G z) ∧
    ∀ U : Set (FullWeightedHilbert c s), U ⊆ ball (0 : FullWeightedHilbert c s) r →
      NullPresOn c s hs G U ∧ ∀ᶠ k in atTop, NullPresOn c s hs (projField k G) U := by
  refine ⟨fun z hz => ramerJac_pos_of_isUnit c s hs G z (hGU z hz), fun U hU => ?_⟩
  have hT : NullPresOn c s hs G U := by
    intro N hN
    obtain ⟨-, hii⟩ := localPieces_ii hK hε₀ hlt n hn hr4 hr G hG hGh hGPi
    set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
    set N' := toMeasurable γ N with hN'
    have hN'0 : γ N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
    have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
    have h0 := hii (N'.indicator 1) (measurable_one.indicator hN'm)
    have hL : ∫⁻ y in PiOf hs n K ε₀ '' ball (0 : FullWeightedHilbert c s) r,
        N'.indicator 1 y ∂γ = 0 := by
      refine le_antisymm ?_ zero_le
      calc _ ≤ ∫⁻ y, N'.indicator 1 y ∂γ := setLIntegral_le_lintegral _ _
        _ = γ N' := lintegral_indicator_one hN'm
        _ = 0 := hN'0
    rw [hL] at h0
    have hGc : Continuous (TM c s hs G) := (contDiff_TM c s hs G hG).continuous
    have hmeas : AEMeasurable (fun x => N'.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞)
        (PiOf hs n K ε₀ x) * ENNReal.ofReal (ramerJac c s hs G x))
        (γ.restrict (ball (0 : FullWeightedHilbert c s) r)) := by
      have e : ∀ x ∈ ball (0 : FullWeightedHilbert c s) r,
          N'.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞) (PiOf hs n K ε₀ x) =
          N'.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞) (TM c s hs G x) := fun x hx => by
        rw [hGPi x hx]
      refine AEMeasurable.congr (f := fun x => N'.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞)
        (TM c s hs G x) * ENNReal.ofReal (ramerJac c s hs G x)) ?_ ?_
      · exact (((measurable_one.indicator hN'm).comp hGc.measurable).aemeasurable.mul
          (aemeasurable_ofReal_ramerJac c s hs G hG)).restrict
      · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
        exact Filter.Eventually.of_forall fun x hx => by rw [e x hx]
    have hz0 := (lintegral_eq_zero_iff' hmeas).1 h0.symm
    have hz : ∀ᵐ x ∂γ.restrict (ball (0 : FullWeightedHilbert c s) r),
        N'.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞) (PiOf hs n K ε₀ x) *
          ENNReal.ofReal (ramerJac c s hs G x) = 0 := hz0
    rw [ae_restrict_iff' measurableSet_ball] at hz
    rw [measure_eq_zero_iff_ae_notMem]
    have hpos := fun z hz => ramerJac_pos_of_isUnit c s hs G z (hGU z hz)
    filter_upwards [hz] with x hx hxS
    have hxr := hU hxS.1
    have h1 := hx hxr
    rw [mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have hmem : PiOf hs n K ε₀ x ∈ N' := by
        rw [← hGPi x hxr]; exact subset_toMeasurable _ _ hxS.2
      simp [Set.indicator_of_mem hmem] at h1
    · have := ENNReal.ofReal_pos.2 (hpos x hxr)
      exact absurd h1 this.ne'
  refine ⟨hT, ?_⟩
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [projField_eq_of_headValued hk G hGh]
  exact hT

/-- **R10-P3 (main).**  For `K` as in Step 4 (`LocalField`) and `ε₀ < ε`, there is `n₀` such that
for every `n ≥ n₀`, with `L = (I - P_n) K`, `S = I + iL`, `Π' = PiMap`:
(i) `L` is in class N2; and for every `r` with `4 r < ε₀` there is a globally `C²`, `V_n`-valued
`G_Π` with `I + i G_Π = Π'` on `ball 0 r`, such that
(ii) `Π'(ball 0 r)` is measurable and the change-of-variables identity holds with density
`ramerJac G_Π`; (iii) `ramerJac G_Π > 0` on `ball 0 r`, and `TM G_Π` and all `TM (P_k G_Π)`,
`k ≥ n`, preserve null sets on every `U ⊆ ball 0 r`. -/
theorem ramer_local_pieces (hK : LocalField hs K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (Step8Hyp c s hs (tailField c s n K) ε₀ ∧ Step8Concl c s hs (tailField c s n K) ε₀ ∧
        (∀ U : Set (FullWeightedHilbert c s),
          U ⊆ closedBall (0 : FullWeightedHilbert c s) ε₀ ∩
            TM c s hs (tailField c s n K) ⁻¹' ball (0 : FullWeightedHilbert c s) (ε₀ / 2) →
          NullPresOn c s hs (tailField c s n K) U) ∧
        (∀ U : Set (FullWeightedHilbert c s), U ⊆ ball (0 : FullWeightedHilbert c s) (ε₀ / 4) →
          NullPresOn c s hs (tailField c s n K) U ∧
          ∀ k : ℕ, NullPresOn c s hs (projField k (tailField c s n K)) U)) ∧
      ∀ r : ℝ, 0 < r → 4 * r < ε₀ →
        ∃ G : FullWeightedHilbert c s → ActualCM c, ContDiff ℝ 2 G ∧
          (∀ z, headProj c n (G z) = G z) ∧
          (∀ z ∈ ball (0 : FullWeightedHilbert c s) r, TM c s hs G z = PiOf hs n K ε₀ z) ∧
          MeasurableSet (PiOf hs n K ε₀ '' ball (0 : FullWeightedHilbert c s) r) ∧
          (∀ f : FullWeightedHilbert c s → ℝ≥0∞, Measurable f →
            ∫⁻ y in PiOf hs n K ε₀ '' ball (0 : FullWeightedHilbert c s) r, f y
                ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
              ∫⁻ x in ball (0 : FullWeightedHilbert c s) r, f (PiOf hs n K ε₀ x) *
                ENNReal.ofReal (ramerJac c s hs G x)
                ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s)) ∧
          (∀ z ∈ ball (0 : FullWeightedHilbert c s) r, 0 < ramerJac c s hs G z) ∧
          (∀ U : Set (FullWeightedHilbert c s), U ⊆ ball (0 : FullWeightedHilbert c s) r →
            NullPresOn c s hs G U ∧ ∀ᶠ k in atTop, NullPresOn c s hs (projField k G) U) := by
  obtain ⟨n₀, hn₀⟩ := exists_tailSmall c s hs d ε₀ hε₀
  refine ⟨n₀, fun n hn => ⟨localPieces_i hK hε₀ hlt n (hn₀ n hn), fun r hr hr4 => ?_⟩⟩
  have hnS := hn₀ n hn
  obtain ⟨G, hG, hGh, hGPi, hGU⟩ := exists_headField hK hε₀ hlt n hnS hr hr4
  obtain ⟨hm, hii⟩ := localPieces_ii hK hε₀ hlt n hnS hr4 hr G hG hGh hGPi
  obtain ⟨hpos, hiii⟩ := localPieces_iii hK hε₀ hlt n hnS hr4 hr G hG hGh hGPi hGU
  exact ⟨G, hG, hGh, hGPi, hm, hii, hpos, hiii⟩

end GPi

end NlsGge.Ramer
