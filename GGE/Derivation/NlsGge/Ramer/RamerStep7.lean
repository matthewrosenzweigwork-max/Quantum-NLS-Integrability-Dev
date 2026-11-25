import Mathlib
import NlsGge.Ramer.RamerLemma52
import NlsGge.Ramer.RamerLemma53
import NlsGge.Ramer.RamerStep5
import NlsGge.Ramer.SpaceTransfer

/-!
# Ramer Step 7: the map `Π' = T' ∘ S⁻¹` on `B_{ε/2}`

Abstract setting: `i : H →L E`, `L : E → H` with Lemma 5.2 hypotheses, `S y = y + i (L y)`.
Route (b): direct construction of `S⁻¹` by the fibre contraction (see `RamerStep7.md`).
-/

namespace NlsGge.Ramer

open Metric Set Filter Topology

section Step7

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Hypotheses of Lemma 5.2 for `S y = y + i (L y)`. -/
structure Step7Hyp (i : H →L[ℝ] E) (L : E → H) (ε : ℝ) : Prop where
  pos : 0 < ε
  diff : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ L y
  small : ∀ y ∈ closedBall (0 : E) ε, ‖i (L y)‖ < ε / 2
  contr : ∀ y ∈ closedBall (0 : E) ε, ‖(fderiv ℝ L y).comp i‖ ≤ 1 / 2

/-- The inverse of `S` on `B_{ε/2}` (arbitrary value `0` outside). -/
noncomputable def Sinv (i : H →L[ℝ] E) (L : E → H) (ε : ℝ) (z : E) : E := by
  classical exact if h : ∃ x ∈ closedBall (0 : E) ε, x + i (L x) = z then h.choose else 0

variable [CompleteSpace H]

theorem Sinv_spec {i : H →L[ℝ] E} {L : E → H} {ε : ℝ} (hy : Step7Hyp i L ε) {z : E}
    (hz : z ∈ ball (0 : E) (ε / 2)) :
    Sinv i L ε z ∈ closedBall (0 : E) ε ∧ Sinv i L ε z + i (L (Sinv i L ε z)) = z := by
  have hex : ∃ x ∈ closedBall (0 : E) ε, x + i (L x) = z :=
    exists_add_image_eq i L hy.pos hy.diff hy.contr hy.small (by simpa using hz)
  unfold Sinv
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

theorem Sinv_unique {i : H →L[ℝ] E} {L : E → H} {ε : ℝ} (hy : Step7Hyp i L ε) {z x : E}
    (hx : x ∈ closedBall (0 : E) ε) (hxz : x + i (L x) = z) (hz : z ∈ ball (0 : E) (ε / 2)) :
    x = Sinv i L ε z :=
  injOn_add_image i L hy.diff hy.contr hx (Sinv_spec hy hz).1 (by
    simp only; rw [hxz, (Sinv_spec hy hz).2])

/-- `Sinv` is injective on `B_{ε/2}` (it has the left inverse `S`). -/
theorem injOn_Sinv {i : H →L[ℝ] E} {L : E → H} {ε : ℝ} (hy : Step7Hyp i L ε) :
    InjOn (Sinv i L ε) (ball (0 : E) (ε / 2)) := by
  intro z hz z' hz' h
  rw [← (Sinv_spec hy hz).2, ← (Sinv_spec hy hz').2, h]

/-- `h z = -L (S⁻¹ z)`: `S⁻¹ z = z + i (h z)`. -/
theorem Sinv_eq {i : H →L[ℝ] E} {L : E → H} {ε : ℝ} (hy : Step7Hyp i L ε) {z : E}
    (hz : z ∈ ball (0 : E) (ε / 2)) :
    Sinv i L ε z = z + i (-L (Sinv i L ε z)) := by
  rw [map_neg]; exact eq_add_neg_of_add_eq (Sinv_spec hy hz).2

/-- Continuity of `S⁻¹` on `B_{ε/2}`. -/
theorem continuousOn_Sinv {i : H →L[ℝ] E} {L : E → H} {ε : ℝ} (hy : Step7Hyp i L ε) :
    ContinuousOn (Sinv i L ε) (ball (0 : E) (ε / 2)) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  set h : E → H := fun z => -L (Sinv i L ε z) with hh
  have hxz := (Sinv_spec hy hz).1
  -- the key estimate
  have key : ∀ z' ∈ ball (0 : E) (ε / 2),
      ‖h z' - h z‖ ≤ 2 * ‖L (z' + i (h z)) - L (z + i (h z))‖ := by
    intro z' hz'
    have hx' := (Sinv_spec hy hz').1
    have hm : z' + i (h z) ∈ closedBall (0 : E) ε := by
      have h1 : ‖i (h z)‖ < ε / 2 := by
        simp only [hh, map_neg, norm_neg]; exact hy.small _ hxz
      have h2 : ‖z'‖ < ε / 2 := by simpa using hz'
      rw [mem_closedBall, dist_zero_right]
      calc ‖z' + i (h z)‖ ≤ ‖z'‖ + ‖i (h z)‖ := norm_add_le _ _
        _ ≤ ε := by linarith
    have e1 : Sinv i L ε z' - (z' + i (h z)) = i (h z' - h z) := by
      have := Sinv_eq hy hz'
      rw [map_sub]; nth_rewrite 1 [this]; simp only [hh]; abel
    have hlip := fibre_lipschitz i L hy.diff hy.contr hx' hm e1
    have e2 : h z' - h z = -(L (Sinv i L ε z') - L (z' + i (h z))) - (L (z' + i (h z)) - L (z + i (h z))) := by
      have : L (z + i (h z)) = L (Sinv i L ε z) := by
        congr 1; exact (Sinv_eq hy hz).symm
      rw [this]; simp only [hh]; abel
    have : ‖h z' - h z‖ ≤ ‖L (Sinv i L ε z') - L (z' + i (h z))‖ +
        ‖L (z' + i (h z)) - L (z + i (h z))‖ := by
      rw [e2]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
    linarith
  have hLc : ContinuousAt L (z + i (h z)) := by
    have : z + i (h z) = Sinv i L ε z := (Sinv_eq hy hz).symm
    rw [this]; exact (hy.diff _ hxz).continuousAt
  have hlim : Tendsto (fun z' => L (z' + i (h z))) (𝓝 z) (𝓝 (L (z + i (h z)))) :=
    hLc.tendsto.comp (by fun_prop : Continuous fun z' : E => z' + i (h z)).continuousAt
  have hball : ball (0 : E) (ε / 2) ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hh0 : Tendsto (fun z' => ‖h z' - h z‖) (𝓝 z) (𝓝 0) := by
    have hr : Tendsto (fun z' => 2 * ‖L (z' + i (h z)) - L (z + i (h z))‖) (𝓝 z) (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).const_mul 2
      simpa using this
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.mono hball key) hr
  have hhc : ContinuousAt h z :=
    tendsto_iff_norm_sub_tendsto_zero.2 hh0
  have : ContinuousAt (fun z' => z' + i (h z')) z :=
    continuousAt_id.add (i.continuous.continuousAt.comp hhc)
  exact this.congr (Eventually.mono hball fun z' hz' => (Sinv_eq hy hz').symm)

/-- `Π' z = T' (S⁻¹ z)` with `T' y = y + i (K'' y)`. -/
noncomputable def PiMap (i : H →L[ℝ] E) (L K : E → H) (ε : ℝ) (z : E) : E :=
  Sinv i L ε z + i (K (Sinv i L ε z))

/-- Head-valuedness: `Π' z - z = i (R (K'' (S⁻¹ z)))` when `L = (I - R) ∘ K''`. -/
theorem PiMap_sub {i : H →L[ℝ] E} {K : E → H} {R : H →L[ℝ] H} {ε : ℝ}
    (hy : Step7Hyp i (fun y => K y - R (K y)) ε) {z : E} (hz : z ∈ ball (0 : E) (ε / 2)) :
    PiMap i (fun y => K y - R (K y)) K ε z - z =
      i (R (K (Sinv i (fun y => K y - R (K y)) ε z))) := by
  have h2 := (Sinv_spec hy hz).2
  unfold PiMap
  generalize Sinv i (fun y => K y - R (K y)) ε z = x at h2 ⊢
  rw [← h2, map_sub]; abel

theorem PiMap_sub_mem_range {i : H →L[ℝ] E} {K : E → H} {R : H →L[ℝ] H} {ε : ℝ}
    (hy : Step7Hyp i (fun y => K y - R (K y)) ε) {z : E} (hz : z ∈ ball (0 : E) (ε / 2)) :
    PiMap i (fun y => K y - R (K y)) K ε z - z ∈ LinearMap.range ((i.comp R : H →L[ℝ] E) : H →ₗ[ℝ] E) := by
  rw [PiMap_sub hy hz]; exact ⟨K (Sinv i (fun y => K y - R (K y)) ε z), rfl⟩

/-- Injectivity of `Π'`, given injectivity of `T'` on the closed ball. -/
theorem injOn_PiMap {i : H →L[ℝ] E} {L K : E → H} {ε : ℝ} (hy : Step7Hyp i L ε)
    (hT : InjOn (fun y => y + i (K y)) (closedBall (0 : E) ε)) :
    InjOn (PiMap i L K ε) (ball (0 : E) (ε / 2)) := by
  intro z hz z' hz' h
  have := hT (Sinv_spec hy hz).1 (Sinv_spec hy hz').1 h
  exact injOn_Sinv hy hz hz' this

/-- Continuity of `Π'`, given differentiability of `K''` on the closed ball. -/
theorem continuousOn_PiMap {i : H →L[ℝ] E} {L K : E → H} {ε : ℝ} (hy : Step7Hyp i L ε)
    (hK : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ K y) :
    ContinuousOn (PiMap i L K ε) (ball (0 : E) (ε / 2)) := by
  have hc := continuousOn_Sinv hy
  have hT : ContinuousOn (fun y => y + i (K y)) (closedBall (0 : E) ε) :=
    continuousOn_add_image i K hK
  exact hT.comp hc (fun z hz => (Sinv_spec hy hz).1)

/-! ### Head-direction differentiability -/

/-- `I + D` is a continuous linear equivalence when `‖D‖ ≤ 1/2`. -/
theorem exists_equiv_one_add (D : H →L[ℝ] H) (hD : ‖D‖ ≤ 1 / 2) :
    ∃ e : H ≃L[ℝ] H, (e : H →L[ℝ] H) = 1 + D := by
  have hu : IsUnit (1 + D) := ⟨Units.oneSub (-D) (by rw [norm_neg]; linarith), by
    simp [sub_neg_eq_add]⟩
  have hb := ContinuousLinearMap.isUnit_iff_bijective.1 hu
  exact ⟨ContinuousLinearEquiv.ofBijective _
    (LinearMap.ker_eq_bot.2 hb.1) (LinearMap.range_eq_top.2 hb.2), rfl⟩

/-- Differentiability of `v ↦ S⁻¹ (z + i v)` along `H`-directions. -/
theorem differentiableAt_Sinv_fibre {i : H →L[ℝ] E} {L : E → H} {ε : ℝ}
    (hy : Step7Hyp i L ε) {z : E} {v₀ : H} (hv : z + i v₀ ∈ ball (0 : E) (ε / 2)) :
    DifferentiableAt ℝ (fun v : H => Sinv i L ε (z + i v)) v₀ := by
  -- ψ v = v - L (S⁻¹ (z + i v))
  set ψ : H → H := fun v => v - L (Sinv i L ε (z + i v)) with hψ
  have hfib : ∀ v, z + i v ∈ ball (0 : E) (ε / 2) → Sinv i L ε (z + i v) = z + i (ψ v) := by
    intro v hv
    have := Sinv_eq hy hv
    rw [this, hψ]; simp only [map_sub, map_neg]; abel
  have hcont : ContinuousAt (fun v : H => z + i v) v₀ := by fun_prop
  have hSc : ContinuousAt (fun v : H => Sinv i L ε (z + i v)) v₀ :=
    ContinuousAt.comp (f := fun v : H => z + i v) (g := Sinv i L ε)
      ((continuousOn_Sinv hy).continuousAt (isOpen_ball.mem_nhds hv)) hcont
  have hLc : ContinuousAt (fun v : H => L (Sinv i L ε (z + i v))) v₀ :=
    ContinuousAt.comp (f := fun v : H => Sinv i L ε (z + i v)) (g := L)
      (hy.diff _ (Sinv_spec hy hv).1).continuousAt hSc
  have hψc : ContinuousAt ψ v₀ := continuousAt_id.sub hLc
  have hev : ∀ᶠ v in 𝓝 v₀, z + i v ∈ ball (0 : E) (ε / 2) :=
    hcont.eventually (isOpen_ball.mem_nhds hv)
  -- the map φ w = w + L (z + i w)
  set φ : H → H := fun w => w + L (z + i w) with hφ
  have hxeq : z + i (ψ v₀) = Sinv i L ε (z + i v₀) := (hfib v₀ hv).symm
  have hxm := (Sinv_spec hy hv).1
  have hdiffL : HasFDerivAt L (fderiv ℝ L (z + i (ψ v₀))) (z + i (ψ v₀)) := by
    rw [hxeq]; exact (hy.diff _ hxm).hasFDerivAt
  have hφd : HasFDerivAt φ (1 + (fderiv ℝ L (z + i (ψ v₀))).comp i) (ψ v₀) := by
    have h1 : HasFDerivAt (fun w : H => z + i w) i (ψ v₀) := by
      simpa using i.hasFDerivAt.const_add z
    exact (hasFDerivAt_id _).add (hdiffL.comp (ψ v₀) h1)
  obtain ⟨e, he⟩ := exists_equiv_one_add ((fderiv ℝ L (z + i (ψ v₀))).comp i)
    (by rw [hxeq]; exact hy.contr _ hxm)
  have hφd' : HasFDerivAt φ (e : H →L[ℝ] H) (ψ v₀) := by rw [he]; exact hφd
  have hlin : ∀ᶠ v in 𝓝 v₀, φ (ψ v) = v := by
    filter_upwards [hev] with v hv'
    show ψ v + L (z + i (ψ v)) = v
    rw [← hfib v hv', hψ]; simp
  have hψd : HasFDerivAt ψ (e.symm : H →L[ℝ] H) v₀ :=
    HasFDerivAt.of_local_left_inverse hψc hφd' hlin
  have : (fun v : H => Sinv i L ε (z + i v)) =ᶠ[𝓝 v₀] fun v => z + i (ψ v) :=
    hev.mono fun v hv' => hfib v hv'
  refine DifferentiableAt.congr_of_eventuallyEq ?_ this
  exact (i.differentiableAt.comp v₀ hψd.differentiableAt).const_add z

/-- Head-direction differentiability of `Π'`: `v ↦ Π' (z + i v)` is differentiable. -/
theorem differentiableAt_PiMap_fibre {i : H →L[ℝ] E} {L K : E → H} {ε : ℝ}
    (hy : Step7Hyp i L ε) (hK : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ K y)
    {z : E} {v₀ : H} (hv : z + i v₀ ∈ ball (0 : E) (ε / 2)) :
    DifferentiableAt ℝ (fun v : H => PiMap i L K ε (z + i v)) v₀ := by
  have hs := differentiableAt_Sinv_fibre hy hv
  have hm := (Sinv_spec hy hv).1
  unfold PiMap
  exact hs.add (i.differentiableAt.comp v₀ (DifferentiableAt.comp v₀ (hK _ hm) hs))

/-- Restriction to a finite-dimensional (any) subspace `V` of `H`. -/
theorem differentiableAt_PiMap_subspace {i : H →L[ℝ] E} {L K : E → H} {ε : ℝ}
    (hy : Step7Hyp i L ε) (hK : ∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ K y)
    (V : Submodule ℝ H) {z : E} {v₀ : V} (hv : z + i (v₀ : H) ∈ ball (0 : E) (ε / 2)) :
    DifferentiableAt ℝ (fun v : V => PiMap i L K ε (z + i (v : H))) v₀ :=
  (differentiableAt_PiMap_fibre hy hK hv).comp v₀ (V.subtypeL.differentiableAt)

end Step7

end NlsGge.Ramer
