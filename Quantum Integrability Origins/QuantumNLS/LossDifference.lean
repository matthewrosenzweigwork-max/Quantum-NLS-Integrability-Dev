import Mathlib

/-!
# R-8C922B25 `lem:loss` (`DYNAMICS_LEMMAS.tex:13`), part 1: mixed finite differences and their Taylor estimate

Fully general (real normed spaces; no scale).  `mdiff j w φ x = Δ_{w_1}⋯Δ_{w_j} φ (x)` is the mixed forward difference (`Δ_w φ = φ(· + w) − φ`,
first difference applied first).  `taylor_mdiff` is the mixed-difference Taylor estimate on a convex open set `s` carrying a Taylor series up to
order `j+1`: `‖Δ_{w_1}⋯Δ_{w_j}φ(x) − D^jφ(x)[w_1,…,w_j]‖ ≤ C (∏‖w_i‖)(∑‖w_i‖)` when `‖D^{j+1}φ‖ ≤ C` on `s` and `closedBall x (∑‖w_i‖) ⊆ s`
(this is the printed estimate `‖Q_{j,h} − D^j f‖ ≤ C_j h` of the proof, in mixed form, so no polarization is needed).  `mdiff_map` (linear maps commute
with `mdiff`) and `mdiff_bound` (`‖Δ^j φ‖ ≤ 2^j M`) are the elementary companions.  No EXT-025 contract is used; the Taylor-series calculus is mathlib's
`HasFTaylorSeriesUpToOn`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
open scoped ContDiff
open Filter Topology Set Metric

noncomputable section
namespace QuantumNLS.Loss

variable {X F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def mdiff : (j : ℕ) → (Fin j → X) → (X → F) → X → F
  | 0, _, φ => φ
  | j + 1, w, φ => mdiff j (Fin.tail w) (fun x => φ (x + w 0) - φ x)

theorem mdiff_succ (j : ℕ) (w : Fin (j + 1) → X) (φ : X → F) :
    mdiff (j + 1) w φ = mdiff j (Fin.tail w) (fun x => φ (x + w 0) - φ x) := rfl

theorem mdiff_zero (w : Fin 0 → X) (φ : X → F) : mdiff 0 w φ = φ := rfl

theorem mdiff_map (ι : F →L[ℝ] G) : ∀ (j : ℕ) (w : Fin j → X) (φ : X → F) (x : X),
    mdiff j w (fun y => ι (φ y)) x = ι (mdiff j w φ x) := by
  intro j
  induction j with
  | zero => intro w φ x; rfl
  | succ j ih =>
    intro w φ x
    rw [mdiff_succ, mdiff_succ, ← ih]
    congr 1
    funext y
    simp [map_sub]

theorem mdiff_bound : ∀ (j : ℕ) (w : Fin j → X) (φ : X → F) (x : X) (M : ℝ),
    (∀ y, ‖y - x‖ ≤ ∑ i, ‖w i‖ → ‖φ y‖ ≤ M) → ‖mdiff j w φ x‖ ≤ 2 ^ j * M := by
  intro j
  induction j with
  | zero =>
    intro w φ x M h
    have := h x (by simp)
    simpa [mdiff_zero] using this
  | succ j ih =>
    intro w φ x M h
    rw [mdiff_succ]
    have hsum : ∑ i, ‖w i‖ = ‖w 0‖ + ∑ i : Fin j, ‖Fin.tail w i‖ := Fin.sum_univ_succ _
    have := ih (Fin.tail w) (fun y => φ (y + w 0) - φ y) x (2 * M) (fun y hy => by
      have h1 : ‖φ y‖ ≤ M := h y (by rw [hsum]; linarith [norm_nonneg (w 0)])
      have h2 : ‖φ (y + w 0)‖ ≤ M := h (y + w 0) (by
        rw [hsum]
        calc ‖y + w 0 - x‖ = ‖(y - x) + w 0‖ := by rw [add_sub_right_comm]
          _ ≤ ‖y - x‖ + ‖w 0‖ := norm_add_le _ _
          _ ≤ _ := by linarith)
      calc ‖φ (y + w 0) - φ y‖ ≤ ‖φ (y + w 0)‖ + ‖φ y‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith)
    calc _ ≤ 2 ^ j * (2 * M) := this
      _ = 2 ^ (j + 1) * M := by ring

/-- Taylor series of a translate difference. -/
theorem taylor_shift {n : ℕ∞ω} {φ : X → F} {p : X → FormalMultilinearSeries ℝ X F} {s : Set X}
    (hs : IsOpen s) (hp : HasFTaylorSeriesUpToOn n φ p s) (w : X) :
    HasFTaylorSeriesUpToOn n (fun x => φ (x + w) - φ x) (fun x => p (x + w) - p x)
      (s ∩ (fun x => x + w) ⁻¹' s) := by
  have hs' : IsOpen (s ∩ (fun x => x + w) ⁻¹' s) :=
    hs.inter (hs.preimage (continuous_id.add continuous_const))
  refine ⟨fun x hx => ?_, fun m hm x hx => ?_, fun m hm => ?_⟩
  · have h1 := hp.zero_eq (x + w) hx.2
    have h2 := hp.zero_eq x hx.1
    rw [← h1, ← h2]
    simp [ContinuousMultilinearMap.curry0_apply]
  · have h1 := ((hp.fderivWithin m hm (x + w) hx.2).hasFDerivAt (hs.mem_nhds hx.2))
    have h2 := ((hp.fderivWithin m hm x hx.1).hasFDerivAt (hs.mem_nhds hx.1))
    have h1' := (hasFDerivAt_comp_add_right (f := fun y => p y m) w).2 h1
    have h3 := h1'.sub h2
    refine h3.hasFDerivWithinAt.congr_fderiv ?_
    ext u v
    simp [ContinuousMultilinearMap.curryLeft_apply]
  · have h1 : ContinuousOn (fun y => p (y + w) m) (s ∩ (fun x => x + w) ⁻¹' s) :=
      (hp.cont m hm).comp (continuous_id.add continuous_const).continuousOn (fun y hy => hy.2)
    exact h1.sub ((hp.cont m hm).mono inter_subset_left)

theorem curryLeft_apply_le {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) F)
    (u : X) (ws : Fin j → X) : ‖(A.curryLeft u) ws‖ ≤ ‖A‖ * ‖u‖ * ∏ i, ‖ws i‖ := by
  rw [ContinuousMultilinearMap.curryLeft_apply]
  have := A.le_opNorm (Fin.cons u ws : Fin (j + 1) → X)
  rw [Fin.prod_univ_succ] at this
  simpa [mul_assoc] using this

theorem taylor_lip {n : ℕ} {φ : X → F} {p : X → FormalMultilinearSeries ℝ X F} {s : Set X} {C : ℝ}
    (hp : HasFTaylorSeriesUpToOn ((n + 1 : ℕ) : ℕ∞ω) φ p s) (hc : Convex ℝ s)
    (hb : ∀ y ∈ s, ‖p y (n + 1)‖ ≤ C) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖p y n - p x n‖ ≤ C * ‖y - x‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun z => p z n)
    (f' := fun z => (p z (n + 1)).curryLeft) (fun z hz => hp.fderivWithin n (by exact_mod_cast Nat.lt_succ_self n) z hz)
    (fun z hz => ?_) hc hx hy
  rw [ContinuousMultilinearMap.curryLeft_norm]
  exact hb z hz

theorem taylor_mdiff : ∀ (j : ℕ) (φ : X → F) (p : X → FormalMultilinearSeries ℝ X F) (s : Set X) (C : ℝ),
    IsOpen s → Convex ℝ s → HasFTaylorSeriesUpToOn ((j + 1 : ℕ) : ℕ∞ω) φ p s →
    (∀ y ∈ s, ‖p y (j + 1)‖ ≤ C) → ∀ (w : Fin j → X) (x : X), closedBall x (∑ i, ‖w i‖) ⊆ s →
    ‖mdiff j w φ x - p x j w‖ ≤ C * (∏ i, ‖w i‖) * ∑ i, ‖w i‖ := by
  intro j
  induction j with
  | zero =>
    intro φ p s C hs hc hp hb w x hx
    have hxs : x ∈ s := hx (mem_closedBall_self (by simp))
    have h0 := hp.zero_eq x hxs
    have : p x 0 w = φ x := by
      rw [← h0, ContinuousMultilinearMap.curry0_apply]
      congr 1
      exact Subsingleton.elim _ _
    simp [mdiff, this]
  | succ j ih =>
    intro φ p s C hs hc hp hb w x hx
    set w0 := w 0 with hw0
    set ws := Fin.tail w with hws
    have hsum : ∑ i, ‖w i‖ = ‖w0‖ + ∑ i : Fin j, ‖ws i‖ := Fin.sum_univ_succ _
    have hprod : ∏ i, ‖w i‖ = ‖w0‖ * ∏ i : Fin j, ‖ws i‖ := Fin.prod_univ_succ _
    have hxs : x ∈ s := hx (mem_closedBall_self (by positivity))
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb x hxs)
    have hxw : x + w0 ∈ s := hx (by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; rw [hsum]
      linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (ws i))])
    have hp1 : HasFTaylorSeriesUpToOn ((j + 1 : ℕ) : ℕ∞ω) φ p s :=
      hp.of_le (by exact_mod_cast Nat.le_succ (j + 1))
    set s' : Set X := s ∩ (fun y => y + w0) ⁻¹' s with hs'
    have hs'o : IsOpen s' := hs.inter (hs.preimage (continuous_id.add continuous_const))
    have hs'c : Convex ℝ s' := hc.inter (hc.translate_preimage_left w0)
    have hψ := taylor_shift hs hp1 w0
    have hb' : ∀ y ∈ s', ‖(p (y + w0) - p y) (j + 1)‖ ≤ C * ‖w0‖ := by
      intro y hy
      have := taylor_lip hp hc hb hy.1 hy.2
      simpa using this
    have hball : closedBall x (∑ i : Fin j, ‖ws i‖) ⊆ s' := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      have hn : 0 ≤ ‖w0‖ := norm_nonneg _
      refine ⟨hx ?_, hx ?_⟩
      · rw [mem_closedBall, dist_eq_norm, hsum]; linarith
      · rw [mem_closedBall, dist_eq_norm, hsum]
        calc ‖y + w0 - x‖ = ‖(y - x) + w0‖ := by rw [add_sub_right_comm]
          _ ≤ ‖y - x‖ + ‖w0‖ := norm_add_le _ _
          _ ≤ _ := by linarith
    have h1 := ih (fun y => φ (y + w0) - φ y) (fun y => p (y + w0) - p y) s' (C * ‖w0‖) hs'o hs'c hψ hb' ws x hball
    set A := p x (j + 1) with hA
    set χ : X → F := fun y => p y j ws - (A.curryLeft y) ws with hχ
    have hlt : ((j : ℕ) : ℕ∞ω) < ((j + 1 + 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (by omega : j < j + 1 + 1)
    have hder : ∀ z ∈ s, HasFDerivWithinAt χ
        (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp (p z (j + 1)).curryLeft) -
          ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp A.curryLeft)) s z := by
      intro z hz
      have hz' := hp.fderivWithin j hlt z hz
      have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).hasFDerivAt.comp_hasFDerivWithinAt z hz'
      have h3 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp A.curryLeft).hasFDerivWithinAt
        (s := s) (x := z)
      exact h2.sub h3
    have hseg : segment ℝ x (x + w0) ⊆ s := hc.segment_subset hxs hxw
    have hzseg : ∀ z ∈ segment ℝ x (x + w0), ‖z - x‖ ≤ ‖w0‖ := by
      intro z hz
      rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖(x + w0 - x)‖ ≤ 1 * ‖(x + w0 - x)‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖w0‖ := by rw [one_mul, add_sub_cancel_left]
    have hP : 0 ≤ ∏ i : Fin j, ‖ws i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have hbd : ∀ z ∈ segment ℝ x (x + w0), ‖((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp
        (p z (j + 1)).curryLeft) - ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp A.curryLeft)‖ ≤
        C * ‖w0‖ * ∏ i : Fin j, ‖ws i‖ := by
      intro z hz
      have hzs := hseg hz
      have hlip : ‖p z (j + 1) - A‖ ≤ C * ‖w0‖ :=
        (taylor_lip (n := j + 1) hp hc hb hxs hzs).trans (mul_le_mul_of_nonneg_left (hzseg z hz) hC0)
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
      have e : (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp (p z (j + 1)).curryLeft) -
          ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X) F ws).comp A.curryLeft)) u =
          ((p z (j + 1) - A).curryLeft u) ws := by
        simp [ContinuousMultilinearMap.curryLeft_apply]
      rw [e]
      calc ‖((p z (j + 1) - A).curryLeft u) ws‖ ≤ ‖p z (j + 1) - A‖ * ‖u‖ * ∏ i, ‖ws i‖ :=
            curryLeft_apply_le _ _ _
        _ ≤ C * ‖w0‖ * ‖u‖ * ∏ i, ‖ws i‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlip (norm_nonneg u)) hP
        _ = (C * ‖w0‖ * ∏ i : Fin j, ‖ws i‖) * ‖u‖ := by ring
    have h2 := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := χ) (s := segment ℝ x (x + w0))
      (fun z hz => (hder z (hseg hz)).mono hseg) hbd (convex_segment x (x + w0)) (left_mem_segment ℝ x (x + w0))
      (right_mem_segment ℝ x (x + w0))
    have e2 : χ (x + w0) - χ x = (p (x + w0) - p x) j ws - p x (j + 1) w := by
      have : p x (j + 1) w = (A.curryLeft w0) ws := by
        rw [ContinuousMultilinearMap.curryLeft_apply, hw0, hws, Fin.cons_self_tail]
      rw [this]
      have hsub : (p (x + w0) - p x) j = p (x + w0) j - p x j := rfl
      show (p (x + w0) j ws - (A.curryLeft (x + w0)) ws) - (p x j ws - (A.curryLeft x) ws) = _
      rw [map_add, hsub]
      simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
      abel
    rw [add_sub_cancel_left, e2] at h2
    have e3 : mdiff (j + 1) w φ x - p x (j + 1) w =
        (mdiff j ws (fun y => φ (y + w0) - φ y) x - (p (x + w0) - p x) j ws) +
          ((p (x + w0) - p x) j ws - p x (j + 1) w) := by
      rw [mdiff_succ]; abel
    rw [e3]
    refine (norm_add_le _ _).trans ?_
    rw [hsum, hprod]
    nlinarith [h1, h2]

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.mdiff_map
#print axioms QuantumNLS.Loss.mdiff_bound
#print axioms QuantumNLS.Loss.taylor_mdiff
