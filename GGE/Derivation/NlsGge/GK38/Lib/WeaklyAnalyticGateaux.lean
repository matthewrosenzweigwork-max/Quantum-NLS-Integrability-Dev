import NlsGge.GK38.Lib.WeaklyAnalyticLine

/-!
# Directional derivatives of line-holomorphic maps (library piece L3a, part 2)

Local re-proof from Mathlib (E01-D8).  Let `U ⊆ E` be open and `f : E → F` (complex Banach spaces).
`LineDiff U f` says that `ζ ↦ f (x + ζ • h)` is differentiable at `0` for all `x ∈ U`, `h ∈ E`, and
`LocBdd U f` that `f` is locally bounded.  `LineGood U f` is the conjunction.

Everything is derived from Cauchy estimates for one-variable functions (no integrals, no
polarization):

* `LineGood.continuousOn`: Lipschitz bound on small balls;
* `dirD k f x := d/dζ f (x + ζ k) |₀` is again `LineGood`, with explicit bounds (`LineGood.dirD`);
* `dirD_add`: additivity in the direction `k` (the several-variable step, proved by a second order
  estimate), hence linearity `k ↦ dirD k f x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Metric Set Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `f` is differentiable along every complex line through every point of `U`. -/
def LineDiff (U : Set E) (f : E → F) : Prop :=
  ∀ x ∈ U, ∀ h : E, DifferentiableAt ℂ (fun t : ℂ => f (x + t • h)) 0

/-- `f` is locally bounded on `U`. -/
def LocBdd (U : Set E) (f : E → F) : Prop :=
  ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ ball x r, ‖f y‖ ≤ M

/-- Line-differentiable and locally bounded. -/
def LineGood (U : Set E) (f : E → F) : Prop := LineDiff U f ∧ LocBdd U f

/-- Directional derivative `d/dζ f (x + ζ k)` at `ζ = 0`. -/
def dirD (k : E) (f : E → F) (x : E) : F := deriv (fun t : ℂ => f (x + t • k)) 0

section Lines

variable {U : Set E} {f : E → F}

theorem LineDiff.hasDerivAt (hf : LineDiff U f) {x h : E} {ζ : ℂ} (hx : x + ζ • h ∈ U) :
    HasDerivAt (fun t : ℂ => f (x + t • h)) (dirD h f (x + ζ • h)) ζ := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + ζ • h + t • h)) (dirD h f (x + ζ • h)) (ζ - ζ) := by
    rw [sub_self]; exact (hf _ hx h).hasDerivAt
  have h2 := h1.comp_sub_const ζ ζ
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  show f (x + t • h) = f (x + ζ • h + (t - ζ) • h)
  congr 1
  rw [add_assoc, ← add_smul]; congr 2; ring

theorem LineDiff.at (hf : LineDiff U f) {x h : E} {ζ : ℂ} (hx : x + ζ • h ∈ U) :
    DifferentiableAt ℂ (fun t : ℂ => f (x + t • h)) ζ :=
  (hf.hasDerivAt hx).differentiableAt

theorem norm_dirD_le_of_line (hf : LineDiff U f) {y k : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ w : ℂ, ‖w‖ ≤ ρ → y + w • k ∈ U ∧ ‖f (y + w • k)‖ ≤ M) :
    ‖dirD k f y‖ ≤ M / ρ :=
  norm_deriv_le_of_closedBall (g := fun t : ℂ => f (y + t • k)) (c := 0) hρ
    (fun w hw => hf.at (hsub w (by simpa using hw)).1)
    (fun w hw => (hsub w (by simpa using hw)).2)

theorem norm_sub_sub_dirD_le_of_line (hf : LineDiff U f) {y k : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ w : ℂ, ‖w‖ ≤ ρ → y + w • k ∈ U ∧ ‖f (y + w • k)‖ ≤ M) {s : ℂ}
    (hs : ‖s‖ ≤ ρ / 4) :
    ‖f (y + s • k) - f y - s • dirD k f y‖ ≤ 8 * M * ‖s‖ ^ 2 / ρ ^ 2 := by
  have := norm_sub_sub_deriv_le (g := fun t : ℂ => f (y + t • k)) (c := 0) (δ := ρ) (M := M) hρ
    (fun w hw => hf.at (hsub w (by simpa using hw)).1)
    (fun w hw => (hsub w (by simpa using hw)).2) (s := s) hs
  simpa [dirD] using this

/-- Points of `ball x (r/2)` stay in `ball x r` along the line of direction `k` for `‖w‖ ≤ ρ`. -/
theorem line_mem_ball {x y k : E} {r : ℝ} (hy : y ∈ ball x (r / 2)) {w : ℂ}
    (hw : ‖w‖ ≤ r / (2 * (‖k‖ + 1))) : y + w • k ∈ ball x r := by
  rw [mem_ball_iff_norm] at hy ⊢
  have hk : 0 ≤ ‖k‖ := norm_nonneg k
  have hr : 0 < r := by linarith [norm_nonneg (y - x)]
  have h1 : ‖w‖ * ‖k‖ ≤ r / 2 := by
    calc ‖w‖ * ‖k‖ ≤ r / (2 * (‖k‖ + 1)) * ‖k‖ := by gcongr
      _ = r / 2 * (‖k‖ / (‖k‖ + 1)) := by field_simp
      _ ≤ r / 2 * 1 := by
        gcongr; rw [div_le_one (by linarith)]; linarith
      _ = r / 2 := by ring
  calc ‖y + w • k - x‖ = ‖(y - x) + w • k‖ := by congr 1; abel
    _ ≤ ‖y - x‖ + ‖w • k‖ := norm_add_le _ _
    _ < r := by rw [norm_smul]; linarith

theorem lipschitz_ball (hf : LineDiff U f) {x : E} {r M : ℝ} (hrU : ball x r ⊆ U)
    (hM : ∀ y ∈ ball x r, ‖f y‖ ≤ M) {y₁ y₂ : E} (h₁ : y₁ ∈ ball x (r / 2))
    (h₂ : y₂ ∈ ball x (r / 2)) : ‖f y₂ - f y₁‖ ≤ (2 * M / r) * ‖y₂ - y₁‖ := by
  have hr : 0 < r := by
    have := mem_ball_iff_norm.mp h₁
    linarith [norm_nonneg (y₁ - x)]
  by_cases hv : y₂ - y₁ = 0
  · have : y₂ = y₁ := sub_eq_zero.mp hv
    subst this; simp
  set v := y₂ - y₁ with hvdef
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set ρ : ℝ := r / (2 * ‖v‖) with hρ
  have hρpos : 0 < ρ := by positivity
  have h₁' := mem_ball_iff_norm.mp h₁
  have h₂' := mem_ball_iff_norm.mp h₂
  -- points on the segment
  have hseg : ∀ t ∈ segment ℝ (0 : ℂ) 1, ‖y₁ + t • v - x‖ < r / 2 := by
    intro t ht
    rw [segment_eq_image'] at ht
    obtain ⟨b, ⟨hb0, hb1⟩, rfl⟩ := ht
    have e : y₁ + ((0:ℂ) + b • ((1:ℂ) - 0)) • v - x = (1 - (b:ℂ)) • (y₁ - x) + (b:ℂ) • (y₂ - x) := by
      simp only [zero_add, sub_zero, Complex.real_smul, mul_one, hvdef]
      module
    rw [e]
    calc _ ≤ ‖(1 - (b:ℂ)) • (y₁ - x)‖ + ‖(b:ℂ) • (y₂ - x)‖ := norm_add_le _ _
      _ = (1 - b) * ‖y₁ - x‖ + b * ‖y₂ - x‖ := by
        rw [norm_smul, norm_smul]
        have : ‖(1 - (b:ℂ))‖ = 1 - b := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      _ ≤ (1 - b) * max ‖y₁ - x‖ ‖y₂ - x‖ + b * max ‖y₁ - x‖ ‖y₂ - x‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb0)
      _ = max ‖y₁ - x‖ ‖y₂ - x‖ := by ring
      _ < r / 2 := max_lt h₁' h₂'
  have hder : ∀ t ∈ segment ℝ (0 : ℂ) 1, DifferentiableAt ℂ (fun t : ℂ => f (y₁ + t • v)) t := by
    intro t ht
    have := hseg t ht
    exact hf.at (hrU (by rw [mem_ball_iff_norm]; linarith))
  have hbd : ∀ t ∈ segment ℝ (0 : ℂ) 1, ‖deriv (fun t : ℂ => f (y₁ + t • v)) t‖ ≤ M / ρ := by
    intro t ht
    have hpt := hseg t ht
    rw [(hf.hasDerivAt (hrU (by rw [mem_ball_iff_norm]; linarith : y₁ + t • v ∈ ball x r))).deriv]
    refine norm_dirD_le_of_line hf hρpos ?_
    intro w hw
    have hmem : y₁ + t • v + w • v ∈ ball x r := by
      rw [mem_ball_iff_norm]
      have : ‖w • v‖ ≤ r / 2 := by
        rw [norm_smul]
        calc ‖w‖ * ‖v‖ ≤ ρ * ‖v‖ := by gcongr
          _ = r / 2 := by rw [hρ]; field_simp
      calc ‖y₁ + t • v + w • v - x‖ = ‖(y₁ + t • v - x) + w • v‖ := by congr 1; abel
        _ ≤ ‖y₁ + t • v - x‖ + ‖w • v‖ := norm_add_le _ _
        _ < r := by linarith
    have e : y₁ + t • v + w • v = y₁ + (t + w) • v := by rw [add_assoc, ← add_smul]
    refine ⟨hrU hmem, hM _ hmem⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t : ℂ => f (y₁ + t • v))
    (s := segment ℝ (0 : ℂ) 1) (C := M / ρ) hder hbd (convex_segment _ _)
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  simp only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one, hvdef,
    add_sub_cancel] at this
  calc ‖f y₂ - f y₁‖ ≤ M / ρ := this
    _ = (2 * M / r) * ‖y₂ - y₁‖ := by rw [hρ, hvdef]; field_simp

theorem exists_ball_of_locBdd (hU : IsOpen U) (hf : LocBdd U f) {x : E} (hx : x ∈ U) :
    ∃ r > 0, ∃ M : ℝ, ball x r ⊆ U ∧ ∀ y ∈ ball x r, ‖f y‖ ≤ M := by
  obtain ⟨r₁, hr₁, M, hM⟩ := hf x hx
  obtain ⟨r₂, hr₂, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, M, ?_, fun y hy => hM y ?_⟩
  · exact (ball_subset_ball (min_le_right _ _)).trans hsub
  · exact ball_subset_ball (min_le_left _ _) hy

theorem LineGood.continuousOn (hU : IsOpen U) (hf : LineGood U f) : ContinuousOn f U := by
  intro x hx
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hf.2 hx
  refine ContinuousAt.continuousWithinAt ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hK : 0 ≤ 2 * M / r := by
    have := (norm_nonneg _).trans (hM x (mem_ball_self hr))
    positivity
  refine ⟨min (r / 2) (ε / (2 * M / r + 1)), lt_min (by positivity) (by positivity), fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  have hy1 : y ∈ ball x (r / 2) := by
    rw [mem_ball_iff_norm]; exact lt_of_lt_of_le hy (min_le_left _ _)
  have := lipschitz_ball hf.1 hrU hM (mem_ball_self (by positivity : (0:ℝ) < r / 2)) hy1
  have hy2 : ‖y - x‖ < ε / (2 * M / r + 1) := lt_of_lt_of_le hy (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at hy2
  calc ‖f y - f x‖ ≤ (2 * M / r) * ‖y - x‖ := this
    _ ≤ (2 * M / r + 1) * ‖y - x‖ := by gcongr; linarith
    _ = ‖y - x‖ * (2 * M / r + 1) := mul_comm _ _
    _ < ε := hy2

/-- Lipschitz estimate for the directional derivative. -/
theorem norm_dirD_sub_le (hf : LineDiff U f) {x : E} {r M : ℝ} (hrU : ball x r ⊆ U)
    (hM : ∀ y ∈ ball x r, ‖f y‖ ≤ M) {y₁ y₂ : E} (h₁ : y₁ ∈ ball x (r / 4))
    (h₂ : y₂ ∈ ball x (r / 4)) (k : E) :
    ‖dirD k f y₁ - dirD k f y₂‖ ≤ (8 * M * (‖k‖ + 1) / r ^ 2) * ‖y₁ - y₂‖ := by
  have hr : 0 < r := by
    have := mem_ball_iff_norm.mp h₁
    linarith [norm_nonneg (y₁ - x)]
  set ρ : ℝ := r / (4 * (‖k‖ + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hmem : ∀ y, y ∈ ball x (r / 4) → ∀ w : ℂ, ‖w‖ ≤ ρ → y + w • k ∈ ball x (r / 2) := by
    intro y hy w hw
    have hy' : y ∈ ball x (r / 2 / 2) := by
      have : r / 2 / 2 = r / 4 := by ring
      rwa [this]
    refine line_mem_ball (k := k) hy' ?_
    have : r / 2 / (2 * (‖k‖ + 1)) = ρ := by rw [hρ]; field_simp; ring
    rw [this]; exact hw
  set φ : ℂ → F := fun w => f (y₁ + w • k) - f (y₂ + w • k) with hφ
  have hdiff : ∀ w : ℂ, ‖w‖ ≤ ρ → DifferentiableAt ℂ φ w := by
    intro w hw
    have a1 := hrU ((ball_subset_ball (by linarith : r / 2 ≤ r)) (hmem y₁ h₁ w hw))
    have a2 := hrU ((ball_subset_ball (by linarith : r / 2 ≤ r)) (hmem y₂ h₂ w hw))
    exact (hf.at a1).sub (hf.at a2)
  have hbd : ∀ w : ℂ, ‖w‖ ≤ ρ → ‖φ w‖ ≤ (2 * M / r) * ‖y₁ - y₂‖ := by
    intro w hw
    have := lipschitz_ball hf hrU hM (hmem y₂ h₂ w hw) (hmem y₁ h₁ w hw)
    simpa [hφ, add_sub_add_right_eq_sub] using this
  have := norm_deriv_le_of_closedBall (g := φ) (c := 0) hρpos
    (fun w hw => hdiff w (by simpa using hw)) (fun w hw => hbd w (by simpa using hw))
  have hd : deriv φ 0 = dirD k f y₁ - dirD k f y₂ := by
    have a1 := hf.at (x := y₁) (h := k) (ζ := 0) (by
      have := hrU ((ball_subset_ball (by linarith : r / 4 ≤ r)) h₁); simpa using this)
    have a2 := hf.at (x := y₂) (h := k) (ζ := 0) (by
      have := hrU ((ball_subset_ball (by linarith : r / 4 ≤ r)) h₂); simpa using this)
    exact deriv_fun_sub a1 a2
  rw [hd] at this
  calc _ ≤ (2 * M / r) * ‖y₁ - y₂‖ / ρ := this
    _ = _ := by rw [hρ]; field_simp; ring

/-- Difference quotient approximation of `dirD`, uniform on `ball x (r/4)`. -/
theorem norm_dirD_sub_quot_le (hf : LineDiff U f) {x : E} {r M : ℝ} (hrU : ball x r ⊆ U)
    (hM : ∀ y ∈ ball x r, ‖f y‖ ≤ M) {y : E} (hy : y ∈ ball x (r / 4)) (k : E) {w : ℂ}
    (hw0 : w ≠ 0) (hw : ‖w‖ ≤ r / (2 * (‖k‖ + 1)) / 4) :
    ‖dirD k f y - w⁻¹ • (f (y + w • k) - f y)‖ ≤
      8 * M * ‖w‖ / (r / (2 * (‖k‖ + 1))) ^ 2 := by
  have hr : 0 < r := by
    have := mem_ball_iff_norm.mp hy
    linarith [norm_nonneg (y - x)]
  set ρ : ℝ := r / (2 * (‖k‖ + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hy2 : y ∈ ball x (r / 2) := ball_subset_ball (by linarith) hy
  have hsub : ∀ v : ℂ, ‖v‖ ≤ ρ → y + v • k ∈ U ∧ ‖f (y + v • k)‖ ≤ M := fun v hv =>
    ⟨hrU (line_mem_ball hy2 hv), hM _ (line_mem_ball hy2 hv)⟩
  have h := norm_sub_sub_dirD_le_of_line hf hρpos hsub hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have e : dirD k f y - w⁻¹ • (f (y + w • k) - f y)
      = -(w⁻¹ • (f (y + w • k) - f y - w • dirD k f y)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hw0, one_smul]; abel
  rw [e, norm_neg, norm_smul, norm_inv]
  calc ‖w‖⁻¹ * ‖f (y + w • k) - f y - w • dirD k f y‖
      ≤ ‖w‖⁻¹ * (8 * M * ‖w‖ ^ 2 / ρ ^ 2) := by gcongr
    _ = 8 * M * ‖w‖ / ρ ^ 2 := by field_simp

theorem lineDiff_dirD (hU : IsOpen U) (hf : LineGood U f) (k : E) : LineDiff U (dirD k f) := by
  intro x hx h
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hf.2 hx
  set ρ : ℝ := r / (2 * (‖k‖ + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  set ρ₀ : ℝ := r / (4 * (‖h‖ + 1)) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by positivity
  have hζ : ∀ ζ : ℂ, ζ ∈ ball (0 : ℂ) ρ₀ → x + ζ • h ∈ ball x (r / 4) := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    rw [mem_ball_iff_norm]
    have : x + ζ • h - x = ζ • h := by abel
    rw [this, norm_smul]
    have hh : 0 ≤ ‖h‖ := norm_nonneg h
    calc ‖ζ‖ * ‖h‖ ≤ ρ₀ * ‖h‖ := by gcongr
      _ = r / 4 * (‖h‖ / (‖h‖ + 1)) := by rw [hρ₀]; field_simp
      _ < r / 4 := by
        have : ‖h‖ / (‖h‖ + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith
  set w : ℕ → ℂ := fun n => (((ρ / 4) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hw
  have hwn : ∀ n, ‖w n‖ = (ρ / 4) * (1 / ((n : ℝ) + 1)) := fun n => by
    simp only [hw, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos (by positivity)
  have hw0 : ∀ n, w n ≠ 0 := fun n => by
    rw [← norm_pos_iff, hwn]; positivity
  have hwle : ∀ n, ‖w n‖ ≤ ρ / 4 := fun n => by
    rw [hwn]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ρ / 4 * (1 / ((n : ℝ) + 1)) ≤ ρ / 4 * 1 := by gcongr
      _ = ρ / 4 := by ring
  set Q : ℕ → ℂ → F := fun n ζ => (w n)⁻¹ • (f (x + ζ • h + w n • k) - f (x + ζ • h)) with hQ
  have hQd : ∀ n, DifferentiableOn ℂ (Q n) (ball (0 : ℂ) ρ₀) := by
    intro n ζ hζ'
    refine DifferentiableAt.differentiableWithinAt ?_
    have hy : x + ζ • h ∈ ball x (r / 4) := hζ ζ hζ'
    have hy2 : x + ζ • h ∈ ball x (r / 2) := ball_subset_ball (by linarith) hy
    have hmem : x + ζ • h + w n • k ∈ U := hrU (line_mem_ball hy2 ((hwle n).trans (by linarith)))
    have a1 : DifferentiableAt ℂ (fun t : ℂ => f ((x + w n • k) + t • h)) ζ := by
      refine hf.1.at ?_
      have : x + w n • k + ζ • h = x + ζ • h + w n • k := by abel
      rw [this]; exact hmem
    have a2 : DifferentiableAt ℂ (fun t : ℂ => f (x + t • h)) ζ :=
      hf.1.at (hrU (ball_subset_ball (by linarith) hy))
    refine ((a1.sub a2).const_smul (w n)⁻¹).congr_of_eventuallyEq ?_
    refine Eventually.of_forall fun t => ?_
    simp only [hQ]
    congr 3 
    abel
  have hlim : TendstoUniformlyOn Q (fun ζ => dirD k f (x + ζ • h)) atTop (ball (0 : ℂ) ρ₀) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set C : ℝ := 8 * M / ρ ^ 2 with hC
    have hlim0 : Tendsto (fun n : ℕ => C * ((ρ / 4) * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ρ / 4)
      have := this.const_mul C
      simpa using this
    filter_upwards [hlim0.eventually (gt_mem_nhds hε)] with n hn ζ hζ'
    rw [dist_eq_norm]
    have := norm_dirD_sub_quot_le hf.1 hrU hM (hζ ζ hζ') k (hw0 n) (hwle n)
    rw [hwn, ← hρ] at this
    refine lt_of_le_of_lt ?_ hn
    simpa [hQ, hC, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using this
  have := (hlim.tendstoLocallyUniformlyOn).differentiableOn (Eventually.of_forall hQd)
    isOpen_ball
  exact this.differentiableAt (isOpen_ball.mem_nhds (by simpa using hρ₀pos))

theorem locBdd_dirD (hU : IsOpen U) (hf : LineGood U f) (k : E) : LocBdd U (dirD k f) := by
  intro x hx
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hf.2 hx
  refine ⟨r / 2, by positivity, M / (r / (2 * (‖k‖ + 1))), fun y hy => ?_⟩
  refine norm_dirD_le_of_line hf.1 (by positivity) fun w hw => ?_
  exact ⟨hrU (line_mem_ball hy hw), hM _ (line_mem_ball hy hw)⟩

theorem LineGood.dirD (hU : IsOpen U) (hf : LineGood U f) (k : E) : LineGood U (dirD k f) :=
  ⟨lineDiff_dirD hU hf k, locBdd_dirD hU hf k⟩

theorem dirD_smul (c : ℂ) (k : E) (f : E → F) {x : E}
    (hd : DifferentiableAt ℂ (fun t : ℂ => f (x + t • k)) 0) :
    dirD (c • k) f x = c • dirD k f x := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • k)) (dirD k f x) ((fun t : ℂ => c * t) 0) := by
    simpa [dirD] using hd.hasDerivAt
  have h2 : HasDerivAt (fun t : ℂ => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul c
  have h3 := h1.scomp 0 h2
  have : (fun t : ℂ => f (x + t • (c • k))) = (fun t : ℂ => f (x + t • k)) ∘ fun t : ℂ => c * t := by
    funext t; simp [Function.comp, smul_smul, mul_comm]
  rw [dirD, this]; exact h3.deriv

theorem hasDerivAt_of_quad {g : ℂ → F} {a : F} {C z₀ : ℝ} (hz₀ : 0 < z₀)
    (h : ∀ z : ℂ, ‖z‖ ≤ z₀ → ‖g z - g 0 - z • a‖ ≤ C * ‖z‖ ^ 2) : HasDerivAt g a 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hpos : 0 < min z₀ (ε / (|C| + 1)) := lt_min hz₀ (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with s hs
  rw [mem_ball_zero_iff] at hs
  have hs1 : ‖s‖ ≤ z₀ := (lt_of_lt_of_le hs (min_le_left _ _)).le
  have hs2 : ‖s‖ < ε / (|C| + 1) := lt_of_lt_of_le hs (min_le_right _ _)
  have := h s hs1
  simp only [zero_add]
  calc ‖g s - g 0 - s • a‖ ≤ C * ‖s‖ ^ 2 := this
    _ ≤ |C| * ‖s‖ * ‖s‖ := by rw [sq, ← mul_assoc]; gcongr; exact le_abs_self C
    _ ≤ ε * ‖s‖ := by
      have hC1 : (0:ℝ) < |C| + 1 := by positivity
      have : ‖s‖ * (|C| + 1) < ε := by rwa [lt_div_iff₀ hC1] at hs2
      nlinarith [norm_nonneg s, abs_nonneg C]

/-- **Additivity of the directional derivative** in the direction (the several-variable step). -/
theorem dirD_add (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) (k₁ k₂ : E) :
    dirD (k₁ + k₂) f x = dirD k₁ f x + dirD k₂ f x := by
  obtain ⟨r, hr, M, hrU, hM⟩ := exists_ball_of_locBdd hU hf.2 hx
  set ρ₁ : ℝ := r / (2 * (‖k₁‖ + 1)) with hρ₁
  set ρ₂ : ℝ := r / (2 * (‖k₂‖ + 1)) with hρ₂
  have hρ₁pos : 0 < ρ₁ := by positivity
  have hρ₂pos : 0 < ρ₂ := by positivity
  set z₀ : ℝ := min (ρ₁ / 4) (ρ₂ / 4) with hz₀def
  have hz₀ : 0 < z₀ := lt_min (by positivity) (by positivity)
  set C : ℝ := 8 * M / ρ₁ ^ 2 + 8 * M / ρ₂ ^ 2 + (8 * M * (‖k₁‖ + 1) / r ^ 2) * ‖k₂‖ with hC
  have hbound : ∀ z : ℂ, ‖z‖ ≤ z₀ →
      ‖f (x + z • (k₁ + k₂)) - f (x + (0 : ℂ) • (k₁ + k₂)) - z • (dirD k₁ f x + dirD k₂ f x)‖
        ≤ C * ‖z‖ ^ 2 := by
    intro z hz
    have hz1 : ‖z‖ ≤ ρ₁ / 4 := hz.trans (min_le_left _ _)
    have hz2 : ‖z‖ ≤ ρ₂ / 4 := hz.trans (min_le_right _ _)
    have hxball : x ∈ ball x (r / 4 / 2) := mem_ball_self (by positivity)
    have hv4 : x + z • k₂ ∈ ball x (r / 4) := by
      refine line_mem_ball (r := r / 4) hxball ?_
      have : r / 4 / (2 * (‖k₂‖ + 1)) = ρ₂ / 4 := by rw [hρ₂]; field_simp
      rw [this]; exact hz2
    have hv2 : x + z • k₂ ∈ ball x (r / 2) := ball_subset_ball (by linarith) hv4
    have hx2 : x ∈ ball x (r / 2) := mem_ball_self (by positivity)
    set v : E := x + z • k₂ with hv
    have hsub1 : ∀ w : ℂ, ‖w‖ ≤ ρ₁ → v + w • k₁ ∈ U ∧ ‖f (v + w • k₁)‖ ≤ M := fun w hw =>
      ⟨hrU (line_mem_ball hv2 hw), hM _ (line_mem_ball hv2 hw)⟩
    have hsub2 : ∀ w : ℂ, ‖w‖ ≤ ρ₂ → x + w • k₂ ∈ U ∧ ‖f (x + w • k₂)‖ ≤ M := fun w hw =>
      ⟨hrU (line_mem_ball (by simpa using hx2) hw), hM _ (line_mem_ball hx2 hw)⟩
    have T1 := norm_sub_sub_dirD_le_of_line hf.1 hρ₁pos hsub1 hz1
    have T3 := norm_sub_sub_dirD_le_of_line hf.1 hρ₂pos hsub2 hz2
    have T2 := norm_dirD_sub_le hf.1 hrU hM hv4 (mem_ball_self (by positivity)) k₁
    have e : f (x + z • (k₁ + k₂)) - f (x + (0 : ℂ) • (k₁ + k₂)) - z • (dirD k₁ f x + dirD k₂ f x)
        = (f (v + z • k₁) - f v - z • dirD k₁ f v) + z • (dirD k₁ f v - dirD k₁ f x)
          + (f (x + z • k₂) - f x - z • dirD k₂ f x) := by
      have e1 : x + z • (k₁ + k₂) = v + z • k₁ := by rw [hv]; module
      rw [e1, zero_smul, add_zero]
      simp only [smul_sub, smul_add]
      rw [← hv]; abel
    rw [e]
    have hvx : ‖v - x‖ = ‖z‖ * ‖k₂‖ := by
      rw [hv, add_sub_cancel_left, norm_smul]
    have T2' : ‖z • (dirD k₁ f v - dirD k₁ f x)‖ ≤ (8 * M * (‖k₁‖ + 1) / r ^ 2) * ‖k₂‖ * ‖z‖ ^ 2 := by
      rw [norm_smul]
      calc ‖z‖ * ‖dirD k₁ f v - dirD k₁ f x‖
          ≤ ‖z‖ * ((8 * M * (‖k₁‖ + 1) / r ^ 2) * ‖v - x‖) := by gcongr
        _ = _ := by rw [hvx]; ring
    calc _ ≤ ‖(f (v + z • k₁) - f v - z • dirD k₁ f v) + z • (dirD k₁ f v - dirD k₁ f x)‖
            + ‖f (x + z • k₂) - f x - z • dirD k₂ f x‖ := norm_add_le _ _
      _ ≤ ‖f (v + z • k₁) - f v - z • dirD k₁ f v‖ + ‖z • (dirD k₁ f v - dirD k₁ f x)‖
            + ‖f (x + z • k₂) - f x - z • dirD k₂ f x‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 8 * M * ‖z‖ ^ 2 / ρ₁ ^ 2 + (8 * M * (‖k₁‖ + 1) / r ^ 2) * ‖k₂‖ * ‖z‖ ^ 2
            + 8 * M * ‖z‖ ^ 2 / ρ₂ ^ 2 := by gcongr
      _ = C * ‖z‖ ^ 2 := by rw [hC]; ring
  have hder : HasDerivAt (fun t : ℂ => f (x + t • (k₁ + k₂)))
      (dirD k₁ f x + dirD k₂ f x) 0 := hasDerivAt_of_quad hz₀ hbound
  have h0 : HasDerivAt (fun t : ℂ => f (x + t • (k₁ + k₂))) (dirD (k₁ + k₂) f x) 0 := by
    simpa using hf.1.hasDerivAt (x := x) (h := k₁ + k₂) (ζ := 0) (by simpa using hx)
  exact h0.unique hder

end Lines

end

end NlsGge.GK38.Lib
