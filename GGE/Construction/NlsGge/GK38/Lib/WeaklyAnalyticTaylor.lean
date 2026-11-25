import NlsGge.GK38.Lib.WeaklyAnalyticGateaux

/-!
# Iterated directional derivatives (library piece L3a, part 3)

Local re-proof from Mathlib (E01-D8).  For `f : E → F` put
`iterDirD 0 f x _ = f x` and `iterDirD (n+1) f x m = iterDirD n (dirD (m 0) f) x (Fin.tail m)`, the iterated
directional derivative `∂_{m 0} ∂_{m 1} ⋯ f (x)`.  For `LineGood U f` (see `WeaklyAnalyticGateaux`):

* `iterDirD n f x` is multilinear (`iterDirDML`), obtained from the additivity `dirD_add` by induction
  (no polarization and no symmetry is needed);
* Cauchy bound `‖iterDirD n f x m‖ rⁿ ≤ M nⁿ ∏ ‖m i‖` (`norm_iterDirD_le`), same bookkeeping as in the
  repository's `norm_iteratedFDeriv_le38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Metric Set Filter Topology Function

namespace NlsGge.GK38.Lib

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Iterated directional derivative `∂_{m 0} ∂_{m 1} ⋯ ∂_{m (n-1)} f (x)`. -/
def iterDirD : (n : ℕ) → (E → F) → E → (Fin n → E) → F
  | 0, f, x, _ => f x
  | n + 1, f, x, m => iterDirD n (dirD (m 0) f) x (Fin.tail m)

section Closure

variable {U : Set E} {f g : E → F}

theorem dirD_congr (hU : IsOpen U) (hfg : EqOn f g U) (k : E) {y : E} (hy : y ∈ U) :
    dirD k f y = dirD k g y := by
  unfold dirD
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : ContinuousAt (fun t : ℂ => y + t • k) 0 := by fun_prop
  have : ∀ᶠ t : ℂ in 𝓝 0, y + t • k ∈ U := hc.eventually (hU.mem_nhds (by simpa using hy))
  filter_upwards [this] with t ht using hfg ht

theorem iterDirD_congr (hU : IsOpen U) :
    ∀ (n : ℕ) {f g : E → F}, EqOn f g U → ∀ {x : E}, x ∈ U → ∀ m : Fin n → E,
      iterDirD n f x m = iterDirD n g x m := by
  intro n
  induction n with
  | zero => intro f g hfg x hx m; exact hfg hx
  | succ n ih =>
    intro f g hfg x hx m
    exact ih (fun y hy => dirD_congr hU hfg (m 0) hy) hx _

theorem LineGood.add (hf : LineGood U f) (hg : LineGood U g) : LineGood U (fun y => f y + g y) := by
  refine ⟨fun x hx h => (hf.1 x hx h).add (hg.1 x hx h), fun x hx => ?_⟩
  obtain ⟨r₁, hr₁, M₁, h₁⟩ := hf.2 x hx
  obtain ⟨r₂, hr₂, M₂, h₂⟩ := hg.2 x hx
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, M₁ + M₂, fun y hy => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (h₁ y (ball_subset_ball (min_le_left _ _) hy))
    (h₂ y (ball_subset_ball (min_le_right _ _) hy)))

theorem LineGood.smul (hf : LineGood U f) (c : ℂ) : LineGood U (fun y => c • f y) := by
  refine ⟨fun x hx h => (hf.1 x hx h).const_smul c, fun x hx => ?_⟩
  obtain ⟨r, hr, M, h⟩ := hf.2 x hx
  refine ⟨r, hr, ‖c‖ * M, fun y hy => ?_⟩
  rw [norm_smul]; gcongr; exact h y hy

theorem dirD_add_fun (hf : LineGood U f) (hg : LineGood U g) (k : E) {y : E} (hy : y ∈ U) :
    dirD k (fun z => f z + g z) y = dirD k f y + dirD k g y := by
  unfold dirD
  exact deriv_fun_add (hf.1.at (by simpa using hy)) (hg.1.at (by simpa using hy))

theorem dirD_smul_fun (hf : LineGood U f) (c : ℂ) (k : E) {y : E} (hy : y ∈ U) :
    dirD k (fun z => c • f z) y = c • dirD k f y := by
  unfold dirD
  exact deriv_fun_const_smul c (hf.1.at (by simpa using hy))

theorem iterDirD_add (hU : IsOpen U) :
    ∀ (n : ℕ) {f g : E → F}, LineGood U f → LineGood U g → ∀ {x : E}, x ∈ U → ∀ m : Fin n → E,
      iterDirD n (fun z => f z + g z) x m = iterDirD n f x m + iterDirD n g x m := by
  intro n
  induction n with
  | zero => intro f g _ _ x _ m; rfl
  | succ n ih =>
    intro f g hf hg x hx m
    show iterDirD n (dirD (m 0) (fun z => f z + g z)) x (Fin.tail m) = _
    rw [iterDirD_congr hU n (fun y hy => dirD_add_fun hf hg (m 0) hy) hx]
    exact ih (hf.dirD hU (m 0)) (hg.dirD hU (m 0)) hx _

theorem iterDirD_smul (hU : IsOpen U) :
    ∀ (n : ℕ) {f : E → F}, LineGood U f → ∀ (c : ℂ) {x : E}, x ∈ U → ∀ m : Fin n → E,
      iterDirD n (fun z => c • f z) x m = c • iterDirD n f x m := by
  intro n
  induction n with
  | zero => intro f _ c x _ m; rfl
  | succ n ih =>
    intro f hf c x hx m
    show iterDirD n (dirD (m 0) (fun z => c • f z)) x (Fin.tail m) = _
    rw [iterDirD_congr hU n (fun y hy => dirD_smul_fun hf c (m 0) hy) hx]
    exact ih (hf.dirD hU (m 0)) c hx _

theorem iterDirD_update_add (hU : IsOpen U) :
    ∀ (n : ℕ) {f : E → F}, LineGood U f → ∀ {x : E}, x ∈ U → ∀ (m : Fin n → E) (i : Fin n) (a b : E),
      iterDirD n f x (Function.update m i (a + b))
        = iterDirD n f x (Function.update m i a) + iterDirD n f x (Function.update m i b) := by
  intro n
  induction n with
  | zero => intro f _ x _ m i; exact i.elim0
  | succ n ih =>
    intro f hf x hx m i a b
    refine Fin.cases ?_ (fun j => ?_) i
    · show iterDirD n (dirD ((Function.update m 0 (a + b)) 0) f) x _ =
        iterDirD n (dirD ((Function.update m 0 a) 0) f) x _ + iterDirD n (dirD ((Function.update m 0 b) 0) f) x _
      simp only [Function.update_self, Fin.tail_update_zero]
      rw [iterDirD_congr hU n (fun y hy => ?_) hx (m := Fin.tail m) (g := fun z => dirD a f z + dirD b f z)]
      · exact iterDirD_add hU n (hf.dirD hU a) (hf.dirD hU b) hx _
      · exact (dirD_add hU hf hy a b)
    · show iterDirD n (dirD ((Function.update m j.succ (a + b)) 0) f) x _ =
        iterDirD n (dirD ((Function.update m j.succ a) 0) f) x _
          + iterDirD n (dirD ((Function.update m j.succ b) 0) f) x _
      simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm, Fin.tail_update_succ]
      exact ih (hf.dirD hU (m 0)) hx _ j a b

theorem iterDirD_update_smul (hU : IsOpen U) :
    ∀ (n : ℕ) {f : E → F}, LineGood U f → ∀ {x : E}, x ∈ U → ∀ (m : Fin n → E) (i : Fin n) (c : ℂ) (a : E),
      iterDirD n f x (Function.update m i (c • a)) = c • iterDirD n f x (Function.update m i a) := by
  intro n
  induction n with
  | zero => intro f _ x _ m i; exact i.elim0
  | succ n ih =>
    intro f hf x hx m i c a
    refine Fin.cases ?_ (fun j => ?_) i
    · show iterDirD n (dirD ((Function.update m 0 (c • a)) 0) f) x _ =
        c • iterDirD n (dirD ((Function.update m 0 a) 0) f) x _
      simp only [Function.update_self, Fin.tail_update_zero]
      rw [iterDirD_congr hU n (fun y hy => ?_) hx (m := Fin.tail m) (g := fun z => c • dirD a f z)]
      · exact iterDirD_smul hU n (hf.dirD hU a) c hx _
      · exact dirD_smul c a f (hf.1.at (x := y) (h := a) (ζ := 0) (by simpa using hy))
    · show iterDirD n (dirD ((Function.update m j.succ (c • a)) 0) f) x _ =
        c • iterDirD n (dirD ((Function.update m j.succ a) 0) f) x _
      simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm, Fin.tail_update_succ]
      exact ih (hf.dirD hU (m 0)) hx _ j c a

/-- The multilinear map `iterDirD n f x`. -/
def iterDirDML (hU : IsOpen U) (hf : LineGood U f) {x : E} (hx : x ∈ U) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E) F where
  toFun := iterDirD n f x
  map_update_add' := fun m i a b => by
    convert iterDirD_update_add hU n hf hx m i a b
  map_update_smul' := fun m i c a => by
    convert iterDirD_update_smul hU n hf hx m i c a

end Closure

section Cauchy

variable {U : Set E}

/-- **Iterated Cauchy estimate**: `‖iterDirD n f x m‖ rⁿ ≤ M nⁿ ∏ ‖m i‖`. -/
theorem norm_iterDirD_le (hU : IsOpen U) {x : E} :
    ∀ (n : ℕ) {f : E → F}, LineGood U f → ∀ (r M : ℝ), 0 ≤ r → closedBall x r ⊆ U →
      (∀ z ∈ closedBall x r, ‖f z‖ ≤ M) → ∀ m : Fin n → E,
      ‖iterDirD n f x m‖ * r ^ n ≤ M * (n : ℝ) ^ n * ∏ i, ‖m i‖ := by
  intro n
  induction n with
  | zero =>
    intro f _ r M hr _ hb m
    simpa [iterDirD] using hb x (mem_closedBall_self hr)
  | succ n ih =>
    intro f hf r M hr hrU hb m
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb x (mem_closedBall_self hr))
    rcases hr.eq_or_lt with h0 | hpos
    · subst h0
      simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
      positivity
    set R : ℝ := r / (n + 1) with hR
    set r' : ℝ := r * n / (n + 1) with hr'
    have hn1 : (0:ℝ) < n + 1 := by positivity
    have hRpos : 0 < R := by positivity
    have hr'0 : 0 ≤ r' := by positivity
    have hrr : r' + R = r := by rw [hr', hR]; field_simp
    have hsub : closedBall x r' ⊆ closedBall x r := closedBall_subset_closedBall (by linarith)
    set k : E := m 0 with hk
    have hbd : ∀ z ∈ closedBall x r', ‖dirD k f z‖ ≤ M * ‖k‖ / R := by
      intro z hz
      by_cases hk0 : k = 0
      · simp [hk0, dirD]
      have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
      have hz' : ‖z - x‖ ≤ r' := by simpa [dist_eq_norm] using hz
      have := norm_dirD_le_of_line hf.1 (y := z) (k := k) (ρ := R / ‖k‖) (M := M)
        (by positivity) (fun w hw => by
          have hwk : ‖w • k‖ ≤ R := by
            rw [norm_smul]
            calc ‖w‖ * ‖k‖ ≤ R / ‖k‖ * ‖k‖ := by gcongr
              _ = R := by field_simp
          have hmem : z + w • k ∈ closedBall x r := by
            rw [mem_closedBall_iff_norm]
            calc ‖z + w • k - x‖ = ‖(z - x) + w • k‖ := by congr 1; abel
              _ ≤ ‖z - x‖ + ‖w • k‖ := norm_add_le _ _
              _ ≤ r := by linarith
          exact ⟨hrU hmem, hb _ hmem⟩)
      calc ‖dirD k f z‖ ≤ M / (R / ‖k‖) := this
        _ = M * ‖k‖ / R := by field_simp
    have key := ih (hf.dirD hU k) r' (M * ‖k‖ / R) hr'0 (hsub.trans hrU) hbd (Fin.tail m)
    show ‖iterDirD n (dirD k f) x (Fin.tail m)‖ * r ^ (n + 1) ≤ _
    have hnn : (0:ℝ) < (n:ℝ) ^ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact pow_pos (by exact_mod_cast hn) _
    have hrn : r ^ n * (n:ℝ) ^ n = r' ^ n * ((n:ℝ) + 1) ^ n := by
      rw [hr', div_pow, mul_pow]; field_simp
    have hprod : ∏ i : Fin (n+1), ‖m i‖ = ‖k‖ * ∏ i : Fin n, ‖Fin.tail m i‖ := by
      rw [Fin.prod_univ_succ]; rfl
    rw [hprod]
    set A := ‖iterDirD n (dirD k f) x (Fin.tail m)‖
    set P := ∏ i : Fin n, ‖Fin.tail m i‖
    set a := ‖k‖
    have hA : 0 ≤ A := norm_nonneg _
    have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have hrR : r / R = (n:ℝ) + 1 := by rw [hR]; field_simp
    have hA1 : A * r ^ (n+1) * (n:ℝ) ^ n ≤ M * ((n:ℝ) + 1) ^ (n + 1) * a * P * (n:ℝ) ^ n := by
      have e1 : A * r ^ (n+1) * (n:ℝ) ^ n = r * (A * r' ^ n) * ((n:ℝ) + 1) ^ n := by
        calc A * r ^ (n+1) * (n:ℝ) ^ n = r * A * (r ^ n * (n:ℝ) ^ n) := by ring
          _ = _ := by rw [hrn]; ring
      rw [e1]
      calc r * (A * r' ^ n) * ((n:ℝ) + 1) ^ n
          ≤ r * (M * a / R * (n:ℝ) ^ n * P) * ((n:ℝ) + 1) ^ n := by gcongr
        _ = (r / R) * M * a * (n:ℝ) ^ n * P * ((n:ℝ) + 1) ^ n := by ring
        _ = _ := by rw [hrR]; ring
    have hA2 : A * r ^ (n+1) ≤ M * ((n:ℝ) + 1) ^ (n + 1) * a * P :=
      le_of_mul_le_mul_right hA1 hnn
    push_cast
    calc _ ≤ M * ((n:ℝ) + 1) ^ (n + 1) * a * P := hA2
      _ = _ := by ring

end Cauchy

end

end NlsGge.GK38.Lib
