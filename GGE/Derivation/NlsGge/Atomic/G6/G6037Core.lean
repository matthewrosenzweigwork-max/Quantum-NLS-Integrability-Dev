import Mathlib
import NlsGge.Atomic.G6.G6037Host
import NlsGge.Atomic.G4.G4004
import NlsGge.GK38.Lib.ParamProductsRoot

/- G6037 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6037Core.lean,
   namespace NlsGge.ThirdConsultation.G6037S.  SUPPORT (no packet increment): G6037_of = the G6-037 head body
   (followup13 STATEMENTS/G6.md, verbatim), unconditional.  Route (Pro "CORRECTED" head: finite active head kept as
   parameters, only zero-centred inactive S coordinates squared):
   * shrink to a sup-norm ball B = ball x₀ ρ on which f is analytic, S-even and bounded;
   * flips of S coordinates preserve B (x₀ vanishes on S), so f y = f x whenever y and x agree off S and have equal
     squares on S (f_of_sq; induction over Finset of flipped coordinates);
   * g := f ∘ root, root w = (√w_j on S, w_j off S); V = product of discs (‖w_j‖ < ρ² on S, dist < ρ off S);
     f = g ∘ squareInactive S on B;
   * analyticity of g on V: landed G4-004 (weak analyticity + local boundedness).  Along a line ζ ↦ w + ζh,
     g = f ∘ lroot p (branches √p_j·√(w_j/p_j), p_j ≠ 0; √w_j, p_j = 0) is differentiable off a finite set and
     continuous at 0; Mathlib's removable-singularity theorem gives analyticity at 0.
   Mathlib names verified in the pinned tree (d13f23b7). -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6037S
noncomputable section

/-! ### Square roots -/

theorem sqrt_sq' (z : ℂ) : Complex.sqrt z ^ 2 = z := NlsGge.GK38.Lib.sqrt_sq z

theorem norm_sqrt_sq (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by rw [← norm_pow, sqrt_sq']

theorem norm_sqrt_lt {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (h : ‖z‖ < ρ ^ 2) : ‖Complex.sqrt z‖ < ρ :=
  lt_of_pow_lt_pow_left₀ 2 hρ.le (by rw [norm_sqrt_sq]; exact h)

theorem continuousAt_sqrt_zero : ContinuousAt Complex.sqrt 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε ^ 2, by positivity, fun {z} hz => ?_⟩
  rw [dist_zero_right] at hz
  rw [Complex.sqrt_zero, dist_zero_right]
  exact norm_sqrt_lt hε hz

/-! ### Sign flips -/

variable {d : ℕ}

def flipSet (T : Finset (Fin d)) (x : Fin d → ℂ) : Fin d → ℂ :=
  fun j => if j ∈ T then -x j else x j

theorem flipSet_mem (S : Finset (Fin d)) (x₀ : Fin d → ℂ) (ρ : ℝ) (hzero : ∀ j ∈ S, x₀ j = 0)
    (hρ : 0 < ρ) {T : Finset (Fin d)} (hT : T ⊆ S) {x : Fin d → ℂ} (hx : x ∈ ball x₀ ρ) :
    flipSet T x ∈ ball x₀ ρ := by
  rw [mem_ball, dist_pi_lt_iff hρ] at hx ⊢
  intro j
  unfold flipSet
  split_ifs with hj
  · have h := hx j
    rw [hzero j (hT hj), dist_zero_right] at h ⊢
    rwa [norm_neg]
  · exact hx j

theorem f_flipSet (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (x₀ : Fin d → ℂ) (ρ : ℝ)
    (hzero : ∀ j ∈ S, x₀ j = 0) (hρ : 0 < ρ) (hev : finiteCoordinateEvenOn f S (ball x₀ ρ)) :
    ∀ T : Finset (Fin d), T ⊆ S → ∀ x ∈ ball x₀ ρ, f (flipSet T x) = f x := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ x _
    have : flipSet (∅ : Finset (Fin d)) x = x := by funext j; simp [flipSet]
    rw [this]
  | insert a T ha ih =>
    intro hT x hx
    have hT' : T ⊆ S := (Finset.subset_insert a T).trans hT
    have haS : a ∈ S := hT (Finset.mem_insert_self a T)
    have heq : flipSet (insert a T) x = Function.update (flipSet T x) a (-(flipSet T x a)) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [flipSet, ha]
      · simp [flipSet, Function.update_of_ne hj, hj]
    rw [heq, hev _ (flipSet_mem S x₀ ρ hzero hρ hT' hx) a haS, ih hT' x hx]

theorem f_of_sq (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (x₀ : Fin d → ℂ) (ρ : ℝ)
    (hzero : ∀ j ∈ S, x₀ j = 0) (hρ : 0 < ρ) (hev : finiteCoordinateEvenOn f S (ball x₀ ρ))
    {x y : Fin d → ℂ} (hx : x ∈ ball x₀ ρ) (hoff : ∀ j, j ∉ S → y j = x j)
    (hon : ∀ j ∈ S, y j ^ 2 = x j ^ 2) : f y = f x := by
  classical
  have hy : y = flipSet (S.filter (fun j => y j ≠ x j)) x := by
    funext j
    unfold flipSet
    by_cases hjS : j ∈ S
    · by_cases hne : y j = x j
      · rw [if_neg (by simp [hne])]; exact hne
      · rw [if_pos (by simp [hjS, hne])]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hon j hjS) with h | h
        · exact absurd h hne
        · exact h
    · rw [if_neg (by simp [hjS])]; exact hoff j hjS
  rw [hy]
  exact f_flipSet S f x₀ ρ hzero hρ hev _ (Finset.filter_subset _ _) x hx

/-! ### Roots, the target set and the descended function -/

def root (S : Finset (Fin d)) (w : Fin d → ℂ) : Fin d → ℂ :=
  fun j => if j ∈ S then Complex.sqrt (w j) else w j

def lroot (S : Finset (Fin d)) (p w : Fin d → ℂ) : Fin d → ℂ :=
  fun j => if j ∈ S then
    (if p j = 0 then Complex.sqrt (w j) else Complex.sqrt (p j) * Complex.sqrt (w j / p j))
  else w j

def Vset (S : Finset (Fin d)) (x₀ : Fin d → ℂ) (ρ : ℝ) : Set (Fin d → ℂ) :=
  ⋂ j : Fin d, {w | (j ∈ S → ‖w j‖ < ρ ^ 2) ∧ (j ∉ S → dist (w j) (x₀ j) < ρ)}

theorem mem_Vset {S : Finset (Fin d)} {x₀ : Fin d → ℂ} {ρ : ℝ} {w : Fin d → ℂ} :
    w ∈ Vset S x₀ ρ ↔ ∀ j, (j ∈ S → ‖w j‖ < ρ ^ 2) ∧ (j ∉ S → dist (w j) (x₀ j) < ρ) := by
  simp [Vset]

theorem Vset_open (S : Finset (Fin d)) (x₀ : Fin d → ℂ) (ρ : ℝ) : IsOpen (Vset S x₀ ρ) := by
  refine isOpen_iInter_of_finite (fun j => ?_)
  by_cases hj : j ∈ S
  · simp only [hj, true_implies, not_true_eq_false, false_implies, and_true]
    exact isOpen_lt ((continuous_apply j).norm) continuous_const
  · simp only [hj, false_implies, not_false_eq_true, true_implies, true_and]
    exact isOpen_lt ((continuous_apply j).dist continuous_const) continuous_const

theorem root_mem (S : Finset (Fin d)) (x₀ : Fin d → ℂ) (ρ : ℝ) (hzero : ∀ j ∈ S, x₀ j = 0)
    (hρ : 0 < ρ) {w : Fin d → ℂ} (hw : w ∈ Vset S x₀ ρ) : root S w ∈ ball x₀ ρ := by
  rw [mem_Vset] at hw
  rw [mem_ball, dist_pi_lt_iff hρ]
  intro j
  unfold root
  split_ifs with hj
  · rw [hzero j hj, dist_zero_right]; exact norm_sqrt_lt hρ ((hw j).1 hj)
  · exact (hw j).2 hj

theorem sq_mem (S : Finset (Fin d)) (x₀ : Fin d → ℂ) (ρ : ℝ) (hzero : ∀ j ∈ S, x₀ j = 0)
    (hρ : 0 < ρ) {x : Fin d → ℂ} (hx : x ∈ ball x₀ ρ) : squareInactive S x ∈ Vset S x₀ ρ := by
  rw [mem_ball, dist_pi_lt_iff hρ] at hx
  rw [mem_Vset]
  intro j
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · have h := hx j
    rw [hzero j hj, dist_zero_right] at h
    simp only [squareInactive, hj, if_true, norm_pow]
    exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  · simp only [squareInactive, hj, if_false]; exact hx j

theorem lroot_sq (S : Finset (Fin d)) (p w : Fin d → ℂ) (j : Fin d) (hj : j ∈ S) :
    lroot S p w j ^ 2 = w j := by
  unfold lroot
  rw [if_pos hj]
  split_ifs with hp
  · exact sqrt_sq' _
  · rw [mul_pow, sqrt_sq', sqrt_sq']; field_simp

theorem lroot_self (S : Finset (Fin d)) (p : Fin d → ℂ) : lroot S p p = root S p := by
  funext j
  unfold lroot root
  split_ifs with hj hp
  · rfl
  · rw [div_self hp, Complex.sqrt_one, mul_one]
  · rfl

/-- The descended function. -/
def gfun (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (w : Fin d → ℂ) : ℂ := f (root S w)

theorem g_eq_lroot (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (x₀ : Fin d → ℂ) (ρ : ℝ)
    (hzero : ∀ j ∈ S, x₀ j = 0) (hρ : 0 < ρ) (hev : finiteCoordinateEvenOn f S (ball x₀ ρ))
    (p : Fin d → ℂ) {w : Fin d → ℂ} (hw : w ∈ Vset S x₀ ρ) :
    gfun S f w = f (lroot S p w) := by
  unfold gfun
  refine (f_of_sq S f x₀ ρ hzero hρ hev (root_mem S x₀ ρ hzero hρ hw) (fun j hj => ?_) (fun j hj => ?_)).symm
  · simp [lroot, root, hj]
  · rw [lroot_sq S p w j hj]; simp [root, hj, sqrt_sq']

/-! ### One-variable analyticity along lines -/

theorem lroot_line_differentiableAt (S : Finset (Fin d)) (w h : Fin d → ℂ) (ζ₀ : ℂ)
    (hgood : ∀ j ∈ S, (w + ζ₀ • h) j = 0 → h j = 0) :
    DifferentiableAt ℂ (fun ζ : ℂ => lroot S (w + ζ₀ • h) (w + ζ • h)) ζ₀ := by
  rw [differentiableAt_pi]
  intro j
  have hlin : DifferentiableAt ℂ (fun ζ : ℂ => w j + ζ * h j) ζ₀ :=
    (differentiableAt_const _).add (differentiableAt_id.mul (differentiableAt_const _))
  simp only [lroot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j ∈ S
  · simp only [hj, if_true]
    by_cases hp : w j + ζ₀ * h j = 0
    · simp only [hp, if_true]
      have hh : h j = 0 := hgood j hj (by simp [hp])
      simp only [hh, mul_zero, add_zero]
      exact differentiableAt_const _
    · simp only [hp, if_false]
      refine (differentiableAt_const _).mul ?_
      have hq : DifferentiableAt ℂ (fun ζ : ℂ => (w j + ζ * h j) / (w j + ζ₀ * h j)) ζ₀ :=
        hlin.div_const _
      have h1 : (w j + ζ₀ * h j) / (w j + ζ₀ * h j) ∈ Complex.slitPlane := by
        rw [div_self hp]; exact Complex.one_mem_slitPlane
      exact (Complex.differentiableAt_sqrt h1).comp ζ₀ hq
  · simp only [hj, if_false]
    exact hlin

theorem lroot_line_continuousAt (S : Finset (Fin d)) (w h : Fin d → ℂ) :
    ContinuousAt (fun ζ : ℂ => lroot S w (w + ζ • h)) 0 := by
  rw [continuousAt_pi]
  intro j
  have hlin : Continuous (fun ζ : ℂ => w j + ζ * h j) := by continuity
  simp only [lroot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j ∈ S
  · simp only [hj, if_true]
    by_cases hp : w j = 0
    · simp only [hp, if_true, zero_add]
      exact continuousAt_sqrt_zero.comp_of_eq (by fun_prop) (by simp)
    · simp only [hp, if_false]
      refine continuousAt_const.mul ?_
      have h1 : (w j + 0 * h j) / w j ∈ Complex.slitPlane := by
        rw [zero_mul, add_zero, div_self hp]; exact Complex.one_mem_slitPlane
      exact ContinuousAt.comp (f := fun ζ : ℂ => (w j + ζ * h j) / w j) (x := (0 : ℂ))
        (Complex.differentiableAt_sqrt h1).continuousAt ((hlin.div_const (w j)).continuousAt)
  · simp only [hj, if_false]
    exact hlin.continuousAt

theorem eventually_ne_finite (c : ℂ) : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ζ ≠ c := by
  by_cases hc : c = 0
  · subst hc; exact eventually_nhdsWithin_of_forall (fun ζ hζ => hζ)
  · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hc))

theorem line_analytic (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (x₀ : Fin d → ℂ) (ρ : ℝ)
    (hzero : ∀ j ∈ S, x₀ j = 0) (hρ : 0 < ρ) (hev : finiteCoordinateEvenOn f S (ball x₀ ρ))
    (hA : AnalyticOnNhd ℂ f (ball x₀ ρ)) {w : Fin d → ℂ} (hw : w ∈ Vset S x₀ ρ) (h : Fin d → ℂ) :
    AnalyticAt ℂ (fun ζ : ℂ => gfun S f (w + ζ • h)) 0 := by
  have hcont_aff : Continuous (fun ζ : ℂ => w + ζ • h) := by continuity
  have hV : ∀ ζ₀ : ℂ, w + ζ₀ • h ∈ Vset S x₀ ρ →
      ∀ᶠ ζ in 𝓝 ζ₀, w + ζ • h ∈ Vset S x₀ ρ := fun ζ₀ hζ₀ =>
    hcont_aff.continuousAt.eventually_mem ((Vset_open S x₀ ρ).mem_nhds hζ₀)
  have hloc : ∀ ζ₀ : ℂ, w + ζ₀ • h ∈ Vset S x₀ ρ →
      (fun ζ : ℂ => f (lroot S (w + ζ₀ • h) (w + ζ • h))) =ᶠ[𝓝 ζ₀] fun ζ => gfun S f (w + ζ • h) :=
    fun ζ₀ hζ₀ => (hV ζ₀ hζ₀).mono fun ζ hζ =>
      (g_eq_lroot S f x₀ ρ hzero hρ hev (w + ζ₀ • h) hζ).symm
  have hdiff : ∀ ζ₀ : ℂ, w + ζ₀ • h ∈ Vset S x₀ ρ →
      (∀ j ∈ S, (w + ζ₀ • h) j = 0 → h j = 0) →
      DifferentiableAt ℂ (fun ζ : ℂ => gfun S f (w + ζ • h)) ζ₀ := by
    intro ζ₀ hζ₀ hgood
    have hfx : DifferentiableAt ℂ f (lroot S (w + ζ₀ • h) (w + ζ₀ • h)) := by
      rw [lroot_self]
      exact (hA _ (root_mem S x₀ ρ hzero hρ hζ₀)).differentiableAt
    have hcomp : DifferentiableAt ℂ (fun ζ : ℂ => f (lroot S (w + ζ₀ • h) (w + ζ • h))) ζ₀ :=
      hfx.comp ζ₀ (lroot_line_differentiableAt S w h ζ₀ hgood)
    exact hcomp.congr_of_eventuallyEq (hloc ζ₀ hζ₀).symm
  have hw0 : w + (0 : ℂ) • h = w := by simp
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hE1 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), w + ζ • h ∈ Vset S x₀ ρ :=
      nhdsWithin_le_nhds (hV 0 (by rw [hw0]; exact hw))
    have hE2 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∀ j ∈ S, h j ≠ 0 → ζ ≠ -w j / h j :=
      (eventually_all_finset S).2 fun j _ =>
        (eventually_ne_finite (-w j / h j)).mono fun ζ hζ _ => hζ
    filter_upwards [hE1, hE2] with ζ hζV hζZ
    refine hdiff ζ hζV (fun j hj hzj => ?_)
    by_contra hh
    apply hζZ j hj hh
    rw [eq_div_iff hh]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzj
    linear_combination hzj
  · have hfx : ContinuousAt f (lroot S w (w + (0 : ℂ) • h)) := by
      rw [hw0, lroot_self]
      exact (hA _ (root_mem S x₀ ρ hzero hρ hw)).continuousAt
    have hc : ContinuousAt (fun ζ : ℂ => f (lroot S w (w + ζ • h))) 0 :=
      hfx.comp (f := fun ζ : ℂ => lroot S w (w + ζ • h)) (lroot_line_continuousAt S w h)
    have heq := hloc 0 (by rw [hw0]; exact hw)
    rw [hw0] at heq
    exact hc.congr heq

theorem g_analytic (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ) (x₀ : Fin d → ℂ) (ρ : ℝ)
    (hzero : ∀ j ∈ S, x₀ j = 0) (hρ : 0 < ρ) (hev : finiteCoordinateEvenOn f S (ball x₀ ρ))
    (hA : AnalyticOnNhd ℂ f (ball x₀ ρ)) (M : ℝ) (hM : ∀ x ∈ ball x₀ ρ, ‖f x‖ ≤ M) :
    AnalyticOnNhd ℂ (gfun S f) (Vset S x₀ ρ) := by
  apply NlsGge.Atomic.G4.analyticOnNhd_of_weakAnalytic_locallyBounded (Vset_open S x₀ ρ)
  · intro w hw h ℓ
    exact (ℓ.analyticAt _).comp (line_analytic S f x₀ ρ hzero hρ hev hA hw h)
  · intro w hw
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (Vset_open S x₀ ρ) w hw
    exact ⟨r, hr, M, fun y hy => hM _ (root_mem S x₀ ρ hzero hρ (hsub hy))⟩

theorem G6037_of (d : ℕ) (S : Finset (Fin d)) (f : (Fin d → ℂ) → ℂ)
    (x₀ : Fin d → ℂ) (hzero : ∀ j ∈ S, x₀ j = 0)
    (han : AnalyticAt ℂ f x₀)
    (heven : ∃ U : Set (Fin d → ℂ), U ∈ 𝓝 x₀ ∧ finiteCoordinateEvenOn f S U) :
  ∃ (U V : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
    IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ squareInactive S x₀ ∈ V ∧
    AnalyticOnNhd ℂ g V ∧ Set.MapsTo (squareInactive S) U V ∧
    ∀ x ∈ U, f x = g (squareInactive S x) := by
  obtain ⟨r₁, hr₁, hA₁⟩ := han.exists_ball_analyticOnNhd
  obtain ⟨U₀, hU₀, hev₀⟩ := heven
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU₀
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 han.continuousAt 1 one_pos
  set ρ := min r₁ (min ε δ) with hρdef
  have hρ : 0 < ρ := lt_min hr₁ (lt_min hε hδ)
  have hsub1 : ball x₀ ρ ⊆ ball x₀ r₁ := ball_subset_ball (min_le_left _ _)
  have hsub2 : ball x₀ ρ ⊆ ball x₀ ε :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub3 : ball x₀ ρ ⊆ ball x₀ δ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hA : AnalyticOnNhd ℂ f (ball x₀ ρ) := hA₁.mono hsub1
  have hev : finiteCoordinateEvenOn f S (ball x₀ ρ) :=
    fun x hx j hj => hev₀ x (hεU (hsub2 hx)) j hj
  have hM : ∀ x ∈ ball x₀ ρ, ‖f x‖ ≤ ‖f x₀‖ + 1 := by
    intro x hx
    have h1 := hδf (hsub3 hx)
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (f x) (f x₀)
    linarith
  have hx₀ : x₀ ∈ ball x₀ ρ := mem_ball_self hρ
  refine ⟨ball x₀ ρ, Vset S x₀ ρ, gfun S f, isOpen_ball, hx₀, Vset_open S x₀ ρ,
    sq_mem S x₀ ρ hzero hρ hx₀, g_analytic S f x₀ ρ hzero hρ hev hA _ hM,
    fun x hx => sq_mem S x₀ ρ hzero hρ hx, fun x hx => ?_⟩
  unfold gfun
  refine (f_of_sq S f x₀ ρ hzero hρ hev hx (fun j hj => ?_) (fun j hj => ?_)).symm
  · simp [root, squareInactive, hj]
  · simp [root, squareInactive, hj, sqrt_sq']

end
end NlsGge.ThirdConsultation.G6037S
