import NlsGge.Hierarchy.RiccatiPeriodicSolutionAsymptotic38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core

/-! # R3c piece P2: uniform Riccati existence and Born remainders

For a continuous 1-periodic `U` with `‖U‖_∞ ≤ A` and `η ≥ max (4A) 1` there is a continuous periodic
solution `Γ` of `Γ' = -2ηΓ + Ū - UΓ²` with `‖Γ - R Ū‖_∞ ≤ A³/(4η³)` (constants in `A` only), and the
Born remainders `Γ - G₁`, `Γ - G₁ - G₃`, `Γ - G₁ - G₃ - G₅` obey sup-norm bounds in `A` and `η`. -/

/-- Sup bound of the resolvent, with the bound written as `c * η`. -/
lemma resolv38_bound_scaled_r3c {η c : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hB : ∀ x, ‖g x‖ ≤ c * η) (x : ℝ) : ‖resolv38 η g x‖ ≤ c / 2 := by
  have h := resolv38_bound hη hg hB x
  have e : c * η / (2 * η) = c / 2 := by field_simp
  rwa [e] at h

lemma resolv38_continuous_r3c {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) : Continuous (resolv38 η g) :=
  continuous_iff_continuousAt.mpr fun x => (resolv38_hasDerivAt hη hg hB x).continuousAt

/-- Basic facts on `G₁ = R Ū` when `‖U‖_∞ ≤ t * η`. -/
lemma g1_facts_r3c {η t : ℝ} (hη : 0 < η) {U : ℝ → ℂ} (hU : Continuous U)
    (hp : Function.Periodic U 1) (hA : ∀ x, ‖U x‖ ≤ t * η) :
    Continuous (resolv38 η (fun y => star (U y))) ∧
    Function.Periodic (resolv38 η (fun y => star (U y))) 1 ∧
    (∀ x, HasDerivAt (resolv38 η (fun y => star (U y)))
      (-(2 * (η : ℂ)) * resolv38 η (fun y => star (U y)) x + star (U x)) x) ∧
    ∀ x, ‖resolv38 η (fun y => star (U y)) x‖ ≤ t / 2 := by
  have hc : Continuous (fun y => star (U y)) := hU.star
  have hb : ∀ x, ‖star (U x)‖ ≤ t * η := fun x => by rw [norm_star]; exact hA x
  have hper : Function.Periodic (fun y => star (U y)) 1 := fun x => by
    show star (U (x + 1)) = star (U x)
    rw [hp x]
  exact ⟨resolv38_continuous_r3c hη hc hb, resolv38_periodic hper,
    fun x => resolv38_hasDerivAt hη hc hb x, fun x => resolv38_bound_scaled_r3c hη hc hb x⟩

lemma t_cube_le_r3c {t : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 1 / 4) : t ^ 3 ≤ t / 16 := by
  have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left ht2 ht0]

theorem riccati_exists_uniform38 {η A : ℝ} (U : ℝ → ℂ) (hU : Continuous U)
    (hp : Function.Periodic U 1) (hA0 : 0 ≤ A) (hA : ∀ x, ‖U x‖ ≤ A) (hη : max (4*A) 1 ≤ η) :
    ∃ Γ : ℝ → ℂ, Continuous Γ ∧ Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (U x) - U x * Γ x ^ 2) x) ∧
      ∀ x, ‖Γ x - resolv38 η (fun y => star (U y)) x‖ ≤ A^3 / (4*η^3) := by
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
  have hη4 : 4 * A ≤ η := (le_max_left _ _).trans hη
  have hηpos : 0 < η := by linarith
  obtain ⟨t, ht0, ht4, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 / 4 ∧ A = t * η :=
    ⟨A / η, div_nonneg hA0 hηpos.le, by rw [div_le_iff₀ hηpos]; linarith, by field_simp⟩
  obtain ⟨hGc, hGp, hGd, hGb⟩ := g1_facts_r3c hηpos hU hp hA
  set G1 : ℝ → ℂ := resolv38 η (fun y => star (U y)) with hG1
  have hρc : Continuous (fun y => U y * G1 y ^ 2) := by fun_prop
  have hρp : Function.Periodic (fun y => U y * G1 y ^ 2) 1 := fun x => by
    show U (x + 1) * G1 (x + 1) ^ 2 = U x * G1 x ^ 2
    rw [hp x, hGp x]
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0 (by linarith)
  obtain ⟨R, hRc, hRp, hRb, hRd⟩ := riccati_correction_exists38 hηpos (u := U) (S := G1)
    (ρ := fun y => U y * G1 y ^ 2) hU hGc hρc hp hGp hρp (Mu := t * η) (by positivity) hA
    (fun x => (hGb x).trans (by linarith)) (by linarith) (δ := t ^ 3 / 4) (by positivity)
    (by linarith) (fun x => by
      rw [norm_mul, norm_pow]
      calc ‖U x‖ * ‖G1 x‖ ^ 2 ≤ (t * η) * (t / 2) ^ 2 :=
            mul_le_mul (hA x) (pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2) (by positivity)
              (by positivity)
        _ = η * (t ^ 3 / 4) := by ring)
  have e3 : (t * η) ^ 3 / (4 * η ^ 3) = t ^ 3 / 4 := by field_simp
  refine ⟨fun x => G1 x + R x, hGc.add hRc, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · show G1 (x + 1) + R (x + 1) = G1 x + R x
    rw [hGp x, hRp x]
  · have h := (hGd x).add (hRd x)
    convert h using 1
    beta_reduce
    ring
  · rw [e3]
    have : G1 x + R x - G1 x = R x := by ring
    simp only [this]
    exact hRb x

/-- The abstract form of `born_remainder38`, with `G₁ G₃ G₅` given by defining identities. -/
theorem born_core_r3c {η A : ℝ} (U Γ G1 G3 G5 : ℝ → ℂ) (hU : Continuous U)
    (hp : Function.Periodic U 1) (hA0 : 0 ≤ A) (hA : ∀ x, ‖U x‖ ≤ A) (hη : max (4*A) 1 ≤ η)
    (hΓc : Continuous Γ) (hΓp : Function.Periodic Γ 1)
    (hΓd : ∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (U x) - U x * Γ x ^ 2) x)
    (hG1 : ∀ x, G1 x = resolv38 η (fun y => star (U y)) x)
    (hΓb : ∀ x, ‖Γ x - G1 x‖ ≤ A^3 / (4*η^3))
    (hG3 : ∀ x, G3 x = -resolv38 η (fun y => U y * G1 y ^ 2) x)
    (hG5 : ∀ x, G5 x = -resolv38 η (fun y => 2 * U y * G1 y * G3 y) x) :
    (∀ x, Γ x - G1 x = -resolv38 η (fun y => U y * Γ y ^ 2) x) ∧
    (∀ x, ‖Γ x - G1 x - G3 x‖ ≤ A^5 / η^5) ∧
    (∀ x, ‖Γ x - G1 x - G3 x - G5 x‖ ≤ A^7 / η^7) := by
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
  have hη4 : 4 * A ≤ η := (le_max_left _ _).trans hη
  have hηpos : 0 < η := by linarith
  obtain ⟨t, ht0, ht4, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 / 4 ∧ A = t * η :=
    ⟨A / η, div_nonneg hA0 hηpos.le, by rw [div_le_iff₀ hηpos]; linarith, by field_simp⟩
  have hG1f : G1 = resolv38 η (fun y => star (U y)) := funext hG1
  obtain ⟨hGc, hGp, hGd, hGb⟩ := g1_facts_r3c hηpos hU hp hA
  rw [← hG1f] at hGc hGp hGd hGb
  have e3 : (t * η) ^ 3 / (4 * η ^ 3) = t ^ 3 / 4 := by field_simp
  have e5 : (t * η) ^ 5 / η ^ 5 = t ^ 5 := by field_simp
  have e7 : (t * η) ^ 7 / η ^ 7 = t ^ 7 := by field_simp
  have hD : ∀ x, ‖Γ x - G1 x‖ ≤ t ^ 3 / 4 := fun x => by rw [← e3]; exact hΓb x
  have ht3 := t_cube_le_r3c ht0 ht4
  have hΓn : ∀ x, ‖Γ x‖ ≤ t := fun x => by
    have h1 : Γ x = (Γ x - G1 x) + G1 x := by ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    have := hD x
    have := hGb x
    linarith
  -- the three integrands
  have hf₁c : Continuous (fun y => U y * Γ y ^ 2) := by fun_prop
  have hf₁p : Function.Periodic (fun y => U y * Γ y ^ 2) 1 := fun x => by
    show U (x + 1) * Γ (x + 1) ^ 2 = U x * Γ x ^ 2
    rw [hp x, hΓp x]
  have hf₁b : ∀ x, ‖U x * Γ x ^ 2‖ ≤ (t * t ^ 2) * η := fun x => by
    rw [norm_mul, norm_pow]
    calc ‖U x‖ * ‖Γ x‖ ^ 2 ≤ (t * η) * t ^ 2 :=
          mul_le_mul (hA x) (pow_le_pow_left₀ (norm_nonneg _) (hΓn x) 2) (by positivity)
            (by positivity)
      _ = (t * t ^ 2) * η := by ring
  have hf₂c : Continuous (fun y => U y * G1 y ^ 2) := by fun_prop
  have hf₂p : Function.Periodic (fun y => U y * G1 y ^ 2) 1 := fun x => by
    show U (x + 1) * G1 (x + 1) ^ 2 = U x * G1 x ^ 2
    rw [hp x, hGp x]
  have hf₂b : ∀ x, ‖U x * G1 x ^ 2‖ ≤ (t * (t / 2) ^ 2) * η := fun x => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hA x) (pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2) (by positivity)
      (by positivity) |>.trans_eq (by ring)
  -- claim 1
  have hW1 : ∀ x, Γ x - G1 x = -resolv38 η (fun y => U y * Γ y ^ 2) x := by
    have hd1 : ∀ x, HasDerivAt (fun y => (Γ y - G1 y) - (-resolv38 η (fun y => U y * Γ y ^ 2) y))
        (-(2 * (η : ℂ)) * ((Γ x - G1 x) - (-resolv38 η (fun y => U y * Γ y ^ 2) x))) x := by
      intro x
      have h1 := (hΓd x).sub (hGd x)
      have h2 := (resolv38_hasDerivAt hηpos hf₁c hf₁b x).neg
      have h3 := h1.sub h2
      convert h3 using 1
      ring
    have hz := periodic_ode_zero hηpos hd1 (fun x => by
      simp only [hΓp x, hGp x, resolv38_periodic hf₁p x])
    exact fun x => sub_eq_zero.mp (hz x)
  -- claim 2
  have hh₂c : Continuous (fun y => U y * Γ y ^ 2 - U y * G1 y ^ 2) := hf₁c.sub hf₂c
  have hh₂b : ∀ x, ‖U x * Γ x ^ 2 - U x * G1 x ^ 2‖ ≤ (3 / 8 * t ^ 5) * η := fun x => by
    have e : U x * Γ x ^ 2 - U x * G1 x ^ 2 = U x * ((Γ x - G1 x) * (Γ x + G1 x)) := by ring
    rw [e, norm_mul, norm_mul]
    have h1 : ‖Γ x + G1 x‖ ≤ 3 * t / 2 :=
      (norm_add_le _ _).trans (by linarith [hΓn x, hGb x])
    have h2 : ‖Γ x - G1 x‖ * ‖Γ x + G1 x‖ ≤ t ^ 3 / 4 * (3 * t / 2) :=
      mul_le_mul (hD x) h1 (norm_nonneg _) (by positivity)
    calc ‖U x‖ * (‖Γ x - G1 x‖ * ‖Γ x + G1 x‖) ≤ (t * η) * (t ^ 3 / 4 * (3 * t / 2)) :=
          mul_le_mul (hA x) h2 (by positivity) (by positivity)
      _ = (3 / 8 * t ^ 5) * η := by ring
  have hE2 : ∀ x, Γ x - G1 x - G3 x =
      -resolv38 η (fun y => U y * Γ y ^ 2 - U y * G1 y ^ 2) x := fun x => by
    rw [hW1 x, hG3 x, resolv38_sub hηpos hf₁c hf₂c hf₁b hf₂b x]
    ring
  have hE2b : ∀ x, ‖Γ x - G1 x - G3 x‖ ≤ t ^ 5 := fun x => by
    rw [hE2 x, norm_neg]
    have := resolv38_bound_scaled_r3c hηpos hh₂c hh₂b x
    have h5 : 0 ≤ t ^ 5 := by positivity
    linarith
  -- claim 3
  have hG3c : Continuous G3 := by
    have : G3 = fun x => -resolv38 η (fun y => U y * G1 y ^ 2) x := funext hG3
    rw [this]
    exact (resolv38_continuous_r3c hηpos hf₂c hf₂b).neg
  have hG3p : Function.Periodic G3 1 := fun x => by
    rw [hG3 x, hG3 (x + 1), resolv38_periodic hf₂p x]
  have hG3b : ∀ x, ‖G3 x‖ ≤ (t * (t / 2) ^ 2) / 2 := fun x => by
    rw [hG3 x, norm_neg]
    exact resolv38_bound_scaled_r3c hηpos hf₂c hf₂b x
  have hf₃c : Continuous (fun y => 2 * U y * G1 y * G3 y) := by fun_prop
  have hf₃b : ∀ x, ‖2 * U x * G1 x * G3 x‖ ≤ (t ^ 5 / 8) * η := fun x => by
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [norm_mul, norm_mul, norm_mul, h2]
    have h3 : ‖G3 x‖ ≤ t ^ 3 / 8 := (hG3b x).trans (le_of_eq (by ring))
    calc 2 * ‖U x‖ * ‖G1 x‖ * ‖G3 x‖ ≤ 2 * (t * η) * (t / 2) * (t ^ 3 / 8) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hA x) (by norm_num))
            (hGb x) (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = (t ^ 5 / 8) * η := by ring
  have hh₃c : Continuous (fun y => (U y * Γ y ^ 2 - U y * G1 y ^ 2) - 2 * U y * G1 y * G3 y) :=
    hh₂c.sub hf₃c
  have hh₃b : ∀ x, ‖(U x * Γ x ^ 2 - U x * G1 x ^ 2) - 2 * U x * G1 x * G3 x‖ ≤
      (17 / 16 * t ^ 7) * η := fun x => by
    have e : (U x * Γ x ^ 2 - U x * G1 x ^ 2) - 2 * U x * G1 x * G3 x =
        U x * (2 * G1 x * (Γ x - G1 x - G3 x) + (Γ x - G1 x) ^ 2) := by ring
    rw [e, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h1 : ‖2 * G1 x * (Γ x - G1 x - G3 x) + (Γ x - G1 x) ^ 2‖ ≤ 17 / 16 * t ^ 6 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, h2]
      have a1 : 2 * ‖G1 x‖ * ‖Γ x - G1 x - G3 x‖ ≤ 2 * (t / 2) * t ^ 5 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hGb x) (by norm_num)) (hE2b x) (norm_nonneg _)
          (by positivity)
      have a2 : ‖Γ x - G1 x‖ ^ 2 ≤ (t ^ 3 / 4) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hD x) 2
      nlinarith [a1, a2]
    calc ‖U x‖ * ‖2 * G1 x * (Γ x - G1 x - G3 x) + (Γ x - G1 x) ^ 2‖
        ≤ (t * η) * (17 / 16 * t ^ 6) := mul_le_mul (hA x) h1 (norm_nonneg _) (by positivity)
      _ = (17 / 16 * t ^ 7) * η := by ring
  have hE3 : ∀ x, Γ x - G1 x - G3 x - G5 x =
      -resolv38 η (fun y => (U y * Γ y ^ 2 - U y * G1 y ^ 2) - 2 * U y * G1 y * G3 y) x :=
    fun x => by
      rw [hE2 x, hG5 x,
        resolv38_sub hηpos hh₂c hf₃c hh₂b hf₃b x]
      ring
  refine ⟨hW1, fun x => ?_, fun x => ?_⟩
  · rw [e5]; exact hE2b x
  · rw [e7, hE3 x, norm_neg]
    have := resolv38_bound_scaled_r3c hηpos hh₃c hh₃b x
    have h7 : 0 ≤ t ^ 7 := by positivity
    linarith

/-- L7: Born remainders, sup norm, constants in `A` only -/
theorem born_remainder38 {η A : ℝ} (U Γ : ℝ → ℂ) (hU : Continuous U) (hp : Function.Periodic U 1)
    (hA0 : 0 ≤ A) (hA : ∀ x, ‖U x‖ ≤ A) (hη : max (4*A) 1 ≤ η)
    (hΓc : Continuous Γ) (hΓp : Function.Periodic Γ 1)
    (hΓd : ∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (U x) - U x * Γ x ^ 2) x)
    (hΓb : ∀ x, ‖Γ x - resolv38 η (fun y => star (U y)) x‖ ≤ A^3 / (4*η^3)) :
    (∀ x, Γ x - resolv38 η (fun y => star (U y)) x = -resolv38 η (fun y => U y * Γ y ^ 2) x) ∧
    (∀ x, ‖Γ x - resolv38 η (fun y => star (U y)) x
        - (-resolv38 η (fun y => U y * resolv38 η (fun z => star (U z)) y ^ 2) x)‖ ≤ A^5 / η^5) ∧
    (∀ x, ‖Γ x - resolv38 η (fun y => star (U y)) x
        - (-resolv38 η (fun y => U y * resolv38 η (fun z => star (U z)) y ^ 2) x)
        - (-resolv38 η (fun y => 2 * U y * resolv38 η (fun z => star (U z)) y *
            (-resolv38 η (fun w => U w * resolv38 η (fun z => star (U z)) w ^ 2) y)) x)‖
        ≤ A^7 / η^7) :=
  born_core_r3c U Γ (fun x => resolv38 η (fun y => star (U y)) x)
    (fun x => -resolv38 η (fun y => U y * resolv38 η (fun z => star (U z)) y ^ 2) x)
    (fun x => -resolv38 η (fun y => 2 * U y * resolv38 η (fun z => star (U z)) y *
      (-resolv38 η (fun w => U w * resolv38 η (fun z => star (U z)) w ^ 2) y)) x)
    hU hp hA0 hA hη hΓc hΓp hΓd (fun _ => rfl) hΓb (fun _ => rfl) (fun _ => rfl)

end NlsGge.SpectralFoundations
