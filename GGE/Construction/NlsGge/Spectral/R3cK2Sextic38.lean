import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Spectral.R3cPlaneSobolev38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P7: the sextic Born term `⟪U, Γ₅⟫ = ∫|U|⁶/(16 η⁵) + O(η⁻⁶)`

Writing `q = 1/(2η)`, three applications of the one-step expansion `R g = q g - q R(g')` give
`‖G₅ - 2 U² Ū³ q⁵‖_∞ ≤ 22 A⁴ A₁ q⁶` for `‖U‖_∞ ≤ A`, `‖U'‖_∞ ≤ A₁`. -/

lemma norm_cast_q_r3c {q : ℝ} (hq0 : 0 < q) (k : ℕ) : ‖((q : ℝ) : ℂ) ^ k‖ = q ^ k := by
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]

/-- One resolvent step in the variable `q = 1/(2η)`. -/
lemma resolv_step_r3c {η q : ℝ} (hη : 0 < η) (hq : 2 * η * q = 1) {g g' : ℝ → ℂ}
    (h : PerC1_38 g g') {b b' : ℝ} (hb : ∀ x, ‖g x‖ ≤ b) (hb' : ∀ x, ‖g' x‖ ≤ b') (x : ℝ) :
    ‖resolv38 η g x‖ ≤ b * q ∧ ‖resolv38 η g' x‖ ≤ b' * q ∧
    resolv38 η g x = g x * (q : ℂ) - resolv38 η g' x * (q : ℂ) ∧
    ‖resolv38 η g x - g x * (q : ℂ)‖ ≤ b' * q ^ 2 := by
  have hq0 : 0 < q := by
    by_contra hc
    push Not at hc
    nlinarith
  have hqe : q = 1 / (2 * η) := by
    field_simp
    linarith
  have e1 : ∀ c : ℝ, c / (2 * η) = c * q := fun c => by rw [hqe]; field_simp
  have h1 := resolv38_bound hη h.cont hb x
  have h2 := resolv38_bound hη h.cont' hb' x
  rw [e1] at h1 h2
  have h3 := resolv38_expand38 hη h x
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have e2 : ∀ c : ℂ, c / (2 * (η : ℂ)) = c * (q : ℂ) := fun c => by
    rw [hqe]; push_cast; field_simp
  rw [e2, e2] at h3
  refine ⟨h1, h2, h3, ?_⟩
  have h4 : resolv38 η g x - g x * (q : ℂ) = -(resolv38 η g' x * (q : ℂ)) := by
    rw [h3]; ring
  rw [h4, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  calc ‖resolv38 η g' x‖ * q ≤ (b' * q) * q := by gcongr
    _ = _ := by ring

theorem sextic_core_r3c {η q A A1 : ℝ} (hη : 0 < η) (hq : 2 * η * q = 1)
    {U U' G1 G1' F3 F3' G3 G3' F5 F5' G5 : ℝ → ℂ} (hU : PerC1_38 U U')
    (hA0 : 0 ≤ A) (hA1 : 0 ≤ A1) (hA : ∀ x, ‖U x‖ ≤ A) (hA' : ∀ x, ‖U' x‖ ≤ A1)
    (hG1d : G1 = resolv38 η (fun y => star (U y)))
    (hG1'd : G1' = resolv38 η (fun y => star (U' y)))
    (hF3d : F3 = fun y => U y * G1 y ^ 2)
    (hF3'd : F3' = fun y => U' y * G1 y ^ 2 + U y * (2 * G1 y * G1' y))
    (hG3d : G3 = fun x => -resolv38 η F3 x) (hG3'd : G3' = fun x => -resolv38 η F3' x)
    (hF5d : F5 = fun y => 2 * U y * G1 y * G3 y)
    (hF5'd : F5' = fun y => (2 * U' y * G1 y + 2 * U y * G1' y) * G3 y
      + 2 * U y * G1 y * G3' y)
    (hG5d : G5 = fun x => -resolv38 η F5 x) :
    Continuous G5 ∧ ∀ x, ‖G5 x - 2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5‖ ≤
      22 * A ^ 4 * A1 * q ^ 6 := by
  have hq0 : 0 < q := by
    by_contra hc
    push Not at hc
    nlinarith
  have hqn : ∀ k : ℕ, ‖(q : ℂ) ^ k‖ = q ^ k := norm_cast_q_r3c hq0
  have hq1 : ‖(q : ℂ)‖ = q := by simpa using hqn 1
  have hUs : PerC1_38 (fun y => star (U y)) (fun y => star (U' y)) := hU.star
  have hAs : ∀ x, ‖star (U x)‖ ≤ A := fun x => by rw [norm_star]; exact hA x
  have hAs' : ∀ x, ‖star (U' x)‖ ≤ A1 := fun x => by rw [norm_star]; exact hA' x
  have hG1 : PerC1_38 G1 G1' := by
    rw [hG1d, hG1'd]; exact perC1_resolv38 hη hUs
  -- G1 bounds
  have s1 := fun x => resolv_step_r3c hη hq hUs hAs hAs' x
  rw [← hG1d, ← hG1'd] at s1
  have hG1b : ∀ x, ‖G1 x‖ ≤ A * q := fun x => (s1 x).1
  have hG1'b : ∀ x, ‖G1' x‖ ≤ A1 * q := fun x => (s1 x).2.1
  have hG1e : ∀ x, ‖G1 x - star (U x) * (q : ℂ)‖ ≤ A1 * q ^ 2 := fun x => (s1 x).2.2.2
  -- F3
  have hF3 : PerC1_38 F3 F3' := by
    rw [hF3d, hF3'd]; exact hU.mul hG1.pow_two
  have hF3b : ∀ x, ‖F3 x‖ ≤ A ^ 3 * q ^ 2 := by
    intro x
    rw [hF3d]
    show ‖U x * G1 x ^ 2‖ ≤ _
    have := hG1b x
    have := hA x
    calc ‖U x * G1 x ^ 2‖ = ‖U x‖ * ‖G1 x‖ ^ 2 := by rw [norm_mul, norm_pow]
      _ ≤ A * (A * q) ^ 2 := by gcongr
      _ = _ := by ring
  have hF3'b : ∀ x, ‖F3' x‖ ≤ 3 * A ^ 2 * A1 * q ^ 2 := by
    intro x
    rw [hF3'd]
    show ‖U' x * G1 x ^ 2 + U x * (2 * G1 x * G1' x)‖ ≤ _
    have := hG1b x
    have := hG1'b x
    have := hA x
    have := hA' x
    calc ‖U' x * G1 x ^ 2 + U x * (2 * G1 x * G1' x)‖
        ≤ ‖U' x‖ * ‖G1 x‖ ^ 2 + ‖U x‖ * (2 * ‖G1 x‖ * ‖G1' x‖) := by
          refine (norm_add_le _ _).trans ?_
          simp only [norm_mul, norm_pow]
          norm_num
      _ ≤ A1 * (A * q) ^ 2 + A * (2 * (A * q) * (A1 * q)) := by gcongr
      _ = _ := by ring
  -- G3
  have hG3 : PerC1_38 G3 G3' := by
    rw [hG3d, hG3'd]; exact (perC1_resolv38 hη hF3).neg
  have s3 := fun x => resolv_step_r3c hη hq hF3 hF3b hF3'b x
  have hG3x : ∀ x, G3 x = -resolv38 η F3 x := fun x => by rw [hG3d]
  have hG3'x : ∀ x, G3' x = -resolv38 η F3' x := fun x => by rw [hG3'd]
  have hG3b : ∀ x, ‖G3 x‖ ≤ A ^ 3 * q ^ 3 := fun x => by
    rw [hG3x, norm_neg]
    calc _ ≤ A ^ 3 * q ^ 2 * q := (s3 x).1
      _ = _ := by ring
  have hG3'b : ∀ x, ‖G3' x‖ ≤ 3 * A ^ 2 * A1 * q ^ 3 := fun x => by
    rw [hG3'x, norm_neg]
    calc _ ≤ 3 * A ^ 2 * A1 * q ^ 2 * q := (s3 x).2.1
      _ = _ := by ring
  have hF3e : ∀ x, ‖F3 x - U x * star (U x) ^ 2 * (q : ℂ) ^ 2‖ ≤ 2 * A ^ 2 * A1 * q ^ 3 := by
    intro x
    have e : F3 x - U x * star (U x) ^ 2 * (q : ℂ) ^ 2
        = U x * ((G1 x - star (U x) * (q : ℂ)) * (G1 x + star (U x) * (q : ℂ))) := by
      rw [hF3d]; show U x * G1 x ^ 2 - _ = _; ring
    rw [e]
    have h1 := hG1b x
    have h2 := hG1e x
    have h3 := hAs x
    have h4 := hA x
    have h5 : ‖G1 x + star (U x) * (q : ℂ)‖ ≤ 2 * A * q := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hq1]
      nlinarith
    calc ‖U x * ((G1 x - star (U x) * (q : ℂ)) * (G1 x + star (U x) * (q : ℂ)))‖
        = ‖U x‖ * (‖G1 x - star (U x) * (q : ℂ)‖ * ‖G1 x + star (U x) * (q : ℂ)‖) := by
          rw [norm_mul, norm_mul]
      _ ≤ A * (A1 * q ^ 2 * (2 * A * q)) := by gcongr
      _ = _ := by ring
  have hG3e : ∀ x, ‖G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))‖ ≤ 5 * A ^ 2 * A1 * q ^ 4 := by
    intro x
    have e : G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))
        = -(resolv38 η F3 x - F3 x * (q : ℂ))
          - (F3 x - U x * star (U x) ^ 2 * (q : ℂ) ^ 2) * (q : ℂ) := by
      rw [hG3x]; ring
    rw [e]
    have h1 := (s3 x).2.2.2
    have h2 := hF3e x
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, hq1]
    have : ‖F3 x - U x * star (U x) ^ 2 * (q : ℂ) ^ 2‖ * q ≤ 2 * A ^ 2 * A1 * q ^ 3 * q := by
      gcongr
    nlinarith
  -- F5
  have hF5 : PerC1_38 F5 F5' := by
    rw [hF5d, hF5'd]; exact ((hU.const_mul 2).mul hG1).mul hG3
  have hF5b : ∀ x, ‖F5 x‖ ≤ 2 * A ^ 5 * q ^ 4 := by
    intro x
    rw [hF5d]
    show ‖2 * U x * G1 x * G3 x‖ ≤ _
    have := hG1b x
    have := hG3b x
    have := hA x
    calc ‖2 * U x * G1 x * G3 x‖ = 2 * ‖U x‖ * ‖G1 x‖ * ‖G3 x‖ := by
          simp only [norm_mul]; norm_num
      _ ≤ 2 * A * (A * q) * (A ^ 3 * q ^ 3) := by gcongr
      _ = _ := by ring
  have hF5'b : ∀ x, ‖F5' x‖ ≤ 10 * A ^ 4 * A1 * q ^ 4 := by
    intro x
    rw [hF5'd]
    show ‖(2 * U' x * G1 x + 2 * U x * G1' x) * G3 x + 2 * U x * G1 x * G3' x‖ ≤ _
    have := hG1b x
    have := hG1'b x
    have := hG3b x
    have := hG3'b x
    have := hA x
    have := hA' x
    calc ‖(2 * U' x * G1 x + 2 * U x * G1' x) * G3 x + 2 * U x * G1 x * G3' x‖
        ≤ (2 * ‖U' x‖ * ‖G1 x‖ + 2 * ‖U x‖ * ‖G1' x‖) * ‖G3 x‖
          + 2 * ‖U x‖ * ‖G1 x‖ * ‖G3' x‖ := by
          refine (norm_add_le _ _).trans ?_
          have h1 : ‖(2 * U' x * G1 x + 2 * U x * G1' x) * G3 x‖
              ≤ (2 * ‖U' x‖ * ‖G1 x‖ + 2 * ‖U x‖ * ‖G1' x‖) * ‖G3 x‖ := by
            rw [norm_mul]
            gcongr
            refine (norm_add_le _ _).trans ?_
            simp only [norm_mul]
            norm_num
          have h2 : ‖2 * U x * G1 x * G3' x‖ = 2 * ‖U x‖ * ‖G1 x‖ * ‖G3' x‖ := by
            simp only [norm_mul]; norm_num
          rw [h2]
          linarith
      _ ≤ (2 * A1 * (A * q) + 2 * A * (A1 * q)) * (A ^ 3 * q ^ 3)
          + 2 * A * (A * q) * (3 * A ^ 2 * A1 * q ^ 3) := by gcongr
      _ = _ := by ring
  have hF5e : ∀ x, ‖F5 x - 2 * U x * (star (U x) * (q : ℂ))
      * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))‖ ≤ 12 * A ^ 4 * A1 * q ^ 5 := by
    intro x
    have e : F5 x - 2 * U x * (star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))
        = 2 * U x * (G1 x * (G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))
          + (G1 x - star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))) := by
      rw [hF5d]; show 2 * U x * G1 x * G3 x - _ = _; ring
    rw [e]
    have h1 := hG1b x
    have h2 := hG1e x
    have h3 := hG3e x
    have h4 := hA x
    have h5 := hAs x
    have hg : ‖-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)‖ ≤ A ^ 3 * q ^ 3 := by
      rw [norm_neg, norm_mul, norm_mul, norm_pow, hqn]
      have : ‖U x‖ * ‖star (U x)‖ ^ 2 ≤ A * A ^ 2 := by gcongr
      calc _ ≤ A * A ^ 2 * q ^ 3 := by gcongr
        _ = _ := by ring
    have hin : ‖G1 x * (G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))
          + (G1 x - star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))‖
        ≤ A * q * (5 * A ^ 2 * A1 * q ^ 4) + A1 * q ^ 2 * (A ^ 3 * q ^ 3) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      gcongr
    calc ‖2 * U x * (G1 x * (G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))
          + (G1 x - star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))‖
        = 2 * ‖U x‖ * ‖G1 x * (G3 x - (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))
          + (G1 x - star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))‖ := by
          rw [norm_mul, norm_mul]; norm_num
      _ ≤ 2 * A * (A * q * (5 * A ^ 2 * A1 * q ^ 4) + A1 * q ^ 2 * (A ^ 3 * q ^ 3)) := by
          gcongr
      _ = _ := by ring
  -- G5
  have hG5 : PerC1_38 G5 (fun x => -resolv38 η F5' x) := by
    rw [hG5d]; exact (perC1_resolv38 hη hF5).neg
  have s5 := fun x => resolv_step_r3c hη hq hF5 hF5b hF5'b x
  have hG5x : ∀ x, G5 x = -resolv38 η F5 x := fun x => by rw [hG5d]
  refine ⟨hG5.cont, fun x => ?_⟩
  have e : G5 x - 2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5
      = -(F5 x - 2 * U x * (star (U x) * (q : ℂ)) * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3)))
          * (q : ℂ) + resolv38 η F5' x * (q : ℂ) := by
    have h3 := (s5 x).2.2.1
    rw [hG5x]
    linear_combination (-1 : ℂ) * h3
  rw [e]
  have h1 := hF5e x
  have h2 := (s5 x).2.1
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_neg, hq1]
  have h6 : ‖F5 x - 2 * U x * (star (U x) * (q : ℂ))
      * (-(U x * star (U x) ^ 2 * (q : ℂ) ^ 3))‖ * q ≤ 12 * A ^ 4 * A1 * q ^ 5 * q := by
    gcongr
  have h7 : ‖resolv38 η F5' x‖ * q ≤ 10 * A ^ 4 * A1 * q ^ 4 * q * q := by
    gcongr
  nlinarith

theorem r3c_k2_sextic (B : ℝ) : ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧
    ∀ (N : ℕ) (z : FourierPlane N),
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 ≤ B ^ 2 →
      ∀ η : ℝ, η₀ ≤ η →
      ‖pair38 (planeReal N z)
          (fun x => -resolv38 η (fun y => 2 * planeReal N z y *
              resolv38 η (fun y' => star (planeReal N z y')) y *
              (-resolv38 η (fun w => planeReal N z w *
                  resolv38 η (fun y' => star (planeReal N z y')) w ^ 2) y)) x)
        - (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 6) / (16 * η ^ 5)‖ ≤ C / η ^ 6 := by
  set K := Real.sqrt bracketSumE02_38 with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set A : ℝ := K * |B| with hAdef
  set A1 : ℝ := 2 * Real.pi * K * |B| with hA1def
  have hA0 : 0 ≤ A := by positivity
  have hA10 : 0 ≤ A1 := by positivity
  refine ⟨1, 11 * A ^ 5 * A1 / 32, one_pos, by positivity, ?_⟩
  intro N z hS η hη
  have hη0 : 0 < η := by linarith
  have hS2 : Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2)
      ≤ |B| := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hS
  have hS1 : Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2)
      ≤ |B| := by
    refine le_trans (Real.sqrt_le_sqrt (plane_S_mono_r3c N z (by norm_num : 1 ≤ 2))) hS2
  have hA : ∀ x, ‖planeReal N z x‖ ≤ A := fun x =>
    (plane_sup_le_r3c N z x).trans (mul_le_mul_of_nonneg_left hS1 hK0)
  have hA' : ∀ x, ‖planeReal N (derivativePlane N z) x‖ ≤ A1 := fun x =>
    (plane_deriv_sup_le_r3c N z x).trans (by
      rw [hA1def]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity))
  set q : ℝ := 1 / (2 * η) with hqdef
  have hq : 2 * η * q = 1 := by rw [hqdef]; field_simp
  have hq0 : 0 < q := by rw [hqdef]; positivity
  obtain ⟨hGc, hG⟩ := sextic_core_r3c (η := η) (q := q) (A := A) (A1 := A1) hη0 hq
    (perC1_plane38 N z) hA0 hA10 hA hA'
    (G1 := resolv38 η (fun y => star (planeReal N z y)))
    (G1' := resolv38 η (fun y => star (planeReal N (derivativePlane N z) y)))
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set U := planeReal N z with hUdef
  have hUc : Continuous U := (perC1_plane38 N z).cont
  have hc : ∀ x, ((‖U x‖ ^ 6 : ℝ) : ℂ) * ((2 * q ^ 5 : ℝ) : ℂ)
      = U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5) := by
    intro x
    have h1 : U x * star (U x) = ((‖U x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
    have : U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5)
        = 2 * (U x * star (U x)) ^ 3 * (q : ℂ) ^ 5 := by ring
    rw [this, h1]; push_cast; ring
  have key : ∀ G5 : ℝ → ℂ, Continuous G5 →
      (∀ x, ‖G5 x - 2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5‖ ≤ 22 * A ^ 4 * A1 * q ^ 6) →
      ‖pair38 U G5 - ((∫ x in (0:ℝ)..1, ‖U x‖ ^ 6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)‖
        ≤ 11 * A ^ 5 * A1 / 32 / η ^ 6 := by
    intro G5 hc5 h5
    have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη0.ne'
    have hcoef : ((2 * q ^ 5 : ℝ) : ℂ) = 1 / (16 * (η : ℂ) ^ 5) := by
      rw [hqdef]; push_cast; field_simp; ring
    have e1 : ((∫ x in (0:ℝ)..1, ‖U x‖ ^ 6 : ℝ) : ℂ) / (16 * (η : ℂ) ^ 5)
        = ∫ x in (0:ℝ)..1, U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5) := by
      have : ∀ x, U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5)
          = ((‖U x‖ ^ 6 : ℝ) : ℂ) * ((2 * q ^ 5 : ℝ) : ℂ) := fun x => (hc x).symm
      simp only [this]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hcoef]
      ring
    have hUT : Continuous fun x => U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5) := by
      have := hUc.star
      fun_prop
    have hUG : Continuous fun x => U x * G5 x := hUc.mul hc5
    have e2 : pair38 U G5 - ∫ x in (0:ℝ)..1, U x * (2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5)
        = ∫ x in (0:ℝ)..1, U x * (G5 x - 2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5) := by
      unfold pair38
      rw [← intervalIntegral.integral_sub (hUG.intervalIntegrable _ _) (hUT.intervalIntegrable _ _)]
      congr 1
      funext x
      ring
    rw [e1, e2]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := A * (22 * A ^ 4 * A1 * q ^ 6))
      (f := fun x => U x * (G5 x - 2 * U x ^ 2 * star (U x) ^ 3 * (q : ℂ) ^ 5))
      (fun x _ => by
        rw [norm_mul]
        exact mul_le_mul (hA x) (h5 x) (norm_nonneg _) hA0)
    refine hb.trans ?_
    rw [sub_zero, abs_one, mul_one, hqdef]
    have : A * (22 * A ^ 4 * A1 * (1 / (2 * η)) ^ 6) = 11 * A ^ 5 * A1 / 32 / η ^ 6 := by
      field_simp; ring
    exact this.le
  exact key _ hGc hG

end NlsGge.SpectralFoundations
end
