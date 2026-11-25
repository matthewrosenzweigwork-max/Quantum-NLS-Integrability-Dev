import QuantumNLS.HighRootLocalization

/-!
# QG:cor:high-contours (R-93DEB242): a common contour and summable resolvent moments

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex`, subsection `QG:sec:high-roots`
(lines 128-142: `ω = 2π/L`, `c = κ/N`, `QG:eq:our-bethe`, `QG:eq:our-global-root-bound`),
Corollary `QG:cor:high-contours` (lines 226-244) and proof (lines 245-265). The configurations are
those of `QG:prop:high-root-localization` (R-9A585DC2, `HighRootLocalization`): on-shell
`IsActualConfig L (κ/N) n q` with `N^{-1} Σ_j q_j² ≤ E`.

Realization:
* `rect L m = {z : |Re z − ωm| < ω/4, |Im z| < ω/4}`; `Γ L m = frontier (rect L m)` (the boundary
  as a set); `boundaryIntegral` is the positively oriented (counter-clockwise) boundary integral
  of the rectangle, in the four-edge form of mathlib's `Complex.integral_boundary_rect_*`. No
  printed clause of the corollary integrates over `Γ_n`, so the orientation enters only the
  definition.
* `nbhd L m = {z : ∃ w ∈ Γ L m, dist z w < ω/32}` — the neighbourhood of width `ω/32`.
* `high_contours`: there is `R ≥ R_E` ("after increasing `R_E`", with HR1's `RE`) such that for
  every configuration above and every `|m| > R`: (exclusion) every root is at distance `≥ d = ω/8`
  from every point of the neighbourhood; (enclosed labels) `q_j ∈ rect ↔ n_j = m`; (moments) for
  every integer `s ≥ 1` and every `z` in the neighbourhood,
  `N^{-1} Σ_j |z − q_j|^{-s} ≤ (4/|ωm|)^s + 4E/(d^s |ωm|²)` (`QG:eq:high-resolvent-moments`).
* `moment_bound_summable`: for `s ≥ 2` the bounds are summable over `m ∈ ℤ`, and their tails over
  `|m| > M` are at most `K/M` (`O_{E,s}(R^{-1})`).

Route (as printed): a preliminary threshold where `C_E/|ωn| ≤ ω/16`; high-label roots are then
separated from the contour neighbourhoods by more than `d`, distinct high labels by their spacing;
the low labels lie in one bounded interval by `QG:eq:our-global-root-bound`; increase the
threshold once more. For the moments, `|Re z − p| < ω/3`; roots with `|q_j| ≤ |p|/2` are at
distance `≥ |p|/4`, the others number at most `4EN/|p|²` and each summand is `≤ d^{-s}`;
summability by comparison with `Σ n^{-2}`.

Recorded deviations (none changes the statement): all estimates are proved on the square annulus
`{|Re z − p| < 9ω/32, |Im z| < 9ω/32} \ {|Re z − p| ≤ 7ω/32, |Im z| ≤ 7ω/32}`, which contains the
width-`ω/32` neighbourhood (`nbhd_subset_annulus`); the threshold for the moment bound is uniform
in `s`; the comparison series tail is bounded by `2/M` through the telescoping
`1/k² ≤ 1/(k−1) − 1/k`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.HighContours

open QuantumNLS.RootContraction QuantumNLS.UniformLabelDistance QuantumNLS.HighRootLocalization

/-! ## 1. The contours -/

/-- `ω = 2π/L`. -/
def om (L : ℝ) : ℝ := 2 * Real.pi / L

/-- The open square `{z : |Re z − ωm| < ω/4, |Im z| < ω/4}`. -/
def rect (L : ℝ) (m : ℤ) : Set ℂ := {z | |z.re - om L * m| < om L / 4 ∧ |z.im| < om L / 4}

/-- `Γ_m`, the boundary of the square. -/
def Γ (L : ℝ) (m : ℤ) : Set ℂ := frontier (rect L m)

/-- The positively oriented boundary integral over `Γ_m` (counter-clockwise: bottom edge left to
right, right edge upwards, top edge right to left, left edge downwards). -/
def boundaryIntegral (L : ℝ) (m : ℤ) (f : ℂ → ℂ) : ℂ :=
  let a := om L * m - om L / 4
  let b := om L * m + om L / 4
  let y0 := -(om L / 4)
  let y1 := om L / 4
  ((∫ x in a..b, f (x + y0 * Complex.I)) - ∫ x in a..b, f (x + y1 * Complex.I)) +
    Complex.I * (∫ y in y0..y1, f (b + y * Complex.I)) -
      Complex.I * ∫ y in y0..y1, f (a + y * Complex.I)

/-- The neighbourhood of `Γ_m` of width `ω/32`. -/
def nbhd (L : ℝ) (m : ℤ) : Set ℂ := {z | ∃ w ∈ Γ L m, dist z w < om L / 32}

/-- The square annulus used in the estimates. -/
def annulus (L : ℝ) (m : ℤ) : Set ℂ :=
  {z | |z.re - om L * m| < 9 * om L / 32 ∧ |z.im| < 9 * om L / 32 ∧
    ¬ (|z.re - om L * m| ≤ 7 * om L / 32 ∧ |z.im| ≤ 7 * om L / 32)}

lemma om_pos {L : ℝ} (hL : 0 < L) : 0 < om L := by unfold om; have := Real.pi_pos; positivity

lemma rect_isOpen (L : ℝ) (m : ℤ) : IsOpen (rect L m) := by
  unfold rect
  exact (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
    continuous_const).inter (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

/-- Points of `Γ_m`: `max(|Re w − ωm|, |Im w|) = ω/4`. -/
lemma mem_Γ {L : ℝ} {m : ℤ} {w : ℂ} (hw : w ∈ Γ L m) :
    |w.re - om L * m| ≤ om L / 4 ∧ |w.im| ≤ om L / 4 ∧
      ¬ (|w.re - om L * m| < om L / 4 ∧ |w.im| < om L / 4) := by
  have hcl : closure (rect L m) ⊆ {z : ℂ | |z.re - om L * m| ≤ om L / 4 ∧ |z.im| ≤ om L / 4} := by
    refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) ?_
    exact (isClosed_le (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
      continuous_const).inter (isClosed_le (continuous_abs.comp Complex.continuous_im)
        continuous_const)
  have h1 := hcl (frontier_subset_closure hw)
  refine ⟨h1.1, h1.2, fun h => ?_⟩
  have : w ∈ interior (rect L m) := (rect_isOpen L m).interior_eq.symm ▸ h
  exact hw.2 this

/-- The width-`ω/32` neighbourhood lies in the square annulus. -/
lemma nbhd_subset_annulus {L : ℝ} (_hL : 0 < L) (m : ℤ) : nbhd L m ⊆ annulus L m := by
  rintro z ⟨w, hw, hd⟩
  obtain ⟨h1, h2, h3⟩ := mem_Γ hw
  have hre : |z.re - w.re| < om L / 32 := by
    have := Complex.abs_re_le_norm (z - w); rw [Complex.sub_re] at this
    rw [Complex.dist_eq] at hd; linarith
  have him : |z.im - w.im| < om L / 32 := by
    have := Complex.abs_im_le_norm (z - w); rw [Complex.sub_im] at this
    rw [Complex.dist_eq] at hd; linarith
  have ar := abs_sub_abs_le_abs_sub (z.re - om L * m) (w.re - om L * m)
  have ar' := abs_sub_abs_le_abs_sub (w.re - om L * m) (z.re - om L * m)
  have ai := abs_sub_abs_le_abs_sub z.im w.im
  have ai' := abs_sub_abs_le_abs_sub w.im z.im
  rw [show z.re - om L * m - (w.re - om L * m) = z.re - w.re by ring] at ar
  rw [show w.re - om L * m - (z.re - om L * m) = -(z.re - w.re) by ring, abs_neg] at ar'
  rw [show w.im - z.im = -(z.im - w.im) by ring, abs_neg] at ai'
  refine ⟨by linarith, by linarith, fun ⟨h4, h5⟩ => h3 ⟨by linarith, by linarith⟩⟩

/-! ## 2. Root localisation inputs -/

lemma norm_ge_re {z : ℂ} {x : ℝ} : |z.re - x| ≤ ‖z - x‖ := by
  have := Complex.abs_re_le_norm (z - x); simpa using this

lemma norm_ge_im {z : ℂ} {x : ℝ} : |z.im| ≤ ‖z - x‖ := by
  have := Complex.abs_im_le_norm (z - x); simpa using this

/-- **QG:cor:high-contours**, the exclusion, enclosed-label and moment clauses. -/
theorem high_contours {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (E : ℝ) (hE : 0 < E) :
    ∃ R : ℝ, RE L κ ≤ R ∧ ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ),
      IsActualConfig L (κ / N) n q → (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
      ∀ m : ℤ, R < |(m : ℝ)| →
        (∀ z ∈ nbhd L m, ∀ j, om L / 8 ≤ ‖z - q j‖) ∧
        (∀ j, ((q j : ℂ) ∈ rect L m ↔ n j = m)) ∧
        (∀ s : ℕ, 1 ≤ s → ∀ z ∈ nbhd L m,
          (N : ℝ)⁻¹ * ∑ j, (‖z - q j‖ ^ s)⁻¹ ≤
            (4 / |om L * m|) ^ s + 4 * E / ((om L / 8) ^ s * |om L * m| ^ 2)) := by
  set ω := om L with hωdef
  have hω : 0 < ω := om_pos hL
  obtain ⟨C, R0, hR0, hloc⟩ := high_root_localization hL hκ E hE
  set C0 := max C 0
  set R1 := max R0 (16 * C0 / ω ^ 2 + 1)
  set D := 3 * Real.sqrt (κ / L)
  set B0 := ω * R1 + D
  have hD : 0 ≤ D := by positivity
  have hR1 : 0 < R1 := lt_of_lt_of_le hR0 (le_max_left _ _)
  set R := max (max R1 ((B0 + ω) / ω)) (max (RE L κ) 2)
  refine ⟨R, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro N n q h hEn m hm
  have hN : ∀ j : Fin N, 1 ≤ N := fun j => Nat.one_le_iff_ne_zero.mpr (fun h0 => (h0 ▸ j).elim0)
  have hRR1 : R1 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRB : (B0 + ω) / ω ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR2 : 2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  set p := ω * m
  have hpabs : |p| = ω * |(m : ℝ)| := by rw [abs_mul, abs_of_pos hω]
  have hpB : B0 + ω < |p| := by
    rw [hpabs]; rw [div_le_iff₀ hω] at hRB; nlinarith
  -- high labels: `|q_j − ωn_j| ≤ ω/16`
  have hhigh : ∀ j, R1 ≤ |(n j : ℝ)| → |q j - ω * n j| ≤ ω / 16 := by
    intro j hj
    have h1 := hloc N n q h hEn j ((le_max_left _ _).trans hj)
    rw [show 2 * Real.pi / L = ω from rfl] at h1
    have hnj : 0 < |(n j : ℝ)| := lt_of_lt_of_le hR1 hj
    have hpj : |ω * n j| = ω * |(n j : ℝ)| := by rw [abs_mul, abs_of_pos hω]
    rw [hpj] at h1
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : 16 * C0 / ω ^ 2 + 1 ≤ |(n j : ℝ)| := (le_max_right _ _).trans hj
    have h3 : 16 * C0 ≤ ω ^ 2 * |(n j : ℝ)| := by
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)] at h2; nlinarith
    have : C ≤ C0 := le_max_left _ _
    nlinarith
  -- low labels: `|q_j| ≤ B0`
  have hlow : ∀ j, |(n j : ℝ)| < R1 → |q j| ≤ B0 := by
    intro j hj
    have h1 := uniform_label_distance (hN j) hL hκ h j
    have e : 2 * Real.pi * n j / L = ω * n j := by rw [hωdef, om]; ring
    rw [e] at h1
    have h2 : |ω * n j| ≤ ω * R1 := by
      rw [abs_mul, abs_of_pos hω]; exact mul_le_mul_of_nonneg_left hj.le hω.le
    have := abs_sub_abs_le_abs_sub (q j) (ω * n j)
    linarith
  -- separation of real roots from the annulus
  have hsep : ∀ z ∈ annulus L m, ∀ j, ω / 8 ≤ ‖z - q j‖ := by
    rintro z ⟨hz1, hz2, hz3⟩ j
    have hre := norm_ge_re (z := z) (x := q j)
    have him := norm_ge_im (z := z) (x := q j)
    by_cases hj : R1 ≤ |(n j : ℝ)|
    · have hq := hhigh j hj
      by_cases hnm : n j = m
      · rw [hnm] at hq
        by_cases hzi : 7 * ω / 32 < |z.im|
        · linarith
        · have hzr : 7 * ω / 32 < |z.re - p| := by
            by_contra hh; push Not at hh hzi; exact hz3 ⟨hh, hzi⟩
          have := abs_sub_abs_le_abs_sub (z.re - p) (z.re - q j)
          rw [show z.re - p - (z.re - q j) = q j - p by ring] at this
          have : |q j - p| ≤ ω / 16 := hq
          linarith
      · have hgap : 1 ≤ |((n j - m : ℤ) : ℝ)| := by
          have : n j - m ≠ 0 := sub_ne_zero.mpr hnm
          exact_mod_cast Int.one_le_abs this
        have hd : ω ≤ |ω * n j - p| := by
          rw [show ω * n j - p = ω * ((n j - m : ℤ) : ℝ) by push_cast; ring, abs_mul,
            abs_of_pos hω]
          nlinarith
        have h1 := abs_sub_abs_le_abs_sub (ω * n j - p) (q j - p)
        rw [show ω * n j - p - (q j - p) = -(q j - ω * n j) by ring, abs_neg] at h1
        have h2 := abs_sub_abs_le_abs_sub (q j - p) (z.re - p)
        rw [show q j - p - (z.re - p) = -(z.re - q j) by ring, abs_neg] at h2
        linarith
    · push Not at hj
      have hq := hlow j hj
      have h1 := abs_sub_abs_le_abs_sub p (z.re - q j)
      rw [show p - (z.re - q j) = -(z.re - p) + q j by ring] at h1
      have h2 := abs_add_le (-(z.re - p)) (q j)
      rw [abs_neg] at h2
      have : ω / 8 ≤ |z.re - q j| := by linarith
      linarith
  refine ⟨fun z hz j => hsep z (nbhd_subset_annulus hL m hz) j, fun j => ?_, ?_⟩
  · -- enclosed labels
    show (|((q j : ℂ)).re - om L * m| < om L / 4 ∧ |((q j : ℂ)).im| < om L / 4) ↔ n j = m
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    change (|q j - p| < ω / 4 ∧ (0 : ℝ) < ω / 4) ↔ n j = m
    constructor
    · rintro ⟨hin, -⟩
      by_contra hnm
      by_cases hj : R1 ≤ |(n j : ℝ)|
      · have hq := hhigh j hj
        have hgap : 1 ≤ |((n j - m : ℤ) : ℝ)| := by
          have : n j - m ≠ 0 := sub_ne_zero.mpr hnm
          exact_mod_cast Int.one_le_abs this
        have hd : ω ≤ |ω * n j - p| := by
          rw [show ω * n j - p = ω * ((n j - m : ℤ) : ℝ) by push_cast; ring, abs_mul,
            abs_of_pos hω]
          nlinarith
        have h1 := abs_sub_abs_le_abs_sub (ω * n j - p) (q j - p)
        rw [show ω * n j - p - (q j - p) = -(q j - ω * n j) by ring, abs_neg] at h1
        linarith
      · push Not at hj
        have hq := hlow j hj
        have h1 := abs_sub_abs_le_abs_sub p (q j)
        rw [abs_sub_comm] at h1
        linarith
    · intro hnm
      have hj : R1 ≤ |(n j : ℝ)| := by rw [hnm]; linarith
      have hq := hhigh j hj
      rw [hnm] at hq
      have hq' : |q j - p| ≤ ω / 16 := hq
      exact ⟨by linarith, by linarith⟩
  · -- moments
    intro s hs z hz
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
      positivity
    have hN0 : (0 : ℝ) < N := by exact_mod_cast h0
    have hza := nbhd_subset_annulus hL m hz
    obtain ⟨hz1, -, -⟩ := hza
    have hz1' : |z.re - p| < 9 * ω / 32 := hz1
    have hpm : 2 * ω ≤ |p| := by rw [hpabs]; nlinarith
    have hp0 : 0 < |p| := by linarith
    have hen : ∑ l, q l ^ 2 ≤ N * E := by rw [inv_mul_le_iff₀ hN0] at hEn; exact hEn
    set G := univ.filter fun l => |p| ^ 2 / 4 < q l ^ 2
    have hcnt : (G.card : ℝ) ≤ 4 * E * N / |p| ^ 2 := count_high q hp0 hen
    have hterm1 : ∀ l ∉ G, (‖z - q l‖ ^ s)⁻¹ ≤ (4 / |p|) ^ s := by
      intro l hl
      have hl' : q l ^ 2 ≤ |p| ^ 2 / 4 := by
        simp only [G, mem_filter, mem_univ, true_and, not_lt] at hl; exact hl
      have hql : |q l| ≤ |p| / 2 := by
        rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs]; nlinarith
      have hdist : |p| / 4 ≤ ‖z - q l‖ := by
        have h1 := norm_ge_re (z := z) (x := q l)
        have h2 := abs_sub_abs_le_abs_sub p (z.re - q l)
        have h3 := abs_add_le (-(z.re - p)) (q l)
        rw [abs_neg] at h3
        rw [show p - (z.re - q l) = -(z.re - p) + q l by ring] at h2
        linarith
      calc (‖z - q l‖ ^ s)⁻¹ ≤ ((|p| / 4) ^ s)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hdist s)
        _ = (4 / |p|) ^ s := by rw [← inv_pow, inv_div]
    have hterm2 : ∀ l, (‖z - q l‖ ^ s)⁻¹ ≤ ((ω / 8) ^ s)⁻¹ := by
      intro l
      exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (hsep z (nbhd_subset_annulus hL m hz) l) s)
    have hsplit := (Finset.sum_filter_add_sum_filter_not univ (fun l => |p| ^ 2 / 4 < q l ^ 2)
      (fun l => (‖z - q l‖ ^ s)⁻¹)).symm
    have b1 : ∑ l ∈ univ.filter (fun l => ¬ |p| ^ 2 / 4 < q l ^ 2), (‖z - q l‖ ^ s)⁻¹ ≤
        N * (4 / |p|) ^ s := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun l hl => hterm1 l ?_).trans ?_
      · simp only [G, mem_filter, mem_univ, true_and]; exact (Finset.mem_filter.mp hl).2
      · rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := Finset.card_le_univ (univ.filter (fun l : Fin N => ¬ |p| ^ 2 / 4 < q l ^ 2))
        simp only [Fintype.card_fin] at this
        exact_mod_cast this
    have b2 : ∑ l ∈ G, (‖z - q l‖ ^ s)⁻¹ ≤ 4 * E * N / |p| ^ 2 * ((ω / 8) ^ s)⁻¹ := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun l _ => hterm2 l).trans ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcnt (by positivity)
    change (N : ℝ)⁻¹ * ∑ j, (‖z - q j‖ ^ s)⁻¹ ≤ (4 / |p|) ^ s + 4 * E / ((ω / 8) ^ s * |p| ^ 2)
    rw [hsplit]
    calc (N : ℝ)⁻¹ * (∑ l ∈ G, (‖z - q l‖ ^ s)⁻¹ +
          ∑ l ∈ univ.filter (fun l => ¬ |p| ^ 2 / 4 < q l ^ 2), (‖z - q l‖ ^ s)⁻¹)
        ≤ (N : ℝ)⁻¹ * (4 * E * N / |p| ^ 2 * ((ω / 8) ^ s)⁻¹ + N * (4 / |p|) ^ s) :=
          mul_le_mul_of_nonneg_left (add_le_add b2 b1) (inv_nonneg.mpr hN0.le)
      _ = (4 / |p|) ^ s + 4 * E / ((ω / 8) ^ s * |p| ^ 2) := by field_simp; ring

/-! ## 3. Summability of the moment bounds -/

lemma tele_nat (M : ℕ) (hM : 1 ≤ M) :
    ∀ K, M ≤ K → ∑ k ∈ Finset.Ioc M K, (1 / (k : ℝ) ^ 2) ≤ 1 / (M : ℝ) - 1 / (K : ℝ) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hMK ih =>
    rw [Finset.sum_Ioc_succ_top hMK]
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le hM hMK)
    have : 1 / ((K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hK0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- Finite partial sums of `n^{-2}` over `n > M` (integers) are at most `1/M`. -/
lemma int_tail_pos (M : ℕ) (hM : 1 ≤ M) (S : Finset ℤ) :
    ∑ n ∈ S, (if (M : ℤ) < n then 1 / (n : ℝ) ^ 2 else 0) ≤ 1 / (M : ℝ) := by
  set T := S.filter fun n => (M : ℤ) < n
  rw [show (∑ n ∈ S, if (M : ℤ) < n then 1 / (n : ℝ) ^ 2 else 0) = ∑ n ∈ T, 1 / (n : ℝ) ^ 2 from
    (Finset.sum_filter _ _).symm]
  set K : ℕ := M + ∑ n ∈ T, n.toNat
  have hinj : Set.InjOn Int.toNat T := fun a ha b hb hab => by
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    omega
  have e : ∑ n ∈ T, 1 / (n : ℝ) ^ 2 = ∑ k ∈ T.image Int.toNat, 1 / (k : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n hn => ?_
    have := (Finset.mem_filter.mp hn).2
    rw [show ((n.toNat : ℕ) : ℝ) = (n : ℝ) by exact_mod_cast Int.toNat_of_nonneg (by omega)]
  rw [e]
  have hsub : T.image Int.toNat ⊆ Finset.Ioc M K := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hn' := (Finset.mem_filter.mp hn).2
    have hle : n.toNat ≤ ∑ n ∈ T, n.toNat := Finset.single_le_sum (f := Int.toNat)
      (fun _ _ => Nat.zero_le _) hn
    rw [Finset.mem_Ioc]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  have := tele_nat M hM K (by omega)
  have : 0 ≤ 1 / (K : ℝ) := by positivity
  linarith

/-- `Σ_{|n| > M} n^{-2} ≤ 2/M` (summable, tsum form). -/
lemma int_tail (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun n : ℤ => if (M : ℝ) < |(n : ℝ)| then 1 / (n : ℝ) ^ 2 else 0) ∧
    ∑' n : ℤ, (if (M : ℝ) < |(n : ℝ)| then 1 / (n : ℝ) ^ 2 else 0) ≤ 2 / (M : ℝ) := by
  have hnn : 0 ≤ fun n : ℤ => if (M : ℝ) < |(n : ℝ)| then 1 / (n : ℝ) ^ 2 else 0 := fun n => by
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  have hS : ∀ S : Finset ℤ, ∑ n ∈ S, (if (M : ℝ) < |(n : ℝ)| then 1 / (n : ℝ) ^ 2 else 0) ≤ 2 / (M : ℝ) := by
    intro S
    have hpt : ∀ n : ℤ, (if (M : ℝ) < |(n : ℝ)| then 1 / (n : ℝ) ^ 2 else 0) ≤
        (if (M : ℤ) < n then 1 / (n : ℝ) ^ 2 else 0) +
          (if (M : ℤ) < -n then 1 / ((-n : ℤ) : ℝ) ^ 2 else 0) := by
      intro n
      have hA : 0 ≤ (if (M : ℤ) < n then 1 / (n : ℝ) ^ 2 else 0) := by split_ifs <;> positivity
      have hB : 0 ≤ (if (M : ℤ) < -n then 1 / ((-n : ℤ) : ℝ) ^ 2 else 0) := by
        split_ifs <;> positivity
      by_cases h1 : (M : ℝ) < |(n : ℝ)|
      · simp only [h1, ↓reduceIte]
        have h1' : (M : ℤ) < |n| := by
          have : ((M : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by push_cast; exact h1
          exact_mod_cast this
        rcases lt_abs.mp h1' with h2 | h3
        · simp only [h2, ↓reduceIte]; linarith
        · simp only [h3, ↓reduceIte]; push_cast; rw [neg_sq]; linarith
      · simp only [h1, ↓reduceIte]; linarith
    refine (Finset.sum_le_sum fun n _ => hpt n).trans ?_
    rw [Finset.sum_add_distrib]
    have h1 := int_tail_pos M hM S
    have h2 := int_tail_pos M hM (S.image Neg.neg)
    rw [Finset.sum_image (fun a _ b _ h => neg_injective h)] at h2
    have e : (2 : ℝ) / M = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    linarith
  exact ⟨summable_of_sum_le hnn hS, Real.tsum_le_of_sum_le hnn hS⟩

/-- The moment bound of `QG:eq:high-resolvent-moments` at label `m`. -/
def momentBound (L E : ℝ) (s : ℕ) (m : ℤ) : ℝ :=
  (4 / |om L * m|) ^ s + 4 * E / ((om L / 8) ^ s * |om L * m| ^ 2)

/-- **Summability and tails** (`s ≥ 2`): the bounds over `|m| > M` are summable with tail
`≤ K/M` for a constant `K` depending only on `L, E, s`. -/
theorem moment_bound_summable {L E : ℝ} (hL : 0 < L) (hE : 0 < E) {s : ℕ} (hs : 2 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, 1 ≤ M →
      Summable (fun m : ℤ => if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0) ∧
      ∑' m : ℤ, (if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0) ≤ K / (M : ℝ) := by
  set ω := om L
  have hω : 0 < ω := om_pos hL
  set K1 := (4 / ω) ^ s + 4 * E / ((ω / 8) ^ s * ω ^ 2)
  have hK1 : 0 ≤ K1 := by positivity
  refine ⟨2 * K1, by positivity, fun M hM => ?_⟩
  obtain ⟨hsum, htail⟩ := int_tail M hM
  have hpt : ∀ m : ℤ, (if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0) ≤
      K1 * (if (M : ℝ) < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) := by
    intro m
    split_ifs with h
    · have hm1 : 1 ≤ |(m : ℝ)| := le_trans (by exact_mod_cast hM) h.le
      have hm0 : 0 < |(m : ℝ)| := by linarith
      have hpow : |(m : ℝ)| ^ 2 ≤ |(m : ℝ)| ^ s := pow_le_pow_right₀ hm1 hs
      have hsq : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
      unfold momentBound
      rw [abs_mul, abs_of_pos hω, hsq]
      have t1 : (4 / (ω * |(m : ℝ)|)) ^ s ≤ (4 / ω) ^ s * (1 / |(m : ℝ)| ^ 2) := by
        rw [show 4 / (ω * |(m : ℝ)|) = (4 / ω) / |(m : ℝ)| by field_simp, div_pow, mul_one_div]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      have t2 : 4 * E / ((ω / 8) ^ s * (ω * |(m : ℝ)|) ^ 2) =
          4 * E / ((ω / 8) ^ s * ω ^ 2) * (1 / |(m : ℝ)| ^ 2) := by
        field_simp
      rw [t2]
      calc (4 / (ω * |(m : ℝ)|)) ^ s + 4 * E / ((ω / 8) ^ s * ω ^ 2) * (1 / |(m : ℝ)| ^ 2)
          ≤ (4 / ω) ^ s * (1 / |(m : ℝ)| ^ 2) +
            4 * E / ((ω / 8) ^ s * ω ^ 2) * (1 / |(m : ℝ)| ^ 2) := by linarith
        _ = K1 * (1 / |(m : ℝ)| ^ 2) := by ring
    · simp
  have hnn : ∀ m : ℤ, 0 ≤ (if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0) := by
    intro m; split_ifs
    · unfold momentBound; positivity
    · exact le_rfl
  have hsum2 : Summable fun m : ℤ => if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0 :=
    Summable.of_nonneg_of_le hnn hpt (hsum.mul_left K1)
  refine ⟨hsum2, ?_⟩
  calc ∑' m : ℤ, (if (M : ℝ) < |(m : ℝ)| then momentBound L E s m else 0)
      ≤ ∑' m : ℤ, K1 * (if (M : ℝ) < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) :=
        Summable.tsum_le_tsum hpt hsum2 (hsum.mul_left K1)
    _ = K1 * ∑' m : ℤ, (if (M : ℝ) < |(m : ℝ)| then 1 / (m : ℝ) ^ 2 else 0) := tsum_mul_left
    _ ≤ K1 * (2 / (M : ℝ)) := mul_le_mul_of_nonneg_left htail hK1
    _ = 2 * K1 / (M : ℝ) := by ring

/-! Kernel axiom audit (checkpoint HC1). -/
#print axioms rect_isOpen
#print axioms mem_Γ
#print axioms nbhd_subset_annulus
#print axioms high_contours
#print axioms tele_nat
#print axioms int_tail_pos
#print axioms int_tail
#print axioms moment_bound_summable

end QuantumNLS.HighContours
