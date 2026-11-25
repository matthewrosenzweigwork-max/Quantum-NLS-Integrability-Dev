import QuantumNLS.LocalWellPosedness

/-!
# EXT-003, stage A: the periodic `L⁴` estimate for the free Schrödinger group on `𝕋_L`

Source: `source/chapters/foundations/ROOT_L2_extension.tex`, Lemma `lem:root-L4-duality`
(R-02871DC6), equation `eq:root-L4-free` and the first paragraph of its proof (lines 20-50);
EXT-003 (Bourgain 1993, Section 4, the periodic `L⁴` estimate).

Conventions (realized, read-only): `𝕋_L = AddCircle L` with Lebesgue measure of mass `L`;
`e_n = Fourier.mode L n` (`L^{-1/2} e^{2πinx/L}`); `p_n = Fourier.freq L n = 2πn/L`; the free group
`U(t) = e^{it∂²}` acts by `LocalWellPosedness.phase L t n = e^{−itp_n²}` on the coefficients (the
multiplier of LW1's `Sgrp`). `T_L = L²/(2π)` is the time period of `U`.

Proved here, for a finite Fourier sum `u(t,x) = Σ_{n∈S} a_n e^{−itp_n²} e_n(x)` and every `s`:
* the exact identity `∫_s^{s+T_L} ∫_{𝕋_L} |u|⁴ = (T_L/L)(2(Σ|a_n|²)² − Σ|a_n|⁴)` (the printed
  computation: only quadruples with equal sums and equal sums of squares survive, and these
  coincide as multisets);
* hence `∫_J ∫ |u|⁴ ≤ (2T_L/L)(Σ|a_n|²)²` on every interval `J` of length `≤ T_L`, i.e.
  `‖U(·)f‖_{L⁴(J×𝕋_L)} ≤ C_L‖f‖_2` with `C_L = (2T_L/L)^{1/4}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness

namespace QuantumNLS.L4Strichartz

variable {L : ℝ} [Fact (0 < L)]

/-- The time period `T_L = L²/(2π)` of the free group. -/
def TL (L : ℝ) : ℝ := L ^ 2 / (2 * Real.pi)

lemma TL_pos : 0 < TL L := by
  have hL : 0 < L := Fact.out
  unfold TL; positivity

/-! ## 1. Spatial orthogonality of fourfold products -/

lemma mode_mul (a b : ℤ) (x : AddCircle L) :
    mode L a x * mode L b x = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * mode L (a + b) x := by
  unfold mode; rw [fourier_add]; ring

lemma continuous_mode' (n : ℤ) : Continuous (mode L n) := continuous_mode (L := L) n

lemma integrable_cont {f : AddCircle L → ℂ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `∫ e_{n₁} e_{n₂} ē_{n₃} ē_{n₄} = L⁻¹ [n₁ + n₂ = n₃ + n₄]`. -/
lemma integral_mode4 (n1 n2 n3 n4 : ℤ) :
    ∫ x, mode L n1 x * mode L n2 x * conj (mode L n3 x) * conj (mode L n4 x) =
      if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0 := by
  have hL : 0 < L := Fact.out
  have hs : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) = (L : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hL.le, Complex.ofReal_inv]
  have e : ∀ x, mode L n1 x * mode L n2 x * conj (mode L n3 x) * conj (mode L n4 x) =
      (L : ℂ)⁻¹ * (conj (mode L (n3 + n4) x) * mode L (n1 + n2) x) := by
    intro x
    have h1 := mode_mul (L := L) n1 n2 x
    have h3 : conj (mode L n3 x) * conj (mode L n4 x) =
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conj (mode L (n3 + n4) x) := by
      rw [← map_mul, mode_mul, map_mul, Complex.conj_ofReal]
    calc mode L n1 x * mode L n2 x * conj (mode L n3 x) * conj (mode L n4 x)
        = (mode L n1 x * mode L n2 x) * (conj (mode L n3 x) * conj (mode L n4 x)) := by ring
      _ = _ := by rw [h1, h3, ← hs]; ring
  simp_rw [e]
  rw [integral_const_mul]
  have h := coeff_mode (L := L) (n1 + n2) (n3 + n4)
  unfold coeff at h
  rw [h]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

/-! ## 2. The free solution of a finite Fourier sum and its spatial `L⁴` integral -/

/-- `u(t,x) = Σ_{n∈S} a_n e^{−itp_n²} e_n(x)`. -/
def freeSol (S : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) (x : AddCircle L) : ℂ :=
  ∑ n ∈ S, a n * phase L t n * mode L n x

lemma norm4 (z : ℂ) : ((‖z‖ ^ 4 : ℝ) : ℂ) = z * z * conj z * conj z := by
  have h := Complex.mul_conj z
  rw [Complex.normSq_eq_norm_sq] at h
  calc ((‖z‖ ^ 4 : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = (z * conj z) * (z * conj z) := by rw [h]
    _ = z * z * conj z * conj z := by ring

lemma expand4 (S : Finset ℤ) (f : ℤ → ℂ) :
    (∑ i ∈ S, f i) * (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i) =
      ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, ∑ l ∈ S, f i * f j * conj (f k) * conj (f l) := by
  have h1 : (∑ i ∈ S, f i) * (∑ i ∈ S, f i) = ∑ i ∈ S, ∑ j ∈ S, f i * f j := Finset.sum_mul_sum _ _ _ _
  have h2 : conj (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i) = ∑ k ∈ S, ∑ l ∈ S, conj (f k) * conj (f l) := by
    rw [map_sum]; exact Finset.sum_mul_sum _ _ _ _
  calc (∑ i ∈ S, f i) * (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i)
      = ((∑ i ∈ S, f i) * (∑ i ∈ S, f i)) * (conj (∑ i ∈ S, f i) * conj (∑ i ∈ S, f i)) := by ring
    _ = _ := by
      rw [h1, h2, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring

/-- The coefficient product `a₁a₂ā₃ā₄`. -/
def A4 (a : ℤ → ℂ) (n1 n2 n3 n4 : ℤ) : ℂ := a n1 * a n2 * conj (a n3) * conj (a n4)

/-- The phase product `e^{−it(p₁²+p₂²−p₃²−p₄²)}`. -/
def P4 (L t : ℝ) (n1 n2 n3 n4 : ℤ) : ℂ :=
  phase L t n1 * phase L t n2 * conj (phase L t n3) * conj (phase L t n4)

lemma integral_x (S : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    ((∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 : ℝ) : ℂ) =
      ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S,
        A4 a n1 n2 n3 n4 * P4 L t n1 n2 n3 n4 * (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) := by
  rw [← integral_complex_ofReal]
  have hexp : ∀ x, ((‖freeSol (L := L) S a t x‖ ^ 4 : ℝ) : ℂ) =
      ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, A4 a n1 n2 n3 n4 * P4 L t n1 n2 n3 n4 *
        (mode L n1 x * mode L n2 x * conj (mode L n3 x) * conj (mode L n4 x)) := by
    intro x
    rw [norm4, freeSol, expand4]
    refine Finset.sum_congr rfl fun n1 _ => Finset.sum_congr rfl fun n2 _ =>
      Finset.sum_congr rfl fun n3 _ => Finset.sum_congr rfl fun n4 _ => ?_
    simp only [A4, P4, map_mul]
    ring
  simp_rw [hexp]
  have hc : ∀ n1 n2 n3 n4 : ℤ, Continuous fun x : AddCircle L =>
      A4 a n1 n2 n3 n4 * P4 L t n1 n2 n3 n4 *
        (mode L n1 x * mode L n2 x * conj (mode L n3 x) * conj (mode L n4 x)) := fun n1 n2 n3 n4 =>
    continuous_const.mul ((((continuous_mode' n1).mul (continuous_mode' n2)).mul
      (Complex.continuous_conj.comp (continuous_mode' n3))).mul
        (Complex.continuous_conj.comp (continuous_mode' n4)))
  rw [integral_finsetSum _ fun n1 _ => integrable_cont (continuous_finsetSum _ fun n2 _ =>
    continuous_finsetSum _ fun n3 _ => continuous_finsetSum _ fun n4 _ => hc n1 n2 n3 n4)]
  refine Finset.sum_congr rfl fun n1 _ => ?_
  rw [integral_finsetSum _ fun n2 _ => integrable_cont (continuous_finsetSum _ fun n3 _ =>
    continuous_finsetSum _ fun n4 _ => hc n1 n2 n3 n4)]
  refine Finset.sum_congr rfl fun n2 _ => ?_
  rw [integral_finsetSum _ fun n3 _ => integrable_cont (continuous_finsetSum _ fun n4 _ =>
    hc n1 n2 n3 n4)]
  refine Finset.sum_congr rfl fun n3 _ => ?_
  rw [integral_finsetSum _ fun n4 _ => integrable_cont (hc n1 n2 n3 n4)]
  refine Finset.sum_congr rfl fun n4 _ => ?_
  rw [integral_const_mul, integral_mode4]

#print axioms integral_x

/-! ## 3. Time integrals over one period -/

lemma freq_sq (n : ℤ) : freq L n ^ 2 = (4 * Real.pi ^ 2 / L ^ 2) * (n : ℝ) ^ 2 := by
  unfold freq; ring

lemma P4_eq (t : ℝ) (n1 n2 n3 n4 : ℤ) :
    P4 L t n1 n2 n3 n4 = Complex.exp ((-(Complex.I) *
      ((freq L n1 ^ 2 + freq L n2 ^ 2 - freq L n3 ^ 2 - freq L n4 ^ 2 : ℝ) : ℂ)) * t) := by
  unfold P4 phase
  rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma continuous_P4 (n1 n2 n3 n4 : ℤ) : Continuous fun t : ℝ => P4 L t n1 n2 n3 n4 := by
  unfold P4
  exact (((continuous_phase L n1).mul (continuous_phase L n2)).mul
    (Complex.continuous_conj.comp (continuous_phase L n3))).mul
      (Complex.continuous_conj.comp (continuous_phase L n4))

/-- Over one time period, `∫ e^{−it(p₁²+p₂²−p₃²−p₄²)} dt = T_L` if `n₁²+n₂² = n₃²+n₄²`, else `0`. -/
lemma integral_P4 (s : ℝ) (n1 n2 n3 n4 : ℤ) :
    ∫ t in s..s + TL L, P4 L t n1 n2 n3 n4 =
      if n1 ^ 2 + n2 ^ 2 = n3 ^ 2 + n4 ^ 2 then (TL L : ℂ) else 0 := by
  have hL : 0 < L := Fact.out
  set k : ℤ := n1 ^ 2 + n2 ^ 2 - n3 ^ 2 - n4 ^ 2
  have hΩ : (freq L n1 ^ 2 + freq L n2 ^ 2 - freq L n3 ^ 2 - freq L n4 ^ 2 : ℝ) =
      (4 * Real.pi ^ 2 / L ^ 2) * (k : ℝ) := by
    simp only [freq_sq, k]; push_cast; ring
  simp_rw [P4_eq, hΩ]
  split_ifs with h
  · have hk0 : k = 0 := by simp only [k]; linarith
    have hk : (k : ℝ) = 0 := by exact_mod_cast hk0
    simp [hk]
  · have hk : k ≠ 0 := fun h0 => h (by simp only [k] at h0; linarith)
    set c : ℂ := -Complex.I * (((4 * Real.pi ^ 2 / L ^ 2) * (k : ℝ) : ℝ) : ℂ)
    have hc : c ≠ 0 := by
      simp only [c]
      refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
      exact_mod_cast mul_ne_zero (by positivity) (Int.cast_ne_zero.mpr hk)
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp (c * ((s + TL L : ℝ) : ℂ)) = Complex.exp (c * (s : ℂ)) := by
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have e : c * ((s + TL L : ℝ) : ℂ) = c * (s : ℂ) + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [c, TL]
        push_cast
        field_simp
        ring
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]

#print axioms integral_P4

/-! ## 4. The lattice count: equal sums and equal sums of squares -/

lemma count (n1 n2 n3 n4 : ℤ) :
    (n1 + n2 = n3 + n4 ∧ n1 ^ 2 + n2 ^ 2 = n3 ^ 2 + n4 ^ 2) ↔
      (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h : 2 * ((n3 - n1) * (n3 - n2)) = 0 := by
      linear_combination (-1 : ℤ) * h2 + (n1 + n2 - n3 + n4) * h1
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left two_ne_zero) with h3 | h3
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> ring

lemma ind_split (n1 n2 n3 n4 : ℤ) :
    (if (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) then (1 : ℂ) else 0) =
      (if n3 = n1 then (if n4 = n2 then 1 else 0) else 0) +
        (if n3 = n2 then (if n4 = n1 then 1 else 0) else 0) -
          (if n1 = n2 then (if n3 = n1 then (if n4 = n1 then 1 else 0) else 0) else 0) := by
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma mul_conj' (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma dsum (S : Finset ℤ) (g : ℤ → ℤ → ℂ) {p q : ℤ} (hp : p ∈ S) (hq : q ∈ S) :
    ∑ n3 ∈ S, ∑ n4 ∈ S, g n3 n4 * (if n3 = p then (if n4 = q then (1 : ℂ) else 0) else 0) =
      g p q := by
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (fun h => absurd hp h),
    Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (fun h => absurd hq h)]
  simp

lemma A4_12 (a : ℤ → ℂ) (n1 n2 : ℤ) :
    A4 a n1 n2 n1 n2 = ((‖a n1‖ ^ 2 : ℝ) : ℂ) * ((‖a n2‖ ^ 2 : ℝ) : ℂ) := by
  rw [A4, ← mul_conj', ← mul_conj']; ring

lemma A4_21 (a : ℤ → ℂ) (n1 n2 : ℤ) :
    A4 a n1 n2 n2 n1 = ((‖a n1‖ ^ 2 : ℝ) : ℂ) * ((‖a n2‖ ^ 2 : ℝ) : ℂ) := by
  rw [A4, ← mul_conj', ← mul_conj']; ring

lemma A4_11 (a : ℤ → ℂ) (n1 : ℤ) : A4 a n1 n1 n1 n1 = ((‖a n1‖ ^ 4 : ℝ) : ℂ) := by
  rw [A4, show ‖a n1‖ ^ 4 = ‖a n1‖ ^ 2 * ‖a n1‖ ^ 2 by ring, Complex.ofReal_mul, ← mul_conj']; ring

/-- `Σ a₁a₂ā₃ā₄ [{n₃,n₄} = {n₁,n₂}] = 2(Σ|a_n|²)² − Σ|a_n|⁴`. -/
lemma sum_resonant (S : Finset ℤ) (a : ℤ → ℂ) :
    ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, A4 a n1 n2 n3 n4 *
        (if (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) then (1 : ℂ) else 0) =
      ((2 * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 - ∑ n ∈ S, ‖a n‖ ^ 4 : ℝ) : ℂ) := by
  have inner : ∀ n1 ∈ S, ∀ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, A4 a n1 n2 n3 n4 *
        (if (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) then (1 : ℂ) else 0) =
      2 * (((‖a n1‖ ^ 2 : ℝ) : ℂ) * ((‖a n2‖ ^ 2 : ℝ) : ℂ)) -
        (if n1 = n2 then ((‖a n1‖ ^ 4 : ℝ) : ℂ) else 0) := by
    intro n1 h1 n2 h2
    simp_rw [ind_split, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [dsum S (A4 a n1 n2) h1 h2, dsum S (A4 a n1 n2) h2 h1, A4_12, A4_21]
    split_ifs with h12
    · subst h12
      rw [dsum S (A4 a n1 n1) h1 h1, A4_11]; ring
    · simp only [mul_zero, Finset.sum_const_zero, sub_zero]; ring
  rw [Finset.sum_congr rfl fun n1 h1 => Finset.sum_congr rfl fun n2 h2 => inner n1 h1 n2 h2]
  have hz : ∀ n1 ∈ S, ∑ n2 ∈ S, (2 * (((‖a n1‖ ^ 2 : ℝ) : ℂ) * ((‖a n2‖ ^ 2 : ℝ) : ℂ)) -
        (if n1 = n2 then ((‖a n1‖ ^ 4 : ℝ) : ℂ) else 0)) =
      2 * ((‖a n1‖ ^ 2 : ℝ) : ℂ) * ∑ n2 ∈ S, ((‖a n2‖ ^ 2 : ℝ) : ℂ) - ((‖a n1‖ ^ 4 : ℝ) : ℂ) := by
    intro n1 h1
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp only [h1, ite_true]
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n2 _ => by ring
  rw [Finset.sum_congr rfl hz, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  push_cast
  ring

#print axioms sum_resonant

/-! ## 5. The exact fourth-power identity and the `L⁴` estimate -/

lemma continuous_inner (S : Finset ℤ) (a : ℤ → ℂ) :
    Continuous fun t : ℝ => ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 := by
  have h : (fun t : ℝ => ((∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 : ℝ) : ℂ)) = fun t =>
      ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S,
        A4 a n1 n2 n3 n4 * P4 L t n1 n2 n3 n4 * (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) :=
    funext fun t => integral_x S a t
  have hc : Continuous fun t : ℝ => ((∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 : ℝ) : ℂ) := by
    rw [h]
    exact continuous_finsetSum _ fun n1 _ => continuous_finsetSum _ fun n2 _ =>
      continuous_finsetSum _ fun n3 _ => continuous_finsetSum _ fun n4 _ =>
        (continuous_const.mul (continuous_P4 n1 n2 n3 n4)).mul continuous_const
  exact (Complex.continuous_re.comp hc).congr fun t => Complex.ofReal_re _

/-- **The exact identity** (the printed computation): over one time period,
`∫_s^{s+T_L} ∫_{𝕋_L} |u|⁴ dx dt = (T_L/L)(2(Σ|a_n|²)² − Σ|a_n|⁴)`. -/
theorem fourth_power_identity (S : Finset ℤ) (a : ℤ → ℂ) (s : ℝ) :
    ∫ t in s..s + TL L, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 =
      TL L / L * (2 * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 - ∑ n ∈ S, ‖a n‖ ^ 4) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [integral_x]
  have hF : ∀ n1 n2 n3 n4 : ℤ, Continuous fun t : ℝ => A4 a n1 n2 n3 n4 *
      P4 L t n1 n2 n3 n4 * (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) := fun n1 n2 n3 n4 =>
    (continuous_const.mul (continuous_P4 n1 n2 n3 n4)).mul continuous_const
  have key : ∀ n1 n2 n3 n4 : ℤ, ∫ t in s..s + TL L, A4 a n1 n2 n3 n4 * P4 L t n1 n2 n3 n4 *
      (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0) =
      ((TL L / L : ℝ) : ℂ) * (A4 a n1 n2 n3 n4 *
        (if (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) then (1 : ℂ) else 0)) := by
    intro n1 n2 n3 n4
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_P4]
    have hP : ((n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1)) ↔
        (n1 + n2 = n3 + n4 ∧ n1 ^ 2 + n2 ^ 2 = n3 ^ 2 + n4 ^ 2) := (count _ _ _ _).symm
    simp only [hP, ite_and]
    split_ifs <;> rw [Complex.ofReal_div] <;> ring
  calc ∫ t in s..s + TL L, ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, A4 a n1 n2 n3 n4 *
        P4 L t n1 n2 n3 n4 * (if n1 + n2 = n3 + n4 then (L : ℂ)⁻¹ else 0)
      = ∑ n1 ∈ S, ∑ n2 ∈ S, ∑ n3 ∈ S, ∑ n4 ∈ S, ((TL L / L : ℝ) : ℂ) * (A4 a n1 n2 n3 n4 *
          (if (n3 = n1 ∧ n4 = n2) ∨ (n3 = n2 ∧ n4 = n1) then (1 : ℂ) else 0)) := by
        rw [intervalIntegral.integral_finsetSum fun n1 _ => (continuous_finsetSum _ fun n2 _ =>
          continuous_finsetSum _ fun n3 _ => continuous_finsetSum _ fun n4 _ =>
            hF n1 n2 n3 n4).intervalIntegrable _ _]
        refine Finset.sum_congr rfl fun n1 _ => ?_
        rw [intervalIntegral.integral_finsetSum fun n2 _ => (continuous_finsetSum _ fun n3 _ =>
          continuous_finsetSum _ fun n4 _ => hF n1 n2 n3 n4).intervalIntegrable _ _]
        refine Finset.sum_congr rfl fun n2 _ => ?_
        rw [intervalIntegral.integral_finsetSum fun n3 _ => (continuous_finsetSum _ fun n4 _ =>
          hF n1 n2 n3 n4).intervalIntegrable _ _]
        refine Finset.sum_congr rfl fun n3 _ => ?_
        rw [intervalIntegral.integral_finsetSum fun n4 _ => (hF n1 n2 n3 n4).intervalIntegrable _ _]
        exact Finset.sum_congr rfl fun n4 _ => key n1 n2 n3 n4
    _ = _ := by
        simp only [← Finset.mul_sum]
        rw [sum_resonant]
        push_cast
        ring

#print axioms fourth_power_identity

/-- **`eq:root-L4-free` for finite Fourier sums**: on every interval `[α, β]` of length at most
`T_L`, `∫_α^β ∫_{𝕋_L} |U(t)f|⁴ dx dt ≤ (2T_L/L) ‖f‖₂⁴`, `‖f‖₂² = Σ|a_n|²`. -/
theorem L4_free_bound (S : Finset ℤ) (a : ℤ → ℂ) {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) :
    ∫ t in α..β, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 ≤
      2 * TL L / L * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
  have hL : 0 < L := Fact.out
  have hmono := intervalIntegral.integral_mono_interval (μ := MeasureSpace.volume)
    (f := fun t => ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4) (le_refl α) hαβ hlen
    (Eventually.of_forall fun t => integral_nonneg fun x => by positivity)
    ((continuous_inner S a).intervalIntegrable _ _)
  refine hmono.trans ?_
  rw [fourth_power_identity]
  have h4 : 0 ≤ ∑ n ∈ S, ‖a n‖ ^ 4 := Finset.sum_nonneg fun n _ => by positivity
  have hT : 0 ≤ TL L / L := div_nonneg TL_pos.le hL.le
  calc TL L / L * (2 * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 - ∑ n ∈ S, ‖a n‖ ^ 4)
      ≤ TL L / L * (2 * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2) := by gcongr; linarith
    _ = 2 * TL L / L * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by ring

#print axioms L4_free_bound

end QuantumNLS.L4Strichartz
