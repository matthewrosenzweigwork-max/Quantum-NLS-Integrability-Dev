import Mathlib
import QuantumNLS.Local007Link
import QuantumNLS.Local007MassC
import QuantumNLS.Local007AlgA
import QuantumNLS.RootIndexedMassesCollapsed

/-! LOCAL-007 stage N: the index-`n` mass through the quadratic factor.

For `r ∈ (0, 2π/L)` there is `ρ > 0` such that for every `u` with `‖u‖ < ρ`, every `n`, and every `(a, b)` satisfying
the LOCAL-003 eigen/resolvent conclusions at `(u, n, r)` (with `a ± |b|` in the disc):
`I_n(u) = (L |b|²/(4κ)) Re Phi(F(boost(-n)u), a - p_n, |b|²)`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace QuantumNLS.Local007MassN
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Zeros (Dl)
open QuantumNLS.Local007AlgB (Phi A)
open QuantumNLS.LocalSpectral (H2 LuGraph IsResolvent parity circleRep)
open QuantumNLS.RootMassBoostSymbol (boost norm_boost)
variable {L κ : ℝ} [Fact (0 < L)]

theorem mass_n (hκ : 0 < κ) {r : ℝ} (hr0 : 0 < r) (hr : r < 2 * Real.pi / L) {c : ℝ} (hc : c = 1 / (8 * L))
    (Fh : L2T L → A) (hFh : ∀ v : L2T L, ‖v‖ < 1 → ∀ θ : ℝ,
      Fh v θ = Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : L2T L, ‖u‖ < ρ → ∀ (n : ℤ) (a : ℝ) (b : ℂ),
      (∀ lam : ℂ, ‖lam - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r →
        ∃ Eig : Submodule ℂ (H2 L),
          (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ∧
          Module.finrank ℂ Eig = Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)}) →
      (∀ lam : ℂ, ‖lam - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r → lam ≠ ((a + ‖b‖ : ℝ) : ℂ) →
        lam ≠ ((a - ‖b‖ : ℝ) : ℂ) → ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) lam R) →
      ‖((a + ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r →
      ‖((a - ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r →
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n =
        (L * ‖b‖ ^ 2 / (4 * κ)) *
          (Phi c L (Fh (boost (-n) u)) (a - QuantumNLS.LocalSpectral.pm L n) (‖b‖ ^ 2)).re := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρZ, hρZ, hZ⟩ := QuantumNLS.Local007Zeros.phys_factor (L := L) κ hr0 hr
  obtain ⟨ρc, hρc, hcl⟩ := QuantumNLS.Local007Zeros.close_free (L := L) κ (2 * Real.pi / L) (1 / 400) (by norm_num)
  refine ⟨min (min ρZ ρc) (min 1 (1 / (κ * L + 1))), lt_min (lt_min hρZ hρc) (lt_min one_pos (by positivity)), ?_⟩
  intro u hu n a b hEig hRes hin1 hin2
  have hu1 : ‖u‖ < ρZ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu2 : ‖u‖ < ρc := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu3 : ‖u‖ < 1 := lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_left _ _))
  have hu4 : ‖u‖ < 1 / (κ * L + 1) := lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_right _ _))
  set v : L2T L := boost (-n) u with hv
  have hvn : ‖v‖ = ‖u‖ := norm_boost _ _
  have hsmall : κ * L * ‖v‖ ^ 2 < 1 := by
    rw [hvn]
    have h0 : 0 ≤ ‖u‖ := norm_nonneg _
    have h1 : ‖u‖ * (κ * L + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hu4
    have h2 : ‖u‖ ^ 2 ≤ ‖u‖ := by nlinarith
    nlinarith [mul_pos hκ hL]
  have hclB : ∀ j : ℤ, ∀ z : ℂ, ‖z‖ ≤ 2 * Real.pi / L →
      ‖Dl κ (boost (-j) v) z - 2 * Complex.cos ((L : ℂ) * z / 2)‖ ≤ 1 / 400 := fun j z hz =>
    hcl (boost (-j) v) (by rw [norm_boost, hvn]; exact hu2) z hz
  have hzc := QuantumNLS.Local007Link.zero_char (r := r) u n a b hEig hRes hκ.le
  have hα : |a - QuantumNLS.LocalSpectral.pm L n| + ‖b‖ < r := by
    have e1 : ‖((a + ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ =
        |a - QuantumNLS.LocalSpectral.pm L n + ‖b‖| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; congr 1; ring
    have e2 : ‖((a - ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ =
        |a - QuantumNLS.LocalSpectral.pm L n - ‖b‖| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; congr 1; ring
    rw [e1] at hin1; rw [e2] at hin2
    have h1 := abs_lt.1 hin1
    have h2 := abs_lt.1 hin2
    rcases abs_cases (a - QuantumNLS.LocalSpectral.pm L n) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨hloc, hz1, hz2, hder, H, hH, hfH, hHre, hHb⟩ :=
    hZ v (by rw [hvn]; exact hu1) (a - QuantumNLS.LocalSpectral.pm L n) ‖b‖ (norm_nonneg _) hα hzc
  have hcl2 : ∀ x : ℝ, |x| ≤ Real.pi / L →
      |(Dl κ v (x : ℂ)).re - 2 * Real.cos (L * x / 2)| ≤ 1 / 400 := by
    intro x hx
    have hxn : ‖(x : ℂ)‖ ≤ 2 * Real.pi / L := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine hx.trans ?_
      rw [div_le_div_iff_of_pos_right hL]; linarith [Real.pi_pos]
    have h1 := hcl v (by rw [hvn]; exact hu2) (x : ℂ) hxn
    have : (Dl κ v (x : ℂ)).re - 2 * Real.cos (L * x / 2) =
        (Dl κ v (x : ℂ) - 2 * Complex.cos ((L : ℂ) * (x : ℂ) / 2)).re := by
      have e : (L : ℂ) * (x : ℂ) / 2 = ((L * x / 2 : ℝ) : ℂ) := by push_cast; ring
      have e2 : (2 * Complex.cos ((L : ℂ) * (x : ℂ) / 2)).re = 2 * Real.cos (L * x / 2) := by
        rw [e, show (2 : ℂ) * Complex.cos ((L * x / 2 : ℝ) : ℂ) = ((2 * Real.cos (L * x / 2) : ℝ) : ℂ) by
          push_cast; ring, Complex.ofReal_re]
      rw [Complex.sub_re, e2]
    rw [this]
    exact (Complex.abs_re_le_norm _).trans h1
  have hmass := QuantumNLS.Local007MassB.cell_mass hκ v hc hH (norm_nonneg b) (by linarith [hloc]) hfH hHre hHb hcl2
    (Fh v) (hFh v (by rw [hvn]; exact hu3))
  rw [← hmass, ← QuantumNLS.Local007MassC.masses_zero hκ v hclB hsmall]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hboost⟩ := QuantumNLS.RootIndexedMassesCollapsed.root_indexed_masses_collapsed hκ u
  have := hboost (-n) 0
  rw [zero_sub, neg_neg] at this
  exact this.symm

end QuantumNLS.Local007MassN
#print axioms QuantumNLS.Local007MassN.mass_n
