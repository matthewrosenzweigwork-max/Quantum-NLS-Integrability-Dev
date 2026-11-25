import Mathlib
import QuantumNLS.Local007Bridge
import QuantumNLS.Local007Gauge

/-! LOCAL-007 stage K: from the LOCAL-003 spectral package at index `n` to the zero set of the discriminant.

`zero_char`: if the eigenspaces of `𝓛_u` (parity `n`) at `λ` in the disc `|λ - p_n| < r` have dimension
`count λ {a+|b|, a-|b|}` and every other `λ` in the disc is in the resolvent set (exactly the LOCAL-003
conclusions), then for `|w| < r`:
`Δ_{boost(-n)u}(w) = 2 ↔ w = (a - p_n) ± |b|`.
`params_unique`: the pair `(α, t)` with `t ≥ 0` is determined by this characterization. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace QuantumNLS.Local007Link
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.LocalSpectral (H2 LuGraph IsResolvent parity circleRep)
open QuantumNLS.RootMassBoostSymbol (boost)
variable {L κ r : ℝ} [Fact (0 < L)]

theorem parity_cast (n : ℤ) : (((parity n : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ n := by
  unfold QuantumNLS.LocalSpectral.parity
  by_cases h : Even n
  · rw [if_pos h, h.neg_one_zpow]; simp
  · rw [if_neg h]
    have : Odd n := Int.not_even_iff_odd.1 h
    rw [this.neg_one_zpow]; simp

theorem zero_char (u : L2T L) (n : ℤ) (a : ℝ) (b : ℂ)
    (hEig : ∀ lam : ℂ, ‖lam - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r →
      ∃ Eig : Submodule ℂ (H2 L),
        (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ∧
        Module.finrank ℂ Eig = Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)})
    (hRes : ∀ lam : ℂ, ‖lam - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r → lam ≠ ((a + ‖b‖ : ℝ) : ℂ) →
      lam ≠ ((a - ‖b‖ : ℝ) : ℂ) → ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) lam R)
    (hκ : 0 ≤ κ) :
    ∀ w : ℂ, ‖w‖ < r →
      (QuantumNLS.L2SpatialTransfer.discriminant κ (boost (-n) u) w = 2 ↔
        (w = ((a - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) + (‖b‖ : ℂ) ∨
          w = ((a - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) - (‖b‖ : ℂ))) := by
  intro w hw
  set lam : ℂ := (QuantumNLS.LocalSpectral.pm L n : ℂ) + w with hlam
  have hl : ‖lam - (QuantumNLS.LocalSpectral.pm L n : ℂ)‖ < r := by rw [hlam]; simpa using hw
  have hpm : QuantumNLS.Local007Gauge.pm L n = QuantumNLS.LocalSpectral.pm L n := rfl
  have h1 : QuantumNLS.L2SpatialTransfer.discriminant κ (boost (-n) u) w = 2 ↔
      QuantumNLS.L2SpatialTransfer.discriminant κ u lam = 2 * (((parity n : ℤˣ) : ℤ) : ℂ) := by
    rw [parity_cast, hlam]
    have := QuantumNLS.Local007Gauge.disc_shift hκ n u w
    rw [hpm] at this
    rw [this]
    have hne : ((-1 : ℂ) ^ n) ≠ 0 := zpow_ne_zero _ (by norm_num)
    constructor
    · intro h; rw [h]; ring
    · intro h; exact mul_left_cancel₀ hne (by rw [h]; ring)
  rw [h1, ← QuantumNLS.Local007Bridge.eigen_iff_disc]
  have h2 : (∃ f : H2 L, f ≠ 0 ∧ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ↔
      (lam = ((a + ‖b‖ : ℝ) : ℂ) ∨ lam = ((a - ‖b‖ : ℝ) : ℂ)) := by
    constructor
    · rintro ⟨f, hf0, hf⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨R, hR⟩ := hRes lam hl hcon.1 hcon.2
      have := hR.2 (f, lam • f) hf
      simp only [sub_self, map_zero] at this
      exact hf0 this.symm
    · intro hlm
      obtain ⟨Eig, hE, hdim⟩ := hEig lam hl
      have hc : 1 ≤ Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} := by
        rcases hlm with h | h
        · rw [h]
          have : ((a + ‖b‖ : ℝ) : ℂ) ∈ ({((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} : Multiset ℂ) := by simp
          exact Multiset.count_pos.2 this
        · rw [h]
          have : ((a - ‖b‖ : ℝ) : ℂ) ∈ ({((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} : Multiset ℂ) := by simp
          exact Multiset.count_pos.2 this
      have hpos : 0 < Module.finrank ℂ Eig := by rw [hdim]; exact hc
      haveI : Module.Finite ℂ Eig := Module.finite_of_finrank_pos hpos
      haveI : Nontrivial Eig := Module.finrank_pos_iff.1 hpos
      obtain ⟨f, hf⟩ := exists_ne (0 : Eig)
      exact ⟨f, fun h => hf (Subtype.ext h), (hE f).1 f.2⟩
  rw [h2, hlam]
  constructor
  · rintro (h | h)
    · left; have : w = ((a + ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ) := by
        rw [← h]; ring
      rw [this]; push_cast; ring
    · right; have : w = ((a - ‖b‖ : ℝ) : ℂ) - (QuantumNLS.LocalSpectral.pm L n : ℂ) := by
        rw [← h]; ring
      rw [this]; push_cast; ring
  · rintro (h | h)
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring

theorem params_unique {α₁ t₁ α₂ t₂ r : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (h1 : |α₁| + t₁ < r)
    (h2 : |α₂| + t₂ < r) {P : ℂ → Prop}
    (c1 : ∀ w : ℂ, ‖w‖ < r → (P w ↔ (w = (α₁ : ℂ) + (t₁ : ℂ) ∨ w = (α₁ : ℂ) - (t₁ : ℂ))))
    (c2 : ∀ w : ℂ, ‖w‖ < r → (P w ↔ (w = (α₂ : ℂ) + (t₂ : ℂ) ∨ w = (α₂ : ℂ) - (t₂ : ℂ)))) :
    α₁ = α₂ ∧ t₁ = t₂ := by
  have hn : ∀ α t : ℝ, 0 ≤ t → |α| + t < r → ‖((α : ℂ) + (t : ℂ))‖ < r ∧ ‖((α : ℂ) - (t : ℂ))‖ < r := by
    intro α t ht h
    constructor
    · rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_le_of_lt ((abs_add_le _ _).trans (by rw [abs_of_nonneg ht])) h
    · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_le_of_lt ((abs_sub _ _).trans (by rw [abs_of_nonneg ht])) h
  obtain ⟨p1, m1⟩ := hn α₁ t₁ ht₁ h1
  obtain ⟨p2, m2⟩ := hn α₂ t₂ ht₂ h2
  have a1 : ((α₁ : ℂ) + t₁ = (α₂ : ℂ) + t₂ ∨ (α₁ : ℂ) + t₁ = (α₂ : ℂ) - t₂) := (c2 _ p1).1 ((c1 _ p1).2 (Or.inl rfl))
  have a2 : ((α₁ : ℂ) - t₁ = (α₂ : ℂ) + t₂ ∨ (α₁ : ℂ) - t₁ = (α₂ : ℂ) - t₂) := (c2 _ m1).1 ((c1 _ m1).2 (Or.inr rfl))
  have a3 : ((α₂ : ℂ) + t₂ = (α₁ : ℂ) + t₁ ∨ (α₂ : ℂ) + t₂ = (α₁ : ℂ) - t₁) := (c1 _ p2).1 ((c2 _ p2).2 (Or.inl rfl))
  have a4 : ((α₂ : ℂ) - t₂ = (α₁ : ℂ) + t₁ ∨ (α₂ : ℂ) - t₂ = (α₁ : ℂ) - t₁) := (c1 _ m2).1 ((c2 _ m2).2 (Or.inr rfl))
  have cast : ∀ x y : ℝ, (x : ℂ) = (y : ℂ) → x = y := fun x y h => Complex.ofReal_injective h
  have b1 : (α₁ + t₁ = α₂ + t₂ ∨ α₁ + t₁ = α₂ - t₂) := by
    rcases a1 with h | h
    · left; exact cast _ _ (by push_cast; exact h)
    · right; exact cast _ _ (by push_cast; exact h)
  have b2 : (α₁ - t₁ = α₂ + t₂ ∨ α₁ - t₁ = α₂ - t₂) := by
    rcases a2 with h | h
    · left; exact cast _ _ (by push_cast; exact h)
    · right; exact cast _ _ (by push_cast; exact h)
  have b3 : (α₂ + t₂ = α₁ + t₁ ∨ α₂ + t₂ = α₁ - t₁) := by
    rcases a3 with h | h
    · left; exact cast _ _ (by push_cast; exact h)
    · right; exact cast _ _ (by push_cast; exact h)
  have b4 : (α₂ - t₂ = α₁ + t₁ ∨ α₂ - t₂ = α₁ - t₁) := by
    rcases a4 with h | h
    · left; exact cast _ _ (by push_cast; exact h)
    · right; exact cast _ _ (by push_cast; exact h)
  constructor <;> rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> rcases b3 with h3 | h3 <;>
    rcases b4 with h4 | h4 <;> first | linarith | (exfalso; linarith)

end QuantumNLS.Local007Link
#print axioms QuantumNLS.Local007Link.zero_char
#print axioms QuantumNLS.Local007Link.params_unique
