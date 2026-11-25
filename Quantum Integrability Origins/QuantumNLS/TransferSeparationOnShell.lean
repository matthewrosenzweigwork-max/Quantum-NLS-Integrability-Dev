import QuantumNLS.TransferSeparationLiteral
import QuantumNLS.BetheOnShell
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# R-533B0EC6 `basis:lem:separation` (periodic_basis.tex:399-416), clause (2) by the printed route

Printed text (lines 415-418): "For on-shell vectors the transfer functions are entire. If their values
agreed for every real `x`, the identity theorem would make them identical. The parameter at which they
differ may also be chosen away from the finitely many displayed apparent poles."  (Lines 353-354: "Apparent
poles ... are removable on shell, by `basis:eq:bethe`.")

This module (imports read-only: `TransferSeparationLiteral` 74654f7e, hence Sol's
`TransferSeparationContinuityRepair` 32eec7f8; `BetheOnShell` for `entire_factor_finset` and
`shifted_difference_ne_zero`) proves exactly these three printed steps.

* (i) `numer_zero_of_onShell`, `exists_entire_factor`, `exists_entire_extension`: on the literal Bethe
  equations the denominator-cleared numerator vanishes at every rapidity; with distinct rapidities the
  denominator `∏(z - q_j)` divides it in the ring of entire functions, so `s_q` has an entire extension.
* (ii)+(iii) `separation_entire`: for two such configurations with distinct multisets and any finite
  `F ⊂ ℝ`, if `s_p(x) = s_q(x)` at all real `x` outside `F` and the rapidities, the entire extensions
  agree on a real accumulation point, hence on all of `ℂ` (identity theorem on connected `univ`), hence
  `s_p = s_q` off the poles, contradicting clause (1).

**Hypothesis precision (deviation recorded).**  "On shell" means `OnShell` (the literal Bethe
equations) *together with distinct rapidities* (`BetheRoots`).  This is the source's setting: the
eigenvalue calculation "require[s] distinct roots and the on-shell equations" (line 365) and the actual
roots are strictly decreasing (`sourceRoots_betheRoots`).  The distinctness is necessary for the printed
removability step: `repeated_root_not_entire` proves that `OnShell` alone (e.g. `N = 2`, `q = (π/L, π/L)`)
does NOT make `s_q` entire (double pole, nonzero simple-pole residue), so (i) is false for repeated roots.
For merely `OnShell` hypotheses the conclusion of clause (2) remains true by the (non-printed)
identity-theorem route on the punctured plane (frozen `TransferSeparationLiteral.separation_on_shell`).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial
open Polynomial Filter Topology
open QuantumNLS.TransferSeparationContinuityRepair

namespace QuantumNLS.TransferSeparationOnShell

variable {N : ℕ}

/-- Denominator-cleared numerator of the literal transfer function. -/
def numer (L c : ℝ) (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (shiftPoly q (-(Complex.I * c))).eval z +
    Complex.exp (Complex.I * L * z) * (shiftPoly q (Complex.I * c)).eval z

/-- **On-shell vector in the source's sense**: distinct real rapidities satisfying the literal
Bethe equations `basis:eq:bethe`. -/
def BetheRoots (L c : ℝ) (q : Fin N → ℝ) : Prop :=
  Function.Injective q ∧ OnShell L c q

theorem numer_differentiable (L c : ℝ) (q : Fin N → ℝ) : Differentiable ℂ (numer L c q) := by
  intro z
  apply DifferentiableAt.add (Polynomial.differentiableAt _)
  exact (Complex.differentiableAt_exp.comp z
    ((differentiableAt_const _).mul differentiableAt_id)).mul (Polynomial.differentiableAt _)

theorem sFun_mul_denominator (L c : ℝ) (q : Fin N → ℝ) (z : ℂ) (hz : ∀ k, z ≠ q k) :
    sFun L c q z * (shiftPoly q 0).eval z = numer L c q z := by
  unfold sFun numer
  rw [add_mul, mul_assoc, prod_plus_mul c q z hz, prod_minus_mul c q z hz]

/-! ### (i) Removability of the apparent poles on shell -/

/-- **The Bethe equations make the numerator vanish at every rapidity** (no distinctness needed). -/
theorem numer_zero_of_onShell {L c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hos : OnShell L c q)
    (i : Fin N) : numer L c q (q i) = 0 := by
  classical
  have hden : (∏ k ∈ Finset.univ.erase i, (((q i : ℂ) - q k) - Complex.I * c)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => QuantumNLS.BetheOnShell.shifted_difference_ne_zero hc.ne' _ _
  have hb : Complex.exp (Complex.I * L * q i) *
      (∏ k ∈ Finset.univ.erase i, (((q i : ℂ) - q k) - Complex.I * c)) =
      ∏ k ∈ Finset.univ.erase i, (((q i : ℂ) - q k) + Complex.I * c) := by
    rw [hos i, Finset.prod_div_distrib, div_mul_cancel₀ _ hden]
  have hplus : (∏ k, ((q i : ℂ) - ((q k : ℂ) + -(Complex.I * c)))) =
      Complex.I * c * ∏ k ∈ Finset.univ.erase i, (((q i : ℂ) - q k) + Complex.I * c) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [sub_add_eq_sub_sub, sub_neg_eq_add, sub_self, zero_add]
  have hminus : (∏ k, ((q i : ℂ) - ((q k : ℂ) + Complex.I * c))) =
      -(Complex.I * c) * ∏ k ∈ Finset.univ.erase i, (((q i : ℂ) - q k) - Complex.I * c) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
  unfold numer
  simp only [eval_shiftPoly]
  rw [hplus, hminus, ← hb]
  ring

/-- With distinct rapidities, the full denominator `∏(z - q_j)` divides the numerator in the entire
functions. -/
theorem exists_entire_factor {L c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : BetheRoots L c q) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, numer L c q z = (shiftPoly q 0).eval z * g z := by
  classical
  let S : Finset ℂ := Finset.univ.image (fun i => (q i : ℂ))
  have hi : Function.Injective (fun i => (q i : ℂ)) := Complex.ofReal_injective.comp hq.1
  obtain ⟨g, hg, hfg⟩ := QuantumNLS.BetheOnShell.entire_factor_finset S
    (numer_differentiable L c q) (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact numer_zero_of_onShell hc hq.2 i)
  refine ⟨g, hg, fun z => ?_⟩
  have hprod : (∏ a ∈ S, (z - a)) = (shiftPoly q 0).eval z := by
    rw [Finset.prod_image (fun i _ j _ h => hi h)]
    simp only [eval_shiftPoly, add_zero]
  rw [hfg, hprod]

/-- **Printed step (i)**: on shell (distinct roots, literal Bethe equations) `s_q` has an entire
extension (the apparent poles are removable).  Equality is asserted off the rapidities; Lean's total
division is not used at the apparent poles. -/
theorem exists_entire_extension {L c : ℝ} (hc : 0 < c) {q : Fin N → ℝ} (hq : BetheRoots L c q) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, (∀ k, z ≠ q k) → g z = sFun L c q z := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_factor hc hq
  refine ⟨g, hg, fun z hz => ?_⟩
  have hd : (shiftPoly q 0).eval z ≠ 0 := by
    rw [eval_shiftPoly]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by
      simpa only [add_zero] using sub_ne_zero.mpr (hz k)
  have he := sFun_mul_denominator L c q z hz
  rw [hfg, mul_comm] at he
  exact (mul_left_cancel₀ hd he).symm

/-! ### (ii)-(iii) Identity theorem on `ℂ` -/

/-- **Clause (2), printed route** (`L, c > 0`): for two on-shell configurations (distinct rapidities,
literal Bethe equations) with distinct multisets, and any finite `F ⊂ ℝ`, there is a real `x ∉ F`,
distinct from all the (apparent-pole) rapidities, with `s_p(x) ≠ s_q(x)`.

Proof: otherwise the entire extensions `g_p, g_q` (step (i)) agree on all real `x` outside the finite
set `F ∪ {p_j} ∪ {q_j}`, hence on a real accumulation point; the identity theorem on `ℂ` makes
`g_p = g_q`; so `s_p = s_q` off the poles; clause (1) gives equal multisets. -/
theorem separation_entire {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {p q : Fin N → ℝ}
    (hp : BetheRoots L c p) (hq : BetheRoots L c q) (hne : msOf p ≠ msOf q) (F : Finset ℝ) :
    ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧ sFun L c p x ≠ sFun L c q x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨gp, hgp, hgpe⟩ := exists_entire_extension hc hp
  obtain ⟨gq, hgq, hgqe⟩ := exists_entire_extension hc hq
  set B : Finset ℝ := F ∪ Finset.univ.image p ∪ Finset.univ.image q with hB
  obtain ⟨x0, hx0⟩ := Infinite.exists_notMem_finset B
  have hev : ∀ᶠ x : ℝ in 𝓝 x0, gp (x : ℂ) = gq (x : ℂ) := by
    have hmem : ((B : Set ℝ))ᶜ ∈ 𝓝 x0 :=
      B.finite_toSet.isClosed.isOpen_compl.mem_nhds hx0
    filter_upwards [hmem] with x hx
    have hxB : x ∉ B := hx
    have hxF : x ∉ F := fun h => hxB (by simp [hB, h])
    have hxpq : ∀ j, x ≠ p j ∧ x ≠ q j := fun j =>
      ⟨fun h => hxB (by simp [hB, h]), fun h => hxB (by simp [hB, h])⟩
    rw [hgpe x (fun k h => (hxpq k).1 (by exact_mod_cast h)),
      hgqe x (fun k h => (hxpq k).2 (by exact_mod_cast h))]
    exact hcon x hxF hxpq
  have hfreq : ∃ᶠ x : ℝ in 𝓝[≠] x0, gp (x : ℂ) = gq (x : ℂ) :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x0) (𝓝[≠] (x0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun h' => hx (Complex.ofReal_injective h')
  have hfreqC : ∃ᶠ z : ℂ in 𝓝[≠] (x0 : ℂ), gp z = gq z := htend.frequently hfreq
  have hap : AnalyticOnNhd ℂ gp Set.univ := fun z _ => hgp.analyticAt z
  have haq : AnalyticOnNhd ℂ gq Set.univ := fun z _ => hgq.analyticAt z
  have heq := hap.eqOn_of_preconnected_of_frequently_eq haq isPreconnected_univ
    (Set.mem_univ (x0 : ℂ)) hfreqC
  refine hne (QuantumNLS.TransferSeparationLiteral.separation_literal hL hc p q ∅ ?_)
  intro z hz
  have hz' : z ∉ poles p q := by simpa using hz
  obtain ⟨h1, h2⟩ := not_mem_poles hz'
  rw [← hgpe z h1, ← hgqe z h2]
  exact heq (Set.mem_univ z)

/-! ### Assembly -/

/-- **`basis:lem:separation` (R-533B0EC6), literal assembly** for `c > 0`, `L > 0`:
(1) [printed asymptotic route] distinct real rapidity multisets have distinct transfer functions
(equal transfer functions away from the real poles force equal multisets);
(2) [printed entire-function route] if both configurations are on shell, i.e. distinct rapidities
satisfying the literal Bethe equations, and their multisets differ, then their values differ at some
real spectral parameter, which can be chosen outside any prescribed finite set and away from the
finitely many apparent poles. -/
theorem basis_lem_separation_literal {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    (∀ p q : Fin N → ℝ, (∀ z : ℂ, z ∉ poles p q → sFun L c p z = sFun L c q z) →
      msOf p = msOf q) ∧
    (∀ p q : Fin N → ℝ, BetheRoots L c p → BetheRoots L c q → msOf p ≠ msOf q →
      ∀ F : Finset ℝ, ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧
        sFun L c p x ≠ sFun L c q x) :=
  ⟨fun p q h => QuantumNLS.TransferSeparationLiteral.separation_literal hL hc p q ∅
      fun z hz => h z (by simpa using hz),
   fun _ _ hp hq hne F => separation_entire hL hc hp hq hne F⟩

/-! ### Binding to the actual source roots, and necessity of distinctness -/

/-- The actual Yang-Yang source roots are on shell in the above sense (Sol's frozen
`BetheOnShell.sourceRoots_onShell`, `BetheSmooth.sourceRoots_strictAnti`). -/
theorem sourceRoots_betheRoots {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (M+1) → ℤ} (hn : Antitone n) :
    BetheRoots L c (BetheSmooth.sourceRoots L n c) :=
  ⟨(BetheSmooth.sourceRoots_strictAnti hL hc hn).injective,
    QuantumNLS.BetheOnShell.sourceRoots_onShell hL hc hn⟩

/-- Repeated rapidities `q = (a, a)`. -/
def repeatedRoots (a : ℝ) : Fin 2 → ℝ := fun _ => a

theorem repeatedRoots_onShell {L c a : ℝ} (hc : 0 < c)
    (ha : Complex.exp (Complex.I * L * (a : ℂ)) = -1) : OnShell L c (repeatedRoots a) := by
  classical
  intro j
  have hcard : (Finset.univ.erase j).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; simp
  have hIc : Complex.I * (c : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hc.ne')
  have hterm : ((a : ℂ) - a + Complex.I * c) / ((a : ℂ) - a - Complex.I * c) = -1 := by
    rw [sub_self, zero_add, zero_sub, div_neg_self hIc]
  simp only [repeatedRoots]
  rw [ha, Finset.prod_const, hcard, pow_one, hterm]

/-- **Distinctness is necessary for step (i)**: for the on-shell repeated configuration `(a, a)`
(`e^{iLa} = -1`, e.g. `a = π/L`; `c, L > 0`) the transfer function has NO entire extension (the double
pole survives: the simple-pole coefficient of the cleared numerator is `4ic + iLc² ≠ 0`). -/
theorem repeated_root_not_entire {L c a : ℝ} (hL : 0 < L) (hc : 0 < c)
    (ha : Complex.exp (Complex.I * L * (a : ℂ)) = -1) :
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, (∀ k, z ≠ repeatedRoots a k) →
      g z = sFun L c (repeatedRoots a) z := by
  rintro ⟨g, hg, hge⟩
  have hnum : ∀ z : ℂ, numer L c (repeatedRoots a) z =
      (z - a + Complex.I * c) ^ 2 + Complex.exp (Complex.I * L * z) * (z - a - Complex.I * c) ^ 2 := by
    intro z
    simp only [numer, eval_shiftPoly, Fin.prod_univ_two, repeatedRoots]
    ring
  have hden : ∀ z : ℂ, (shiftPoly (repeatedRoots a) 0).eval z = (z - a) ^ 2 := by
    intro z
    simp only [eval_shiftPoly, Fin.prod_univ_two, repeatedRoots]
    ring
  have hoff : ∀ z : ℂ, z ≠ a → (z - a) ^ 2 * g z = numer L c (repeatedRoots a) z := by
    intro z hz
    have hz' : ∀ k, z ≠ repeatedRoots a k := fun k => by simpa [repeatedRoots] using hz
    rw [hge z hz', ← sFun_mul_denominator L c _ z hz', hden, mul_comm]
  have hall : (fun z : ℂ => (z - a) ^ 2 * g z) = numer L c (repeatedRoots a) := by
    refine Continuous.ext_on (dense_compl_singleton (a : ℂ)) ?_ (numer_differentiable L c _).continuous ?_
    · exact (continuous_id.sub continuous_const).pow 2 |>.mul hg.continuous
    · intro z hz
      exact hoff z hz
  have h1 : HasDerivAt (fun z : ℂ => (z - a) ^ 2 * g z)
      (((2 : ℕ) : ℂ) * (a - a) ^ (2 - 1) * 1 * g a + (a - a) ^ 2 * deriv g a) a :=
    (((hasDerivAt_id (a : ℂ)).sub_const (a : ℂ)).pow 2).mul (hg.differentiableAt.hasDerivAt)
  have he : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * L * z))
      (Complex.exp (Complex.I * L * a) * (Complex.I * L)) a := by
    simpa using ((hasDerivAt_id (a : ℂ)).const_mul (Complex.I * (L : ℂ))).cexp
  have hA : HasDerivAt (fun z : ℂ => (z - a + Complex.I * c) ^ 2)
      (((2 : ℕ) : ℂ) * (a - a + Complex.I * c) ^ (2 - 1) * 1) a :=
    (((hasDerivAt_id (a : ℂ)).sub_const (a : ℂ)).add_const (Complex.I * c)).pow 2
  have hB : HasDerivAt (fun z : ℂ => (z - a - Complex.I * c) ^ 2)
      (((2 : ℕ) : ℂ) * (a - a - Complex.I * c) ^ (2 - 1) * 1) a :=
    (((hasDerivAt_id (a : ℂ)).sub_const (a : ℂ)).sub_const (Complex.I * c)).pow 2
  have h2 : HasDerivAt (fun z : ℂ => (z - a + Complex.I * c) ^ 2 +
      Complex.exp (Complex.I * L * z) * (z - a - Complex.I * c) ^ 2)
      (((2 : ℕ) : ℂ) * (a - a + Complex.I * c) ^ (2 - 1) * 1 +
        (Complex.exp (Complex.I * L * a) * (Complex.I * L) * (a - a - Complex.I * c) ^ 2 +
          Complex.exp (Complex.I * L * a) * (((2 : ℕ) : ℂ) * (a - a - Complex.I * c) ^ (2 - 1) * 1)))
      a := hA.add (he.mul hB)
  have hfun : (fun z : ℂ => (z - a + Complex.I * c) ^ 2 +
      Complex.exp (Complex.I * L * z) * (z - a - Complex.I * c) ^ 2) =
      fun z : ℂ => (z - a) ^ 2 * g z := by
    funext z
    rw [← hnum z, ← congrFun hall z]
  rw [hfun] at h2
  have e := h1.unique h2
  rw [ha] at e
  simp only [sub_self, Nat.cast_ofNat, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_mul, zero_add] at e
  have e2 : Complex.I * c * 4 + Complex.I * L * c ^ 2 = 0 := by
    have : (2 - 1 : ℕ) = 1 := rfl
    simp only [this, pow_one] at e
    linear_combination -e + (Complex.I * c ^ 2 * L) * Complex.I_sq
  have e3 : ((4 * c + L * c ^ 2 : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast; linear_combination e2
  have e4 : ((4 * c + L * c ^ 2 : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.1 e3).resolve_right Complex.I_ne_zero
  have e5 : 4 * c + L * c ^ 2 = 0 := by exact_mod_cast e4
  nlinarith [mul_pos hL (mul_pos hc hc)]

/-- The standard instance `a = π/L`. -/
theorem exp_pi_div {L : ℝ} (hL : 0 < L) :
    Complex.exp (Complex.I * L * ((Real.pi / L : ℝ) : ℂ)) = -1 := by
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have : Complex.I * (L : ℂ) * ((Real.pi / L : ℝ) : ℂ) = Real.pi * Complex.I := by
    push_cast; field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- Instance `a = π/L`: `OnShell` (repeated rapidities) does not make `s_q` entire. -/
theorem repeated_root_pi_div_onShell_not_entire {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    OnShell L c (repeatedRoots (Real.pi / L)) ∧
    ¬ ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, (∀ k, z ≠ repeatedRoots (Real.pi / L) k) →
      g z = sFun L c (repeatedRoots (Real.pi / L)) z :=
  ⟨repeatedRoots_onShell hc (exp_pi_div hL), repeated_root_not_entire hL hc (exp_pi_div hL)⟩

/-- For the actual source roots (Yang-Yang labels, `n` antitone) of two label vectors with distinct
rapidity multisets, clause (2) holds through the entire extensions. -/
theorem sourceRoots_separation {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n n' : Fin (M+1) → ℤ} (hn : Antitone n) (hn' : Antitone n')
    (hne : msOf (BetheSmooth.sourceRoots L n c) ≠ msOf (BetheSmooth.sourceRoots L n' c))
    (F : Finset ℝ) :
    ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ BetheSmooth.sourceRoots L n c j ∧ x ≠ BetheSmooth.sourceRoots L n' c j) ∧
      sFun L c (BetheSmooth.sourceRoots L n c) x ≠ sFun L c (BetheSmooth.sourceRoots L n' c) x :=
  separation_entire hL hc (sourceRoots_betheRoots hL hc hn) (sourceRoots_betheRoots hL hc hn') hne F

end QuantumNLS.TransferSeparationOnShell

#print axioms QuantumNLS.TransferSeparationOnShell.numer_zero_of_onShell
#print axioms QuantumNLS.TransferSeparationOnShell.exists_entire_factor
#print axioms QuantumNLS.TransferSeparationOnShell.exists_entire_extension
#print axioms QuantumNLS.TransferSeparationOnShell.separation_entire
#print axioms QuantumNLS.TransferSeparationOnShell.basis_lem_separation_literal
#print axioms QuantumNLS.TransferSeparationOnShell.sourceRoots_betheRoots
#print axioms QuantumNLS.TransferSeparationOnShell.repeated_root_not_entire
#print axioms QuantumNLS.TransferSeparationOnShell.repeated_root_pi_div_onShell_not_entire
#print axioms QuantumNLS.TransferSeparationOnShell.sourceRoots_separation

/- Compile-time proof-dependency audit (adds no declaration or assumption).  The assembled theorem must
(a) reach the entire extension (`exists_entire_extension` / `exists_entire_factor` /
`numer_zero_of_onShell`), the identity theorem on `univ`, and the clause-1 printed asymptotic route;
(b) NOT reach the frozen punctured-plane identity-theorem proof of clause 2
(`TransferSeparationLiteral.separation_real`, `separation_on_shell`, `sFun_differentiableAt`,
`basis_lem_separation`) nor the inherited differentiation/degree route. -/
open Lean in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[
    ``QuantumNLS.TransferSeparationLiteral.separation_real,
    ``QuantumNLS.TransferSeparationLiteral.separation_on_shell,
    ``QuantumNLS.TransferSeparationLiteral.sFun_differentiableAt,
    ``QuantumNLS.TransferSeparationLiteral.basis_lem_separation,
    ``QuantumNLS.TransferSeparationContinuityRepair.exp_poly_eq_zero,
    ``QuantumNLS.TransferSeparationContinuityRepair.separation_cofinite,
    ``QuantumNLS.TransferSeparationContinuityRepair.separation,
    ``QuantumNLS.TransferSeparationRepairBridge.separation_cofinite]
  let required : Array Name := #[
    ``QuantumNLS.TransferSeparationOnShell.exists_entire_extension,
    ``QuantumNLS.TransferSeparationOnShell.exists_entire_factor,
    ``QuantumNLS.TransferSeparationOnShell.numer_zero_of_onShell,
    ``QuantumNLS.BetheOnShell.entire_factor_finset,
    ``AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq,
    ``QuantumNLS.TransferSeparationLiteral.separation_literal,
    ``QuantumNLS.TransferSeparationLiteral.exp_poly_zero_literal,
    ``QuantumNLS.TransferSeparationLiteral.tendsto_exp_mul_poly,
    ``QuantumNLS.TransferSeparationLiteral.exists_lower_bound]
  let audit (root : Name) : Std.HashSet Name × Array Name := Id.run do
    let mut pending : Array Name := #[root]
    let mut seen : Std.HashSet Name := {}
    let mut bad : Array Name := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      unless seen.contains n do
        seen := seen.insert n
        if forbidden.contains n then
          bad := bad.push n
        if let some ci := env.find? n then
          pending := pending ++ ci.type.getUsedConstants
          if let some v := ci.value? (allowOpaque := true) then
            pending := pending ++ v.getUsedConstants
    return (seen, bad)
  let (seen1, bad1) := audit ``QuantumNLS.TransferSeparationOnShell.basis_lem_separation_literal
  unless bad1.isEmpty do throwError "assembled theorem reached forbidden declaration(s) {bad1}"
  for n in required do
    unless seen1.contains n do throwError "assembled theorem missing required declaration {n}"
  -- clause 2 alone: through the entire extension and the identity theorem, not the TS1 clause-2 route
  let (seen2, bad2) := audit ``QuantumNLS.TransferSeparationOnShell.separation_entire
  unless bad2.isEmpty do throwError "clause 2 reached forbidden declaration(s) {bad2}"
  for n in #[``QuantumNLS.TransferSeparationOnShell.exists_entire_extension,
      ``QuantumNLS.TransferSeparationOnShell.numer_zero_of_onShell,
      ``QuantumNLS.BetheOnShell.entire_factor_finset,
      ``AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq] do
    unless seen2.contains n do throwError "clause 2 missing required declaration {n}"
  Lean.logInfo m!"audit passed: assembled theorem {seen1.size} transitive constants, clause 2 {seen2.size}; clause 2 reaches the entire extension (numerator zeros, entire_factor_finset) and the identity theorem on univ; frozen punctured-plane clause-2 route and inherited exp_poly_eq_zero / separation_cofinite not reached."
