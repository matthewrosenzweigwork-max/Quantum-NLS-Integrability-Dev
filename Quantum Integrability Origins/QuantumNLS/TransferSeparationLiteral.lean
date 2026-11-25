import QuantumNLS.TransferSeparationContinuityRepair
import QuantumNLS.TransferSeparationRepairBridge
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# R-533B0EC6 `basis:lem:separation` (periodic_basis.tex:399-416), literal closure

Imports (read-only): Sol's `TransferSeparationContinuityRepair` (definitions `sFun`, `msOf`, `OnShell`,
`poles`, `shiftPoly`, root/multiset lemma `msOf_eq_of_prod_eq`, clearing-denominator lemmas) and
`TransferSeparationRepairBridge` (binding to the original scalar definitions).

**Clause (1), printed route.** Write the difference `s_p - s_q` as `R + e^{iLz} T` with rational
`R = A_p - A_q`, `T = B_p - B_q`; after clearing the denominators `D_p D_q`, `R = U/(D_pD_q)`,
`T = V/(D_pD_q)` with polynomials `U, V`.  On `z = iy`, `y → +∞`: `|e^{iLz}| = e^{-Ly}`, so
`e^{iLz} V(iy)` is exponential decay times at most a power of `y`
(`tendsto_exp_mul_poly`), while a nonzero polynomial is bounded below by a positive constant
(`exists_lower_bound`, polynomial growth `Polynomial.tendsto_norm_atTop`). Hence `U = 0`, then
`V = 0` (`exp_poly_zero_literal`). `U = 0` is `A_p = A_q`; the real poles of
`∏(1 + ic/(z - q_j))` (numerator zeros at `q_j - ic`, off the real axis) give the multiset
(`msOf_eq_of_prod_eq`). No differentiation/degree argument is used.

**Clause (2), identity theorem.** Deviation recorded in `separation_real`: the identity theorem is
applied on the connected punctured plane `ℂ ∖ (poles ∪ F)` (where both `s_p, s_q` are analytic),
not on `ℂ`; the on-shell hypothesis (literal Bethe equations) is therefore not needed for the
conclusion, and the removability of apparent poles on shell is not used (nor claimed: the literal
`OnShell` does not force distinct roots, which a simple-pole removability argument would need).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial
open Polynomial Filter Topology
open QuantumNLS.TransferSeparationContinuityRepair

namespace QuantumNLS.TransferSeparationLiteral

variable {N : ℕ}

/-! ### Asymptotics on `z = iy` -/

theorem norm_exp_imag (L y : ℝ) :
    ‖Complex.exp (Complex.I * L * (Complex.I * y))‖ = Real.exp (-(L * y)) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem norm_eval_le (V : ℂ[X]) {y : ℝ} (hy : 0 ≤ y) :
    ‖V.eval (Complex.I * y)‖ ≤ ∑ k ∈ Finset.range (V.natDegree + 1), ‖V.coeff k‖ * y ^ k := by
  rw [Polynomial.eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hy]

/-- **The exponential term is exponential decay times at most a power of `y`**: for `L > 0` and any
polynomial `V`, `e^{iLz}V(z) → 0` along `z = iy`, `y → +∞`. -/
theorem tendsto_exp_mul_poly {L : ℝ} (hL : 0 < L) (V : ℂ[X]) :
    Tendsto (fun y : ℝ => ‖Complex.exp (Complex.I * L * (Complex.I * y)) *
      V.eval (Complex.I * y)‖) atTop (𝓝 0) := by
  have hk : ∀ k : ℕ, Tendsto (fun y : ℝ => y ^ k * Real.exp (-(L * y))) atTop (𝓝 0) := by
    intro k
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop hL)
    have h2 := h1.const_mul ((L ^ k)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp, id, mul_pow]
    have : L ^ k ≠ 0 := pow_ne_zero _ hL.ne'
    field_simp
  have hg : Tendsto (fun y : ℝ => ∑ k ∈ Finset.range (V.natDegree + 1),
      ‖V.coeff k‖ * (y ^ k * Real.exp (-(L * y)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (V.natDegree + 1))
      (fun k _ => (hk k).const_mul ‖V.coeff k‖)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hg
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [norm_mul, norm_exp_imag]
  have hb := norm_eval_le V hy
  calc Real.exp (-(L * y)) * ‖V.eval (Complex.I * y)‖
      ≤ Real.exp (-(L * y)) * ∑ k ∈ Finset.range (V.natDegree + 1), ‖V.coeff k‖ * y ^ k :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ∑ k ∈ Finset.range (V.natDegree + 1), ‖V.coeff k‖ * (y ^ k * Real.exp (-(L * y))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **A nonzero rational (polynomial numerator) has nonzero algebraic asymptotics on `z = iy`**:
`‖U(iy)‖ ≥ δ > 0` for all large `y`. -/
theorem exists_lower_bound {U : ℂ[X]} (hU : U ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ y : ℝ in atTop, δ ≤ ‖U.eval (Complex.I * y)‖ := by
  by_cases hd : 0 < U.degree
  · refine ⟨1, one_pos, ?_⟩
    have hz : Tendsto (fun y : ℝ => ‖Complex.I * (y : ℂ)‖) atTop atTop := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact tendsto_abs_atTop_atTop
    exact (U.tendsto_norm_atTop hd hz).eventually_ge_atTop 1
  · obtain ⟨a, rfl⟩ : ∃ a, U = C a :=
      ⟨U.coeff 0, eq_C_of_degree_le_zero (not_lt.1 hd)⟩
    have ha : a ≠ 0 := fun h => hU (by simp [h])
    exact ⟨‖a‖, norm_pos_iff.2 ha, Eventually.of_forall fun y => by simp⟩

/-- **`R = 0` and then `T = 0`** (printed step): if `U(iy) + e^{iLz}V(iy) = 0` for all large `y`,
then `U = 0` and `V = 0`. -/
theorem exp_poly_zero_literal {L : ℝ} (hL : 0 < L) (U V : ℂ[X]) (Y : ℝ)
    (h : ∀ y : ℝ, Y ≤ y → U.eval (Complex.I * y) +
      Complex.exp (Complex.I * L * (Complex.I * y)) * V.eval (Complex.I * y) = 0) :
    U = 0 ∧ V = 0 := by
  have hU : U = 0 := by
    by_contra hU
    obtain ⟨δ, hδ, hlow⟩ := exists_lower_bound hU
    have hsmall := (tendsto_exp_mul_poly hL V).eventually (gt_mem_nhds hδ)
    have hev : ∀ᶠ y : ℝ in atTop, False := by
      filter_upwards [hlow, hsmall, eventually_ge_atTop Y] with y h1 h2 h3
      have h4 := h y h3
      have hu : U.eval (Complex.I * y) = -(Complex.exp (Complex.I * L * (Complex.I * y)) *
          V.eval (Complex.I * y)) := by linear_combination h4
      rw [hu, norm_neg] at h1
      exact absurd h2 (not_lt.2 h1)
    exact hev.exists.elim fun _ hf => hf
  refine ⟨hU, ?_⟩
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun y : ℝ => Complex.I * (y : ℂ)) := fun a b hab => by
    have := mul_left_cancel₀ Complex.I_ne_zero hab
    exact_mod_cast this
  have hsub : (fun y : ℝ => Complex.I * (y : ℂ)) '' Set.Ici Y ⊆ {x | IsRoot V x} := by
    rintro _ ⟨y, hy, rfl⟩
    have h4 := h y hy
    rw [hU, eval_zero, zero_add] at h4
    exact (mul_eq_zero.1 h4).resolve_left (Complex.exp_ne_zero _)
  exact ((Set.Ici_infinite Y).image hinj.injOn).mono hsub


/-! ### Clause (1) -/

/-- Clearing denominators and the printed asymptotic separation:
`A_p = A_q` and `B_p = B_q` in polynomial form, from equality of the transfer functions outside the
real poles and a finite exceptional set `Q`. -/
theorem numerators_eq {L c : ℝ} (hL : 0 < L) (p q : Fin N → ℝ) (Q : Finset ℂ)
    (h : ∀ z : ℂ, z ∉ poles p q ∪ Q → sFun L c p z = sFun L c q z) :
    shiftPoly p (-(Complex.I * c)) * shiftPoly q 0 = shiftPoly q (-(Complex.I * c)) * shiftPoly p 0 ∧
    shiftPoly p (Complex.I * c) * shiftPoly q 0 = shiftPoly q (Complex.I * c) * shiftPoly p 0 := by
  set Dp := shiftPoly p 0 with hDp
  set Dq := shiftPoly q 0 with hDq
  set U : ℂ[X] := shiftPoly p (-(Complex.I * c)) * Dq - shiftPoly q (-(Complex.I * c)) * Dp with hU
  set V : ℂ[X] := shiftPoly p (Complex.I * c) * Dq - shiftPoly q (Complex.I * c) * Dp with hV
  have hoff : ∀ z : ℂ, z ∉ poles p q ∪ Q →
      U.eval z + Complex.exp (Complex.I * L * z) * V.eval z = 0 := by
    intro z hz
    have hzp : z ∉ poles p q := fun h' => hz (Finset.mem_union_left _ h')
    obtain ⟨hp, hq⟩ := not_mem_poles hzp
    have hs := h z hz
    unfold sFun at hs
    have h1 := prod_plus_mul c p z hp
    have h2 := prod_minus_mul c p z hp
    have h3 := prod_plus_mul c q z hq
    have h4 := prod_minus_mul c q z hq
    simp only [hU, hV, eval_sub, eval_mul]
    rw [← h1, ← h2, ← h3, ← h4]
    linear_combination (Dp.eval z * Dq.eval z) * hs
  -- the points `iy`, `y` large, avoid the finite set `poles ∪ Q`
  set B : Finset ℂ := poles p q ∪ Q with hB
  set M : ℝ := ∑ w ∈ B, ‖w‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun w _ => norm_nonneg w
  have hY : ∀ y : ℝ, M + 1 ≤ y → Complex.I * (y : ℂ) ∉ B := by
    intro y hy hmem
    have h1 : ‖Complex.I * (y : ℂ)‖ ≤ M :=
      Finset.single_le_sum (f := fun w : ℂ => ‖w‖) (fun w _ => norm_nonneg w) hmem
    have h2 : ‖Complex.I * (y : ℂ)‖ = y := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by linarith)
    linarith
  obtain ⟨hU0, hV0⟩ := exp_poly_zero_literal hL U V (M + 1) fun y hy => hoff _ (hY y hy)
  exact ⟨sub_eq_zero.1 hU0, sub_eq_zero.1 hV0⟩

/-- **Printed route, clause (1)** (`c > 0`, `L > 0`): equality of the transfer functions away from the
real poles (and any finite exceptional set) forces equal rapidity multisets. -/
theorem separation_literal {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (p q : Fin N → ℝ) (Q : Finset ℂ)
    (h : ∀ z : ℂ, z ∉ poles p q ∪ Q → sFun L c p z = sFun L c q z) : msOf p = msOf q :=
  msOf_eq_of_prod_eq hc.ne' p q (numerators_eq hL p q Q h).1

/-- Equality of the first products (and of the second) follows (`R = T = 0`). -/
theorem products_eq_of_sFun_eq {L c : ℝ} (hL : 0 < L) (p q : Fin N → ℝ)
    (h : ∀ z : ℂ, z ∉ poles p q → sFun L c p z = sFun L c q z) {z : ℂ} (hz : z ∉ poles p q) :
    (∏ j, (1 + Complex.I * c / (z - p j))) = ∏ j, (1 + Complex.I * c / (z - q j)) := by
  obtain ⟨hp, hq⟩ := not_mem_poles hz
  have h1 := (numerators_eq hL p q ∅ (fun z hz => h z (by simpa using hz))).1
  have h2 := congrArg (Polynomial.eval z) h1
  simp only [eval_mul] at h2
  have e1 := prod_plus_mul c p z hp
  have e2 := prod_plus_mul c q z hq
  have hDp : (shiftPoly p 0).eval z ≠ 0 := by
    rw [eval_shiftPoly]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using sub_ne_zero.2 (hp j)
  have hDq : (shiftPoly q 0).eval z ≠ 0 := by
    rw [eval_shiftPoly]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using sub_ne_zero.2 (hq j)
  have key : ((∏ j, (1 + Complex.I * c / (z - p j))) - ∏ j, (1 + Complex.I * c / (z - q j))) *
      ((shiftPoly p 0).eval z * (shiftPoly q 0).eval z) = 0 := by
    linear_combination (shiftPoly q 0).eval z * e1 - (shiftPoly p 0).eval z * e2 + h2
  have := (mul_eq_zero.1 key).resolve_right (mul_ne_zero hDp hDq)
  exact sub_eq_zero.1 this


/-! ### Clause (2) -/

theorem sFun_differentiableAt (L c : ℝ) (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ q j) :
    DifferentiableAt ℂ (sFun L c q) z := by
  have hA : DifferentiableAt ℂ (fun w : ℂ => ∏ j, (1 + Complex.I * c / (w - q j))) z := by
    refine DifferentiableAt.fun_finsetProd (fun j _ => ?_)
    have : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
    fun_prop (disch := assumption)
  have hB : DifferentiableAt ℂ (fun w : ℂ => ∏ j, (1 - Complex.I * c / (w - q j))) z := by
    refine DifferentiableAt.fun_finsetProd (fun j _ => ?_)
    have : z - q j ≠ 0 := sub_ne_zero.2 (hz j)
    fun_prop (disch := assumption)
  have hE : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.I * L * w)) z := by fun_prop
  exact hA.add (hE.mul hB)

/-- **Clause (2), identity-theorem route** (`c > 0`): if the rapidity multisets differ then, for every
finite set `F ⊂ ℝ`, there is a real `x ∉ F`, away from the finitely many (apparent) poles, at which
the transfer values differ.  *Deviation*: the identity theorem is applied on the connected set
`ℂ ∖ (poles ∪ F)`, so on-shell hypotheses are not needed (see `separation_on_shell`). -/
theorem separation_real {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {p q : Fin N → ℝ}
    (hne : msOf p ≠ msOf q) (F : Finset ℝ) :
    ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧ sFun L c p x ≠ sFun L c q x := by
  by_contra hcon
  push Not at hcon
  set B : Finset ℂ := poles p q ∪ F.image (fun r : ℝ => (r : ℂ)) with hB
  set Uo : Set ℂ := ((B : Set ℂ))ᶜ with hUo
  have hopen : IsOpen Uo := B.finite_toSet.isClosed.isOpen_compl
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hconn : IsPreconnected Uo :=
    (B.finite_toSet.countable.isConnected_compl_of_one_lt_rank hrank).isPreconnected
  have hnp : ∀ {z : ℂ}, z ∈ Uo → (∀ j, z ≠ p j) ∧ ∀ j, z ≠ q j := fun {z} hz =>
    not_mem_poles (fun h' => hz (Finset.mem_union_left _ h'))
  have hdp : DifferentiableOn ℂ (sFun L c p) Uo := fun z hz =>
    (sFun_differentiableAt L c p (hnp hz).1).differentiableWithinAt
  have hdq : DifferentiableOn ℂ (sFun L c q) Uo := fun z hz =>
    (sFun_differentiableAt L c q (hnp hz).2).differentiableWithinAt
  -- a real base point outside `B`
  obtain ⟨x0, hx0⟩ := Infinite.exists_notMem_finset (B.image Complex.re)
  have hx0B : (x0 : ℂ) ∉ B := fun hmem =>
    hx0 (Finset.mem_image.2 ⟨_, hmem, by simp⟩)
  have hx0U : (x0 : ℂ) ∈ Uo := hx0B
  -- near `x0` the real transfer values agree
  have hev : ∀ᶠ x : ℝ in 𝓝 x0, sFun L c p (x : ℂ) = sFun L c q (x : ℂ) := by
    have hmem : Uo ∈ 𝓝 (x0 : ℂ) := hopen.mem_nhds hx0U
    filter_upwards [Complex.continuous_ofReal.continuousAt.eventually_mem hmem] with x hx
    have hxp := hnp hx
    refine hcon x ?_ (fun j => ⟨fun h' => hxp.1 j (by rw [h']), fun h' => hxp.2 j (by rw [h'])⟩)
    intro hxF
    exact hx (Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hxF, rfl⟩))
  have hfreq : ∃ᶠ x : ℝ in 𝓝[≠] x0, sFun L c p (x : ℂ) = sFun L c q (x : ℂ) :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x0) (𝓝[≠] (x0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact fun h' => hx (Complex.ofReal_injective h')
  have hfreqC : ∃ᶠ z : ℂ in 𝓝[≠] (x0 : ℂ), sFun L c p z = sFun L c q z :=
    htend.frequently hfreq
  have heq := (hdp.analyticOnNhd hopen).eqOn_of_preconnected_of_frequently_eq
    (hdq.analyticOnNhd hopen) hconn hx0U hfreqC
  exact hne (separation_literal hL hc p q (F.image (fun r : ℝ => (r : ℂ)))
    (fun z hz => heq (by simpa [hUo, hB] using hz)))

/-- **Clause (2) as printed**: both configurations on shell (literal Bethe equations
`basis:eq:bethe`) and distinct as multisets ⇒ the transfer values differ at some real `x`, which can
be chosen away from the finitely many apparent poles (and from any prescribed finite set `F`). -/
theorem separation_on_shell {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {p q : Fin N → ℝ}
    (_hp : OnShell L c p) (_hq : OnShell L c q) (hne : msOf p ≠ msOf q) (F : Finset ℝ) :
    ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧ sFun L c p x ≠ sFun L c q x :=
  separation_real hL hc hne F

/-- **`basis:lem:separation` (R-533B0EC6), assembled** for `c > 0` (and `L > 0`):
(1) two real rapidity multisets with equal transfer functions on the common domain away from their
real poles are equal (equivalently distinct multisets have distinct transfer functions);
(2) if both are on shell and distinct, their values differ at some real `x` away from the finitely
many apparent poles and any prescribed finite set. -/
theorem basis_lem_separation {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    (∀ p q : Fin N → ℝ, (∀ z : ℂ, z ∉ poles p q → sFun L c p z = sFun L c q z) → msOf p = msOf q) ∧
    (∀ p q : Fin N → ℝ, OnShell L c p → OnShell L c q → msOf p ≠ msOf q → ∀ F : Finset ℝ,
      ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧ sFun L c p x ≠ sFun L c q x) :=
  ⟨fun p q h => separation_literal hL hc p q ∅ fun z hz => h z (by simpa using hz),
   fun p q hp hq hne F => separation_on_shell hL hc hp hq hne F⟩

end QuantumNLS.TransferSeparationLiteral

/- Compile-time proof-dependency audit (adds no declaration or assumption): the assembled theorem
must NOT reach the inherited differentiation/degree route. -/
open Lean in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[
    ``QuantumNLS.TransferSeparationContinuityRepair.exp_poly_eq_zero,
    ``QuantumNLS.TransferSeparationContinuityRepair.separation_cofinite,
    ``QuantumNLS.TransferSeparationContinuityRepair.separation,
    ``QuantumNLS.TransferSeparationRepairBridge.separation_cofinite]
  let mut pending : Array Name := #[``QuantumNLS.TransferSeparationLiteral.basis_lem_separation]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "assembled theorem reached the differentiation/degree route: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.TransferSeparationLiteral.exp_poly_zero_literal,
      ``QuantumNLS.TransferSeparationLiteral.tendsto_exp_mul_poly,
      ``QuantumNLS.TransferSeparationLiteral.exists_lower_bound] do
    unless seen.contains n do throwError "missing required declaration {n}"
  logInfo m!"audit passed: {seen.size} transitive constants; printed asymptotic route reached; inherited exp_poly_eq_zero / separation_cofinite not reached."
