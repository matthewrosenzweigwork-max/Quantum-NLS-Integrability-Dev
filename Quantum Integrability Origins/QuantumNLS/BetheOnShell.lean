import QuantumNLS.BethePeriodic
import QuantumNLS.TransferSeparation
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
Vlaar (2011), (2.5.4)--(2.5.8), printed pp.30--31, and the
on-shell pole cancellation in Proposition 2.5.10, printed p.33.
The coupling is gamma=c; the spectral parameter is mu=z.
All on-shell conclusions below use the actual Yang--Yang sourceRoots.
No operator-action formula or eigenrelation is assumed. The physical
operator-action formula and coordinate/QISM identification remain open.
-/
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Polynomial Filter Topology

namespace QuantumNLS.BetheOnShell
open BetheSmooth BethePeriodic TransferSeparation

variable {M : ℕ}

/-- Literal source tau-plus, including the source orientation q_k-z. -/
def tauPlus (c : ℝ) (q : Fin M → ℝ) (z : ℂ) : ℂ :=
  ∏ k, ((q k : ℂ) - z - Complex.I * c) / ((q k : ℂ) - z)

/-- Literal source tau-minus. -/
def tauMinus (c : ℝ) (q : Fin M → ℝ) (z : ℂ) : ℂ :=
  ∏ k, ((q k : ℂ) - z + Complex.I * c) / ((q k : ℂ) - z)

/-- The deleted-root product in the unwanted A term of (2.5.7). -/
def deletedPlus (c : ℝ) (q : Fin M → ℝ) (i : Fin M) : ℂ :=
  ∏ k ∈ Finset.univ.erase i,
    ((q k : ℂ) - q i - Complex.I * c) / ((q k : ℂ) - q i)

/-- The deleted-root product in the unwanted D term of (2.5.8). -/
def deletedMinus (c : ℝ) (q : Fin M → ℝ) (i : Fin M) : ℂ :=
  ∏ k ∈ Finset.univ.erase i,
    ((q k : ℂ) - q i + Complex.I * c) / ((q k : ℂ) - q i)

theorem plus_factor (c a : ℝ) (z : ℂ) (hz : z ≠ a) :
    ((a : ℂ) - z - Complex.I * c) / ((a : ℂ) - z) =
      1 + Complex.I * c / (z - a) := by
  have h := sub_ne_zero.mpr hz
  field_simp
  ring

theorem minus_factor (c a : ℝ) (z : ℂ) (hz : z ≠ a) :
    ((a : ℂ) - z + Complex.I * c) / ((a : ℂ) - z) =
      1 - Complex.I * c / (z - a) := by
  have h := sub_ne_zero.mpr hz
  field_simp
  ring

/-- The exact two source products become the report's sFun off the roots. -/
theorem gauged_tau_eq_sFun (L c : ℝ) (q : Fin M → ℝ) (z : ℂ)
    (hz : ∀ k, z ≠ q k) :
    Complex.exp (Complex.I * L * z / 2) *
      (Complex.exp (-Complex.I * L * z / 2) * tauPlus c q z +
        Complex.exp (Complex.I * L * z / 2) * tauMinus c q z) = sFun L c q z := by
  have hp : tauPlus c q z = ∏ k, (1 + Complex.I * c / (z - q k)) :=
    Finset.prod_congr rfl fun k _ => plus_factor c (q k) z (hz k)
  have hm : tauMinus c q z = ∏ k, (1 - Complex.I * c / (z - q k)) :=
    Finset.prod_congr rfl fun k _ => minus_factor c (q k) z (hz k)
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  have h0 : Complex.I * (L : ℂ) * z / 2 + -Complex.I * L * z / 2 = 0 := by ring
  have h1 : Complex.I * (L : ℂ) * z / 2 + Complex.I * L * z / 2 =
      Complex.I * L * z := by ring
  rw [h0, h1, Complex.exp_zero, one_mul, hp, hm]
  rfl

theorem sourceRoots_onShell {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) : OnShell L c (sourceRoots L n c) := by
  intro i
  simpa only [Complex.ofReal_mul, Complex.ofReal_sub, mul_assoc] using
    sourceRoots_exponential_printed hL hc hn i

/-- The shifted scattering denominator cannot vanish for real rapidities. -/
theorem shifted_difference_ne_zero {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (a : ℂ) - b - Complex.I * c ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  exact hc hi

/-- Actual regularity required for the joint tuple (lambda,mu) in Vlaar's
Proposition 2.5.6, not an assumed regular-root interface. -/
theorem sourceRoots_snoc_regular {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ k, z ≠ (sourceRoots L n c k : ℂ)) :
    Function.Injective (Fin.snoc (fun k => (sourceRoots L n c k : ℂ)) z) := by
  apply Fin.snoc_injective_of_injective
  · exact Complex.ofReal_injective.comp (sourceRoots_strictAnti hL hc hn).injective
  · rintro ⟨k, hk⟩
    exact hz k hk.symm

theorem sourceRoots_deletedPlus_ne_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) :
    deletedPlus c (sourceRoots L n c) i ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply div_ne_zero (shifted_difference_ne_zero hc.ne' _ _)
  apply sub_ne_zero.mpr
  intro h
  exact (Finset.mem_erase.mp hk).1
    ((sourceRoots_strictAnti hL hc hn).injective (Complex.ofReal_injective h))

/-- The actual source roots satisfy Vlaar's deleted-product balance (2.5.6).
This derives the balance from the proved logarithmic Bethe equations. -/
theorem sourceRoots_deleted_balance {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) :
    deletedPlus c (sourceRoots L n c) i =
      Complex.exp (Complex.I * L * sourceRoots L n c i) *
        deletedMinus c (sourceRoots L n c) i := by
  classical
  let q := sourceRoots L n c
  have hq : Function.Injective q := (sourceRoots_strictAnti hL hc hn).injective
  have he := sourceRoots_onShell hL hc hn i
  change Complex.exp (Complex.I * L * q i) = _ at he
  unfold deletedPlus deletedMinus
  rw [he, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  have hd : (q i : ℂ) - q k ≠ 0 := sub_ne_zero.mpr
    (fun h => hki (hq (Complex.ofReal_injective h)).symm)
  have hs := shifted_difference_ne_zero hc.ne' (q i) (q k)
  dsimp [q] at *
  field_simp
  ring

/-- Exactly the scalar multiplying the replaced Bethe vector after adding
(2.5.7) and (2.5.8), before applying the report's transfer gauge. -/
def unwantedCoefficient (L c : ℝ) (q : Fin M → ℝ) (i : Fin M) (z : ℂ) : ℂ :=
  deletedPlus c q i * (Complex.I * c / ((q i : ℂ) - z)) *
      Complex.exp (-Complex.I * L * q i / 2) -
    deletedMinus c q i * (Complex.I * c / ((q i : ℂ) - z)) *
      Complex.exp (Complex.I * L * q i / 2)

/-- Every actual unwanted coefficient cancels, with its original half phases.
No A- or D-action hypothesis is supplied to this theorem. -/
theorem sourceRoots_unwanted_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) (z : ℂ) :
    unwantedCoefficient L c (sourceRoots L n c) i z = 0 := by
  unfold unwantedCoefficient
  rw [sourceRoots_deleted_balance hL hc hn]
  have he : Complex.exp (Complex.I * (L : ℂ) * sourceRoots L n c i) *
      Complex.exp (-Complex.I * L * sourceRoots L n c i / 2) =
      Complex.exp (Complex.I * L * sourceRoots L n c i / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  apply sub_eq_zero.mpr
  calc
    _ = deletedMinus c (sourceRoots L n c) i *
        (Complex.I * c / ((sourceRoots L n c i : ℂ) - z)) *
        (Complex.exp (Complex.I * L * sourceRoots L n c i) *
          Complex.exp (-Complex.I * L * sourceRoots L n c i / 2)) := by ring
    _ = _ := by rw [he]

/-- The original half phase cancellation survives the report's exact gauge. -/
theorem sourceRoots_gauged_unwanted_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) (z : ℂ) :
    Complex.exp (Complex.I * L * z / 2) *
      unwantedCoefficient L c (sourceRoots L n c) i z = 0 := by
  rw [sourceRoots_unwanted_zero hL hc hn, mul_zero]

/-- The individual A unwanted coefficient is nonzero at every regular z.
Cancellation in A+D does not assert separate diagonality of A and D. -/
theorem sourceRoots_A_unwanted_ne_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) {z : ℂ}
    (hz : z ≠ (sourceRoots L n c i : ℂ)) :
    deletedPlus c (sourceRoots L n c) i *
      (Complex.I * c / ((sourceRoots L n c i : ℂ) - z)) *
      Complex.exp (-Complex.I * L * sourceRoots L n c i / 2) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (sourceRoots_deletedPlus_ne_zero hL hc hn i)
    (div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'))
      (sub_ne_zero.mpr hz.symm))) (Complex.exp_ne_zero _)

/-- Denominator-cleared numerator of the literal report transfer function. -/
def numerator (L c : ℝ) (q : Fin M → ℝ) (z : ℂ) : ℂ :=
  (shiftPoly q (-(Complex.I * c))).eval z +
    Complex.exp (Complex.I * L * z) * (shiftPoly q (Complex.I * c)).eval z

theorem sFun_mul_denominator (L c : ℝ) (q : Fin M → ℝ) (z : ℂ)
    (hz : ∀ k, z ≠ q k) :
    sFun L c q z * (shiftPoly q 0).eval z = numerator L c q z := by
  unfold sFun numerator
  rw [add_mul, mul_assoc, prod_plus_mul c q z hz, prod_minus_mul c q z hz]

/-- Actual on-shell roots are zeros of the entire numerator. -/
theorem sourceRoots_numerator_zero {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) :
    numerator L c (sourceRoots L n c) (sourceRoots L n c i) = 0 := by
  classical
  let q := sourceRoots L n c
  let D : ℂ := ∏ k ∈ Finset.univ.erase i, ((q i : ℂ) - q k)
  have hd (k : Fin (N+1)) (hk : k ∈ Finset.univ.erase i) :
      (q i : ℂ) - q k ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact (Finset.mem_erase.mp hk).1
      ((sourceRoots_strictAnti hL hc hn).injective (Complex.ofReal_injective h)).symm
  have hp : deletedPlus c q i * D =
      ∏ k ∈ Finset.univ.erase i, ((q i : ℂ) - q k + Complex.I * c) := by
    rw [deletedPlus, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    have hd' : (q k : ℂ) - q i ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (hd k hk)))
    field_simp [hd']
    ring
  have hm : deletedMinus c q i * D =
      ∏ k ∈ Finset.univ.erase i, ((q i : ℂ) - q k - Complex.I * c) := by
    rw [deletedMinus, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    have hd' : (q k : ℂ) - q i ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (hd k hk)))
    field_simp [hd']
    ring
  have hb := sourceRoots_deleted_balance hL hc hn i
  change deletedPlus c q i = _ at hb
  have hb' := congrArg (fun w : ℂ => w * D) hb
  rw [mul_assoc, hp, hm] at hb'
  unfold numerator
  simp only [eval_shiftPoly]
  have hplus : (∏ k, ((q i : ℂ) - ((q k : ℂ) + -(Complex.I * c)))) =
      Complex.I * c * ∏ k ∈ Finset.univ.erase i,
        ((q i : ℂ) - q k + Complex.I * c) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [sub_add_eq_sub_sub, sub_neg_eq_add, sub_self, zero_add]
  have hminus : (∏ k, ((q i : ℂ) - ((q k : ℂ) + Complex.I * c))) =
      -(Complex.I * c) * ∏ k ∈ Finset.univ.erase i,
        ((q i : ℂ) - q k - Complex.I * c) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
  change (∏ k, ((q i : ℂ) - ((q k : ℂ) + -(Complex.I * c)))) +
    Complex.exp (Complex.I * L * q i) *
      (∏ k, ((q i : ℂ) - ((q k : ℂ) + Complex.I * c))) = 0
  rw [hplus, hminus, hb']
  ring

/-- Constructively remove finitely many distinct zeros of an entire function.
The divided differences fill each removed zero by its derivative. -/
theorem entire_factor_finset (s : Finset ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : ∀ a ∈ s, f a = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, f z = (∏ a ∈ s, (z - a)) * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, fun z => by simp⟩
  | @insert a s ha ih =>
    let F := dslope f a
    have hF : Differentiable ℂ F := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn
    have hfa := hzero a (Finset.mem_insert_self a s)
    have hfactor (z : ℂ) : f z = (z-a) * F z := by
      simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hfa z).symm
    have hFzero (b : ℂ) (hb : b ∈ s) : F b = 0 := by
      have hba : b ≠ a := fun h => ha (h ▸ hb)
      have hz := hzero b (Finset.mem_insert_of_mem hb)
      rw [hfactor b] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hba)
    obtain ⟨g, hg, hfg⟩ := ih hF hFzero
    refine ⟨g, hg, fun z => ?_⟩
    rw [hfactor, hfg, Finset.prod_insert ha]
    ring

theorem numerator_differentiable (L c : ℝ) (q : Fin M → ℝ) :
    Differentiable ℂ (numerator L c q) := by
  intro z
  apply DifferentiableAt.add (Polynomial.differentiableAt _)
  exact (Complex.differentiableAt_exp.comp z
    ((differentiableAt_const _).mul differentiableAt_id)).mul (Polynomial.differentiableAt _)

/-- The denominator-cleared numerator has the full characteristic product as
an entire factor for the actual, distinct, on-shell source roots. -/
theorem sourceRoots_entire_factorization {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z,
      numerator L c (sourceRoots L n c) z =
        (shiftPoly (sourceRoots L n c) 0).eval z * g z := by
  classical
  let q := sourceRoots L n c
  let S : Finset ℂ := Finset.univ.image (fun i => (q i : ℂ))
  have hi : Function.Injective (fun i => (q i : ℂ)) :=
    Complex.ofReal_injective.comp (sourceRoots_strictAnti hL hc hn).injective
  obtain ⟨g, hg, hfg⟩ := entire_factor_finset S (numerator_differentiable L c q) (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact sourceRoots_numerator_zero hL hc hn i)
  refine ⟨g, hg, fun z => ?_⟩
  have hprod : (∏ a ∈ S, (z-a)) = (shiftPoly q 0).eval z := by
    rw [Finset.prod_image (fun i _ j _ h => hi h)]
    simp only [eval_shiftPoly, add_zero]
  rw [hfg, hprod]

/-- Entire extension of the literal sFun, with no transfer-eigenvector premise.
Equality is asserted off the roots: Lean's total field division does not
assign the analytic extension's values at the apparent poles. -/
theorem sourceRoots_exists_entire_extension {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ,
      (∀ k, z ≠ (sourceRoots L n c k : ℂ)) →
        g z = sFun L c (sourceRoots L n c) z := by
  obtain ⟨g, hg, hfg⟩ := sourceRoots_entire_factorization hL hc hn
  refine ⟨g, hg, fun z hz => ?_⟩
  have hd : (shiftPoly (sourceRoots L n c) 0).eval z ≠ 0 := by
    rw [eval_shiftPoly]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by
      simpa only [add_zero] using sub_ne_zero.mpr (hz k)
  have he := sFun_mul_denominator L c (sourceRoots L n c) z hz
  rw [hfg, mul_comm] at he
  exact (mul_left_cancel₀ hd he).symm

/-- The entire continuation is unique; totalized division values at the
roots are never used to identify its analytic values. -/
theorem sourceRoots_entire_extension_unique {N : ℕ} {L c : ℝ}
    {n : Fin (N+1) → ℤ} {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ z : ℂ, (∀ k, z ≠ (sourceRoots L n c k : ℂ)) → f z = g z) : f = g := by
  classical
  let S : Finset ℂ := Finset.univ.image (fun i => (sourceRoots L n c i : ℂ))
  have hdense : Dense ((S : Set ℂ)ᶜ) := by
    simpa only [Set.compl_eq_univ_sdiff] using
      Dense.sdiff_finite (dense_univ (X := ℂ)) S.finite_toSet
  apply hf.continuous.ext_on hdense hg.continuous
  intro z hz
  apply hfg z
  intro k hk
  exact hz (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩)

/-- The literal source scalar has one analytic continuation to all complex
spectral parameters, proved from actual Bethe equations, independently of
any physical transfer action or completeness assumption. -/
theorem sourceRoots_unique_analytic_extension {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ∃! g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧ ∀ z : ℂ,
      (∀ k, z ≠ (sourceRoots L n c k : ℂ)) →
        g z = sFun L c (sourceRoots L n c) z := by
  obtain ⟨g, hg, he⟩ := sourceRoots_exists_entire_extension hL hc hn
  refine ⟨g, ⟨fun z _ => hg.analyticAt z, he⟩, ?_⟩
  rintro f ⟨hf, hfe⟩
  apply sourceRoots_entire_extension_unique (by
    intro z
    exact (hf z (Set.mem_univ z)).differentiableAt) hg
  intro z hz
  rw [hfe z hz, he z hz]

end QuantumNLS.BetheOnShell

#print axioms QuantumNLS.BetheOnShell.tauPlus
#print axioms QuantumNLS.BetheOnShell.tauMinus
#print axioms QuantumNLS.BetheOnShell.deletedPlus
#print axioms QuantumNLS.BetheOnShell.deletedMinus
#print axioms QuantumNLS.BetheOnShell.plus_factor
#print axioms QuantumNLS.BetheOnShell.minus_factor
#print axioms QuantumNLS.BetheOnShell.gauged_tau_eq_sFun
#print axioms QuantumNLS.BetheOnShell.sourceRoots_onShell
#print axioms QuantumNLS.BetheOnShell.shifted_difference_ne_zero
#print axioms QuantumNLS.BetheOnShell.sourceRoots_snoc_regular
#print axioms QuantumNLS.BetheOnShell.sourceRoots_deletedPlus_ne_zero
#print axioms QuantumNLS.BetheOnShell.sourceRoots_deleted_balance
#print axioms QuantumNLS.BetheOnShell.unwantedCoefficient
#print axioms QuantumNLS.BetheOnShell.sourceRoots_unwanted_zero
#print axioms QuantumNLS.BetheOnShell.sourceRoots_gauged_unwanted_zero
#print axioms QuantumNLS.BetheOnShell.sourceRoots_A_unwanted_ne_zero
#print axioms QuantumNLS.BetheOnShell.numerator
#print axioms QuantumNLS.BetheOnShell.sFun_mul_denominator
#print axioms QuantumNLS.BetheOnShell.sourceRoots_numerator_zero
#print axioms QuantumNLS.BetheOnShell.entire_factor_finset
#print axioms QuantumNLS.BetheOnShell.numerator_differentiable
#print axioms QuantumNLS.BetheOnShell.sourceRoots_entire_factorization
#print axioms QuantumNLS.BetheOnShell.sourceRoots_exists_entire_extension
#print axioms QuantumNLS.BetheOnShell.sourceRoots_entire_extension_unique
#print axioms QuantumNLS.BetheOnShell.sourceRoots_unique_analytic_extension

/- Provenance check for the actual scalar clauses; this does not certify an
operator action or constitute independent statement/argument review. -/
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheOnShell.sourceRoots_unwanted_zero,
    ``QuantumNLS.BetheOnShell.sourceRoots_unique_analytic_extension,
    ``QuantumNLS.BetheOnShell.gauged_tau_eq_sFun]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BethePeriodic.sourceRoots_exponential_printed,
      ``QuantumNLS.BetheSmooth.sourceRoots,
      ``QuantumNLS.BetheSmooth.sourceRoots_strictAnti,
      ``QuantumNLS.BetheOnShell.deletedPlus,
      ``QuantumNLS.BetheOnShell.deletedMinus,
      ``QuantumNLS.BetheOnShell.sourceRoots_deleted_balance,
      ``QuantumNLS.BetheOnShell.unwantedCoefficient,
      ``QuantumNLS.BetheOnShell.sourceRoots_numerator_zero,
      ``QuantumNLS.BetheOnShell.entire_factor_finset,
      ``QuantumNLS.TransferSeparation.sFun,
      ``QuantumNLS.TransferSeparation.shiftPoly] do
    unless seen.contains n do
      throwError "On-shell scalar proof missed source ingredient: {n}"
  for n in #[``sorryAx] do
    if seen.contains n then
      throwError "On-shell scalar proof reached prohibited constant: {n}"
  Lean.logInfo m!"On-shell route PASS: {seen.size} transitive constants; actual roots, exponential Bethe equations, deleted-product balance, original half-phase cancellation, exact source-to-report gauge, numerator zeros and entire factorization. No physical operator-action conclusion."
