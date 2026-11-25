import QuantumNLS.FiniteCellCoefficientLaw
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! R-D8BB052C G: derive affinity and total variation from actual residuals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped InnerProductSpace ComplexConjugate Classical
namespace QuantumNLS.FiniteCellTotalVariation
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellCoefficientLaw FiniteCellEstimate FiniteCellTransport
variable {N : ℕ}

theorem affinity_lower (a b : ℤ) (alpha : Donor N a → Phase) (zeta : Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ)
    (hres : ‖transfer a b alpha g - zeta.1 • g‖ ≤ eta) :
    1 - eta ≤ FullOccupationAffinity.affinity a b g := by
  let R := transfer a b alpha g - zeta.1 • g
  have hn : ‖⟪g, R⟫_ℂ‖ ≤ eta := by
    have h := norm_inner_le_norm (𝕜 := ℂ) g R
    rw [hg, one_mul] at h
    exact h.trans hres
  have hi : ⟪g, R⟫_ℂ = ⟪g, transfer a b alpha g⟫_ℂ - zeta.1 := by
    simp [R, inner_self_eq_norm_sq_to_K, hg]
  have he : conj zeta.1 * ⟪g, R⟫_ℂ = conj zeta.1 * ⟪g, transfer a b alpha g⟫_ℂ - 1 := by
    rw [hi, mul_sub, phase_conj_mul]
  have hn' : ‖conj zeta.1 * ⟪g, R⟫_ℂ‖ ≤ eta := by
    rw [norm_mul, Complex.norm_conj, zeta.2, one_mul]
    exact hn
  rw [he] at hn'
  have hr := Complex.abs_re_le_norm (conj zeta.1 * ⟪g, R⟫_ℂ)
  have hr' := neg_abs_le (conj zeta.1 * ⟪g, R⟫_ℂ).re
  rw [he, Complex.sub_re, Complex.one_re, real_inner_eq_affinity_sub_defect] at hr hr'
  linarith [defect_nonneg a b alpha zeta g]

/-- Cauchy--Schwarz on finite partial sums derives the countable TV bound. -/
theorem tv_from_affinity {X : Type*} (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hps : Summable p) (hqs : Summable q)
    (hpone : ∑' x, p x = 1) (hqone : ∑' x, q x = 1)
    (hh : Summable (fun x => Real.sqrt (p x) * Real.sqrt (q x)))
    (eta : ℝ) (heta : 0 ≤ eta)
    (hlower : 1 - eta ≤ ∑' x, Real.sqrt (p x) * Real.sqrt (q x)) :
    Summable (fun x => |p x - q x|) ∧
      (1 / 2 : ℝ) * (∑' x, |p x - q x|) ≤ Real.sqrt (2 * eta) := by
  let A := fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
  have hAe : ∀ x, A x = p x + q x - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
    intro x
    dsimp [A]
    nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x)]
  have hAs : Summable A := ((hps.add hqs).sub (hh.mul_left 2)).congr (fun x => (hAe x).symm)
  have hAt : (∑' x, A x) = 2 - 2 * (∑' x, Real.sqrt (p x) * Real.sqrt (q x)) := by
    rw [tsum_congr hAe, Summable.tsum_sub (hps.add hqs) (hh.mul_left 2),
      hps.tsum_add hqs, tsum_mul_left, hpone, hqone]
    ring
  have hphi : ∀ x, |p x - q x| =
      |Real.sqrt (p x) - Real.sqrt (q x)| * (Real.sqrt (p x) + Real.sqrt (q x)) := by
    intro x
    have he : p x - q x = (Real.sqrt (p x) - Real.sqrt (q x)) *
        (Real.sqrt (p x) + Real.sqrt (q x)) := by
      nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x)]
    rw [he, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hpartial : ∀ S : Finset X, ∑ x ∈ S, |p x - q x| ≤ 2 * Real.sqrt (2 * eta) := by
    intro S
    have hSA : (∑ x ∈ S, A x) ≤ 2 * eta := by
      have h := hAs.sum_le_tsum S (fun x _ => sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x)))
      rw [hAt] at h
      linarith
    have hSB : (∑ x ∈ S, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) ≤ 4 := by
      calc
        _ ≤ ∑ x ∈ S, (2 * p x + 2 * q x) := by
          apply Finset.sum_le_sum
          intro x _
          nlinarith [Real.sq_sqrt (hp x), Real.sq_sqrt (hq x),
            sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
        _ = 2 * (∑ x ∈ S, p x) + 2 * (∑ x ∈ S, q x) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 4 := by
          have h1 := hps.sum_le_tsum S (fun x _ => hp x)
          have h2 := hqs.sum_le_tsum S (fun x _ => hq x)
          rw [hpone] at h1
          rw [hqone] at h2
          linarith
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun x => |Real.sqrt (p x) - Real.sqrt (q x)|)
      (fun x => Real.sqrt (p x) + Real.sqrt (q x))
    simp_rw [← hphi, sq_abs] at hc
    change (∑ x ∈ S, |p x - q x|) ^ 2 ≤ (∑ x ∈ S, A x) *
      (∑ x ∈ S, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) at hc
    have hprod := mul_le_mul hSA hSB
      (Finset.sum_nonneg (fun x _ => sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x))))
      (by positivity : 0 ≤ 2 * eta)
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ 2 * eta)
    have hsqrtn := Real.sqrt_nonneg (2 * eta)
    nlinarith
  have hs : Summable (fun x => |p x - q x|) :=
    summable_of_sum_le (fun x => abs_nonneg _) hpartial
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_of_sum_le hpartial
  linarith

/-- The actual selected translate has the TV bound from one actual seed residual. -/
theorem selected_tv (I : Finset ℤ) (c : OrderedSeeds N) (t : ℤ → Phase)
    (a b : ℤ) (hab : a ≠ b) (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : ‖seedTransfer c a b hab g - ((t a).1 * conj (t b).1) • g‖ ≤ eta) :
    Summable (fun k => |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|) ∧
    (1 / 2 : ℝ) * (∑' k, |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|) ≤ Real.sqrt (2 * eta) := by
  let zeta : Phase := ⟨(t a).1 * conj (t b).1, by
    rw [norm_mul, Complex.norm_conj, (t a).2, (t b).2, one_mul]⟩
  have hl := affinity_lower a b (seedPhase c a b hab) zeta g hg eta hres
  have haff := full_affinity_le_selected I a b hab g
  let P : (↥I → ℤ) → ℝ := pushLaw (selected (N := N) I) g
  let e := selectedStepEquiv I a b
  have hn := pushLaw_normalized (selected (N := N) I) g hg
  have hq : Summable (fun k => P (e k)) := hn.1.comp_injective e.injective
  have hqone : (∑' k, P (e k)) = 1 := by
    rw [e.tsum_eq]
    exact hn.2
  exact tv_from_affinity P (fun k => P (e k)) (pushLaw_nonneg _ _) (fun k => pushLaw_nonneg _ _ _)
    hn.1 hq hn.2 hqone haff.1 eta heta (hl.trans haff.2)

/-- Extraction of one actual operator norm from the actual finite squared sum. -/
theorem pair_residual_norm_le (c : OrderedSeeds N) (t : ℤ → Phase) (G : Finset ℤ)
    (g : H N) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (ha : a ∈ G) (hb : b ∈ G) (hab : a ≠ b) :
    ‖seedTransfer c a b hab g - ((t a).1 * conj (t b).1) • g‖ ≤ eta := by
  let p : Pairs G := ⟨(a,b), Finset.mem_offDiag.mpr ⟨ha,hb,hab⟩⟩
  have hs := Finset.single_le_sum (f := fun p : Pairs G => ‖pairResidual c t G g p‖ ^ 2)
    (fun p _ => sq_nonneg _) (Finset.mem_univ p)
  have hsq := hs.trans hres
  change ‖seedTransfer c a b hab g - ((t a).1 * conj (t b).1) • g‖ ^ 2 ≤ eta ^ 2 at hsq
  nlinarith [norm_nonneg (seedTransfer c a b hab g - ((t a).1 * conj (t b).1) • g)]

theorem selected_tv_from_residual_sum (I G : Finset ℤ) (c : OrderedSeeds N) (t : ℤ → Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (ha : a ∈ G) (hb : b ∈ G) (hab : a ≠ b) :
    Summable (fun k => |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|) ∧
    (1 / 2 : ℝ) * (∑' k, |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|) ≤ Real.sqrt (2 * eta) :=
  selected_tv I c t a b hab g hg eta heta (pair_residual_norm_le c t G g eta heta hres a b ha hb hab)

/-- Equal-total countable laws control every event by half their l1 difference. -/
theorem event_difference_le_tv {X : Type*} (p q : X → ℝ) (hps : Summable p) (hqs : Summable q)
    (hequal : (∑' x, p x) = ∑' x, q x) (htv : Summable (fun x => |p x - q x|)) (E : Set X) :
    |(∑' x : E, p x.1) - (∑' x : E, q x.1)| ≤ (1 / 2 : ℝ) * ∑' x, |p x - q x| := by
  let A := ∑' x : E, (p x.1 - q x.1)
  let B := ∑' x : ↥(Eᶜ), (p x.1 - q x.1)
  have hf := hps.sub hqs
  have hzero : (∑' x, (p x - q x)) = 0 := by rw [hps.tsum_sub hqs, hequal, sub_self]
  have hcomp := hf.tsum_subtype_add_tsum_subtype_compl E
  change A + B = ∑' x, (p x - q x) at hcomp
  rw [hzero] at hcomp
  have he : |A| = |B| := by
    have hab : A = -B := by linarith
    rw [hab, abs_neg]
  have hA : |A| ≤ ∑' x : E, |p x.1 - q x.1| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun x : E => p x.1 - q x.1) (htv.subtype (· ∈ E)))
  have hB : |B| ≤ ∑' x : ↥(Eᶜ), |p x.1 - q x.1| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun x : ↥(Eᶜ) => p x.1 - q x.1) (htv.subtype (· ∈ Eᶜ)))
  have habs := htv.tsum_subtype_add_tsum_subtype_compl E
  have hpE : Summable (fun x : E => p x.1) := hps.subtype (· ∈ E)
  have hqE : Summable (fun x : E => q x.1) := hqs.subtype (· ∈ E)
  have hdiff : (∑' x : E, p x.1) - (∑' x : E, q x.1) = A := (hpE.tsum_sub hqE).symm
  rw [hdiff]
  linarith

/-- Actual selected event translation, derived from the actual residual sum. -/
theorem selected_event_from_residual_sum (I G : Finset ℤ) (c : OrderedSeeds N) (t : ℤ → Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (ha : a ∈ G) (hb : b ∈ G) (hab : a ≠ b) (E : Set (↥I → ℤ)) :
    |(∑' k : E, pushLaw (selected (N := N) I) g k.1) -
      (∑' k : E, pushLaw (selected (N := N) I) g (selectedStep I a b k.1))| ≤ Real.sqrt (2 * eta) := by
  have htv := selected_tv_from_residual_sum I G c t g hg eta heta hres a b ha hb hab
  let P : (↥I → ℤ) → ℝ := pushLaw (selected (N := N) I) g
  let e := selectedStepEquiv I a b
  have hn := pushLaw_normalized (selected (N := N) I) g hg
  have hq : Summable (fun k => P (e k)) := hn.1.comp_injective e.injective
  have hqe : (∑' k, P (e k)) = ∑' k, P k := e.tsum_eq P
  exact (event_difference_le_tv P (fun k => P (e k)) hn.1 hq hqe.symm htv.1 E).trans htv.2

end QuantumNLS.FiniteCellTotalVariation

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellTotalVariation.affinity_lower
#print axioms QuantumNLS.FiniteCellTotalVariation.tv_from_affinity
#print axioms QuantumNLS.FiniteCellTotalVariation.selected_tv
#print axioms QuantumNLS.FiniteCellTotalVariation.pair_residual_norm_le
#print axioms QuantumNLS.FiniteCellTotalVariation.selected_tv_from_residual_sum
#print axioms QuantumNLS.FiniteCellTotalVariation.event_difference_le_tv
#print axioms QuantumNLS.FiniteCellTotalVariation.selected_event_from_residual_sum

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellTotalVariation.affinity_lower,
    ``QuantumNLS.FiniteCellTotalVariation.tv_from_affinity,
    ``QuantumNLS.FiniteCellTotalVariation.selected_tv,
    ``QuantumNLS.FiniteCellTotalVariation.pair_residual_norm_le,
    ``QuantumNLS.FiniteCellTotalVariation.selected_tv_from_residual_sum,
    ``QuantumNLS.FiniteCellTotalVariation.event_difference_le_tv,
    ``QuantumNLS.FiniteCellTotalVariation.selected_event_from_residual_sum]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellTotalVariation aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
