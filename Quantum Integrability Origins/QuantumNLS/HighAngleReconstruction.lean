import QuantumNLS.HaarNonlinearTail

/-! R-F1423202: the summed reconstruction error on the actual Bethe labels.
The finite-support estimate below is derived from R-9A71E77E, including
its C1 tail; no reconstruction or evolution estimate is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.HighAngleReconstruction
open HaarSummableReconstruction HaarSpectralTail

/-- The roots in the increasing order required by the accepted reconstruction. -/
def roots (L κ : ℝ) {N : ℕ} (m : BetheLabels.MArr N) : Fin N → ℝ :=
  BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) ∘ Fin.rev

/-- The actual count multiplier, with a finite set of real angle representatives. -/
def countEigen {N : ℕ} (a : Finset ℤ) (t : ℤ → ℝ) (m : BetheLabels.MArr N) : ℝ :=
  ∑ n ∈ a, t n * (m.val n : ℝ)

/-- The leading reconstruction multiplier in the source's notation. -/
def leadingEigen (L κ : ℝ) {N : ℕ} (a : Finset ℤ) (t : ℤ → ℝ)
    (m : BetheLabels.MArr N) : ℝ :=
  (N : ℝ) * ∑ n ∈ a, t n * C0 L κ (roots L κ m) n

lemma occupation_card {N : ℕ} (m : BetheLabels.MArr N) (n : ℤ) :
    m.val n = (Finset.univ.filter fun j => (NormalityBridge.label m).val (Fin.rev j) = n).card := by
  have h := BetheLabels.correctedEquivArr_apply
    (BetheConditionalBasis.reverseLabel N (NormalityBridge.label m)) n
  have he : BetheLabels.correctedEquivArr
      (BetheConditionalBasis.reverseLabel N (NormalityBridge.label m)) = m :=
    (BetheConditionalBasis.labelArr N).apply_symm_apply m
  rw [he] at h
  exact h

/-- Weighted finite tails of the C1 correction have the same absolute bound
as the accepted absolute infinite tail, uniformly in support cardinality. -/
lemma correction_sum_le {L κ : ℝ} {N : ℕ} {q : Fin N → ℝ} {C R : ℝ}
    (hs : Summable (fun n : ℤ => if R < |(n : ℝ)| then |C1 L κ q n| else 0))
    (hb : ∑' n : ℤ, (if R < |(n : ℝ)| then |C1 L κ q n| else 0) ≤ C / R)
    (a : Finset ℤ) (ha : ∀ n ∈ a, R < |(n : ℝ)|) (t : ℤ → ℝ)
    (ht : ∀ n, |t n| ≤ 1) : |∑ n ∈ a, t n * C1 L κ q n| ≤ C / R := by
  calc
    |∑ n ∈ a, t n * C1 L κ q n| ≤ ∑ n ∈ a, |t n * C1 L κ q n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ a, (if R < |(n : ℝ)| then |C1 L κ q n| else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [ite_eq_left (ha n hn), abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (ht n) (abs_nonneg (C1 L κ q n))
    _ ≤ ∑' n : ℤ, (if R < |(n : ℝ)| then |C1 L κ q n| else 0) :=
      hs.sum_le_tsum a (fun n _ => by split_ifs <;> positivity)
    _ ≤ C / R := hb

/-- The exact finite-angle reconstruction estimate on every energy-admissible
actual Bethe vector. A fixed angle bound scales the two reconstruction errors. -/
theorem finite_reconstruction (L : ℝ) [Fact (0 < L)] {κ E : ℝ}
    (hκ : 0 < κ) (hE : 0 < E) :
    ∃ NE : ℕ, ∃ RE C : ℝ, 0 < NE ∧ 2 ≤ RE ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (_hN : NE ≤ N) (m : BetheLabels.MArr N), m ∈ adm L κ N E →
        ∀ R : ℝ, RE ≤ R → ∀ a : Finset ℤ, (∀ n ∈ a, R < |(n : ℝ)|) →
          ∀ t : ℤ → ℝ, (∀ n, |t n| ≤ 1) →
            |countEigen a t m - leadingEigen L κ a t m| ≤ C / R := by
  obtain ⟨NE, RE, C, hNE, hRE, hC, hmain⟩ := haar_summable_reconstruction (Fact.out : 0 < L) hκ hE
  refine ⟨NE, RE, 2 * C, hNE, hRE, by positivity, ?_⟩
  intro N hNN m hm R hR a ha t ht
  have hN : 0 < N := hNE.trans_le hNN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc : 0 < κ / (N : ℝ) := div_pos hκ hNr
  have hact := sourceRoots_actual (Fact.out : 0 < L) hc (NormalityBridge.label m).property
  have hen : (N : ℝ)⁻¹ * ∑ j, roots L κ m j ^ 2 ≤ E := by
    have he : ∑ j, roots L κ m j ^ 2 = EnergyProjection.energyEig L κ N (NormalityBridge.label m) := by
      unfold roots EnergyProjection.energyEig
      exact sum_rev (fun j => BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j ^ 2)
    rw [he, inv_mul_le_iff₀ hNr]
    exact hm
  obtain ⟨-, -, hsum, hcorr⟩ := hmain N ((NormalityBridge.label m).val ∘ Fin.rev)
    (roots L κ m) hNN hact hen
  have h1 := hsum R hR a ha t ht
  have h2 := correction_sum_le (hcorr R hR).1 (hcorr R hR).2 a ha t ht
  have he : countEigen a t m - leadingEigen L κ a t m =
      (∑ n ∈ a, t n * (((Finset.univ.filter fun j =>
        (NormalityBridge.label m).val (Fin.rev j) = n).card : ℝ) -
        N * C0 L κ (roots L κ m) n - C1 L κ (roots L κ m) n)) +
      ∑ n ∈ a, t n * C1 L κ (roots L κ m) n := by
    simp only [countEigen, leadingEigen, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, occupation_card]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  have hRpos : 0 < R := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : R ≤ (N : ℝ) * R := by nlinarith
  calc
    _ ≤ |∑ n ∈ a, t n * (((Finset.univ.filter fun j =>
        (NormalityBridge.label m).val (Fin.rev j) = n).card : ℝ) -
        N * C0 L κ (roots L κ m) n - C1 L κ (roots L κ m) n)| +
      |∑ n ∈ a, t n * C1 L κ (roots L κ m) n| := abs_add_le _ _
    _ ≤ C / ((N : ℝ) * R) + C / R := add_le_add h1 h2
    _ ≤ 2 * C / R := by
      have hd := div_le_div_of_nonneg_left hC hRpos hden
      calc
        C / ((N : ℝ) * R) + C / R ≤ C / R + C / R := add_le_add hd le_rfl
        _ = 2 * C / R := by ring

end QuantumNLS.HighAngleReconstruction

-- Author audits: every own declaration and its generated/transitive constants.
#print axioms QuantumNLS.HighAngleReconstruction.roots
#print axioms QuantumNLS.HighAngleReconstruction.countEigen
#print axioms QuantumNLS.HighAngleReconstruction.leadingEigen
#print axioms QuantumNLS.HighAngleReconstruction.occupation_card
#print axioms QuantumNLS.HighAngleReconstruction.correction_sum_le
#print axioms QuantumNLS.HighAngleReconstruction.finite_reconstruction

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleReconstruction." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
