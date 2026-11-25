import Mathlib
import QuantumNLS.RootChamberIntegral

/-!
# Torus double integrals as integrals over `Fin r → ℝ × ℝ`

New module (R-7E0532E7 `eq:root-trace-symbol`).  Pure measure theory.  For a measurable `Ψ : (Fin r → ℝ) → (Fin r → ℝ) → ℂ`
supported in the open cube `(0,L)^r × (0,L)^r`,

`∫_{𝕋_L^r × 𝕋_L^r} Ψ(reps x, reps y) d(μ⊗μ) = ∫_{(ℝ×ℝ)^r} Ψ((q_j.1)_j, (q_j.2)_j) dq`

where `reps = BetheWeakGradient.representatives` (the `[0,L)` representatives used by the frozen physical kernels) and
`μ = torusPiMeasure L r`.  Route: the covering map `mk : (0,L] → 𝕋_L` is measure preserving (`AddCircle.measurePreserving_mk`),
`measurePreserving_pi`, `MeasurePreserving.prod`, `integral_map`, `Measure.restrict_pi_pi`, the cube-support hypothesis, and
`volume_measurePreserving_arrowProdEquivProdArrow`.  No EXT-025 contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace QuantumNLS.RootTorusConversion

open QuantumNLS.PhysicalTensor (torusPiMeasure)
open QuantumNLS.BetheWeakGradient (representatives measurable_representatives)

variable {L : ℝ} [Fact (0 < L)]

/-- Coordinatewise covering map `(Fin r → ℝ) → (Fin r → 𝕋_L)`. -/
def piMk (L : ℝ) [Fact (0 < L)] (r : ℕ) (a : Fin r → ℝ) : Fin r → AddCircle L := fun j => (a j : AddCircle L)

theorem rep_mk_of_mem {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) L) :
    ((AddCircle.equivIco L 0 (a : AddCircle L) : Ico (0 : ℝ) (0 + L)) : ℝ) = a := by
  have h : a ∈ Ico (0 : ℝ) (0 + L) := ⟨ha.1.le, by simpa using ha.2⟩
  rw [AddCircle.equivIco_coe_eq h]

theorem rep_mk_of_eq : ((AddCircle.equivIco L 0 ((L : ℝ) : AddCircle L) : Ico (0 : ℝ) (0 + L)) : ℝ) = 0 := by
  have hL : 0 < L := Fact.out
  rw [AddCircle.coe_equivIco_mk_apply]
  have : L / L = 1 := div_self hL.ne'
  simp [this]

theorem rep_piMk_of_mem {r : ℕ} {a : Fin r → ℝ} (ha : ∀ j, a j ∈ Ioc (0 : ℝ) L) (j : Fin r) :
    representatives L (piMk L r a) j = if a j = L then 0 else a j := by
  have hL : 0 < L := Fact.out
  by_cases h : a j = L
  · simp only [h, ↓reduceIte]
    show ((AddCircle.equivIco L 0 ((a j : ℝ) : AddCircle L) : Ico (0 : ℝ) (0 + L)) : ℝ) = 0
    rw [h]; exact rep_mk_of_eq
  · simp only [h, ↓reduceIte]
    exact rep_mk_of_mem ⟨(ha j).1, lt_of_le_of_ne (ha j).2 h⟩

theorem mem_Ioo_of_rep {r : ℕ} {a : Fin r → ℝ} (ha : ∀ j, a j ∈ Ioc (0 : ℝ) L)
    (j : Fin r) (h : representatives L (piMk L r a) j ∈ Ioo (0 : ℝ) L) : a j ∈ Ioo (0 : ℝ) L := by
  rw [rep_piMk_of_mem ha j] at h
  by_cases hj : a j = L
  · rw [if_pos hj] at h; exact absurd h.1 (lt_irrefl _)
  · exact ⟨(ha j).1, lt_of_le_of_ne (ha j).2 hj⟩

theorem torus_pair_integral {r : ℕ} (Ψ : (Fin r → ℝ) → (Fin r → ℝ) → ℂ)
    (hΨm : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => Ψ p.1 p.2))
    (hsupp : ∀ a b, Ψ a b ≠ 0 → ∀ j, a j ∈ Ioo (0 : ℝ) L ∧ b j ∈ Ioo (0 : ℝ) L) :
    ∫ p : (Fin r → AddCircle L) × (Fin r → AddCircle L), Ψ (representatives L p.1) (representatives L p.2)
        ∂((torusPiMeasure L r).prod (torusPiMeasure L r)) =
      ∫ q : Fin r → ℝ × ℝ, Ψ (fun j => (q j).1) (fun j => (q j).2) := by
  have hmk : MeasurePreserving (fun a : Fin r → ℝ => piMk L r a)
      (Measure.pi fun _ : Fin r => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + L)))
      (torusPiMeasure L r) :=
    measurePreserving_pi (fun _ : Fin r => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + L)))
      (fun _ : Fin r => (volume : Measure (AddCircle L)))
      (fun _ => AddCircle.measurePreserving_mk L 0)
  have hmk2 := hmk.prod hmk
  set Θ : (Fin r → AddCircle L) × (Fin r → AddCircle L) → ℂ :=
    fun p => Ψ (representatives L p.1) (representatives L p.2) with hΘ
  have hΘm : Measurable Θ := by
    have h1 : Measurable (fun p : (Fin r → AddCircle L) × (Fin r → AddCircle L) =>
        ((representatives L p.1 : Fin r → ℝ), (representatives L p.2 : Fin r → ℝ))) :=
      ((measurable_representatives r L).comp measurable_fst).prodMk
        ((measurable_representatives r L).comp measurable_snd)
    exact hΨm.comp h1
  rw [← hmk2.map_eq, integral_map hmk2.aemeasurable hΘm.aestronglyMeasurable]
  -- the restricted cube measure
  set A : Set (Fin r → ℝ) := Set.pi univ (fun _ : Fin r => Ioc (0 : ℝ) (0 + L)) with hA
  have hAm : MeasurableSet A := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hν : (Measure.pi fun _ : Fin r => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + L))) =
      (volume : Measure (Fin r → ℝ)).restrict A := by
    rw [hA, volume_pi, Measure.restrict_pi_pi]
  rw [hν, Measure.prod_restrict]
  have hcong : ∫ p : (Fin r → ℝ) × (Fin r → ℝ), Θ (Prod.map (fun a => piMk L r a) (fun a => piMk L r a) p)
      ∂(((volume : Measure (Fin r → ℝ)).prod (volume : Measure (Fin r → ℝ))).restrict (A ×ˢ A)) =
      ∫ p : (Fin r → ℝ) × (Fin r → ℝ), Ψ p.1 p.2
      ∂(((volume : Measure (Fin r → ℝ)).prod (volume : Measure (Fin r → ℝ))).restrict (A ×ˢ A)) := by
    refine setIntegral_congr_fun (hAm.prod hAm) (fun p hp => ?_)
    have h1 : ∀ j, p.1 j ∈ Ioc (0 : ℝ) L := fun j => by simpa using hp.1 j (mem_univ j)
    have h2 : ∀ j, p.2 j ∈ Ioc (0 : ℝ) L := fun j => by simpa using hp.2 j (mem_univ j)
    simp only [hΘ, Prod.map_fst, Prod.map_snd]
    by_cases hne : Ψ p.1 p.2 = 0
    · rw [hne]
      by_contra hc
      obtain ⟨hs1, hs2⟩ : (∀ j, representatives L (piMk L r p.1) j ∈ Ioo (0 : ℝ) L) ∧
          (∀ j, representatives L (piMk L r p.2) j ∈ Ioo (0 : ℝ) L) :=
        ⟨fun j => (hsupp _ _ hc j).1, fun j => (hsupp _ _ hc j).2⟩
      have e1 : representatives L (piMk L r p.1) = p.1 := by
        funext j
        rw [rep_piMk_of_mem h1 j, if_neg]
        exact fun h => by have := mem_Ioo_of_rep h1 j (hs1 j); linarith [this.2]
      have e2 : representatives L (piMk L r p.2) = p.2 := by
        funext j
        rw [rep_piMk_of_mem h2 j, if_neg]
        exact fun h => by have := mem_Ioo_of_rep h2 j (hs2 j); linarith [this.2]
      rw [e1, e2] at hc
      exact hc hne
    · have hs := hsupp _ _ hne
      have e1 : representatives L (piMk L r p.1) = p.1 := by
        funext j
        rw [rep_piMk_of_mem h1 j, if_neg]
        exact ne_of_lt (hs j).1.2
      have e2 : representatives L (piMk L r p.2) = p.2 := by
        funext j
        rw [rep_piMk_of_mem h2 j, if_neg]
        exact ne_of_lt (hs j).2.2
      rw [e1, e2]
  refine hcong.trans ?_
  have hoff : ∀ p : (Fin r → ℝ) × (Fin r → ℝ), p ∉ A ×ˢ A → Ψ p.1 p.2 = 0 := by
    intro p hp
    by_contra hne
    apply hp
    have hs := hsupp _ _ hne
    refine ⟨fun j _ => ?_, fun j _ => ?_⟩
    · exact ⟨(hs j).1.1, by simpa using (hs j).1.2.le⟩
    · exact ⟨(hs j).2.1, by simpa using (hs j).2.2.le⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  have hpair := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin r)
  have := hpair.integral_comp' (g := fun p : (Fin r → ℝ) × (Fin r → ℝ) => Ψ p.1 p.2)
  rw [volume_pi] at *
  exact this.symm

end QuantumNLS.RootTorusConversion

#print axioms QuantumNLS.RootTorusConversion.torus_pair_integral
