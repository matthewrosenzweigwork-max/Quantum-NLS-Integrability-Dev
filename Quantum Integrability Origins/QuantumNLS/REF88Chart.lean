import Mathlib
import QuantumNLS.RAEEMain
import QuantumNLS.StrongSymplectic
import QuantumNLS.ActionTorus
import QuantumNLS.REF88Rotations

/-!
# REF88Chart: `A^t = Φ S^t Φ⁻¹` and the rotation formula (R-EF8C2837, rough-extension assembly)

Source: `source-text/chapters/global/physical_cubic.tex`, proof paragraph "Extension to rough fields
without a rough Hamiltonian" (printed lines 177 to 214), first sentences: "The physical `L²` flow is a
jointly continuous group and preserves the mass and every actual indexed mass.  Define
`A^t = Φ_κ S^t Φ_κ⁻¹`.  It is a jointly continuous group on `ℓ²` preserving each `q_n`.  On finitely
supported sequences, the preceding calculation makes it commute with every finite collection of
coordinate rotations."

* `chartFlow` is `A^t` for the accepted physical `L²` flow `flowMap` (`L2Flow`, R-AEE17FD6), and
  `Φ` a strongly symplectic diffeomorphism (DEF-016) with exact moduli.
* `continuous_flow_joint`: joint continuity of `(f,t) ↦ S^t f` from the accepted Lipschitz dependence
  on bounded sets over compact time intervals and continuity in time.
* `chart_roughGroup`: all fields of `REF88Rotations.RoughGroup (chartFlow …)` follow from the accepted
  flow facts (group law, joint continuity, conservation of every indexed mass `I_n` through
  `RAEEMain.root_L2_flow`) EXCEPT the finite-support commutation field, which is the printed step
  "the preceding calculation makes it commute ..." and is carried here as the single named predicate
  `FiniteCommutation`.  It is NOT REG-015; it is the output of the finite-action Hamiltonian
  calculation (printed paragraphs "Bounded contour energies near arbitrary mass" and "Physical
  rotations on finite action supports") which is NOT proved in this module.
* `physical_rotations_of_commutation` (INTERMEDIATE theorem): under `FiniteCommutation`, the printed
  rotation formula `eq:global-NLS-rotations` with its frequency continuity, the zero-action statement,
  uniqueness of `ν_n`, and strong continuity on fixed-action tori (including weighted norms).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate ENNReal Topology
open Filter

namespace QuantumNLS.REF88Chart

open QuantumNLS.REF88Rotations QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies
open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow
open QuantumNLS.PhysicalTensor (L2T)

/-- The sequence space `ℓ²(ℤ;ℂ)` (same type as `D01LocalPrimitive.K`). -/
abbrev K : Type := E

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### Joint continuity of the physical flow -/

lemma continuous_flow_joint (hκ : 0 ≤ κ) :
    Continuous (fun p : L2T L × ℝ => flowMap hκ p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨f₀, t₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨Kc, hKc, HK⟩ := flow_lipschitz (L := L) hκ (‖f₀‖ + 1) (|t₀| + 1) (by positivity)
    (by positivity)
  have hct : Continuous (flowMap hκ f₀) := (flowMap_spec hκ f₀).1.1
  obtain ⟨δ₂, hδ₂, H₂⟩ := Metric.continuousAt_iff.mp hct.continuousAt (ε / 2) (by positivity)
  refine ⟨min (min 1 δ₂) (ε / (2 * (Kc + 1))), by positivity, ?_⟩
  rintro ⟨f, t⟩ hp
  have hp' := hp
  rw [Prod.dist_eq] at hp'
  have hf : dist f f₀ < min (min 1 δ₂) (ε / (2 * (Kc + 1))) :=
    lt_of_le_of_lt (le_max_left _ _) hp'
  have ht : dist t t₀ < min (min 1 δ₂) (ε / (2 * (Kc + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) hp'
  have hf1 : dist f f₀ < 1 := lt_of_lt_of_le hf ((min_le_left _ _).trans (min_le_left _ _))
  have hf2 : dist f f₀ < ε / (2 * (Kc + 1)) := lt_of_lt_of_le hf (min_le_right _ _)
  have ht1 : dist t t₀ < 1 := lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_left _ _))
  have ht2 : dist t t₀ < δ₂ := lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_right _ _))
  have hfR : ‖f‖ ≤ ‖f₀‖ + 1 := by
    have := norm_le_insert' f f₀
    rw [dist_eq_norm] at hf1
    linarith [norm_sub_rev f f₀]
  have htT : t ∈ Set.Icc (-(|t₀| + 1)) (|t₀| + 1) := by
    rw [Real.dist_eq] at ht1
    constructor <;> cases abs_cases t₀ <;> cases abs_cases (t - t₀) <;> linarith
  have h1 := HK f f₀ hfR (by linarith) t htT
  have h2 := H₂ ht2
  rw [dist_eq_norm] at hf2 ⊢
  rw [dist_eq_norm] at h2
  calc ‖flowMap hκ f t - flowMap hκ f₀ t₀‖
      ≤ ‖flowMap hκ f t - flowMap hκ f₀ t‖ + ‖flowMap hκ f₀ t - flowMap hκ f₀ t₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        have hfd : ‖f - f₀‖ < ε / (2 * (Kc + 1)) := hf2
        have : Kc * ‖f - f₀‖ ≤ ε / 2 := by
          calc Kc * ‖f - f₀‖ ≤ Kc * (ε / (2 * (Kc + 1))) := by gcongr
            _ ≤ ε / 2 := by
                rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
        have h3 : ‖flowMap hκ f t - flowMap hκ f₀ t‖ ≤ ε / 2 := h1.trans this
        have h4 : ‖flowMap hκ f₀ t - flowMap hκ f₀ t₀‖ < ε / 2 := h2
        linarith
    _ = ε := by ring

/-! ### The chart conjugate `A^t = Φ S^t Φ⁻¹` -/

section Chart
variable {Φ : L2T L → K}

/-- The inverse of a strongly symplectic diffeomorphism (a choice; unique). -/
def chartInv (hΦ : IsStronglySymplectic Φ) : K → L2T L := Classical.choose hΦ.exists_inverse

lemma chartInv_left (hΦ : IsStronglySymplectic Φ) (u : L2T L) : chartInv hΦ (Φ u) = u :=
  (Classical.choose_spec hΦ.exists_inverse).1 u

lemma chartInv_right (hΦ : IsStronglySymplectic Φ) (z : K) : Φ (chartInv hΦ z) = z :=
  (Classical.choose_spec hΦ.exists_inverse).2.1 z

/-- `A^t = Φ ∘ S^t ∘ Φ⁻¹` with `S^t` the accepted physical `L²` flow. -/
def chartFlow (hΦ : IsStronglySymplectic Φ) (hκ : 0 ≤ κ) (t : ℝ) (z : K) : K :=
  Φ (flowMap hκ (chartInv hΦ z) t)

lemma chartFlow_zero (hΦ : IsStronglySymplectic Φ) (hκ : 0 ≤ κ) (z : K) :
    chartFlow hΦ hκ 0 z = z := by
  unfold chartFlow
  rw [(flowMap_spec hκ _).2.1, chartInv_right hΦ]

lemma chartFlow_add (hΦ : IsStronglySymplectic Φ) (hκ : 0 ≤ κ) (s t : ℝ) (z : K) :
    chartFlow hΦ hκ (s + t) z = chartFlow hΦ hκ s (chartFlow hΦ hκ t z) := by
  unfold chartFlow
  rw [chartInv_left hΦ, flowMap_comp]

lemma chartFlow_apply (hΦ : IsStronglySymplectic Φ) (hκ : 0 ≤ κ) (t : ℝ) (u : L2T L) :
    chartFlow hΦ hκ t (Φ u) = Φ (flowMap hκ u t) := by
  unfold chartFlow
  rw [chartInv_left hΦ]

lemma continuous_chartFlow (hΦ : IsStronglySymplectic Φ) (hcΦ : Continuous Φ)
    (hcΨ : Continuous (chartInv hΦ)) (hκ : 0 ≤ κ) :
    Continuous (fun p : ℝ × K => chartFlow hΦ hκ p.1 p.2) := by
  unfold chartFlow
  have h1 : Continuous (fun p : ℝ × K => (chartInv hΦ p.2, p.1)) :=
    (hcΨ.comp continuous_snd).prodMk continuous_fst
  exact hcΦ.comp ((continuous_flow_joint hκ).comp h1)

/-- Preservation of every `q_n = |z_n|²`: the exact moduli and the conservation of every indexed mass
along the physical flow (`RAEEMain.root_L2_flow`). -/
lemma chartFlow_modulus (hκ : 0 < κ) (hΦ : IsStronglySymplectic Φ)
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (t : ℝ) (z : K) (n : ℤ) : ‖chartFlow hΦ hκ.le t z n‖ = ‖z n‖ := by
  have hcons := ((QuantumNLS.RAEEMain.root_L2_flow (L := L) hκ.le).2 hκ).1 (chartInv hΦ z) t 0
  have h1 := (hcons.2.2.2 n)
  rw [(flowMap_spec hκ.le _).2.1] at h1
  have e1 := hmod (flowMap hκ.le (chartInv hΦ z) t) n
  have e2 := hmod (chartInv hΦ z) n
  rw [chartInv_right hΦ] at e2
  unfold chartFlow
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), e1, e2, h1]

/-- **The single printed step that is carried as a named hypothesis in this module**: "On finitely
supported sequences, the preceding calculation makes it commute with every finite collection of
coordinate rotations."  Its proof is the finite-action Hamiltonian calculation of the printed
paragraphs "Bounded contour energies near arbitrary mass" and "Physical rotations on finite action
supports" and is NOT part of this module. -/
def FiniteCommutation (hΦ : IsStronglySymplectic Φ) (hκ : 0 ≤ κ) : Prop :=
  ∀ (t : ℝ) (θ : ℤ → ℝ) (z : K), (∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0) →
    chartFlow hΦ hκ t (rotE θ z) = rotE θ (chartFlow hΦ hκ t z)

/-- All fields of `RoughGroup` but the finite-support commutation hold for the chart conjugate of the
accepted physical flow. -/
theorem chart_roughGroup (hκ : 0 < κ) (hΦ : IsStronglySymplectic Φ) (hcΦ : Continuous Φ)
    (hcΨ : Continuous (chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (hfc : FiniteCommutation hΦ hκ.le) : RoughGroup (chartFlow hΦ hκ.le) where
  zero := chartFlow_zero hΦ hκ.le
  add := chartFlow_add hΦ hκ.le
  cont := continuous_chartFlow hΦ hcΦ hcΨ hκ.le
  modulus := chartFlow_modulus hκ hΦ hmod
  finrot := hfc

/-- The action array of a chart point is the actual indexed-mass array. -/
lemma act_chart (hκ : 0 < κ) {Φ : L2T L → K}
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (u : L2T L) : act (Φ u) = fun m => (RootIndexedMasses.masses hκ u).1 m := by
  funext m; exact hmod u m

/-- **INTERMEDIATE THEOREM (rotation formula; conditional on `FiniteCommutation`).**  Let `Φ` be a
strongly symplectic diffeomorphism with exact moduli (`|Φ(u)_n|² = I_n^{(κ)}(u)`), `κ > 0`, and assume
the finite-support commutation `FiniteCommutation`.  Then there are real frequencies `ν_n` on `ℓ¹_+`
(`ActionTorus.PosL1`) with
* `Φ(S^t u)_n = e^{-itν_n(𝓘(u))} Φ(u)_n` whenever `I_n(u) > 0` (printed `eq:global-NLS-rotations`);
* a zero action gives a coordinate that stays zero (no frequency asserted);
* `ν_n` is the unique real number with this property at any such point;
* for each `n`, `ν_n` is continuous on `{a ∈ ℓ¹_+ : a_n > 0}` in the norm topology of `ℓ¹`;
* each `A^t` maps every fixed-action torus to itself, `A^0 = id`, `A^{s+t} = A^s A^t`, the orbit is
  continuous in `ℓ²`, preserves every weighted norm `∑ w_n|z_n|²` and the orbit is continuous in each
  weighted norm at points of finite weighted norm (strong continuity on each fixed-action torus,
  including infinite support). -/
theorem physical_rotations_of_commutation (hκ : 0 < κ) (hΦ : IsStronglySymplectic Φ)
    (hcΦ : Continuous Φ) (hcΨ : Continuous (chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (hfc : FiniteCommutation hΦ hκ.le) :
    ∃ ν : ℤ → ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : ActionTorus.PosL1 | 0 < a.1 n}) ∧
      (∀ a : ActionTorus.PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ hκ.le 0 z = z ∧
        chartFlow hΦ hκ.le (s + t) z = chartFlow hΦ hκ.le s (chartFlow hΦ hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ hκ.le t z n -
          chartFlow hΦ hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0)) := by
  have hR := chart_roughGroup hκ hΦ hcΦ hcΨ hmod hfc
  obtain ⟨ν, h1, h2, h3, h4, h5, h6⟩ := rough_extension hR
  have hne : ∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n ↔ Φ u n ≠ 0 := by
    intro u n
    rw [← hmod u n]
    constructor
    · intro h hz; rw [hz] at h; simp at h
    · intro h; exact pow_pos (norm_pos_iff.mpr h) 2
  refine ⟨fun n a => ν n (fun m => a.1 m), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u t n hn
    have := h1 t (Φ u) n ((hne u n).mp hn)
    rw [act_chart hκ hmod] at this
    rw [← chartFlow_apply hΦ hκ.le t u]
    exact this
  · intro u t n hn
    have hz : Φ u n = 0 := by
      by_contra h
      exact absurd ((hne u n).mpr h) (by rw [hn]; exact lt_irrefl _)
    rw [← chartFlow_apply hΦ hκ.le t u]
    exact h2 t (Φ u) n hz
  · intro u n hn ν' hν'
    have := h3 (Φ u) n ((hne u n).mp hn) ν' (fun t => by rw [chartFlow_apply]; exact hν' t)
    rw [act_chart hκ hmod] at this
    exact this
  · intro n
    refine (h4 n).comp continuous_subtype_val.continuousOn ?_
    intro a ha
    exact ⟨a.2, ha⟩
  · intro a z hz s t
    refine ⟨?_, chartFlow_zero hΦ hκ.le z, chartFlow_add hΦ hκ.le s t z, ?_⟩
    · intro n
      rw [chartFlow_modulus hκ hΦ hmod t z n]
      exact hz n
    · exact (continuous_chartFlow hΦ hcΦ hcΨ hκ.le).comp (continuous_id.prodMk continuous_const)
  · intro w hw z hz
    exact ⟨fun t => h5 w t z, fun t0 => h6 w hw z hz t0⟩

end Chart

end QuantumNLS.REF88Chart

#print axioms QuantumNLS.REF88Chart.chart_roughGroup
#print axioms QuantumNLS.REF88Chart.physical_rotations_of_commutation
#print axioms QuantumNLS.REF88Chart.continuous_flow_joint
