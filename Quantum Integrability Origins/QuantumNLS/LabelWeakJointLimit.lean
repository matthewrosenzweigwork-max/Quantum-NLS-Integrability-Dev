import QuantumNLS.LabelIdentification

/-!
# PROP-002 `lem:B3-weak-joint-limit`: assembly, full-sequence convergence, DEF-043/DEF-010 binding

Source: `source/chapters/propagation/label_periods.tex:43-117`. "Suppose `N⁻¹Σ_j δ_{q_j} ⇀ μ`. Then
`N⁻¹Σ_j δ_{(q_j,n_j)}` converges weakly to `μ(dt) δ_{n(t)}(dn)`, with `n(t)` given in
Definition `def:PF-indexed-scalar`. No moment convergence is required." ... "Every subsequential joint
limit is therefore the same displayed measure. Tightness and this uniqueness prove convergence of the
full sequence without a moment assumption."

Imports ID1 `LabelIdentification` (`639e8e63…`, own, frozen; through it PJ1, JS1, KL1 and the
read-only DEF-043 `IndexedScalarMeasureCuts` `641aaaf7…`, DEF-010 `EmpiricalRapidity` `d418625e…`,
the auxiliary construction's `LabelJointLimit` `4120590e…` / `LabelTightness` `3c7ed0d1…`).

* `graphP μ n` — the displayed measure `μ(dt) δ_{n(t)}(dn)` on `ℝ × ℤ`;
* `subseq_limit_eq` — every subsequential joint limit is `graphP μ g` with `g = n` `μ`-a.e.;
* `exists_label_version` — `n(t) = Lt/(2π) − κ Re G_μ(t+i0)/π` has a measurable integer version;
* **`weak_joint_limit`** — full-sequence weak convergence to `graphP μ n` for every measurable
  integer version `n` of `indexLabel L κ reG`;
* **`weak_joint_limit_DEF043`** — the same with the DEF-043 structure `IndexedScalarMeasureCuts`
  (`μ = S.μ`, `reG = S.reG`, nonatomicity and boundary hypothesis from `S`);
* `rootP_eq_empirical`, **`weak_joint_limit_DEF010`** — the root empirical measures are DEF-010's
  `empiricalMeasureκ L κ m` when the roots are `arrRoots L (κ/N) m`; the lemma with the hypothesis
  stated on DEF-010 empirical measures.
Scope: the sequence `N k` of particle numbers satisfies `N k → ∞` (`hNtop`; the source's limit
`N → ∞`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelWeakJointLimit

open QuantumNLS.LabelJointLimit QuantumNLS.LabelTightness QuantumNLS.LabelJointWeak
  QuantumNLS.LabelJointStructure QuantumNLS.LabelKernelLimit QuantumNLS.LabelIdentification
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts QuantumNLS.EmpiricalRapidity
open QuantumNLS.BetheLabels (MArr arrRoots)

/-- The displayed limit `μ(dt) δ_{n(t)}(dn)`. -/
def graphP (μ : ProbabilityMeasure ℝ) (n : ℝ → ℤ) : ProbabilityMeasure (ℝ × ℤ) :=
  μ.map (fun t => (t, n t))

lemma graphP_toMeasure (μ : ProbabilityMeasure ℝ) (n : ℝ → ℤ) :
    (graphP μ n : Measure (ℝ × ℤ)) = (μ : Measure ℝ).map (fun t => (t, n t)) :=
  ProbabilityMeasure.toMeasure_map _

lemma graphP_congr (μ : ProbabilityMeasure ℝ) {g n : ℝ → ℤ}
    (h : ∀ᵐ t ∂(μ : Measure ℝ), g t = n t) : graphP μ g = graphP μ n := by
  apply Subtype.ext
  show (graphP μ g : Measure (ℝ × ℤ)) = (graphP μ n : Measure (ℝ × ℤ))
  rw [graphP_toMeasure, graphP_toMeasure]
  exact Measure.map_congr (h.mono fun t ht => by
    show (t, g t) = (t, n t)
    rw [ht])

section Seq

variable {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
  {μ : ProbabilityMeasure ℝ}

/-- **Every subsequential joint limit is the displayed measure** with `n = indexLabel` a.e. -/
theorem subseq_limit_eq (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary (μ : Measure ℝ) reG ∨ BoundedAEBoundary (μ : Measure ℝ) reG)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ)) :
    ∃ g : ℝ → ℤ, Measurable g ∧ (∀ᵐ t ∂(μ : Measure ℝ), (g t : ℝ) = indexLabel L κ reG t) ∧
      γ = graphP μ g := by
  obtain ⟨g, hg, heq⟩ := limit_graph hconv hφ hγ
  refine ⟨g, hg, ae_eq_indexLabel hL (μ : Measure ℝ) hbd hg (limit_label_bound hL hκ hγ hg heq)
    (fun f hf hcs => limit_identity hL hκ hconv hNtop hφ hγ hg heq hf hcs), ?_⟩
  apply Subtype.ext
  show (γ : Measure (ℝ × ℤ)) = (graphP μ g : Measure (ℝ × ℤ))
  rw [graphP_toMeasure]
  exact heq

/-- `n(t) = Lt/(2π) − κ Re G_μ(t+i0)/π` has a measurable integer-valued version. -/
theorem exists_label_version (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary (μ : Measure ℝ) reG ∨ BoundedAEBoundary (μ : Measure ℝ) reG) :
    ∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂(μ : Measure ℝ), (n t : ℝ) = indexLabel L κ reG t := by
  obtain ⟨γ, ψ, hψ, hlim⟩ := exists_subseq_tendsto N hN B μ hL hκ hconv id
  obtain ⟨g, hg, hgI, -⟩ := subseq_limit_eq hL hκ hconv hNtop hbd
    (φ := fun k => id (ψ k)) hψ.tendsto_atTop hlim
  exact ⟨g, hg, hgI⟩

/-- **PROP-002 `lem:B3-weak-joint-limit`.** If `N⁻¹Σ_j δ_{q_j} ⇀ μ` (nonatomic, with either DEF-043
boundary-value alternative for `reG`), then `N⁻¹Σ_j δ_{(q_j,n_j)} ⇀ μ(dt) δ_{n(t)}(dn)` along the
full sequence, for every measurable integer version `n` of `Lt/(2π) − κ reG(t)/π`. -/
theorem weak_joint_limit (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary (μ : Measure ℝ) reG ∨ BoundedAEBoundary (μ : Measure ℝ) reG)
    {n : ℝ → ℤ} (hnI : ∀ᵐ t ∂(μ : Measure ℝ), (n t : ℝ) = indexLabel L κ reG t) :
    Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨γ, ψ, hψ, hlim⟩ := exists_subseq_tendsto N hN B μ hL hκ hconv ns
  obtain ⟨g, -, hgI, rfl⟩ := subseq_limit_eq hL hκ hconv hNtop hbd
    (φ := fun k => ns (ψ k)) (hns.comp hψ.tendsto_atTop) hlim
  refine ⟨ψ, ?_⟩
  rw [← graphP_congr μ ((hgI.and hnI).mono fun t ht => by
    have h : (g t : ℝ) = n t := ht.1.trans ht.2.symm
    exact_mod_cast h)]
  exact hlim

/-- **PROP-002 with the DEF-043 structure** (`IndexedScalarMeasureCuts`, `641aaaf7…`): the limit
measure is `S.μ(dt) δ_{n(t)}(dn)`, `n(t) = Lt/(2π) − κ S.reG(t)/π`, and such a measurable integer
`n` exists. -/
theorem weak_joint_limit_DEF043 (S : IndexedScalarMeasureCuts L κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hμ : (μ : Measure ℝ) = S.μ) (hNtop : Tendsto N atTop atTop) :
    (∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) ∧
    ∀ n : ℝ → ℤ, (∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) →
      Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  have hna : NullSingletonClass (μ : Measure ℝ) := by rw [hμ]; exact S.noAtoms
  have hbd : LocallyUniformBoundary (μ : Measure ℝ) S.reG ∨
      BoundedAEBoundary (μ : Measure ℝ) S.reG := by rw [hμ]; exact S.boundary
  refine ⟨?_, fun n hn => weak_joint_limit S.hL S.hκ hconv hNtop hbd (by rw [hμ]; exact hn)⟩
  obtain ⟨n, hn, hnI⟩ := exists_label_version S.hL S.hκ hconv hNtop hbd
  exact ⟨n, hn, by rw [← hμ]; exact hnI⟩

/-- The root empirical measure is DEF-010's `empiricalMeasureκ` when the roots are the realized
`arrRoots L (κ/N) m`. -/
lemma rootP_eq_empirical {N : ℕ} (B : OnShellBethe L κ N) (hN : 0 < N) (m : MArr N)
    (hq : B.q = arrRoots L (κ / N) m) :
    (rootP B hN : Measure ℝ) = empiricalMeasureκ L κ m := by
  show emp B.q = _
  rw [hq]
  rfl

/-- DEF-010's empirical rapidity measure as a probability measure. -/
def empiricalP (L κ : ℝ) {N : ℕ} (hN : 0 < N) (m : MArr N) : ProbabilityMeasure ℝ :=
  ⟨empiricalMeasureκ L κ m, ⟨empiricalMeasure_univ L (κ / N) hN m⟩⟩

/-- **PROP-002 with the hypothesis on DEF-010 empirical measures**: if the on-shell roots are the
realized `arrRoots L (κ/N_k) m_k` and `empiricalMeasureκ L κ m_k ⇀ S.μ`, the joint empirical
measures converge to `S.μ(dt) δ_{n(t)}(dn)`. -/
theorem weak_joint_limit_DEF010 (S : IndexedScalarMeasureCuts L κ) (m : ∀ k, MArr (N k))
    (hq : ∀ k, (B k).q = arrRoots L (κ / N k) (m k))
    (hconv : Tendsto (fun k => empiricalP L κ (hN k) (m k)) atTop (𝓝 μ))
    (hμ : (μ : Measure ℝ) = S.μ) (hNtop : Tendsto N atTop atTop) :
    (∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) ∧
    ∀ n : ℝ → ℤ, (∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) →
      Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  have he : (fun k => rootP (B k) (hN k)) = fun k => empiricalP L κ (hN k) (m k) := by
    funext k
    exact Subtype.ext (rootP_eq_empirical (B k) (hN k) (m k) (hq k))
  exact weak_joint_limit_DEF043 S (he ▸ hconv) hμ hNtop

end Seq

/-- The literal particle-number-indexed case `N = k + 1` (`N → ∞` automatically). -/
theorem weak_joint_limit_seq {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    (B : ∀ k : ℕ, OnShellBethe L κ (k + 1)) {μ : ProbabilityMeasure ℝ}
    (hconv : Tendsto (fun k => rootP (B k) (Nat.succ_pos k)) atTop (𝓝 μ))
    (hμ : (μ : Measure ℝ) = S.μ) :
    (∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) ∧
    ∀ n : ℝ → ℤ, (∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) →
      Tendsto (fun k => jointP (B k) (Nat.succ_pos k)) atTop (𝓝 (graphP μ n)) :=
  weak_joint_limit_DEF043 (N := fun k => k + 1) S hconv hμ (tendsto_add_atTop_nat 1)

end QuantumNLS.LabelWeakJointLimit

#print axioms QuantumNLS.LabelWeakJointLimit.subseq_limit_eq
#print axioms QuantumNLS.LabelWeakJointLimit.exists_label_version
#print axioms QuantumNLS.LabelWeakJointLimit.weak_joint_limit
#print axioms QuantumNLS.LabelWeakJointLimit.weak_joint_limit_DEF043
#print axioms QuantumNLS.LabelWeakJointLimit.weak_joint_limit_DEF010
#print axioms QuantumNLS.LabelWeakJointLimit.weak_joint_limit_seq
