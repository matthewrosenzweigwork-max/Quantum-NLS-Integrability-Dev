import QuantumNLS.MainTheoremR01
import QuantumNLS.FullWickFinalH15

/-!
# MainTheoremR02Carrier: one preparation, one propagator, one evolved state for parts (iii), (iv), (v)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 36-38 (one
normalized preparation `ψ_N` and `U_N(t) = exp(-iΣ_{r∈𝓡} t_r Q_{N,r})`), lines 49-52 (part (iv) uses the same
`U_N(t)ψ_N`), lines 65-71 (part (v): `Γ_N(t)_{ab} = ⟨U_N(t)ψ_N, E^q_{N,ab}U_N(t)ψ_N⟩`).  review record r107
ruling "Carrier/propagator: A, coherence needed".

The assembly uses two carriers for the same sector:
* parts (iii)/(v): `HN L (1+n)`, basis `ReconstructionR33m.basis hκ n`, propagator `ReconstructionR33m.U hκ R t n`
  (= `HierarchyFlow.quantumFlow`), preparations `ReconstructionR33m.Preparation u` (R-8362E5EB/R-FAF88C8A objects);
* part (iv): `HN L (N+1)`, basis `Def044D1SpectralR51a.basis hκ N`, propagator
  `ActualModelQuantumR52a.chargeUnitary hκ R t N` (R-E679E41D/R-568BCDF8 objects), preparations normalized with
  `‖ψ_N - u^{⊗(N+1)}‖ → 0`.

Proved here (kernel-checked, no hypothesis):
* `chargeUnitary_eq_quantumFlow`: `chargeUnitary hκ R t N` IS `quantumFlow (Def044D1SpectralR51a.basis hκ N) κ R t`
  (same spectral multiplier `exp(-iΣ t_r Λ_{N+1,r})` at coupling `κ/(N+1)`);
* `quantumFlow_castHN`: the propagator commutes with the index cast `FullWickO4.castHN` for HEq bases;
* `propagator_bridge`: `U_{1+n}(t)(e_n x) = e_n(chargeUnitary_n(t) x)` with `e_n = FullWickFinalH15.eH L n =
  castHN (Nat.add_comm n 1)` (a linear isometric equivalence, the identity transported along `n+1 = 1+n`);
* `prep_transport`, `prep_transport_symm`: `e` is a bijection between the two preparation classes
  (`castHN_wvec`: it maps `u^{⊗(n+1)}` to `u^{⊗(1+n)}`);
* `forall_prep_iff`: EVERY property of the evolved family over all (iii)/(v) preparations holds iff it holds for
  `e_n(chargeUnitary_n(t)ψ_n)` over all (iv) preparations;
* `common_state`: for one preparation `ψ` (on the part (iv) carrier), one evolved state
  `Ψ_N(t) = chargeUnitary hκ R t N (ψ N)` and one compact time set `K` inside a box, the Cartesian and phase strong
  symbols of (iii), the marginal limit of (iv), and positivity / trace one / entries / trace limit of `Γ_N(t)` in (v)
  hold simultaneously, with (iii)/(v) evaluated at `e_n(Ψ_n(t))`.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace ENNReal

namespace QuantumNLS.MainTheoremR02Carrier

open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox StrongSymbols)
open QuantumNLS.OccupationUnitary (oneBasis)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.ActualModelTargetR53a (hamFlows)
open QuantumNLS.TensorCarrier (HilbertTensorPower)
open QuantumNLS.PhysicalTensor (L2T reducedDensityN)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The carrier identification `HN L (n+1) ≃ HN L (1+n)` (`castHN (Nat.add_comm n 1)`). -/
abbrev e (n : ℕ) : HN L (n + 1) ≃ₗᵢ[ℂ] HN L (1 + n) := FullWickFinalH15.eH L n

/-! ### The propagators -/

/-- The propagator commutes with the index cast, for bases related by the cast. -/
theorem quantumFlow_castHN {N M : ℕ} (h : N = M) (b : BetheBasis L N) (b' : BetheBasis L M) (hb : HEq b b')
    (R : Finset ℕ) (t : ℕ → ℝ) (x : HN L N) :
    HierarchyFlow.quantumFlow b' κ R t (FullWickO4.castHN h x) =
      FullWickO4.castHN h (HierarchyFlow.quantumFlow b κ R t x) := by
  subst h; cases hb; rfl

/-- **The part (iv) propagator is the joint charge flow** `exp(-iΣ_{r∈𝓡} t_r Q_{N+1,r})` on the
`Def044D1SpectralR51a` basis. -/
theorem chargeUnitary_eq_quantumFlow (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) :
    ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n =
      HierarchyFlow.quantumFlow (Def044D1SpectralR51a.basis (L := L) hκ n) κ R t := by
  unfold ActualModelQuantumR52a.chargeUnitary HierarchyFlow.quantumFlow
  unfold ActualModelQuantumR52a.chargeSymbol HierarchyFlow.jointSymbol
  simp only [Nat.cast_add, Nat.cast_one]

/-- **Propagator bridge**: `U_{1+n}(t) ∘ e_n = e_n ∘ chargeUnitary_n(t)`. -/
theorem propagator_bridge (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) (x : HN L (n + 1)) :
    ReconstructionR33m.U (L := L) hκ R t n (e n x) =
      e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n x) := by
  rw [chargeUnitary_eq_quantumFlow]
  exact quantumFlow_castHN _ _ _ (FullWickO4.basis_heq hκ n) R t x

theorem propagator_bridge_symm (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) (y : HN L (1 + n)) :
    ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n ((e n).symm y) =
      (e n).symm (ReconstructionR33m.U (L := L) hκ R t n y) := by
  rw [LinearIsometryEquiv.eq_symm_apply, ← propagator_bridge, LinearIsometryEquiv.apply_symm_apply]

/-! ### The preparations -/

/-- The part (iv) preparation class: normalized, `‖ψ_N - u^{⊗(N+1)}‖ → 0`. -/
def PrepN (u : Smooth L) (ψ : ∀ N : ℕ, HN L (N + 1)) : Prop :=
  (∀ N, ‖ψ N‖ = 1) ∧
    Tendsto (fun N => ‖ψ N - HighMomentsOps.wvec (N + 1) (physical u)‖) atTop (𝓝 0)

theorem e_sub_wvec (u : Smooth L) (n : ℕ) (x : HN L (n + 1)) :
    ‖e n x - ReconstructionR33m.product u n‖ = ‖x - HighMomentsOps.wvec (n + 1) (physical u)‖ := by
  have h : ReconstructionR33m.product u n = e n (HighMomentsOps.wvec (n + 1) (physical u)) :=
    (FullWickFinalH15.eH_wvec L n (physical u)).symm
  rw [h, ← map_sub, LinearIsometryEquiv.norm_map]

/-- **Preparation transport**: `ψ` is a part (iv) preparation iff `e ψ` is a part (iii)/(v) preparation. -/
theorem prep_transport (u : Smooth L) (ψ : ∀ N : ℕ, HN L (N + 1)) :
    PrepN u ψ ↔ Preparation u (fun n => e n (ψ n)) := by
  unfold PrepN Preparation StrongSymbolDef.IsNormClosePrep StrongSymbolDef.IsNormalized
  simp only [LinearIsometryEquiv.norm_map, e_sub_wvec]

theorem prep_transport_symm (u : Smooth L) (φ : ∀ n : ℕ, HN L (1 + n)) :
    Preparation u φ ↔ PrepN u (fun N => (e N).symm (φ N)) := by
  rw [prep_transport]
  simp only [LinearIsometryEquiv.apply_symm_apply]

/-- **Common interface.** Every property `P` of the evolved family holds for all part (iii)/(v) preparations
`φ` with the propagator `U` iff it holds for all part (iv) preparations `ψ` with the evolved state
`e_n(chargeUnitary_n(t) ψ_n)`. -/
theorem forall_prep_iff (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ)
    (P : ((ℕ → ℝ) → ∀ n : ℕ, HN L (1 + n)) → Prop) :
    (∀ φ : ∀ n : ℕ, HN L (1 + n), Preparation u φ →
        P (fun t n => ReconstructionR33m.U (L := L) hκ R t n (φ n))) ↔
      (∀ ψ : ∀ N : ℕ, HN L (N + 1), PrepN u ψ →
        P (fun t n => e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n (ψ n)))) := by
  constructor
  · intro h ψ hψ
    have hv : (fun t n => ReconstructionR33m.U (L := L) hκ R t n (e n (ψ n))) =
        (fun t n => e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n (ψ n))) :=
      funext fun t => funext fun n => propagator_bridge hκ R t n (ψ n)
    rw [← hv]
    exact h _ ((prep_transport u ψ).1 hψ)
  · intro h φ hφ
    have hv : (fun t n => e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n ((e n).symm (φ n)))) =
        (fun t n => ReconstructionR33m.U (L := L) hκ R t n (φ n)) := by
      funext t n
      rw [propagator_bridge_symm, LinearIsometryEquiv.apply_symm_apply]
    rw [← hv]
    exact h _ ((prep_transport_symm u φ).1 hφ)

/-! ### One evolved state for parts (iii), (iv), (v) -/

/-- The one evolved state `Ψ_N(t) = U_N(t)ψ_N` on the part (iv) carrier. -/
abbrev Ψ (hκ : 0 < κ) (R : Finset ℕ) (ψ : ∀ N : ℕ, HN L (N + 1)) (t : ℕ → ℝ) (N : ℕ) : HN L (N + 1) :=
  ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t N (ψ N)

theorem strongSymbols_mono {T : Type*} {K K' : Set T} (hK : K ⊆ K')
    {A : ∀ n : ℕ, HN L (1 + n) →L[ℂ] HN L (1 + n)} {z : T → ℂ} {v : T → ∀ n : ℕ, HN L (1 + n)}
    (h : StrongSymbols K' A z v) : StrongSymbols K A z v := by
  intro ε hε
  filter_upwards [h ε hε] with n hn t ht
  exact hn t (hK ht)

/-- **Simultaneous conclusions on one evolved state.** Fix the gauge `g` and flows `F`. The propagators and
preparation classes are identified (first two conjuncts), and for every unit smooth `u`, finite `𝓡`, box
`TimeBox 𝓡 lo hi`, compact `K` inside it, and ONE preparation `ψ` with `Ψ_N(t) = U_N(t)ψ_N`:
(iii) the Cartesian symbols `c_{ab}(Φ_tu)` and positive-action phase symbols, with adjoints, at `e(Ψ(t))`;
(iv) the trace-norm marginal limit of `Ψ(t)` for every rank `k`;
(v) `Γ_N(t) = Γ_N[e(Ψ_N(t))]` positive, trace one, with entries `⟨e Ψ, E^g_{ab} e Ψ⟩`, and the trace limit to
`|w(Φ_tu)⟩⟨w(Φ_tu)|`, uniformly on `K`. -/
def CommonState (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (g : Gauge) : Prop :=
  (∀ (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) (x : HN L (n + 1)),
    ReconstructionR33m.U (L := L) hκ R t n (e n x) =
      e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n x)) ∧
  (∀ (u : Smooth L) (ψ : ∀ N : ℕ, HN L (N + 1)), PrepN u ψ ↔ Preparation u (fun n => e n (ψ n))) ∧
  (∀ (u : Smooth L) (R : Finset ℕ) (P : ((ℕ → ℝ) → ∀ n : ℕ, HN L (1 + n)) → Prop),
    (∀ φ : ∀ n : ℕ, HN L (1 + n), Preparation u φ →
        P (fun t n => ReconstructionR33m.U (L := L) hκ R t n (φ n))) ↔
      (∀ ψ : ∀ N : ℕ, HN L (N + 1), PrepN u ψ →
        P (fun t n => e n (ActualModelQuantumR52a.chargeUnitary (L := L) hκ R t n (ψ n))))) ∧
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (K : Set (ℕ → ℝ)), IsCompact K → K ⊆ TimeBox R lo hi →
  ∀ (ψ : ∀ N : ℕ, HN L (N + 1)), PrepN u ψ →
    -- (iii)
    (∀ a b : ℤ,
      StrongSymbols K (fun n => ReconstructionR33m.E (L := L) hκ g n a b)
        (fun t => ReconstructionR33m.w hκ F u R t a * conj (ReconstructionR33m.w hκ F u R t b))
        (fun t n => e n (Ψ hκ R ψ t n)) ∧
      (a ≠ b → 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ ^ 2 →
        0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ ^ 2 →
        StrongSymbols K (fun n => ReconstructionR33m.W (L := L) hκ g n a b)
          (fun t => ReconstructionR33m.w hκ F u R t a * conj (ReconstructionR33m.w hκ F u R t b) /
            (Real.sqrt (‖ReconstructionR33m.w hκ F u R t a‖ ^ 2 *
              ‖ReconstructionR33m.w hκ F u R t b‖ ^ 2) : ℂ))
          (fun t n => e n (Ψ hκ R ψ t n)))) ∧
    -- (iv)
    (∀ k : ℕ, Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : K, TraceClass.traceNorm (reducedDensityN (N + 1) k hk
        (Ψ hκ R ψ t.val N : HilbertTensorPower ℂ (L2T L) (N + 1)) -
        Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows F R) t.val u)))
      else 0) atTop (𝓝 0)) ∧
    -- (v)
    (∀ (t : ℕ → ℝ) (n : ℕ),
      (ReconstructionR33m.density hκ g n (e n (Ψ hκ R ψ t n))).IsPositive ∧
      TraceClass.posTrace (ReconstructionR33m.density hκ g n (e n (Ψ hκ R ψ t n))) = 1 ∧
      ∀ a b : ℤ, ⟪oneBasis a, ReconstructionR33m.density hκ g n (e n (Ψ hκ R ψ t n)) (oneBasis b)⟫_ℂ =
        ⟪e n (Ψ hκ R ψ t n), ReconstructionR33m.E (L := L) hκ g n a b (e n (Ψ hκ R ψ t n))⟫_ℂ) ∧
    Tendsto (fun n => ⨆ t : K,
      TraceClass.traceNorm (ReconstructionR33m.density hκ g n (e n (Ψ hκ R ψ t.val n)) -
        ReconstructionR33m.projector (ReconstructionR33m.w hκ F u R t.val))) atTop (𝓝 0)

/-- `CommonState` from the three part conclusions it combines: the R-8362E5EB input (part (iii)), the physical
marginal (part (iv)) at the same flows, and the reconstruction (part (v)). -/
theorem common_state (hκ : 0 < κ) (g : Gauge)
    (D : RD8362E5EBInput hκ (MainTheoremR01.F (L := L) hκ) g)
    (hM : MainTheoremR01Physical.PhysicalMarginal (L := L) hκ)
    (hR : ReconstructionR33m.Reconstruction hκ (MainTheoremR01.F (L := L) hκ) g) :
    CommonState (L := L) hκ (MainTheoremR01.F (L := L) hκ) g := by
  refine ⟨propagator_bridge hκ, prep_transport, fun u R P => forall_prep_iff hκ u R P, ?_⟩
  intro u hu R lo hi K hK hKB ψ hψ
  have hφ : Preparation u (fun n => e n (ψ n)) := (prep_transport u ψ).1 hψ
  have hv : (fun t n => ReconstructionR33m.U (L := L) hκ R t n (e n (ψ n))) =
      (fun t n => e n (Ψ hκ R ψ t n)) :=
    funext fun t => funext fun n => propagator_bridge hκ R t n (ψ n)
  have hunit : ∀ t n, ‖e n (Ψ hκ R ψ t n)‖ = 1 := fun t n => by
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    exact hψ.1 n
  refine ⟨fun a b => ?_, fun k => hM u hu R K hK ψ hψ.1 hψ.2 k, fun t n => ?_, ?_⟩
  · have h := D u hu R lo hi (fun n => e n (ψ n)) hφ a b
    simp only [] at h
    rw [hv] at h
    exact ⟨strongSymbols_mono hKB h.1, fun hab ha hb => strongSymbols_mono hKB (h.2 hab ha hb)⟩
  · exact MainTheoremR01Algebra.density_facts hκ g n _ (hunit t n)
  · have h := hR u hu R K hK (fun n => e n (ψ n)) hφ.1 hφ.2
    simpa only [propagator_bridge] using h

end QuantumNLS.MainTheoremR02Carrier

#print axioms QuantumNLS.MainTheoremR02Carrier.propagator_bridge
#print axioms QuantumNLS.MainTheoremR02Carrier.forall_prep_iff
#print axioms QuantumNLS.MainTheoremR02Carrier.common_state
