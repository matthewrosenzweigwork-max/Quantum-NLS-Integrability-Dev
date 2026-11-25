import QuantumNLS.FullWickH8

/-! FullWickH9 (haiku_inventory, R-140AE34B `thm:full-wick`, assembly stage B: DYNAMIC clause).

Printed item (wick_calculus.tex:82-89, 182-202): on every fixed smooth hierarchy trajectory on a compact
joint-time box, and for every norm-close preparation (here: every `Preparation u ψ`), the Wick operators
`W^G_N(f)` have the strong symbol `f(w(u,t))` and its adjoint the conjugate, together with ordered
products of generators and the scaled Dirac commutator.

Named input (used by reference, NOT restated): `ReconstructionR33m.RD8362E5EBInput hκ F G` (exact printed
R-8362E5EB, frozen by sol_multi r34), which supplies the generator pairs through
`FullWickO2.wick_generator_pair_RD`. The gauge is the one supplied with the input, `G`; no identification
`G = staticGauge q` is assumed here (see FullWickH10 for the exact requirement).

Symbol bound: `|z_a conj z_b| ≤ 1` on the time box is DERIVED from the strong symbol itself
(`FullWickH8.symbol_le_one_of_strong`), using `‖E_ab‖ ≤ 1` and the isometry of the quantum flow
(`U` is a linear isometric equivalence), so no coordinate identity for the dynamic chart is needed.

Constants: `C = K = 1` for the generator pairs; `pair_list_prod` for ordered products; the O(1/N)
comparison `FullWickS1` and the sum transfer `FullWickS2` for `W(f)`; the Dirac commutator through
`FullWickH1.quantization_Dirac_bound`.

Standard axioms only (see the audit at the end of the file).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH9

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH6 (GoodFactor pair_list_prod)
open QuantumNLS.FullWickH8 (norm_gensym_quant_le orderedWord_adjoint evalSym_eq_sum_words
  symbol_le_one_of_strong adjoint_sub_sum norm_adjoint_eq evaluate_bilinearPoly_eq
  norm_sub_comm_clm)
open QuantumNLS.FullWickO1 (bilinear bilinearPoly)
open QuantumNLS.FullWickO2 (wick_generator_pair_RD)
open QuantumNLS.FullWickS1 (orderedWord monomialWord balanced_ordered_word_comparison_uniform)
open QuantumNLS.FullWickS2 (hasUniformPairT_of_sum_opClose hasUniformStrongT_of_opClose)
open QuantumNLS.WickSymbols (Sym Balanced pb)
open QuantumNLS.WickBounds (gensym wordSym labelsOf Cfg balanced_pb)
open QuantumNLS.WickSpectralBridge (evalSym evalSym_gensym evalSym_wordSym)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)

/-- The quantum flow is an isometry: `‖U_t x‖ = ‖x‖`. -/
lemma dyn_U_norm_eq {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ)
    (x : HN L (1 + n)) :
    ‖ReconstructionR33m.U (L := L) hκ R t n x‖ = ‖x‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- Normalized dynamic preparations: `‖U_t ψ_n‖ = 1` for every time `t`. -/
lemma dyn_prep_norm {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    {u : Def033HierarchyR24m.Smooth L} {ψ : ∀ n : ℕ, HN L (1 + n)}
    (hψ : Preparation u ψ) (R : Finset ℕ) (n : ℕ) (t : ℕ → ℝ) :
    ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 :=
  (dyn_U_norm_eq hκ R t n (ψ n)).trans (hψ.1 n)

section Dynamic

variable {L κ : ℝ} [Fact (0 < L)]

/-- **One generator pair (dynamic), as a `GoodFactor` with `C = K = 1`.** The symbol bound `|z_a z̄_b| ≤ 1`
is derived from the strong symbol. -/
theorem dyn_gen_good (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (p : ℤ × ℤ) :
    GoodFactor (H := fun n => HN L (1 + n))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (gensym p.1 p.2))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n)) 1 1 p := by
  have hpair := wick_generator_pair_RD hκ F G D u hu R lo hi ψ hψ p.1 p.2
  simp only [evaluate_bilinearPoly_eq] at hpair
  have hA : ∀ᶠ n : ℕ in atTop, ‖BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.1 p.2)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun n => norm_gensym_quant_le (by omega) _ G p.1 p.2
  have hA' : ∀ᶠ n : ℕ in atTop, ‖BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.2 p.1)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun n => norm_gensym_quant_le (by omega) _ G p.2 p.1
  have hψN : ∀ᶠ n : ℕ in atTop, ∀ _ ∈ (Set.univ : Set Unit), ∀ t ∈ TimeBox R lo hi,
      ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 :=
    Filter.Eventually.of_forall fun n _ _ t _ => dyn_prep_norm hκ hψ R n t
  refine ⟨hA, hA', fun _ _ t ht => ?_, hpair⟩
  exact symbol_le_one_of_strong hA hψN hpair.1 () (Set.mem_univ _) t ht

/-- **Ordered products of generators (dynamic).** The ordered product `E_{a_1b_1} ⋯ E_{a_kb_k}` along a fixed
smooth trajectory and time box has the uniform strong symbol `∏ z_{a_j} conj z_{b_j}` (= `evalSym (wordSym w)`),
with adjoint the reversed product and conjugate symbol. -/
theorem dyn_word_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (w : List (ℤ × ℤ)) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) G w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G (gensym p.2 p.1)).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym w)) := by
  have hgood : ∀ p ∈ w, GoodFactor (H := fun n => HN L (1 + n))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.1 p.2))
      (fun (p : ℤ × ℤ) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G (bilinear p.2 p.1))
      (fun (p : ℤ × ℤ) (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (gensym p.1 p.2))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n)) 1 1 p :=
    fun p _ => dyn_gen_good hκ F G D u hu R lo hi ψ hψ p
  have hp := (pair_list_prod (H := fun n => HN L (1 + n)) _ _ _ (Set.univ : Set Unit)
    (TimeBox R lo hi) _ 1 1 zero_le_one zero_le_one w hgood).1
  have e : (fun (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym w))
      = (fun (_ : Unit) (t : ℕ → ℝ) => (w.map fun p =>
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (gensym p.1 p.2)).prod) := by
    funext _ t
    rw [evalSym_wordSym]
    congr 1
    apply List.map_congr_left
    intro p _
    exact (evalSym_gensym _ _ _).symm
  rw [e]
  exact hp

/-- **Polynomial (dynamic).** For every balanced `f`, `W^G_N(f)` has along the fixed trajectory and time box
the uniform strong symbol `f(w(u,t))` and its adjoint the conjugate. -/
theorem dyn_poly_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {f : Sym} (hf : Balanced f) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f)
      (fun n => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f) := by
  obtain ⟨K, hK0, hK⟩ := balanced_ordered_word_comparison_uniform f hf
  have hAB : ∀ᶠ n : ℕ in atTop,
      ‖BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f
        - ∑ i ∈ f.coeff.support, f.coeff i •
            orderedWord (ReconstructionR33m.basis (L := L) hκ n) G (monomialWord i)‖
        ≤ K * (n : ℝ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := hK L (1 + n) (by omega) (ReconstructionR33m.basis (L := L) hκ n) G
    unfold FullWickS1.polyWordOp at h1
    rw [norm_sub_comm_clm]
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    apply inv_anti₀ (by exact_mod_cast (show 0 < n from hn))
    push_cast
    linarith
  have hAB' : ∀ᶠ n : ℕ in atTop,
      ‖(BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint
        - ∑ i ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff i) •
            ((monomialWord i).map fun p => BalancedWickDefinition.quantization
              (ReconstructionR33m.basis (L := L) hκ n) G (gensym p.2 p.1)).reverse.prod‖
        ≤ K * (n : ℝ)⁻¹ := by
    filter_upwards [hAB] with n hn
    have e : (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint
        - ∑ i ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff i) •
            ((monomialWord i).map fun p => BalancedWickDefinition.quantization
              (ReconstructionR33m.basis (L := L) hκ n) G (gensym p.2 p.1)).reverse.prod
        = (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f
            - ∑ i ∈ f.coeff.support, f.coeff i •
              orderedWord (ReconstructionR33m.basis (L := L) hκ n) G (monomialWord i)).adjoint := by
      rw [adjoint_sub_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [orderedWord_adjoint (N := 1 + n) (by omega)]
    rw [e, norm_adjoint_eq]
    exact hn
  have hbd : ∀ᶠ n : ℕ in atTop, ∀ u ∈ (Set.univ : Set Unit), ∀ t ∈ TimeBox R lo hi,
      ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun n _ _ t _ => (dyn_prep_norm hκ hψ R n t).le
  have key := hasUniformPairT_of_sum_opClose (H := fun n => HN L (1 + n)) f.coeff.support
    (fun i n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) G (monomialWord i))
    (fun i n => ((monomialWord i).map fun p => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G (gensym p.2 p.1)).reverse.prod)
    f.coeff
    (fun i (_ : Unit) (t : ℕ → ℝ) =>
      evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym (monomialWord i)))
    (A := fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f)
    (A' := fun n => (BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint)
    (S := (Set.univ : Set Unit)) (Tb := TimeBox R lo hi)
    (ψ := fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
    hK0 hAB hAB' hbd (fun i _ => dyn_word_pair hκ F G D u hu R lo hi ψ hψ (monomialWord i))
  have hfun : (fun (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f)
      = (fun (_ : Unit) (t : ℕ → ℝ) => ∑ i ∈ f.coeff.support, f.coeff i *
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym (monomialWord i))) := by
    funext _ t
    exact evalSym_eq_sum_words _ hf
  rw [hfun]
  exact key

/-- **Scaled Dirac commutator (dynamic).** `-iN[W^G_N(f), W^G_N(h)]` has along the trajectory the uniform
strong symbol `{f,h}(w(u,t))`, the symbol of the bracket polynomial `pb S f h`. -/
theorem dyn_dirac (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {f h : Sym} (hf : Balanced f)
    (hh : Balanced h) {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSh : labelsOf h ⊆ S) :
    HasUniformStrongT (H := fun n => HN L (1 + n))
      (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f
          * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h
          - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h
          * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (pb S f h)) := by
  have hB := (dyn_poly_pair hκ F G D u hu R lo hi ψ hψ (balanced_pb S hf hh)).1
  refine hasUniformStrongT_of_opClose (K := |Cfg f h + Cfg h f|) (M := 1) (abs_nonneg _) ?_ ?_ hB
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := FullWickH1.quantization_Dirac_bound (N := 1 + n) (by omega)
      (ReconstructionR33m.basis (L := L) hκ n) G hf hh hSf hSh
    refine h1.trans ?_
    refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
    apply inv_anti₀ (by exact_mod_cast (show 0 < n from hn))
    push_cast
    linarith
  · exact Filter.Eventually.of_forall fun n _ _ t _ => (dyn_prep_norm hκ hψ R n t).le

end Dynamic

end QuantumNLS.FullWickH9

#print axioms QuantumNLS.FullWickH9.dyn_U_norm_eq
#print axioms QuantumNLS.FullWickH9.dyn_prep_norm
#print axioms QuantumNLS.FullWickH9.dyn_gen_good
#print axioms QuantumNLS.FullWickH9.dyn_word_pair
#print axioms QuantumNLS.FullWickH9.dyn_poly_pair
#print axioms QuantumNLS.FullWickH9.dyn_dirac

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickH9." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH9." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (name.toString.splitOn "RB7BindFinal").length > 1 ||
          (name.toString.splitOn "DEF033_package").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate then
        throwError "Excluded dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"FullWickH9 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
