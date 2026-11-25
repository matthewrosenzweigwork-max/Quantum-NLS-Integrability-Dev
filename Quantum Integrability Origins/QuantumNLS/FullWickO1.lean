import QuantumNLS.BalancedWickDefinition
import QuantumNLS.ReconstructionInputsR33m
import QuantumNLS.UniformStaticBridgeR50b

/-! FullWickO1 (opus_tensor, R-140AE34B `thm:full-wick`, Stage 3 item 2: gauge conjugation).

Source: `source-text/chapters/core/wick_calculus.tex:28-31`
  "Equation~\eqref{eq:gauge-conjugation} gives $\mathcal W_N^q(c_{ab})=E^q_{N,ab}$, and
   $\mathcal W_N^q(\overline f)=\mathcal W_N^q(f)^*$."
with `eq:gauge-conjugation` printed at `projective_reconstruction.tex:19-21`:
  `J_N E^q_{N,ab} J_N^* = N^{-1} b_b^* b_a |_{Sym^N h}`,
and `eq:full-Wick` (`wick_calculus.tex:20-24`): `W_N^q(z^α z̄^β) = J_N^* N^{-d} (b^*)^β b^α J_N`.

Lean objects.
* `W_N^q` is DEF-032 `BalancedWickDefinition.quantization b g` (and `wick b g` on a
  `BalancedWickDefinition.Polynomial`), pulled back through `J = occupationCoefficient (gaugedBasis b g)`.
* `c_{ab} = z_a z̄_b` is `WickBounds.gensym a b = zm (single a 1) (single b 1)` (α = e_a, β = e_b), so
  `N^{-1} (b^*)^β b^α = N^{-1} b_b^* b_a`.
* `E^q_{N,ab}` is `CartesianOccupationTransfer.physical b g a b = J^* (OccupationHilbert.E N a b) J`
  (the same `J`). This is the operator `ReconstructionR33m.E hκ g n a b` of the R-8362E5EB input
  (basis `ReconstructionR33m.basis hκ n`, particle number `1+n`), and, by the frozen
  `UniformStaticBridgeR50b.cartesian_eq_projective_physical`, the operator `UniformStaticR49b.E hκ q n p`
  of the R-D2F4CE8F static input (basis `Def044D1SpectralR51a.basis hκ n`, particle number `n+1`, Lean
  gauge `UniformProjR01Bridge.fullToGauge q = conj q`).
* Gauge convention: the printed `J_N ψ = Σ d_m |m⟩` with `d_m = q_N(m) g_m`; the Lean coordinates are
  `coordinates b g ψ m = conj(g m) ⟨Ψ_m, ψ⟩`, so the printed `q_N` is `conj g` (for the static input,
  `g = fullToGauge q`, i.e. printed `q_N = q`). No gauge is selected here: every statement is for an
  arbitrary DEF-025 `Gauge`.

Declarations.
* `quantization_bilinear`: `W^q_N(z_a z̄_c) = E^q_{N,ac}` for every positive `N`, Bethe basis and gauge.
* `wick_bilinearPoly`, `evaluate_bilinearPoly`: the same for the DEF-032 polynomial `z_a z̄_c`, whose
  evaluation is `z_a conj(z_c)`.
* `physical_adjoint`, `quantization_bilinear_adjoint`: `(E_{ac})^* = E_{ca}` and
  `W(z_a z̄_c)^* = W(z_c z̄_a) = W(conj(z_a z̄_c))`.
* `gauge_conjugation_RD`, `gauge_conjugation_RD_adjoint`, `gauge_conjugation_RD_fock`: the identities at the
  R-8362E5EB input objects; the last is the printed `eq:gauge-conjugation` itself
  (`J E J^* = N^{-1} b_b^* b_a` on `Sym^N h`, with `J = fockTransform (gaugedBasis b g)`).
* `gauge_conjugation_static`, `gauge_conjugation_static_adjoint`: the identities at the R-D2F4CE8F
  static input objects.

Standard axioms only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped ComplexConjugate

namespace QuantumNLS.FullWickO1

open QuantumNLS.WickSymbols (Sym zm)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheOccupationGauge (Gauge gaugedBasis)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed bilinear `c_{ab} = z_a z̄_b` (`α = e_a`, `β = e_b`). -/
abbrev bilinear (a b : ℤ) : Sym := WickBounds.gensym a b

/-- The auxiliary Wick operator of `z_a z̄_c` on a positive sector is the transfer `E_{N,ac}`. -/
theorem auxiliaryWick_bilinear {N : ℕ} (hN : 0 < N) (a c : ℤ) :
    BalancedWickDefinition.auxiliaryWick N (bilinear a c) = OccupationHilbert.E N a c := by
  rw [BalancedWickDefinition.auxiliaryWick, ite_eq_right hN.ne']
  exact WickBounds.WHil_zm_E hN a c

/-- **`W^q_N(c_{ac}) = E^q_{N,ac}`** (`wick_calculus.tex:30`): the DEF-032 quantization of the bilinear is
the gauged Cartesian transfer, for every positive `N`, every Bethe basis and every gauge. -/
theorem quantization_bilinear {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    BalancedWickDefinition.quantization b g (bilinear a c) =
      CartesianOccupationTransfer.physical b g a c := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hW := auxiliaryWick_bilinear hN a c
  simp only [BalancedWickDefinition.quantization, CartesianOccupationTransfer.physical,
    CartesianOccupationTransfer.coordinates, ContinuousLinearMap.comp_apply, hW]

/-- The DEF-032 polynomial `z_a z̄_c` (coordinates `{a, c}`, degree bound one). -/
def bilinearPoly (a c : ℤ) : BalancedWickDefinition.Polynomial where
  coordinates := {a, c}
  degreeBound := 1
  symbol := bilinear a c
  balanced := WickBounds.balanced_zm_ab a c
  labels := by
    intro p hp
    have hp' : p = (Finsupp.single a 1, Finsupp.single c 1) := by
      simpa [bilinear, WickBounds.gensym, zm] using hp
    subst hp'
    exact ⟨(Finsupp.support_single_subset).trans
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_self a {c})),
      (Finsupp.support_single_subset).trans
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self c)))⟩
  degree := by
    intro p hp
    have hp' : p = (Finsupp.single a 1, Finsupp.single c 1) := by
      simpa [bilinear, WickBounds.gensym, zm] using hp
    subst hp'
    simp [Finsupp.degree_single]

theorem wick_bilinearPoly {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    BalancedWickDefinition.wick b g (bilinearPoly a c) =
      CartesianOccupationTransfer.physical b g a c :=
  quantization_bilinear hN b g a c

/-- The symbol of `bilinearPoly a c` is `z_a conj(z_c)`. -/
theorem evaluate_bilinearPoly (a c : ℤ) (z : ℤ → ℂ) :
    BalancedWickDefinition.evaluate (bilinearPoly a c) z = z a * conj (z c) := by
  simp [BalancedWickDefinition.evaluate, bilinearPoly, bilinear, WickBounds.gensym, zm,
    AddMonoidAlgebra.coeff_single, Finsupp.prod_single_index]

/-- The Cartesian pullback is the R48b conjugation by the gauged coefficient unitary. -/
theorem physical_eq_retarget {N : ℕ} (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    CartesianOccupationTransfer.physical b g a c =
      RetargetPhysicalR48b.physical (gaugedBasis b g) (OccupationHilbert.E N a c) := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  rfl

/-- `(E^q_{N,ac})^* = E^q_{N,ca}`. -/
theorem physical_adjoint {N : ℕ} (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    (CartesianOccupationTransfer.physical b g a c).adjoint =
      CartesianOccupationTransfer.physical b g c a := by
  rw [physical_eq_retarget, physical_eq_retarget, RetargetPhysicalR48b.physical_adjoint,
    OccupationHilbert.E_adjoint]

/-- `W^q_N(z_a z̄_c)^* = W^q_N(z_c z̄_a)`, the printed `W(f̄) = W(f)^*` for the bilinear
(`conj(z_a z̄_c) = z_c z̄_a`). -/
theorem quantization_bilinear_adjoint {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (g : Gauge)
    (a c : ℤ) :
    (BalancedWickDefinition.quantization b g (bilinear a c)).adjoint =
      BalancedWickDefinition.quantization b g (bilinear c a) := by
  rw [quantization_bilinear hN, quantization_bilinear hN, physical_adjoint]

/-! ### At the R-8362E5EB input objects (`ReconstructionR33m`, particle number `1+n`) -/

/-- **Gauge conjugation at the R-8362E5EB objects**: `W^q_N(z_a z̄_b) = E^q_{N,ab}` with
`E = ReconstructionR33m.E hκ g n a b` and `N = 1+n`. -/
theorem gauge_conjugation_RD (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :
    BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g (bilinear a b) =
      ReconstructionR33m.E (L := L) hκ g n a b :=
  quantization_bilinear (by omega) _ g a b

theorem gauge_conjugation_RD_adjoint (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :
    (ReconstructionR33m.E (L := L) hκ g n a b).adjoint =
      BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g (bilinear b a) := by
  rw [gauge_conjugation_RD, ReconstructionR33m.E, physical_adjoint]

/-- The printed `eq:gauge-conjugation` at the R-8362E5EB objects: with
`J_N = fockTransform (gaugedBasis b g) : HN L N ≃ Sym^N h`,
`J_N E^q_{N,ab} = (N^{-1} b_b^* b_a) J_N` on the whole sector, where
`CartesianOccupationTransfer.auxiliary n a b = OccupationConjugacy.collective n a b`. -/
theorem gauge_conjugation_RD_fock (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ)
    (ψ : HN L (1 + n)) :
    BetheCoefficientTransform.fockTransform (gaugedBasis (ReconstructionR33m.basis (L := L) hκ n) g)
        (ReconstructionR33m.E (L := L) hκ g n a b ψ) =
      CartesianOccupationTransfer.auxiliary n a b
        (BetheCoefficientTransform.fockTransform
          (gaugedBasis (ReconstructionR33m.basis (L := L) hκ n) g) ψ) :=
  CartesianOccupationTransfer.physical_fock n _ g a b ψ

/-! ### At the R-D2F4CE8F static input objects (`UniformStaticR49b`, particle number `n+1`) -/

/-- The Lean gauge of the static Wick quantization: `conj q` (`UniformProjR01Bridge.fullToGauge`). -/
abbrev staticGauge (q : UniformStaticR49b.SectorGauge) : Gauge :=
  UniformProjR01Bridge.fullToGauge (UniformStaticBridgeR50b.toFullGauge q)

/-- **Gauge conjugation at the static objects**: `W^q_N(z_a z̄_b) = E^q_{N,ab}` with
`E = UniformStaticR49b.E hκ q n (a, b)` and `N = n+1`. -/
theorem gauge_conjugation_static (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge) (n : ℕ)
    (p : ℤ × ℤ) :
    BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q)
        (bilinear p.1 p.2) =
      UniformStaticR49b.E (L := L) hκ q n p := by
  rw [UniformStaticBridgeR50b.cartesian_eq_projective_physical]
  exact quantization_bilinear (Nat.succ_pos n) _ _ p.1 p.2

theorem gauge_conjugation_static_adjoint (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge)
    (n : ℕ) (p : ℤ × ℤ) :
    (UniformStaticR49b.E (L := L) hκ q n p).adjoint =
      BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q)
        (bilinear p.2 p.1) := by
  rw [UniformStaticBridgeR50b.cartesian_eq_projective_physical, physical_adjoint,
    quantization_bilinear (Nat.succ_pos n)]

end QuantumNLS.FullWickO1

#print axioms QuantumNLS.FullWickO1.auxiliaryWick_bilinear
#print axioms QuantumNLS.FullWickO1.quantization_bilinear
#print axioms QuantumNLS.FullWickO1.bilinearPoly
#print axioms QuantumNLS.FullWickO1.wick_bilinearPoly
#print axioms QuantumNLS.FullWickO1.evaluate_bilinearPoly
#print axioms QuantumNLS.FullWickO1.physical_eq_retarget
#print axioms QuantumNLS.FullWickO1.physical_adjoint
#print axioms QuantumNLS.FullWickO1.quantization_bilinear_adjoint
#print axioms QuantumNLS.FullWickO1.gauge_conjugation_RD
#print axioms QuantumNLS.FullWickO1.gauge_conjugation_RD_adjoint
#print axioms QuantumNLS.FullWickO1.gauge_conjugation_RD_fock
#print axioms QuantumNLS.FullWickO1.gauge_conjugation_static
#print axioms QuantumNLS.FullWickO1.gauge_conjugation_static_adjoint

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickO1." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickO1." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
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
  Lean.logInfo m!"FullWickO1 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
