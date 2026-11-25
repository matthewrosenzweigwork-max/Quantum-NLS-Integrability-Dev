import Mathlib
import QuantumNLS.UniformStaticR31m
import QuantumNLS.PreparationStability
import QuantumNLS.ColumnR01
import QuantumNLS.Fidelity

/-!
# UniformProjR01Bridge: the R-D2F4CE8F operators are the R-BB03032A entry operators (R-98833BEE)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), proof of `thm:uniform-projective`, line 384:
"For each fixed pair, Theorem `thm:uniform-static` bounds the entry error in `eq:density-entry`, uniformly on the
class, by its Cartesian strong residual."

The R-D2F4CE8F input (`UniformStaticR31m.UniformStatic`) is stated with the full gauge `q : ∀ n, Arr (n+1) → Phase`
(particle number `n+1`), the transfer `E^q = C⁻¹ (D_q^* E D_q) C` (`sectorEq`, `C` the occupation coefficients of
the accepted UBB1 basis at coupling `κ/N`).  The accepted R-BB03032A/R-93D28FE1 density
`PreparationStability.density b g` uses a DEF-029 gauge `g : Gauge` with gauged coordinates
`coordinates b g ψ (m) = \bar g(m) ⟨Ψ_m, ψ⟩` (Terra qualification "qPhase = conj g").  The source's single gauge
`q_N(m)` (`d_m = q_N(m) g_m`) is therefore `g = \bar q`: `fullToGauge q (n+1) m = \overline{q n m}`.

* `conj_sectorEq_eq_physical`: for every `N`, basis `b` and sector gauge with `\bar g = q`, the R31m transfer equals the
  DEF-029 pullback `physical b g a c` (so `⟨ψ, E^q ψ⟩ = Γ_N[ψ]_{ac}`, `eq:density-entry`).
* `E_eq_physical`: the instance at the R31m operators.
* `entry_le_cartesianError`: `|Γ_N[u^{⊗N}]_{ac} - w_a(u)\overline{w_c(u)}| ≤` the R31m Cartesian residual, with the
  particle number written `1+n` (accepted density) versus `n+1` (R31m), bridged by `residual_transport`.
* `cartesianError_le_four`, `le_supMax`: the R31m supremum dominates each residual (it is a genuine bounded supremum).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.UniformProjR01Bridge

open QuantumNLS.Occupation (Arr Occ UnitGauge)
open QuantumNLS.OccupationHilbert (gauge gauge_apply extendSectorGauge extendSectorGauge_apply
  extendSectorGauge_unit sectorEq)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN occupationCoefficient occupationCoefficient_apply marrArr)
open QuantumNLS.BetheOccupationGauge (Gauge gaugedBasis gaugedBasis_apply)
open QuantumNLS.CartesianOccupationTransfer (coordinates physical physical_coordinates)
open QuantumNLS.AuxiliaryDensity (gammaEntry)
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)]

/-! ### General `N`: gauged coordinates and the gauge-conjugated transfer -/

theorem coordinates_eq_gauge {N : ℕ} (b : BetheBasis L N) (g : Gauge) (qq : Arr N → ℂ)
    (hq : UnitGauge (extendSectorGauge N qq))
    (hg : ∀ m : MArr N, conj ((g N m).val) = qq (marrArr N m)) (φ : HN L N) :
    coordinates b g φ = gauge N (extendSectorGauge N qq) hq (occupationCoefficient b φ) := by
  apply lp.ext
  funext m
  obtain ⟨m', rfl⟩ := (marrArr N).surjective m
  rw [gauge_apply, extendSectorGauge_apply, occupationCoefficient_apply]
  change occupationCoefficient (gaugedBasis b g) φ (marrArr N m') = _
  rw [occupationCoefficient_apply, gaugedBasis_apply, inner_smul_left, hg]

theorem gauge_gauge_conj (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q)
    (hq' : UnitGauge (fun m => conj (q m))) (y : OccupationHilbert.H N) :
    gauge N q hq (gauge N (fun m => conj (q m)) hq' y) = y := by
  apply lp.ext
  funext m
  rw [gauge_apply, gauge_apply, ← mul_assoc, Occupation.unit_mul_conj hq m.1, one_mul]

/-- **The R31m transfer is the DEF-029 pullback** `E^q = J^* E J` of the accepted R-BB03032A density, for every `N`,
basis `b`, and sector gauge `qq` with `\overline{g} = qq`. -/
theorem conj_sectorEq_eq_physical {N : ℕ} (b : BetheBasis L N) (g : Gauge) (qq : Arr N → ℂ)
    (hq : ∀ m, Complex.normSq (qq m) = 1)
    (hg : ∀ m : MArr N, conj ((g N m).val) = qq (marrArr N m)) (a c : ℤ) :
    (occupationCoefficient b).conjStarAlgEquiv.symm (sectorEq N qq hq a c) = physical b g a c := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  rw [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply]
  apply (coordinates b g).injective
  rw [physical_coordinates, coordinates_eq_gauge b g qq (extendSectorGauge_unit N qq hq) hg,
    LinearIsometryEquiv.apply_symm_apply,
    coordinates_eq_gauge b g qq (extendSectorGauge_unit N qq hq) hg ψ]
  simp only [sectorEq, OccupationHilbert.Eq, mul_apply_eq_comp]
  exact gauge_gauge_conj N _ _ _ _

/-! ### The R-D2F4CE8F full gauge as a DEF-029 gauge -/

/-- `g = \bar q` on the sector `N = n+1` (and phase one on the empty sector, which never occurs). -/
def fullToGauge (q : UniformStaticR31m.FullGauge) : Gauge := fun N =>
  match N with
  | 0 => fun _ => ⟨1, norm_one⟩
  | n + 1 => fun m => ⟨conj (q n (marrArr (n + 1) m)).1, by rw [Complex.norm_conj]; exact (q n _).2⟩

theorem fullToGauge_conj (q : UniformStaticR31m.FullGauge) (n : ℕ) (m : MArr (n + 1)) :
    conj ((fullToGauge q (n + 1) m).val) = (q n (marrArr (n + 1) m)).1 := by
  change conj (conj (q n (marrArr (n + 1) m)).1) = _
  rw [Complex.conj_conj]

/-- The R31m operator `E^q_{N,ab}` (`N = n+1`) is the DEF-029 pullback for the gauge `fullToGauge q`. -/
theorem E_eq_physical {κ : ℝ} (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ) (p : ℤ × ℤ) :
    UniformStaticR31m.E (L := L) hκ q n p =
      physical (UnconditionalBetheBasis.meanField_physicalBasis L (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) hκ) (fullToGauge q) p.1 p.2 := by
  unfold UniformStaticR31m.E UniformStaticR31m.cartesian UniformStaticR31m.coefficientMap
  exact conj_sectorEq_eq_physical _ _ _ _ (fun m => fullToGauge_conj q n m) p.1 p.2

/-! ### Entry bounds -/

theorem norm_wvec {N : ℕ} (u : L2T L) (hu : ‖u‖ = 1) :
    ‖(HighMomentsOps.wvec N u : HN L N)‖ = 1 := by
  rw [← Submodule.norm_coe]
  show ‖(TensorCarrier.htpow N u : TensorCarrier.HilbertTensorPower ℂ (L2T L) N)‖ = 1
  rw [TensorCarrier.norm_htpow, hu, one_pow]

theorem norm_gammaEntry_sub_le {N : ℕ} (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (hψ : ‖ψ‖ = 1)
    (a c : ℤ) (z : ℂ) : ‖gammaEntry b g ψ a c - z‖ ≤ ‖physical b g a c ψ - z • ψ‖ := by
  have e : gammaEntry b g ψ a c - z = ⟪ψ, physical b g a c ψ - z • ψ⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp [gammaEntry]
  rw [e]
  calc _ ≤ ‖ψ‖ * ‖physical b g a c ψ - z • ψ‖ := norm_inner_le_norm _ _
    _ = _ := by rw [hψ, one_mul]

/-- Particle number `1+n` (accepted density) versus `n+1` (R31m): the same residual. -/
theorem residual_transport {κ : ℝ} (hκ : 0 < κ) (g : Gauge) (u : L2T L) (a c : ℤ) (z : ℂ) (n : ℕ) :
    ‖physical (ColumnR01.basis (L := L) hκ n) g a c (HighMomentsOps.wvec (1 + n) u) -
        z • (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))‖ =
      ‖physical (UnconditionalBetheBasis.meanField_physicalBasis L (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) hκ) g a c (HighMomentsOps.wvec (n + 1) u) -
        z • (HighMomentsOps.wvec (n + 1) u : HN L (n + 1))‖ := by
  have key : ∀ (N M : ℕ) (h : N = M) (hN : 1 ≤ N) (hM : 1 ≤ M),
      ‖physical (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g a c
          (HighMomentsOps.wvec N u) - z • (HighMomentsOps.wvec N u : HN L N)‖ =
        ‖physical (UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) g a c
          (HighMomentsOps.wvec M u) - z • (HighMomentsOps.wvec M u : HN L M)‖ := by
    intro N M h hN hM
    subst h
    rfl
  exact key _ _ (Nat.add_comm 1 n) _ _

theorem ev_eq_oneBasis (a : ℤ) : Fidelity.ev a = oneBasis a := by
  rw [OccupationUnitary.oneBasis_apply]
  rfl

/-- **The entry error is bounded by the Cartesian strong residual** (`eq:density-entry` and Cauchy-Schwarz):
`|Γ_N[u^{⊗N}]_{ac} - w_a(u)\overline{w_c(u)}| ≤ ‖(E^q_{N,ac} - c_{ac}(u))u^{⊗N}‖ + ‖((E^q_{N,ac})^* - \bar c_{ac}(u))u^{⊗N}‖`. -/
theorem entry_le_cartesianError {κ : ℝ} (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ)
    (u : L2T L) (hu : ‖u‖ = 1) (a c : ℤ) :
    ‖Fidelity.entry (PreparationStability.density (ColumnR01.basis (L := L) hκ n) (fullToGauge q)
        (HighMomentsOps.wvec (1 + n) u)) a c -
      (Def021ChartR41b.chart L κ hκ).Φ u a * conj ((Def021ChartR41b.chart L κ hκ).Φ u c)‖ ≤
      UniformStaticR31m.cartesianError hκ q n u (a, c) := by
  have h1 : Fidelity.entry (PreparationStability.density (ColumnR01.basis (L := L) hκ n) (fullToGauge q)
      (HighMomentsOps.wvec (1 + n) u)) a c =
      gammaEntry (ColumnR01.basis (L := L) hκ n) (fullToGauge q) (HighMomentsOps.wvec (1 + n) u) a c := by
    rw [Fidelity.entry, ev_eq_oneBasis, ev_eq_oneBasis]
    exact PreparationStability.density_entry _ _ _ a c
  rw [h1]
  refine (norm_gammaEntry_sub_le _ _ _ (norm_wvec u hu) a c _).trans ?_
  rw [residual_transport hκ (fullToGauge q) u a c _ n]
  have h2 : ‖physical (UnconditionalBetheBasis.meanField_physicalBasis L (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) hκ) (fullToGauge q) a c (HighMomentsOps.wvec (n + 1) u) -
        ((Def021ChartR41b.chart L κ hκ).Φ u a * conj ((Def021ChartR41b.chart L κ hκ).Φ u c)) •
          (HighMomentsOps.wvec (n + 1) u : HN L (n + 1))‖ =
      UniformStaticR31m.residual (UniformStaticR31m.E hκ q n (a, c))
        (UniformStaticR31m.symbol hκ u (a, c)) (UniformStaticR31m.product n u) := by
    rw [UniformStaticR31m.residual_apply, E_eq_physical]
    rfl
  rw [h2, UniformStaticR31m.cartesianError]
  exact le_add_of_nonneg_right (norm_nonneg _)

/-! ### The R31m supremum is a genuine bounded supremum -/

theorem norm_physical_le {N : ℕ} (b : BetheBasis L N) (g : Gauge) (a c : ℤ) : ‖physical b g a c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => ?_
  calc ‖physical b g a c ψ‖ = ‖coordinates b g (physical b g a c ψ)‖ := ((coordinates b g).norm_map _).symm
    _ = ‖OccupationHilbert.E N a c (coordinates b g ψ)‖ := by rw [physical_coordinates]
    _ ≤ ‖OccupationHilbert.E N a c‖ * ‖coordinates b g ψ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖coordinates b g ψ‖ :=
        mul_le_mul_of_nonneg_right (OccupationHilbert.E_norm_le _ _ _) (norm_nonneg _)
    _ = 1 * ‖ψ‖ := by rw [(coordinates b g).norm_map]

theorem norm_chart_apply_le {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (a : ℤ) :
    ‖(Def021ChartR41b.chart L κ hκ).Φ u a‖ ≤ 1 := by
  have hn : ‖(Def021ChartR41b.chart L κ hκ).Φ u‖ = 1 := by
    have h := (Def021ChartR41b.chart L κ hκ).norm u
    rw [hu, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  exact (lp.norm_apply_le_norm (by norm_num) _ a).trans hn.le

theorem residual_le_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (hA : ‖A‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) (v : V) (hv : ‖v‖ = 1) :
    UniformStaticR31m.residual A z v ≤ 2 := by
  rw [UniformStaticR31m.residual_apply]
  calc ‖A v - z • v‖ ≤ ‖A v‖ + ‖z • v‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖v‖ + ‖z‖ * ‖v‖ := add_le_add (A.le_opNorm v) (norm_smul_le _ _)
    _ ≤ 1 * 1 + 1 * 1 := by rw [hv]; gcongr
    _ = 2 := by norm_num

theorem cartesianError_le_four {κ : ℝ} (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ)
    (u : L2T L) (hu : ‖u‖ = 1) (p : ℤ × ℤ) : UniformStaticR31m.cartesianError hκ q n u p ≤ 4 := by
  have hE : ‖UniformStaticR31m.E (L := L) hκ q n p‖ ≤ 1 := by
    rw [E_eq_physical]; exact norm_physical_le _ _ _ _
  have hEa : ‖(UniformStaticR31m.E (L := L) hκ q n p).adjoint‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact hE
  have hz : ‖UniformStaticR31m.symbol hκ u p‖ ≤ 1 := by
    rw [UniformStaticR31m.symbol, norm_mul, Complex.norm_conj]
    have h1 := norm_chart_apply_le hκ u hu p.1
    have h2 := norm_chart_apply_le hκ u hu p.2
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hz' : ‖conj (UniformStaticR31m.symbol hκ u p)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hz
  have hv : ‖(UniformStaticR31m.product n u : HN L (n + 1))‖ = 1 := norm_wvec u hu
  have h1 := residual_le_two _ hE _ hz _ hv
  have h2 := residual_le_two _ hEa _ hz' _ hv
  rw [UniformStaticR31m.cartesianError]
  linarith

/-- Every member of a uniformly bounded family is dominated by `supMax`. -/
theorem le_supMax {X P : Type*} (S : Set X) (test : X → Finset P) (error : X → P → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ u ∈ S, ∀ p ∈ test u, error u p ≤ B) {u : X} (hu : u ∈ S) {p : P}
    (hp : p ∈ test u) : error u p ≤ UniformStaticR31m.supMax S test error := by
  have h1 : error u p ≤ UniformStaticR31m.maxWithZero (test u) (error u) :=
    Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
  refine h1.trans (le_csSup ⟨B, ?_⟩ (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩))
  rintro x hx
  rcases Set.mem_insert_iff.1 hx with rfl | ⟨v, hv, rfl⟩
  · exact hB0
  · exact UniformStaticR31m.maxWithZero_le _ _ hB0 (hB v hv)

theorem supMax_nonneg {X P : Type*} (S : Set X) (test : X → Finset P) (error : X → P → ℝ) :
    0 ≤ UniformStaticR31m.supMax S test error := by
  refine Real.sSup_nonneg fun x hx => ?_
  rcases Set.mem_insert_iff.1 hx with rfl | ⟨v, -, rfl⟩
  · exact le_rfl
  · exact UniformStaticR31m.maxWithZero_nonneg _ _

end QuantumNLS.UniformProjR01Bridge

#print axioms QuantumNLS.UniformProjR01Bridge.conj_sectorEq_eq_physical
#print axioms QuantumNLS.UniformProjR01Bridge.E_eq_physical
#print axioms QuantumNLS.UniformProjR01Bridge.entry_le_cartesianError
#print axioms QuantumNLS.UniformProjR01Bridge.cartesianError_le_four
#print axioms QuantumNLS.UniformProjR01Bridge.le_supMax

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.UniformProjR01Bridge." ||
        n.toString.startsWith "_private.QuantumNLS.UniformProjR01Bridge." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"UniformProjR01Bridge aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
