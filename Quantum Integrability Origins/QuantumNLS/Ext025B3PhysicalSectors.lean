import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.OccupationHilbert
import QuantumNLS.Ext025BSectors

/-! C06: the actual Hilbert direct sum of the physical bosonic sectors,
its separating orthogonal projections, and maximal direct sums of the actual
finite transfer traces. No uniform-in-sector bound is imposed. The unbounded
spectral-function closure for arbitrary reducing normal operators remains a
separate obligation. Author sol_ext_b, Round 3. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext025B3PhysicalSectors
open BetheCoefficientTransform
variable (L : ℝ) [Fact (0 < L)]

/-- Full physical bosonic Fock Hilbert space, including the vacuum. -/
abbrev Fock := lp (fun N : ℕ => HN L N) 2

/-- The canonical isometric inclusion of an entire physical particle sector. -/
def inclusion (N : ℕ) : HN L N →ₗᵢ[ℂ] Fock L where
  __ := lp.lsingle (𝕜 := ℂ) 2 N
  norm_map' x := lp.norm_single (by norm_num) N x

/-- The bounded orthogonal particle-number projection. -/
def projection (N : ℕ) : Fock L →L[ℂ] Fock L :=
  (inclusion L N).toContinuousLinearMap ∘L lp.evalCLM (E := fun N => HN L N) (p := 2) ℂ N

theorem projection_eq_single (N : ℕ) (x : Fock L) :
    projection L N x = lp.single 2 N (x N) := rfl

@[simp] theorem projection_same (N : ℕ) (x : Fock L) :
    projection L N x N = x N := by
  simp [projection_eq_single, lp.single_apply]

@[simp] theorem projection_other (N M : ℕ) (h : M ≠ N) (x : Fock L) :
    projection L N x M = 0 := by
  simp [projection_eq_single, lp.single_apply, h]

theorem projection_norm_le (N : ℕ) (x : Fock L) : ‖projection L N x‖ ≤ ‖x‖ := by
  rw [projection_eq_single, lp.norm_single (by norm_num)]
  exact lp.norm_apply_le_norm (by norm_num) x N

@[simp] theorem projection_idempotent (N : ℕ) (x : Fock L) :
    projection L N (projection L N x) = projection L N x := by
  rw [projection_eq_single, projection_same, ← projection_eq_single]

theorem projection_orthogonal (N M : ℕ) (h : M ≠ N) (x : Fock L) :
    projection L M (projection L N x) = 0 := by
  rw [projection_eq_single, projection_other L N M h, lp.single_zero]

theorem projection_selfadjoint (N : ℕ) :
    (projection L N).adjoint = projection L N := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, projection_eq_single,
    projection_eq_single, lp.inner_single_left, lp.inner_single_right]

/-- The sector family separates every vector of the completed direct sum. -/
theorem projection_separates (x : Fock L) (h : ∀ N, projection L N x = 0) : x = 0 := by
  ext N
  have he := congrArg (fun v : Fock L => v N) (h N)
  simpa using he

/-- The full direct-sum decomposition converges in Hilbert norm. -/
theorem projection_hasSum (x : Fock L) : HasSum (fun N => projection L N x) x :=
  by simpa only [projection_eq_single] using lp.hasSum_single (by norm_num) x

variable {L}

/-- Maximal domain of the direct sum of bounded sector operators. Norms may
increase arbitrarily with particle number. -/
def blockDomain (A : ∀ N, HN L N →L[ℂ] HN L N) : Submodule ℂ (Fock L) where
  carrier := {x | Memℓp (fun N => A N (x N)) 2}
  zero_mem' := by
    change Memℓp (fun N => A N 0) 2
    convert (zero_memℓp : Memℓp (0 : ∀ N, HN L N) 2) using 1
    funext N
    exact map_zero (A N)
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun N => A N ((x+y) N)) 2
    convert hx.add hy using 1
    funext N
    change A N (x N + y N) = A N (x N) + A N (y N)
    exact map_add _ _ _
  smul_mem' := by
    intro c x hx
    change Memℓp (fun N => A N ((c • x) N)) 2
    convert hx.const_smul c using 1
    funext N
    change A N (c • x N) = c • A N (x N)
    exact map_smul _ _ _

/-- An actual partial linear operator on the completed physical Fock space. -/
def block (A : ∀ N, HN L N →L[ℂ] HN L N) : Fock L →ₗ.[ℂ] Fock L where
  domain := blockDomain A
  toFun :=
    { toFun := fun x => ⟨fun N => A N (x.val N), x.property⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext N
        change A N (x.val N + y.val N) = A N (x.val N) + A N (y.val N)
        exact map_add _ _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext N
        change A N (c • x.val N) = c • A N (x.val N)
        exact map_smul _ _ _ }

@[simp] theorem block_apply (A : ∀ N, HN L N →L[ℂ] HN L N)
    (x : (block A).domain) (N : ℕ) : block A x N = A N (x.val N) := rfl

/-- Every entire homogeneous sector is in the maximal direct-sum domain. -/
theorem projection_mem_blockDomain (A : ∀ N, HN L N →L[ℂ] HN L N)
    (N : ℕ) (x : Fock L) : projection L N x ∈ (block A).domain := by
  change Memℓp (fun M => A M (projection L N x M)) 2
  have he : (fun M => A M (projection L N x M)) = Pi.single N (A N (x N)) := by
    funext M
    by_cases h : M = N
    · subst M; simp
    · simp [projection_other L N M h, Pi.single_eq_of_ne h]
  rw [he]
  exact lp.memℓp (lp.single 2 N (A N (x N)))

/-- Exact domain invariance and commutation; no boundedness of the whole
Fock operator is assumed. -/
theorem block_commutes (A : ∀ N, HN L N →L[ℂ] HN L N)
    (N : ℕ) (x : (block A).domain) :
    block A ⟨projection L N x, projection_mem_blockDomain A N x⟩ =
      projection L N (block A x) := by
  ext M
  by_cases h : M = N
  · subst M; simp
  · simp [projection_other L N M h]

/-- Actual finite physical transfer traces on every sector, including N=0. -/
def transferFamily (c : ℝ) (z : ℂ) (N : ℕ) : HN L N →L[ℂ] HN L N :=
  BethePhysicalTransfer.transfer L N c z

def transfer (c : ℝ) (z : ℂ) : Fock L →ₗ.[ℂ] Fock L := block (transferFamily (L := L) c z)

/-- The source transfer generator, on its full maximal direct-sum domain. -/
theorem «FIN-EXT025-C06-transfer» (c : ℝ) (z : ℂ) (N : ℕ)
    (x : (transfer (L := L) c z).domain) :
    transfer (L := L) c z ⟨projection L N x, projection_mem_blockDomain (transferFamily (L := L) c z) N x⟩ =
      projection L N (transfer (L := L) c z x) := block_commutes _ N x

/-- The number operator is the maximal direct sum of N times identity. -/
def numberFamily (N : ℕ) : HN L N →L[ℂ] HN L N :=
  (N : ℂ) • ContinuousLinearMap.id ℂ (HN L N)

def number : Fock L →ₗ.[ℂ] Fock L := block (numberFamily (L := L))

theorem «FIN-EXT025-C06-number» (N : ℕ) (x : (number (L := L)).domain) :
    number (L := L) ⟨projection L N x, projection_mem_blockDomain (numberFamily (L := L)) N x⟩ =
      projection L N (number (L := L) x) := block_commutes _ N x


/-- UBB1's accepted interacting physical basis on every positive sector;
the vacuum uses the canonical Fourier occupation basis. -/
def physicalBasis (c : ℝ) (hc : 0 < c) (N : ℕ) : BetheBasis L N :=
  if hN : 1 ≤ N then UnconditionalBetheBasis.physicalBasis L N hN c hc
  else BetheCoefficientTransform.freeBasis L N

theorem physicalBasis_eq (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    physicalBasis (L := L) c hc N = UnconditionalBetheBasis.physicalBasis L N hN c hc := by
  simp only [physicalBasis, dite_eq_left hN]

/-- The literal integer occupation multiplier on all arrays of total N. -/
def countCoefficients (N : ℕ) (j : ℤ) :
    OccupationHilbert.L2 (BetheLabels.MArr N) →L[ℂ] OccupationHilbert.L2 (BetheLabels.MArr N) :=
  OccupationHilbert.diagonal (fun m => (m.val j : ℂ)) (N : ℝ) (Nat.cast_nonneg N)
    (fun m => by
      have hm : Occupation.total m.val = N := m.property
      have hh := Occupation.occ_le_total j m.val
      rw [hm] at hh
      simpa only [Complex.norm_natCast] using (Nat.cast_le (α := ℝ)).mpr hh)

/-- Integer counts in the accepted physical interacting basis. -/
def countFamily (c : ℝ) (hc : 0 < c) (j : ℤ) (N : ℕ) : HN L N →L[ℂ] HN L N :=
  (physicalBasis (L := L) c hc N).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    countCoefficients N j ∘L
      (physicalBasis (L := L) c hc N).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- The coordinate count is exactly m_j, without the normalized 1/N factor. -/
theorem countFamily_coord (c : ℝ) (hc : 0 < c) (j : ℤ) (N : ℕ)
    (x : HN L N) (m : BetheLabels.MArr N) :
    (physicalBasis (L := L) c hc N).repr (countFamily c hc j N x) m =
      (m.val j : ℂ) * (physicalBasis (L := L) c hc N).repr x m := by
  change (physicalBasis (L := L) c hc N).repr
    ((physicalBasis (L := L) c hc N).repr.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

def integerCount (c : ℝ) (hc : 0 < c) (j : ℤ) : Fock L →ₗ.[ℂ] Fock L :=
  block (countFamily (L := L) c hc j)

/-- Counts preserve the full maximal domain and commute with every P_N. -/
theorem «FIN-EXT025-C06-integer-count» (c : ℝ) (hc : 0 < c) (j : ℤ) (N : ℕ)
    (x : (integerCount (L := L) c hc j).domain) :
    integerCount (L := L) c hc j
      ⟨projection L N x, projection_mem_blockDomain (countFamily (L := L) c hc j) N x⟩ =
        projection L N (integerCount (L := L) c hc j x) := block_commutes _ N x

/-- C06's zero obstruction, now with the actual separating physical projections. -/
theorem «FIN-EXT025-C06-physical-obstruction» (D : Submodule ℂ (Fock L))
    (hD : ∀ N (x : D), projection L N x ∈ D) (T : D →ₗ[ℂ] Fock L)
    (hpres : ∀ N (x : D), T ⟨projection L N x, hD N x⟩ = projection L N (T x))
    (hv : ∀ x : D, T ⟨projection L 0 x, hD 0 x⟩ = 0)
    (hlow : ∀ N (x : D), projection L N (T ⟨projection L (N+1) x, hD (N+1) x⟩) =
      T ⟨projection L (N+1) x, hD (N+1) x⟩) : ∀ x, T x = 0 :=
  Ext025BSectors.«FIN-EXT025-C06-obstruction» D (projection L) hD
    (projection_idempotent L) (fun N x => projection_orthogonal L N (N+1) (by omega) x)
    (projection_separates L) T hpres hv hlow

/-- Sums inherit the same actual sector commutation on a common invariant domain. -/
theorem sum_commutes (D : Submodule ℂ (Fock L))
    (hD : ∀ N (x : D), projection L N x ∈ D) (S T : D →ₗ[ℂ] Fock L)
    (hS : ∀ N (x : D), S ⟨projection L N x, hD N x⟩ = projection L N (S x))
    (hT : ∀ N (x : D), T ⟨projection L N x, hD N x⟩ = projection L N (T x))
    (N : ℕ) (x : D) :
    (S+T) ⟨projection L N x, hD N x⟩ = projection L N ((S+T) x) := by
  simp only [LinearMap.add_apply, hS, hT, map_add]

/-- Products on a common invariant domain preserve the same sectors. -/
theorem product_commutes (D : Submodule ℂ (Fock L))
    (hD : ∀ N (x : D), projection L N x ∈ D) (S T : D →ₗ[ℂ] D)
    (hS : ∀ N (x : D), (S ⟨projection L N x, hD N x⟩ : Fock L) =
      projection L N (S x))
    (hT : ∀ N (x : D), (T ⟨projection L N x, hD N x⟩ : Fock L) =
      projection L N (T x)) (N : ℕ) (x : D) :
    (S (T ⟨projection L N x, hD N x⟩) : Fock L) = projection L N (S (T x)) := by
  have he : T ⟨projection L N x, hD N x⟩ = ⟨projection L N (T x), hD N (T x)⟩ :=
    Subtype.ext (hT N x)
  rw [he]
  exact hS N (T x)

/-- Actual physical projections pass through common-domain strong limits. -/
theorem «FIN-EXT025-C06-physical-strong-limit» (D : Submodule ℂ (Fock L))
    (hD : ∀ N (x : D), projection L N x ∈ D) (Tj : ℕ → D → Fock L) (T : D → Fock L)
    (hj : ∀ j N (x : D), Tj j ⟨projection L N x, hD N x⟩ = projection L N (Tj j x))
    (hlim : ∀ x, Tendsto (fun j => Tj j x) atTop (𝓝 (T x))) (N : ℕ) (x : D) :
    T ⟨projection L N x, hD N x⟩ = projection L N (T x) :=
  Ext025BSectors.«FIN-EXT025-C06-strong-limit» D (projection L N) (hD N) Tj T
    (fun j => hj j N) hlim x

end QuantumNLS.Ext025B3PhysicalSectors

#print axioms QuantumNLS.Ext025B3PhysicalSectors.projection_norm_le

#print axioms QuantumNLS.Ext025B3PhysicalSectors.projection_selfadjoint

#print axioms QuantumNLS.Ext025B3PhysicalSectors.projection_hasSum

#print axioms QuantumNLS.Ext025B3PhysicalSectors.block_commutes

#print axioms QuantumNLS.Ext025B3PhysicalSectors.«FIN-EXT025-C06-transfer»

#print axioms QuantumNLS.Ext025B3PhysicalSectors.«FIN-EXT025-C06-number»

#print axioms QuantumNLS.Ext025B3PhysicalSectors.«FIN-EXT025-C06-physical-obstruction»

#print axioms QuantumNLS.Ext025B3PhysicalSectors.countFamily_coord
#print axioms QuantumNLS.Ext025B3PhysicalSectors.«FIN-EXT025-C06-integer-count»

#print axioms QuantumNLS.Ext025B3PhysicalSectors.physicalBasis_eq
#print axioms QuantumNLS.Ext025B3PhysicalSectors.sum_commutes
#print axioms QuantumNLS.Ext025B3PhysicalSectors.«FIN-EXT025-C06-physical-strong-limit»

#print axioms QuantumNLS.Ext025B3PhysicalSectors.product_commutes

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B3PhysicalSectors." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B3PhysicalSectors audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
