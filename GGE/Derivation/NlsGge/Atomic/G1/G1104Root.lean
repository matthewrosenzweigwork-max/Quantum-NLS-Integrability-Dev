import NlsGge.Atomic.G1.G1104Host
import NlsGge.Atomic.G1.G1104FD
import NlsGge.Atomic.G1.G1104Jor

/-!
# G1-104 M6: finite-length Jordan chains versus the root space

Target file `NlsGge/Atomic/G1/G1104Root.lean`, namespace `NlsGge.Atomic.G1104Root`.
Lands after `G1104Host`, `G1104FD` (M7), `G1104Jor` (M4).

For the actual realization `A = zsRealization (intervalPotential φ) bc` and `z0 : ℂ`:

* `rootSpace A z0 ≤ A.domain` and `A - z0` maps the root space to itself; the restriction is
  `rootShift A z0 : Module.End ℂ (rootSpace A z0)`;
* `rootShift` is locally nilpotent (from the descending chains of `rootVector`), so, since the
  root space is finite dimensional (M7), `rootShift ^ N = 0` as soon as `finrank ≤ N`;
* the endpoint evaluation `W ↦ W_N` is a linear equivalence from the ascending chains of length
  `N + 1` onto the root space (`opChainSpace_equiv_rootSpace_of_finrank_le`).

No hypothesis is added: the only hypothesis `hN` is the bound on `finrank` of the root space
(finite dimensionality is the landed M7 theorem).
-/

set_option autoImplicit false

open NlsGge.Atomic.Interval
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1104Jor
open NlsGge.Schur NlsGge.Atomic.LIB033

namespace NlsGge.Atomic.G1104Root
noncomputable section

section Generic

variable (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)

/-- `A - z` on the domain, as a linear map into `SourcePairL2`. -/
def shiftMap : A.domain →ₗ[ℂ] SourcePairL2 := A.toFun - z • A.domain.subtype

theorem shiftMap_apply (x : A.domain) : shiftMap A z x = A x - z • (x : SourcePairL2) := rfl

theorem rootVector_zero : rootVector A z 0 :=
  ⟨0, fun _ => 0, rfl, rfl, fun j hj => absurd hj (by omega)⟩

/-- The first element of a descending chain lies in the domain and `(A - z) v` is again a root
vector. -/
theorem rootVector_step {v : SourcePairL2} (hv : rootVector A z v) :
    ∃ hd : v ∈ A.domain, rootVector A z (A ⟨v, hd⟩ - z • v) := by
  obtain ⟨N, w, h0, hN, hstep⟩ := hv
  cases N with
  | zero =>
    have hv0 : v = 0 := by rw [← h0]; exact hN
    subst hv0
    refine ⟨A.domain.zero_mem, ?_⟩
    have hz : (⟨0, A.domain.zero_mem⟩ : A.domain) = 0 := rfl
    rw [hz, show A (0 : A.domain) = 0 from A.toFun.map_zero, smul_zero, sub_zero]
    exact rootVector_zero A z
  | succ n =>
    obtain ⟨hj, hA⟩ := hstep 0 (by omega)
    have hd : v ∈ A.domain := h0 ▸ hj
    refine ⟨hd, ?_⟩
    have hv' : (⟨v, hd⟩ : A.domain) = ⟨w 0, hj⟩ := Subtype.ext h0.symm
    rw [hv', ← h0, hA]
    exact ⟨n, fun j => w (j + 1), rfl, hN, fun j hj' => hstep (j + 1) (by omega)⟩

/-- Root vectors lie in the preimage under `A - z` of the root space. -/
theorem rootSpace_le_map_comap :
    rootSpace A z ≤
      Submodule.map A.domain.subtype (Submodule.comap (shiftMap A z) (rootSpace A z)) := by
  show Submodule.span ℂ {v | rootVector A z v} ≤ _
  refine Submodule.span_le.2 ?_
  intro v hv
  obtain ⟨hd, hr⟩ := rootVector_step A z hv
  exact ⟨⟨v, hd⟩, Submodule.subset_span hr, rfl⟩

theorem rootSpace_le_domain : rootSpace A z ≤ A.domain := by
  intro v hv
  obtain ⟨x, _, rfl⟩ := rootSpace_le_map_comap A z hv
  exact x.2

theorem shiftMap_mem_rootSpace {v : SourcePairL2} (hv : v ∈ rootSpace A z) (hd : v ∈ A.domain) :
    shiftMap A z ⟨v, hd⟩ ∈ rootSpace A z := by
  obtain ⟨x, hx, rfl⟩ := rootSpace_le_map_comap A z hv
  exact hx

/-- The restriction of `A - z` to the root space. -/
def rootShift : Module.End ℂ (rootSpace A z) :=
  ((shiftMap A z).comp (Submodule.inclusion (rootSpace_le_domain A z))).codRestrict
    (rootSpace A z) (fun x => shiftMap_mem_rootSpace A z x.2 (rootSpace_le_domain A z x.2))

theorem coe_rootShift_of_eq (y : rootSpace A z) (w : SourcePairL2) (hy : (y : SourcePairL2) = w)
    (hw : w ∈ A.domain) :
    ((rootShift A z y : rootSpace A z) : SourcePairL2) = A ⟨w, hw⟩ - z • w := by
  subst hy
  rfl

theorem rootShift_pow_succ_apply (n : ℕ) (y : rootSpace A z) :
    (rootShift A z ^ (n + 1)) y = rootShift A z ((rootShift A z ^ n) y) := by
  rw [pow_succ', Module.End.mul_apply]

/-- Along a descending chain, powers of `rootShift` follow the chain. -/
theorem rootShift_pow_chain {v : SourcePairL2} (hv : v ∈ rootSpace A z) (N : ℕ)
    (w : ℕ → SourcePairL2) (h0 : w 0 = v)
    (hstep : ∀ j : ℕ, j < N → ∃ hj : w j ∈ A.domain, A ⟨w j, hj⟩ - z • w j = w (j + 1)) :
    ∀ j, j ≤ N → (((rootShift A z ^ j) ⟨v, hv⟩ : rootSpace A z) : SourcePairL2) = w j := by
  intro j
  induction j with
  | zero => intro _; simpa using h0.symm
  | succ j ih =>
    intro hj
    have hlt : j < N := by omega
    obtain ⟨hdj, hA⟩ := hstep j hlt
    rw [rootShift_pow_succ_apply, coe_rootShift_of_eq A z _ (w j) (ih (by omega)) hdj, hA]

theorem pow_apply_eq_zero_of_le {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    {x : M} {n m : ℕ} (h : (T ^ n) x = 0) (hnm : n ≤ m) : (T ^ m) x = 0 := by
  have e : m = (m - n) + n := by omega
  rw [e, pow_add, Module.End.mul_apply, h, map_zero]

theorem rootShift_locallyNilpotent (x : rootSpace A z) : ∃ n : ℕ, (rootShift A z ^ n) x = 0 := by
  have key : ∀ v : SourcePairL2, v ∈ Submodule.span ℂ {v | rootVector A z v} →
      ∃ hv : v ∈ rootSpace A z, ∃ n : ℕ, (rootShift A z ^ n) ⟨v, hv⟩ = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∃ hv : v ∈ rootSpace A z,
      ∃ n : ℕ, (rootShift A z ^ n) ⟨v, hv⟩ = 0) ?_ ?_ ?_ ?_ hv
    · intro v hvr
      have hmem : v ∈ rootSpace A z := Submodule.subset_span hvr
      refine ⟨hmem, ?_⟩
      obtain ⟨N, w, h0, hN, hstep⟩ := hvr
      refine ⟨N, ?_⟩
      apply Subtype.ext
      rw [rootShift_pow_chain A z hmem N w h0 hstep N le_rfl, hN]
      rfl
    · exact ⟨Submodule.zero_mem _, 0, by simp⟩
    · rintro x y _ _ ⟨hx, n, hn⟩ ⟨hy, m, hm⟩
      refine ⟨Submodule.add_mem _ hx hy, n + m, ?_⟩
      have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : rootSpace A z) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add, pow_apply_eq_zero_of_le _ hn (Nat.le_add_right n m),
        pow_apply_eq_zero_of_le _ hm (Nat.le_add_left m n), add_zero]
    · rintro a x _ ⟨hx, n, hn⟩
      refine ⟨Submodule.smul_mem _ a hx, n, ?_⟩
      have e : (⟨a • x, Submodule.smul_mem _ a hx⟩ : rootSpace A z) = a • ⟨x, hx⟩ := rfl
      rw [e, map_smul, hn, smul_zero]
  obtain ⟨hv, n, hn⟩ := key x.1 x.2
  exact ⟨n, hn⟩

/-- Local nilpotence plus finite dimension gives a uniform power bound. -/
theorem rootShift_pow_eq_zero [FiniteDimensional ℂ (rootSpace A z)] (N : ℕ)
    (hN : Module.finrank ℂ (rootSpace A z) ≤ N) : rootShift A z ^ N = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, hn⟩ := rootShift_locallyNilpotent A z x
  have h2 := Module.End.ker_pow_le_ker_pow_finrank (rootShift A z) n (LinearMap.mem_ker.2 hn)
  exact pow_apply_eq_zero_of_le _ (LinearMap.mem_ker.1 h2) hN

/-- Elements of an ascending chain lie in the root space. -/
theorem chain_mem_rootSpace {m : ℕ} {V : ℕ → SourcePairL2} (hV : IsOpChain A z m V) {k : ℕ}
    (hk : k < m) : V k ∈ rootSpace A z := by
  apply Submodule.subset_span
  refine (rootVector_iff_opChain A z (V k)).2 ⟨k + 1, V, fun i hi => hV i (by omega), ?_⟩
  simp

/-- An ascending chain of length `N + 1` whose last element is `0` vanishes. -/
theorem chain_eq_zero_of_last {N : ℕ} {V : ℕ → SourcePairL2} (hV : IsOpChain A z (N + 1) V)
    (hlast : V N = 0) : ∀ k, k ≤ N → V k = 0 := by
  have key : ∀ m, m ≤ N → V (N - m) = 0 := by
    intro m
    induction m with
    | zero => intro _; simpa using hlast
    | succ m ih =>
      intro hm
      have hk0 : V (N - m) = 0 := ih (by omega)
      obtain ⟨hk, hA⟩ := hV (N - m) (by omega)
      have e : N - m = (N - (m + 1)) + 1 := by omega
      have hz : (⟨V (N - m), hk⟩ : A.domain) = 0 := Subtype.ext hk0
      have hA0 : A (0 : A.domain) = 0 := A.toFun.map_zero
      have h2 : prevSP V (N - m) = 0 := by
        rw [← hA, hz, hA0, hk0]
        simp
      rw [e] at h2
      exact h2
  intro k hk
  have := key (N - k) (by omega)
  rwa [show N - (N - k) = k by omega] at this

end Generic

/-! ### The endpoint equivalence -/

/-- Endpoint evaluation `W ↦ W_N`. -/
def endpoint (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ) :
    opChainSpace φ bc z0 (N + 1) →ₗ[ℂ]
      rootSpace (zsRealization (intervalPotential φ) bc) z0 :=
  ((LinearMap.proj (Fin.last N) :
      (Fin (N + 1) → SourcePairL2) →ₗ[ℂ] SourcePairL2).comp
    (opChainSpace φ bc z0 (N + 1)).subtype).codRestrict
    (rootSpace (zsRealization (intervalPotential φ) bc) z0)
    (fun W => by
      have hW := (mem_opChainSpace φ bc z0 (N + 1) W.1).1 W.2
      have h := chain_mem_rootSpace _ z0 hW (Nat.lt_succ_self N)
      rw [fget_of_lt W.1 (Nat.lt_succ_self N)] at h
      exact h)

theorem endpoint_apply (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (W : opChainSpace φ bc z0 (N + 1)) :
    ((endpoint φ bc z0 N W : rootSpace (zsRealization (intervalPotential φ) bc) z0) :
      SourcePairL2) = W.1 (Fin.last N) := rfl

theorem endpoint_injective (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ) :
    Function.Injective (endpoint φ bc z0 N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro W hW
  have hlast : W.1 (Fin.last N) = 0 := by
    have := congrArg (fun y : rootSpace (zsRealization (intervalPotential φ) bc) z0 =>
      (y : SourcePairL2)) hW
    simpa [endpoint_apply] using this
  have hV := (mem_opChainSpace φ bc z0 (N + 1) W.1).1 W.2
  have hlast' : fget W.1 N = 0 := by
    rw [fget_of_lt W.1 (Nat.lt_succ_self N)]
    exact hlast
  apply Subtype.ext
  funext i
  have := chain_eq_zero_of_last _ z0 hV hlast' i.1 (Nat.lt_succ_iff.1 i.2)
  rw [fget_of_lt W.1 i.2] at this
  exact this

theorem endpoint_surjective (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    [FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z0)]
    (hN : Module.finrank ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z0) ≤ N) :
    Function.Surjective (endpoint φ bc z0 N) := by
  set A := zsRealization (intervalPotential φ) bc with hA
  intro r
  have hT : rootShift A z0 ^ N = 0 := rootShift_pow_eq_zero A z0 N hN
  have hT1 : rootShift A z0 ^ (N + 1) = 0 := by rw [pow_succ, hT, zero_mul]
  let W : Fin (N + 1) → SourcePairL2 :=
    fun k => (((rootShift A z0 ^ (N - k.1)) r : rootSpace A z0) : SourcePairL2)
  have hW : W ∈ opChainSpace φ bc z0 (N + 1) := by
    rw [mem_opChainSpace]
    intro k hk
    have hf : fget W k = (((rootShift A z0 ^ (N - k)) r : rootSpace A z0) : SourcePairL2) :=
      fget_of_lt W hk
    have hd : fget W k ∈ A.domain := by
      rw [hf]
      exact rootSpace_le_domain A z0 ((rootShift A z0 ^ (N - k)) r).2
    refine ⟨hd, ?_⟩
    have hc := coe_rootShift_of_eq A z0 ((rootShift A z0 ^ (N - k)) r) (fget W k) hf.symm hd
    rw [← hc, ← rootShift_pow_succ_apply]
    cases k with
    | zero =>
      rw [show prevSP (fget W) 0 = 0 from rfl, Nat.sub_zero, hT1]
      simp
    | succ k =>
      rw [show prevSP (fget W) (k + 1) = fget W k from rfl,
        fget_of_lt W (by omega : k < N + 1), show N - (k + 1) + 1 = N - k by omega]
  refine ⟨⟨W, hW⟩, Subtype.ext ?_⟩
  show W (Fin.last N) = (r : SourcePairL2)
  simp [W]

/-- **M6 (endpoint equivalence).** A `def`, since its type is a `Type`, not a `Prop`. -/
def opChainSpace_equiv_rootSpace_of_finrank_le (φ : PotPair) (bc : ZSBoundaryCondition)
    (z0 : ℂ) (N : ℕ)
    (hN : Module.finrank ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z0) ≤ N) :
    opChainSpace φ bc z0 (N + 1) ≃ₗ[ℂ]
      rootSpace (zsRealization (intervalPotential φ) bc) z0 := by
  haveI : FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z0) :=
    NlsGge.Atomic.G1104FD.rootSpace_finiteDimensional_interval φ bc z0
  exact LinearEquiv.ofBijective (endpoint φ bc z0 N)
    ⟨endpoint_injective φ bc z0 N, endpoint_surjective φ bc z0 N hN⟩

end

end NlsGge.Atomic.G1104Root
