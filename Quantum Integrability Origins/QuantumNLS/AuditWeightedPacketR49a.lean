import QuantumNLS.CommonBethePacket

/-! R-115CAA16: finite-packet normalization and all charge domains.
These lemmas construct an actual DEF-034 packet from a nonzero finite
expansion. Selection of a common physical high-probability support and its
approximation to the product vector are separate, still open obligations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.AuditWeightedPacketR49a
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform
open QuantumNLS.CommonBethePacket
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem synthesis_smul (b : BetheBasis L N) (a : MArr N →₀ ℂ) (c : ℂ) :
    synthesis b (c • a) = c • synthesis b a := by
  change (c • a).sum (fun m z => z • b m)=c • a.sum (fun m z => z • b m)
  rw [Finsupp.sum_smul_index (h := fun m (z : ℂ) => z • b m) (fun _ => zero_smul ℂ _)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]

def normalize (b : BetheBasis L N) (a : MArr N →₀ ℂ)
    (ha : ‖synthesis b a‖ ≠ 0) : Packet b where
  coefficients := (‖synthesis b a‖⁻¹ : ℂ) • a
  normalized := by
    rw [synthesis_smul, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ ha]

theorem vector_normalize (b : BetheBasis L N) (a : MArr N →₀ ℂ)
    (ha : ‖synthesis b a‖ ≠ 0) :
    vector (normalize b a ha)=(‖synthesis b a‖⁻¹ : ℂ) • synthesis b a :=
  synthesis_smul b a _

theorem support_normalize_subset (b : BetheBasis L N) (a : MArr N →₀ ℂ)
    (ha : ‖synthesis b a‖ ≠ 0) : support (normalize b a ha) ⊆ a.support :=
  Finsupp.support_smul

/-- Every finite packet belongs to EVERY fixed maximal spectral domain,
without any assertion about the product vector's higher charge domains. -/
theorem packet_mem_every_domain (b : BetheBasis L N) (P : Packet b) (ev : MArr N → ℝ) :
    vector P ∈ (QuantumNLS.BetheSpectralCharges.multiplier b ev).domain := by
  unfold vector synthesis
  apply Submodule.sum_mem
  intro m _
  exact Submodule.smul_mem _ _ (QuantumNLS.BetheSpectralCharges.basis_mem_domain b ev m)

/-- Normalizing any finite approximation within distance <1 from a unit
vector costs at most a factor of two in the approximation error. -/
theorem normalize_approximation (b : BetheBasis L N) (a : MArr N →₀ ℂ)
    (ψ : HN L N) (hψ : ‖ψ‖=1) (hclose : ‖synthesis b a-ψ‖<1) :
    ∃ ha : ‖synthesis b a‖ ≠ 0,
      ‖vector (normalize b a ha)-ψ‖ ≤ 2*‖synthesis b a-ψ‖ := by
  let v := synthesis b a
  have hnorm : |‖v‖-1| ≤ ‖v-ψ‖ := by simpa only [hψ] using abs_norm_sub_norm_le v ψ
  have hv : 0 < ‖v‖ := by
    have : ‖v-ψ‖<1 := hclose
    have := (abs_le.mp hnorm).1
    linarith
  refine ⟨hv.ne',?_⟩
  rw [vector_normalize]
  change ‖(‖v‖⁻¹ : ℂ) • v-ψ‖ ≤ 2*‖v-ψ‖
  have he : (‖v‖⁻¹ : ℂ) • v-ψ = ((‖v‖⁻¹ : ℂ)-1) • v+(v-ψ) := by
    rw [sub_smul, one_smul]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hscale : ‖((‖v‖⁻¹ : ℂ)-1) • v‖=|1-‖v‖| := by
    have ec : ((‖v‖⁻¹ : ℂ)-1)=(((‖v‖⁻¹-1 : ℝ)) : ℂ) := by push_cast; ring
    rw [norm_smul, ec, Complex.norm_real, Real.norm_eq_abs,
      ← abs_of_pos hv, ← abs_mul, abs_of_pos hv]
    congr 1
    field_simp
  rw [hscale, abs_sub_comm]
  linarith

end QuantumNLS.AuditWeightedPacketR49a

#print axioms QuantumNLS.AuditWeightedPacketR49a.synthesis_smul

#print axioms QuantumNLS.AuditWeightedPacketR49a.normalize

#print axioms QuantumNLS.AuditWeightedPacketR49a.vector_normalize

#print axioms QuantumNLS.AuditWeightedPacketR49a.support_normalize_subset

#print axioms QuantumNLS.AuditWeightedPacketR49a.packet_mem_every_domain

#print axioms QuantumNLS.AuditWeightedPacketR49a.normalize_approximation

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedPacketR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedPacketR49a." then
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round49 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
