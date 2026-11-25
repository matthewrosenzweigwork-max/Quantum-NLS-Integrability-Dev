import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.GK38.Defs
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffInput38

/- KSN001 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN001Host.lean.
   Hosts ONCE (round-14 row KSN-001: "host PairScale, scalarBirkhoff, storedSequence, reflectedStored, pairFourier,
   complexBirkhoff and evenWeightedCoefficient once from existing literal bodies") the KSN-001 design names together with
   the literal auxiliaries their bodies use: bracket, scaleWeight, sequenceLift, reflectedPairCoefficient, reflectPairIndex
   and the constructor obligation reflectedStored_mem (proved here: reindexing by the involution reflectPairIndex).
   Bodies byte-identical to followup12 DEFINITIONS/KSN.lean.md (lines 50-52 scalarBirkhoff; 144-200 carrier block).
   NOT hosted (other packets, KSN-012/018/019): rawCoefficient(_mem), pairPotential, complexDomain, IsRealPair,
   smoothingCoefficient, complexSmoothing. cartesianX/cartesianY are the landed G5033Host bodies (not redeclared).
   grep NlsGge/ and Work/isolated_20261027 (2026-11-01): none of these names exists in namespace
   NlsGge.ThirdConsultation.KSN (NlsGge.Atomic.I037.bracket is a different namespace).
   ELABORATION REPAIR: `open Classical in` before sequenceLift (its `if h : Memℓp ...` needs a Decidable instance; body
   unchanged; same device as landed G4039Host `open Classical`; worker-lane request 68db6faa). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def scalarBirkhoff (b : Bool) (n : ℤ) (φ : PotPair) : ℂ :=
  if b then (cartesianX n φ - Complex.I * cartesianY n φ) / (Real.sqrt 2 : ℂ)
  else (cartesianX n φ + Complex.I * cartesianY n φ) / (Real.sqrt 2 : ℂ)

abbrev PairScale (_s : ℝ) := lp (fun _ : Bool × ℤ => ℂ) 2

def bracket (n : ℤ) : ℝ := max 1 (n.natAbs : ℝ)

def scaleWeight (s : ℝ) (n : ℤ) : ℝ := (bracket n) ^ s

def storedSequence (s : ℝ) (f : Bool → ℤ → ℂ) (j : Bool × ℤ) : ℂ :=
  (scaleWeight s j.2 : ℂ) * f j.1 j.2

open Classical in
def sequenceLift (s : ℝ) (f : Bool → ℤ → ℂ) : PairScale s :=
  if h : Memℓp (storedSequence s f) 2 then ⟨storedSequence s f, h⟩ else 0

def reflectedPairCoefficient (φ : PotPair) (b : Bool) (n : ℤ) : ℂ :=
  if b then -physicalFourier φ.1 (-n) else -physicalFourier φ.2 n

def pairFourier (φ : PotPair) : PairScale 0 := sequenceLift 0 (reflectedPairCoefficient φ)

def complexBirkhoff (φ : PotPair) : PairScale 0 :=
  sequenceLift 0 (fun b n => scalarBirkhoff b n φ)

def reflectPairIndex (j : Bool × ℤ) : Bool × ℤ :=
  (j.1, if j.1 then -j.2 else j.2)

theorem reflectedStored_mem (s : ℝ) (x : PairScale s) :
  Memℓp (fun j => -x (reflectPairIndex j)) 2 := by
  have hinv : Function.Involutive reflectPairIndex := by
    rintro ⟨b, n⟩
    cases b <;> simp [reflectPairIndex]
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  have h := (memℓp_gen_iff hp).1 x.2
  have h2 := (Equiv.summable_iff hinv.toPerm).2 h
  simpa [Function.comp_def, norm_neg] using h2

def reflectedStored (s : ℝ) (x : PairScale s) : PairScale s :=
  ⟨fun j => -x (reflectPairIndex j), reflectedStored_mem s x⟩

def evenWeightedCoefficient (w : ℤ → ℝ) (x : PairScale 0) (b : Bool) (n : ℤ) : ℂ :=
  x (b, n) / (w n : ℂ)

end
end NlsGge.ThirdConsultation.KSN
