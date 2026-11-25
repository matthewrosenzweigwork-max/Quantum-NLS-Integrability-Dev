import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST006
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013
import NlsGge.GK38.Defs

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.ThirdConsultation.MTwoMode

def schurPhysicalPair (φ : NlsGge.GK38.PotPair) :
    NlsGge.Atomic.KST002.PhysicalPairLp :=
  WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2)

def ambientT (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ]
      NlsGge.Atomic.KST003.KSTPairL2 :=
  NlsGge.Atomic.KST006.qOperator (schurPhysicalPair φ) n lam hlam

def TwoModeSmallness (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) : Prop :=
  ‖ambientT φ n lam hlam ^ 2‖ ≤ (1 / 2 : ℝ)

def paritySector (n : ℤ)
    (f : NlsGge.Atomic.KST003.KSTPairL2) : Prop :=
  ∀ (b : Bool) (k : ℤ), k % 2 ≠ n % 2 →
    _root_.fourierCoeff (f b) k = 0

def PeriodicEigenvalue (φ : NlsGge.GK38.PotPair) (n : ℤ)
    (lam : ℂ) : Prop :=
  ∃ f : (NlsGge.Atomic.KST013.dirac (schurPhysicalPair φ)).domain,
    (f : NlsGge.Atomic.KST003.KSTPairL2) ≠ 0 ∧
    paritySector n (f : NlsGge.Atomic.KST003.KSTPairL2) ∧
    NlsGge.Atomic.KST013.dirac (schurPhysicalPair φ) f =
      lam • (f : NlsGge.Atomic.KST003.KSTPairL2)

def schurFrame (n : ℤ) (b : Bool) :
    NlsGge.Atomic.KST013.resonantSubspace n :=
  if b then
    ⟨NlsGge.Atomic.KST003.kstPnUpper n,
      ⟨NlsGge.Atomic.KST003.kstPnUpper n,
        NlsGge.Atomic.KST003.spectralPn_upper n⟩⟩
  else
    ⟨NlsGge.Atomic.KST003.kstPnLower n,
      ⟨NlsGge.Atomic.KST003.kstPnLower n,
        NlsGge.Atomic.KST003.spectralPn_lower n⟩⟩

def schurEntry (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (i j : Bool) : ℂ :=
  inner ℂ
    (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2)
    (NlsGge.Atomic.KST013.reducedS (schurPhysicalPair φ) n lam hlam
      (schurFrame n j) : NlsGge.Atomic.KST003.KSTPairL2)

def schurDiagonalPlus (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) : ℂ :=
  (lam - (n : ℂ) * (Real.pi : ℂ)) -
    schurEntry φ n lam hlam false false

def schurDiagonalMinus (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) : ℂ :=
  (lam - (n : ℂ) * (Real.pi : ℂ)) -
    schurEntry φ n lam hlam true true

def offDiagonal (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (plus : Bool) : ℂ :=
  if plus then -schurEntry φ n lam hlam false true
  else -schurEntry φ n lam hlam true false

def fourierPotential (φ : NlsGge.GK38.PotPair)
    (plus : Bool) (k : ℤ) : ℂ :=
  if plus then (NlsGge.Atomic.KST001.periodTwoPairCoeff φ k).2
  else (NlsGge.Atomic.KST001.periodTwoPairCoeff φ k).1

def schurMatrix (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![lam - (n : ℂ) * (Real.pi : ℂ) -
        schurDiagonalPlus φ n lam hlam,
      -offDiagonal φ n lam hlam true;
     -offDiagonal φ n lam hlam false,
      lam - (n : ℂ) * (Real.pi : ℂ) -
        schurDiagonalMinus φ n lam hlam]

def schurPathTerm (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (r : ℕ) (i j : Bool) : ℂ :=
  inner ℂ
    (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2)
    ((ambientT φ n lam hlam ^ r)
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n j : NlsGge.Atomic.KST003.KSTPairL2)))

def schurEvenRemainder (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (plus : Bool) : ℂ :=
  if plus then
    ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 2) false true
  else
    ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 2) true false

def schurOddRemainder (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (plus : Bool) : ℂ :=
  if plus then
    ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 1) false false
  else
    ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 1) true true

end NlsGge.ThirdConsultation.MTwoMode
end
