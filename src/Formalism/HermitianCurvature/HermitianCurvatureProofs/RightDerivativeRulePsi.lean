module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianCovectors.HermBvecLeft
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem herm_bvec_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    herm H (bvec p) (bvec q) = H q p := by
  have hs : star (bvec q) = bvec q := by
    ext i
    by_cases h : i = q <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

section dp
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))

theorem dp1 (hp : p.val < r) (hq : q.val < r) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, ite_eq_left ⟨hp, hq⟩]
theorem dp2 (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by
  rw [dpsiP, ite_eq_right (by omega), ite_eq_left ⟨hp, hq1, hq2⟩]
theorem dp0 (hp : p.val < r) (hq : r + k < q.val) : dpsiP k r z' p q = 0 := by
  rw [dpsiP, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
theorem dp3 (hp1 : r ≤ p.val) (hp2 : p.val ≤ r + k) (hq : r + k < q.val) :
    dpsiP k r z' p q = if q.val = r + k + 1 then herm (Hpk k r) (bvec p) z' else 0 := by
  rw [dpsiP, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hp1, hp2, hq⟩]
theorem dp4 (hp : r + k < p.val) (hq : r + k < q.val) : dpsiP k r z' p q = if q.val = p.val + 1 then 1 else 0 := by
  rw [dpsiP, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hp, hq⟩]
end dp

theorem hpk_row_eI {k r : ℕ} (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) p = if p.val = 2 * r + k - b.val then 1 else 0 := by
  have hb := b.isLt
  have heI : (eI k r b).val = b.val := rfl
  simp only [Hpk]
  by_cases h : p.val = 2 * r + k - b.val
  · rw [ite_eq_left h, ite_eq_left ⟨by rw [heI]; exact hb, by rw [heI]; omega⟩]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (by rw [heI] at hc; omega)),
      ite_eq_right (fun hc => by rw [heI] at hc; omega),
      ite_eq_right (fun hc => by rw [heI] at hc; exact absurd hc.1 (by omega))]

theorem herm_unitary {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (g *ᵥ x) (g *ᵥ y) = herm (Hpk k r) x y := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hg']

theorem herm_bvec_eI {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  have h1 : herm (Hpk k r) v (bvec (eI k r b)) = ∑ p, Hpk k r (eI k r b) p * v p := by
    have hs : star (bvec (eI k r b)) = bvec (eI k r b) := by
      ext i
      by_cases h : i = eI k r b <;> simp [bvec, h]
    unfold herm
    rw [hs]
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp_rw [hpk_row_eI]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp [esI]
  · intro p _ hp
    rw [ite_eq_right, zero_mul]
    intro h
    exact hp (Fin.ext (by simp [esI, h]))
  · simp

theorem xi_Y_zhat_identity : XiYZhat := by
  apply CovecW.covec_entries

end Formalism.FourierDecayAlt.P.SignAntidiagonal
