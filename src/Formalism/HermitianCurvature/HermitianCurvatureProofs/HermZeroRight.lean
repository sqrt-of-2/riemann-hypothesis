module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymDefs
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel

@[expose] public section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [ite_eq_left h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [ite_eq_left ⟨h, by simp; omega⟩]
        · rw [ite_eq_right (by simp; omega), ite_eq_left ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [ite_eq_right h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  apply GlobalTheory.DualFRep.gram_transpose

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, _root_.Formalism.FourierDecayAlt.P.Ux1.hpk_herm]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
