module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP, Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Finset Formalism.QuantumDeterminants

noncomputable section

namespace NFOne

theorem K_iso (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (p q : Fin (2 * r + k + 1)) (hp : r + k < p.val) (hq : r + k < q.val)
    (hb : (sg k r q).val < j) (hc : (sg k r p).val < j) :
    herm (Hpk k r) (V (sg k r q).val) (V (sg k r p).val) =
      star (V (sg k r p).val (sg k r q)) + V (sg k r q).val (sg k r p) +
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
  have hp' := p.isLt; have hq' := q.isLt
  rw [herm_eq]
  have pt : ∀ i : Fin (2 * r + k + 1),
      star (V (sg k r p).val i) * (Hpk k r *ᵥ V (sg k r q).val) i =
        (if i = sg k r q then star (V (sg k r p).val (sg k r q)) else 0) +
        (if i = p then V (sg k r q).val (sg k r p) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then
          dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
    intro i
    have hi := i.isLt
    rw [Hpk_mulVec]
    by_cases h1 : i.val < r
    · rw [ite_eq_right (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
        ite_eq_right (show ¬ (i = p) from fun h => by rw [h] at h1; omega),
        ite_eq_right (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), add_zero, add_zero]
      rw [Vs _ hb (sg k r i) (by simp only [sg_val]; omega)]
      by_cases h2 : i = sg k r q
      · rw [ite_eq_left (show (sg k r (sg k r i)).val = (sg k r q).val by rw [h2, sg_sg]), ite_eq_left h2,
          mul_one, h2]
      · rw [ite_eq_right (show ¬ ((sg k r (sg k r i)).val = (sg k r q).val) by
            intro h; apply h2; ext; simp only [sg_val] at h ⊢; omega), ite_eq_right h2, mul_zero]
    · by_cases h3 : i.val ≤ r + k
      · rw [ite_eq_left (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩),
          ite_eq_right (show ¬ (i = sg k r q) from fun h => by rw [h] at h1; simp only [sg_val] at h1; omega),
          ite_eq_right (show ¬ (i = p) from fun h => by rw [h] at h3; omega),
          ite_eq_left (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩)]
        ring
      · rw [ite_eq_right (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          ite_eq_right (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          ite_eq_right (show ¬ (i = sg k r q) from fun h => by rw [h] at h3; simp only [sg_val] at h3; omega),
          zero_add, add_zero]
        rw [Vs _ hc i (by omega)]
        by_cases h2 : i = p
        · rw [ite_eq_left (show (sg k r i).val = (sg k r p).val by rw [h2]), ite_eq_left h2, h2]; simp
        · rw [ite_eq_right (show ¬ ((sg k r i).val = (sg k r p).val) by
            intro h; apply h2; ext; simp only [sg_val] at h; omega), ite_eq_right h2]; simp
  rw [Finset.sum_congr rfl (fun i _ => pt i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem E_zero (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q + (Hpk k r * Pm k r j V) p q +
      ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = 0 := by
  have hp2 := p.isLt
  have hq2 := q.isLt
  rw [PH_apply, HP_apply, PHP_apply]
  have hC : ¬ (r + k < p.val ∧ r + k < q.val) →
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) = 0 := by
    intro hpq
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · by_cases hp : r + k < p.val
      · rw [P_rowWS_colW k r j V i q hi.1 (by omega), mul_zero]
      · rw [P_rowWS_colW k r j V i p hi.1 (by omega), star_zero, mul_zero, zero_mul]
    · rfl
  by_cases hpX : p.val < r
  · have hpW : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
    have hA : ∀ x : Fin (2 * r + k + 1), Pm k r j V x p = 0 := fun x => P_colX k r j V x p hpX
    have hB : Pm k r j V (sg k r p) q = 0 := P_rowS k r j V (sg k r p) q (by rw [sg_val]; omega)
    rw [ite_eq_right hpW, hB, hC (by omega), hA, hA]
    simp
  · by_cases hpW : r ≤ p.val ∧ p.val ≤ r + k
    · rw [ite_eq_left hpW, hC (by omega), add_zero]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [ite_eq_right hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega), P_colX k r j V p q hqX]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [ite_eq_left hqW, P_rowWS_colW k r j V q p hqW.1 hpW.2, P_rowWS_colW k r j V p q hpW.1 hqW.2]
          simp
        · have hqS : r + k < q.val := by omega
          rw [ite_eq_right hqW, P_XW k r j V (sg k r q) p (by rw [sg_val]; omega) hpW.1 hpW.2,
            P_WS k r j V p q hpW.1 hpW.2 hqS, star_neg, star_mul', star_star, star_dW]
          ring
    · have hpS : r + k < p.val := by omega
      rw [ite_eq_right hpW]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [ite_eq_right hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega),
          P_colX k r j V (sg k r p) q hqX, hC (by omega)]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [ite_eq_left hqW, P_WS k r j V q p hqW.1 hqW.2 hpS,
            P_XW k r j V (sg k r p) q (by rw [sg_val]; omega) hqW.1 hqW.2, hC (by omega)]
          ring
        · have hqS : r + k < q.val := by omega
          rw [ite_eq_right hqW]
          have hC' : ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
              dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) =
              ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
                dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hi
            · rw [P_WS k r j V i p hi.1 hi.2 hpS, P_WS k r j V i q hi.1 hi.2 hqS]
            · rfl
          rw [hC', P_XS k r j V (sg k r q) p (by rw [sg_val]; omega) hpS,
            P_XS k r j V (sg k r p) q (by rw [sg_val]; omega) hqS]
          by_cases hbp : (sg k r p).val < j
          · by_cases hbq : (sg k r q).val < j
            · rw [ite_eq_left hbp, ite_eq_left hbq]
              have hK := K_iso k r j V Vs p q hpS hqS hbq hbp
              rw [Viso _ _ hbq hbp] at hK
              exact hK.symm
            · have h0 := V0 _ (Nat.le_of_not_lt hbq)
              rw [ite_eq_left hbp, ite_eq_right hbq, h0]
              simp
          · have h0 := V0 _ (Nat.le_of_not_lt hbp)
            rw [ite_eq_right hbp, h0]
            by_cases hbq : (sg k r q).val < j
            · rw [ite_eq_left hbq]
              simp
            · have h0' := V0 _ (Nat.le_of_not_lt hbq)
              rw [ite_eq_right hbq, h0']
              simp

theorem unitary_P (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0) :
    (1 + Pm k r j V)ᴴ * Hpk k r * (1 + Pm k r j V) = Hpk k r := by
  have hE : (Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
      (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V) = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact E_zero k r j V V0 Vs Viso p q
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  calc (1 + (Pm k r j V)ᴴ) * Hpk k r * (1 + Pm k r j V)
      = Hpk k r + ((Pm k r j V)ᴴ * Hpk k r + Hpk k r * Pm k r j V +
          (Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = Hpk k r := by rw [hE, add_zero]

end NFOne
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet", "h": "module\n\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV\npublic import Formalism.HermitianCurvature.OperatorsCommuteTranslations\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2

variable {k r : ℕ}

theorem sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by
  have hb := b.isLt
  ext
  simp only [NFOne.sg, esI, eI]
  omega

theorem pm_col_star (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, ite_eq_left hb, ite_eq_right (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, ite_eq_right (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [ite_eq_left h1, ite_eq_left (e.mp h1)]
      · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (e.mpr h2))]

theorem one_add_projection_mem_isotropic_set (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]

private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, ite_eq_right (fun e => by rw [e] at hp; omega), zero_mul,
        ite_eq_right (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, ite_eq_right (fun e => by rw [e] at hp2; omega), zero_mul,
            ite_eq_right (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    exact gS p q hq hp

theorem mul_mem_isotropic_unipotent_set (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2

theorem herm_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  apply PI.StabPairsW.herm_es

end N2

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet =====
