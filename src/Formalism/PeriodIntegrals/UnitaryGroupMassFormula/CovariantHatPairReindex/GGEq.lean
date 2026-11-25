module

public import Formalism.HermitianCurvature.StatementQ
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe", "h": "module\n\npublic import Formalism.HermitianCurvature.StatementQ\npublic import Mathlib.CategoryTheory.Category.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

noncomputable def sgnL {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) : ℂ :=
  Matrix.det (Matrix.of fun k j => if x k = e j then (1 : ℂ) else 0)

theorem sum_fun_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : (Fin (r + 1) → α) → M) :
    ∑ x, f x = ∑ x0 : α, ∑ y : Fin r → α, f (Fin.cons x0 y) := by
  rw [← (Fin.consEquiv fun _ : Fin (r + 1) => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sgnL_eq_sum {r : ℕ} {α : Type*} [DecidableEq α] (x e : Fin r → α) :
    sgnL x e = ∑ σ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if x = e ∘ σ.symm then 1 else 0) := by
  unfold sgnL
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  simp only [Matrix.of_apply]
  rw [Finset.prod_boole]
  by_cases h : x = e ∘ σ.symm
  · rw [ite_eq_left h, ite_eq_left]
    intro i _
    rw [h]
    simp
  · rw [ite_eq_right h, ite_eq_right]
    intro H
    apply h
    funext j
    have h1 := H (σ.symm j) (Finset.mem_univ _)
    simpa using h1

theorem sum_sgnL {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (g : (Fin r → α) → M) :
    ∑ x, sgnL x e • g x = ∑ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • g (e ∘ π) := by
  simp_rw [sgnL_eq_sum, Finset.sum_smul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by simp [Equiv.Perm.inv_def])

theorem sum_sgnL_alt {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin r → α) (F : (Fin r → α) → M)
    (hF : ∀ (x : Fin r → α) (π : Equiv.Perm (Fin r)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x) :
    ∑ x, sgnL x e • F x = (r.factorial : ℂ) • F e := by
  rw [sum_sgnL]
  have h1 : ∀ π : Equiv.Perm (Fin r), ((Equiv.Perm.sign π : ℤ) : ℂ) • F (e ∘ π) = F e := by
    intro π
    rw [hF, smul_smul]
    have h2 : ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign π : ℤ) : ℂ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, one_smul]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem sum_sgnL_succ {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (r + 1) → α) (H : (Fin (r + 1) → α) → M) :
    ∑ x, sgnL x e • H x = ∑ j : Fin (r + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      ∑ y : Fin r → α, sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y) := by
  have hexp : ∀ (x0 : α) (y : Fin r → α), sgnL (Fin.cons x0 y : Fin (r + 1) → α) e =
      ∑ j : Fin (r + 1), (-1 : ℂ) ^ (j : ℕ) *
        ((if x0 = e j then 1 else 0) * sgnL y (e ∘ j.succAbove)) := by
    intro x0 y
    unfold sgnL
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]
    congr 2
  have step : ∀ (x0 : α) (y : Fin r → α),
      sgnL (Fin.cons x0 y : Fin (r + 1) → α) e • H (Fin.cons x0 y) =
        ∑ j : Fin (r + 1), if x0 = e j then
          ((-1 : ℂ) ^ (j : ℕ) • (sgnL y (e ∘ j.succAbove) • H (Fin.cons (e j) y))) else 0 := by
    intro x0 y
    rw [hexp, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · subst h
      rw [one_mul, mul_smul]
    · rw [zero_mul, mul_zero, zero_smul]
  rw [sum_fun_succ]
  simp_rw [step]
  conv_lhs => arg 2; ext x0; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

theorem skip_two_of_lt {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : Fin.castSucc j' < j) :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 (Fin.castSucc j') j := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.val_castSucc] at h ⊢
  split_ifs <;> (try simp only [Fin.val_castSucc, Fin.val_succ] at *) <;> omega

theorem skip_two_of_ge {m : ℕ} (j : Fin (m + 2)) (j' : Fin (m + 1)) (h : j ≤ Fin.castSucc j') :
    (fun k : Fin m => j.succAbove (j'.succAbove k)) = skip2 j j'.succ := by
  funext k
  apply Fin.ext
  simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ] at h ⊢
  split_ifs <;> (try simp only [Fin.val_castSucc, Fin.val_succ] at *) <;> omega

theorem sum_two {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (e : Fin (m + 2) → α) (F : (Fin m → α) → M)
    (hF : ∀ (x : Fin m → α) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : α → ℂ) :
    ∑ c : Fin (m + 2) → α, sgnL c e • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β (e j) * β' (e (j.succAbove j'))) * (m.factorial : ℂ)) •
          F (fun k => e (j.succAbove (j'.succAbove k))) := by
  refine (sum_sgnL_succ e (fun c => (β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := sum_sgnL_succ (e ∘ j.succAbove)
    (fun y : Fin (m + 1) → α => (β (e j) * β' (y 0)) • F (fun k => y k.succ))
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Function.comp_apply] at h2 ⊢
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have h3 : ∑ z : Fin m → α, sgnL z ((e ∘ j.succAbove) ∘ j'.succAbove) •
      ((β (e j) * β' (e (j.succAbove j'))) • F z) =
      (β (e j) * β' (e (j.succAbove j'))) • ((m.factorial : ℂ) • F ((e ∘ j.succAbove) ∘ j'.succAbove)) := by
    simp_rw [smul_comm (sgnL _ _) (β (e j) * β' (e (j.succAbove j')))]
    rw [← Finset.smul_sum, sum_sgnL_alt _ F hF]
  rw [h3, smul_smul, smul_smul, smul_smul, pow_add]
  congr 1

theorem reindex_pairs {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M) (β β' : Fin (m + 2) → ℂ) :
    ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
          F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  have hR : ∀ i : Fin (m + 2), ∑ i' : Fin (m + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
        F (skip2 i i') else 0) =
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i)) •
        F (skip2 i i') else 0) -
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i * β' i')) •
        F (skip2 i i') else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    split_ifs
    · rw [mul_sub, sub_smul]
    · rw [sub_zero]
  have hL : ∀ j : Fin (m + 2), ∑ j' : Fin (m + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
        F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), (if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β j * β' i)) •
        F (skip2 i j) else 0) -
      ∑ i' : Fin (m + 2), (if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) * (β j * β' i')) •
        F (skip2 j i') else 0) := by
    intro j
    rw [Fin.sum_univ_castSucc (f := fun i => if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
        (β j * β' i)) • F (skip2 i j) else 0),
      Fin.sum_univ_succ (f := fun i' => if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) *
        (β j * β' i')) • F (skip2 j i') else 0)]
    simp only [not_lt.mpr (Fin.le_last j), Fin.not_lt_zero, ite_false, add_zero, zero_add]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases h : Fin.castSucc j' < j
    · have h' : ¬ j < j'.succ := by
        rw [← Fin.le_castSucc_iff]
        exact not_le.mpr h
      rw [ite_eq_left h, ite_eq_right h', sub_zero, Fin.succAbove_of_castSucc_lt _ _ h, skip_two_of_lt j j' h,
        Fin.val_castSucc]
      congr 1
      ring
    · have hle : j ≤ Fin.castSucc j' := not_lt.mp h
      have h' : j < j'.succ := Fin.le_castSucc_iff.mp hle
      rw [ite_eq_right h, ite_eq_left h', zero_sub, Fin.succAbove_of_le_castSucc _ _ hle, skip_two_of_ge j j' hle,
        Fin.val_succ, ← neg_smul]
      congr 1
      ring
  rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => hR i, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

end PI.QnCovHat2W
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem one_side {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M)
    (hF : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : Fin (m + 2) → ℂ) :
    ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      (m.factorial : ℂ) • ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  rw [sum_two id F hF, ← reindex_pairs F β β', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [id, smul_smul]
  congr 1
  ring

noncomputable def GG {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M) (β β' a a' : Fin (m + 2) → ℂ) : M :=
  ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
    (sgnL c id * sgnL d id * (β (c 0) * β' (c 1)) * (a (d 0) * a' (d 1))) •
      F (fun k => c k.succ.succ) (fun k => d k.succ.succ)

theorem GG_eq {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (hR : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) y = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (hC : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F x (y ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F β β' a a' = ((m.factorial : ℂ) * m.factorial) •
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
            (a j * a' j' - a j' * a' j)) • F (skip2 i i') (skip2 j j')
        else 0 := by
  let Φ : (Fin m → Fin (m + 2)) → M := fun x =>
    ∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id • ((a (d 0) * a' (d 1)) • F x (fun k => d k.succ.succ))
  have hΦ : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      Φ (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • Φ x := by
    intro x π
    simp only [Φ, hR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm _ (sgnL d id), smul_comm ((Equiv.Perm.sign π : ℤ) : ℂ) (a (d 0) * a' (d 1))]
  have h1 : GG F β β' a a' =
      ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • Φ (fun k => c k.succ.succ)) := by
    unfold GG
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    ring
  have h2 : ∀ i i' : Fin (m + 2), Φ (skip2 i i') = (m.factorial : ℂ) • ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
      if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (a j' * a' j - a j * a' j')) •
        F (skip2 i i') (skip2 j j') else 0 := by
    intro i i'
    exact one_side (fun y => F (skip2 i i') y) (fun y π => hC _ y π) a a'
  rw [h1, one_side Φ hΦ β β', Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, ite_true, true_and, h2, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj : j < j'
    · simp only [hj, ite_true, smul_smul]
      congr 1
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    · simp [hj]
  · simp [hi]

end PI.QnCovHat2W
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq =====
