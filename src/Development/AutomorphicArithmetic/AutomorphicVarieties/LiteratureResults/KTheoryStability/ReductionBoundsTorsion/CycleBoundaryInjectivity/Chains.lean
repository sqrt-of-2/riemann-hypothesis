module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
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
import Mathlib.Data.Finsupp.Pointwise
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open TensorProduct

namespace PositivityTheory.KB.NaturalTheta

section

variable (G : Type) [Group G]

def bdZ (m : ℕ) : ((Fin (m + 1) → G) →₀ ℤ) →ₗ[ℤ] ((Fin m → G) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

theorem bdZ_single (m : ℕ) (g : Fin (m + 1) → G) (a : ℤ) :
    bdZ G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1),
        Finsupp.single (Fin.contractNth j (· * ·) g) ((-1 : ℤ) ^ ((j : ℕ) + 1) * a) := by
  simp only [bdZ, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

def eC (n : ℕ) : ℝ ⊗[ℤ] ((Fin n → G) →₀ ℤ) ≃ₗ[ℝ] Chn G n :=
  letI := Classical.decEq (Fin n → G)
  TensorProduct.finsuppScalarRight ℤ ℝ ℝ (Fin n → G)

omit [Group G] in
theorem eC_single (n : ℕ) (r : ℝ) (g : Fin n → G) (a : ℤ) :
    eC G n (r ⊗ₜ Finsupp.single g a) = Finsupp.single g ((a : ℝ) * r) := by
  let := Classical.decEq (Fin n → G)
  ext i
  rw [eC, TensorProduct.finsuppScalarRight_apply_tmul_apply, zsmul_eq_mul]
  by_cases h : g = i
  · subst h; simp
  · simp [h]

theorem bd_eC (m : ℕ) :
    bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (bdZ G m).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>

    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, eC_single, bdZ_single, tmul_add, tmul_sum, map_add, map_sum,
    bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
    congr 1; congr 1; push_cast; ring_nf

theorem cmap_eC {H : Type} [Group H] (f : G →* H) (n : ℕ) :
    cmap f n ∘ₗ (eC G n).toLinearMap =
      (eC H n).toLinearMap ∘ₗ
        (Finsupp.lmapDomain ℤ ℤ (fun (g : Fin n → G) i => f (g i))).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, eC_single, cmap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

end

end PositivityTheory.KB.NaturalTheta
