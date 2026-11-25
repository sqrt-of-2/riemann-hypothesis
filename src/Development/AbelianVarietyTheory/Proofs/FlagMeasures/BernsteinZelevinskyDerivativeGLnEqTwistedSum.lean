module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerFormula

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {N : ℕ} {M : Mt g N} (hM : IsUniUp M) : IsUnit M := by
  have htri : M.BlockTriangular id := fun i j hij => (hM i j).1 hij
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri]
  simp [(hM _ _).2 rfl]

theorem card_lt_pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hb : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

def ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : Mt g N :=
  fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem isUniUp_ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : IsUniUp (ofUpper f) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · simp only [ofUpper, dite_eq_right (not_lt.mpr hba.le), ite_eq_right hba.ne']
  · subst hab
    simp [ofUpper]

theorem card_uniUp (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  rw [← Fintype.card_subtype]
  have e : {u : Gn g N // IsUniUp (u : Mt g N)} ≃ ({p : Fin N × Fin N // p.1 < p.2} → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(isUnit_of_isUniUp (isUniUp_ofUpper f)).unit, isUniUp_ofUpper f⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        apply Units.ext
        dsimp only
        rw [IsUnit.unit_spec]
        funext a b
        show ofUpper _ a b = (u : Mt g N) a b
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp only [ofUpper, dite_eq_left hab]
        · simp only [ofUpper, dite_eq_right (lt_irrefl a)]
          exact ((hu a a).2 rfl).symm
        · simp only [ofUpper, dite_eq_right (not_lt.mpr hab.le), ite_eq_right hab.ne']
          exact ((hu a b).1 hab).symm
      right_inv := by
        intro f
        funext p
        dsimp only
        rw [IsUnit.unit_spec]
        show ofUpper f p.1.1 p.1.2 = f p
        simp only [ofUpper, dite_eq_left p.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, card_lt_pairs]

theorem eU_coeff (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (u : Gn g N) :
    (eU g N ψ).coeff u = if IsUniUp (u : Mt g N) then
      ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ * (ψ (∑ i ∈ Finset.range (N - 1), entN (u : Mt g N) i (i + 1)))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, card_uniUp, Nat.cast_pow, smul_eq_mul]
  split_ifs <;> simp

theorem sum_br (i n : ℕ) (M : Mt g n) :
    ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) = supFrom i M := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  have hbr : entN (br i (n - i) M) j (j + 1) = entN M (i + j) (i + (j + 1)) := by
    conv_lhs => unfold entN
    rw [dite_eq_left ⟨h1, h2⟩]
    rfl
  rw [hbr, add_assoc]

end GlobalTheory.GLm.DerFormula

namespace GlobalTheory.GLm

open DerFormula

theorem der_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  intro g _ ψ i n F h _
  have key : ∀ x : Gn g n, (∑ v : Gn g (n - i),
      (if IsUniUp (v : Mt g (n - i)) then
        (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
      (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
          br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0)) =
      if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
        F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
    intro x
    unfold InR
    by_cases hx : (InPar i (x : Mt g n) ∧ IsUniUp (br i (n - i) (x : Mt g n))) ∧
        tl i (x : Mt g n) = (h : Mt g i)
    · obtain ⟨⟨hP, hU⟩, ht⟩ := hx
      have hv0 : ((isUnit_of_isUniUp hU).unit : Mt g (n - i)) = br i (n - i) (x : Mt g n) :=
        IsUnit.unit_spec _
      rw [Finset.sum_eq_single (isUnit_of_isUniUp hU).unit]
      · rw [ite_eq_left (by rw [hv0]; exact hU), ite_eq_left ⟨hP, ht, hv0.symm⟩, ite_eq_left ⟨⟨hP, hU⟩, ht⟩, hv0, sum_br,
          mul_comm]
      · intro v _ hv
        refine mul_eq_zero_of_right _ (ite_eq_right ?_)
        rintro ⟨-, -, hb⟩
        exact hv (Units.ext (hb.symm.trans hv0.symm))
      · intro hv
        exact absurd (Finset.mem_univ _) hv
    · rw [ite_eq_right hx]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : IsUniUp (v : Mt g (n - i))
      · refine mul_eq_zero_of_right _ (ite_eq_right ?_)
        rintro ⟨hP, ht, hb⟩
        exact hx ⟨⟨hP, by rw [hb]; exact hv⟩, ht⟩
      · rw [ite_eq_right hv, zero_mul]
  simp only [der, wh, tr, res, eU_coeff]
  calc _ = ∑ v : Gn g (n - i), ((g : ℂ) ^ (i * (n - i)))⁻¹ * ((g : ℂ) ^ ((n - i) * (n - i - 1) / 2))⁻¹ *
        ∑ x : Gn g n, (if IsUniUp (v : Mt g (n - i)) then
          (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
          (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
            br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [key]
        rw [pow_add, mul_inv]

end GlobalTheory.GLm
