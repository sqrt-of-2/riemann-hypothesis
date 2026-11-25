module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose, ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def kE (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def fI (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨q.val, by omega⟩

theorem fI_inj : Function.Injective (fI k r) := by
  intro a b h; simp [fI, Fin.ext_iff] at h; exact Fin.ext h

theorem sumF (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_ff (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) : kE k r h (fI k r q) (fI k r q') = h q q' := by
  simp [kE, fI]

theorem kE_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ i.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  simp [kE, hi]

theorem kE_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ j.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  by_cases hi : i.val < k
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    simp [kE, hi, hj, hne]
  · simp [kE, hi]

theorem ex_fI {i : Fin (2 * r + k + 1)} (hi : i.val < k) : ∃ q, i = fI k r q :=
  ⟨⟨i.val, hi⟩, by ext; simp [fI]⟩

theorem kE_mul (a b : Matrix (Fin k) (Fin k) ℂ) : kE k r (a * b) = kE k r a * kE k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < k
  · obtain ⟨qi, rfl⟩ := ex_fI hi
    rw [sumF _ (fun p hp => by rw [kE_col a _ hp, ite_eq_right (by rintro rfl; exact hp hi), zero_mul])]
    by_cases hj : j.val < k
    · obtain ⟨qj, rfl⟩ := ex_fI hj
      simp only [kE_ff, Matrix.mul_apply]
    · rw [kE_col _ _ hj, ite_eq_right (by rintro rfl; exact hj hi)]
      refine (Finset.sum_eq_zero fun q _ => ?_).symm
      rw [kE_col b _ hj, ite_eq_right (by intro h; apply hj; rw [← h]; exact q.2), mul_zero]
  · rw [kE_row _ j hi]
    rw [Finset.sum_eq_single i (fun p _ hp => by rw [kE_row a p hi, ite_eq_right (Ne.symm hp), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [kE_row a i hi, ite_eq_left rfl, one_mul, kE_row b j hi]

theorem kE_one : kE k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dite_eq_left hi, dite_eq_left hj, Matrix.one_apply, Fin.ext_iff]
    · rw [kE_col _ _ hj, Matrix.one_apply]
  · rw [kE_row _ _ hi, Matrix.one_apply]

theorem kE_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) : (kE k r h)ᴴ = kE k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dite_eq_left hi, dite_eq_left hj, Matrix.conjTranspose_apply]
    · rw [kE_row _ _ hj, kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, star_zero]
  · rw [kE_col _ _ hi, kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, star_zero]

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem cay_col (hW : WCols k r P) (q : Fin k) (l : Fin (2 * r + k + 1)) :
    P l (StandardBasisEmbedding.eB k r q) = if l = fI k r q then 1 else 0 := by
  have h := congrFun (hW q) l
  have e : Formalism.QuantumDeterminants.wI k r q.castSucc = StandardBasisEmbedding.eB k r q := rfl
  rw [e] at h
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [h]
  rfl

theorem cay_entry (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) (j : Fin (2 * r + k + 1)) :
    Hpk k r (StandardBasisEmbedding.eB k r q) j = (if ε (fI k r q) then 1 else -1) * P (fI k r q) j := by
  rw [← hP.2, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cay_col hW, Formalism.REAL.Jm, Matrix.diagonal_apply]
  simp
  rw [Finset.sum_eq_single (fI k r q) (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem cay_eps (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (a : Fin (2 * r + k + 1))
    (ha : a.val < k) : ε a = true := by
  have h := cay_entry hP hW ⟨a.val, ha⟩ (StandardBasisEmbedding.eB k r ⟨a.val, ha⟩)
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), ite_eq_left rfl, cay_col hW, ite_eq_left rfl, mul_one] at h
  have e : fI k r ⟨a.val, ha⟩ = a := Fin.ext rfl
  rw [e] at h
  by_contra hne
  rw [ite_eq_right hne] at h
  norm_num at h

theorem cay_zero (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) {j : Fin (2 * r + k + 1)}
    (hj : ¬ StandardBasisEmbedding.bl k r j) : P (fI k r q) j = 0 := by
  have h := cay_entry hP hW q j
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), ite_eq_right (by rintro rfl; exact hj (StandardBasisEmbedding.bl_eB q))] at h
  have hne : (if ε (fI k r q) then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.1 h.symm).resolve_left hne

theorem cay_mul (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h = kE k r h * P := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hj : StandardBasisEmbedding.bl k r j
  · obtain ⟨q', rfl⟩ := StandardBasisEmbedding.ex_eB hj
    rw [StandardBasisEmbedding.sumB _ (fun p hp => by rw [StandardBasisEmbedding.bw_off h hp hj, mul_zero])]
    simp only [StandardBasisEmbedding.bw_ee, cay_col hW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      simp only [ite_mul, one_mul, zero_mul, kE_ff]
      rw [Finset.sum_eq_single qi (fun b _ hb => by rw [ite_eq_right (fun e => hb (fI_inj e).symm)])
        (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
    · rw [kE_row _ _ hi, ite_eq_right (by intro e; apply hi; rw [e]; exact q'.2)]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [ite_eq_right (by intro e; apply hi; rw [e]; exact q.2), zero_mul]
  · rw [Finset.sum_eq_single j (fun b _ hb => by rw [StandardBasisEmbedding.bw_col h b hj, ite_eq_right hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), StandardBasisEmbedding.bw_col h j hj, ite_eq_left rfl, mul_one]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      rw [cay_zero hP hW qi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l.val < k
      · obtain ⟨ql, rfl⟩ := ex_fI hl
        rw [cay_zero hP hW ql hj, mul_zero]
      · rw [kE_col _ _ hl, ite_eq_right (by rintro rfl; exact hl (by simp [fI])), zero_mul]
    · rw [Finset.sum_eq_single i (fun b _ hb => by rw [kE_row h b hi, ite_eq_right (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), kE_row h i hi, ite_eq_left rfl, one_mul]

theorem cay_kE (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h * P⁻¹ = kE k r h := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  rw [cay_mul hP hW, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.KEConjTranspose\nimport Mathlib.Algebra.Order.Archimedean.Real.Hom\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eq_smul_highestWeight_of_isWeight {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) {v : T.V}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T) Λ v) : ∃ c : ℂ, v = c • T.w := by
  by_cases h0 : v = 0
  · exact ⟨0, by simp [h0]⟩
  have hd := HW.torep_dτ_of_wt T hv
  have hraise : ∀ a b, a < b → ε a = ε b → T.dτ (Matrix.single a b 1) v = 0 := by
    intro a b hab he
    by_contra hx
    have hwx : ∀ c, T.dτ (Matrix.single c c 1) (T.dτ (Matrix.single a b 1) v) =
        (((Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c : ℝ) : ℂ) • T.dτ (Matrix.single a b 1) v := by
      intro c
      have hR := HW.KType.kRel T c c a b rfl he
      have h1 := congrArg (fun f : Module.End ℂ T.V => f v) hR
      simp only [HW.kunits, LinearMap.sub_apply, mul_apply_eq_comp, ContinuousLinearMap.coe_coe] at h1
      have hab' : a ≠ b := ne_of_lt hab
      rw [hd c, map_smul] at h1
      by_cases hca : c = a
      · subst hca
        have hcb : ¬ b = c := fun h => hab' h.symm
        rw [ite_eq_left rfl, ite_eq_right hcb] at h1
        simp only [LinearMap.zero_apply, sub_zero, ContinuousLinearMap.coe_coe] at h1
        rw [sub_eq_iff_eq_add] at h1
        rw [h1]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, ite_eq_right (Ne.symm hcb)]
        push_cast
        module
      · by_cases hcb : b = c
        · subst hcb
          rw [ite_eq_right hca, ite_eq_left rfl] at h1
          simp only [LinearMap.zero_apply, zero_sub, ContinuousLinearMap.coe_coe] at h1
          rw [sub_eq_iff_eq_add] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, ite_eq_right hca]
          push_cast
          module
        · rw [ite_eq_right hca, ite_eq_right hcb] at h1
          simp only [LinearMap.zero_apply, sub_zero] at h1
          rw [sub_eq_zero] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, ite_eq_right hca, ite_eq_right (Ne.symm hcb)]
          simp
    obtain ⟨cc, hc, he'⟩ := HW.KType.weight_le T hx hwx
    let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
        map_add' := by
          intro f g
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp [Finset.mul_sum, mul_left_comm] }
    have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
      intro x
      simp [ψ, Pi.single_apply]
    have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
      abel
    rw [hl] at he'
    have h := congrArg ψ he'

    simp only [map_sum, map_smul, root, map_sub, hψ, smul_eq_mul] at h
    have hr : ∑ x, ∑ y, (cc x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
      refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
      by_cases h0 : cc x y = 0
      · simp [h0]
      · have hxy := (hc x y h0).1
        have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique T h0 ⟨hd, hraise⟩
  exact ⟨c, hc⟩

section Span

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

theorem sumF' {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_mem_Kset (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) : kE k r h ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kE_conjTranspose, ← kE_mul]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hh
    rw [hh, kE_one]
  · ext i j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · rw [hε i hi, hε j hj]; simp
      · rw [kE_col _ _ hj, ite_eq_right (by rintro rfl; exact hj hi)]; simp
    · rw [kE_row _ _ hi]
      by_cases hij : i = j
      · subst hij; ring
      · rw [ite_eq_right hij]; simp

def dg (θ : Fin (2 * r + k + 1) → ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

def th2 (θ : Fin (2 * r + k + 1) → ℝ) : Fin (2 * r + k + 1) → ℝ := fun a => if a.val < k then 0 else θ a

def th1 (θ : Fin (2 * r + k + 1) → ℝ) : Fin k → ℝ := fun q => θ (fI k r q)

def dgk (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I))

theorem dg_mem (θ : Fin (2 * r + k + 1) → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dg, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dg, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dgk_mem (t : Fin k → ℝ) : dgk t ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have := dg_mem (k := k) (r := 0) (ε := fun _ => true)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dgk, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dgk, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dg_split (θ : Fin (2 * r + k + 1) → ℝ) : dg θ = kE k r (dgk (th1 θ)) * dg (th2 θ) := by
  ext i j
  unfold dg
  rw [Matrix.mul_diagonal]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [dgk, kE, th1, th2, dite_eq_left hi, dite_eq_left hj, ite_eq_left hj, Matrix.diagonal_apply, fI]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right hij, ite_eq_right (by intro e; apply hij; exact Fin.ext (by simpa using e))]; simp
    · simp only [th2, ite_eq_right hj, Matrix.diagonal_apply]
      rw [kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; exact absurd hi hj
      · simp [hij]
  · simp only [th2, Matrix.diagonal_apply]
    rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem central_diagonal_commute (θ : Fin (2 * r + k + 1) → ℝ) (h : Matrix (Fin k) (Fin k) ℂ) :
    kE k r h * dg (th2 θ) = dg (th2 θ) * kE k r h := by
  ext i j
  rw [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp [th2, hi, hj]
    · rw [kE_col _ _ hj, ite_eq_right (by rintro rfl; exact hj hi)]; simp
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; ring
    · rw [ite_eq_right hij]; simp

variable (T : S7.KType ε Λ)

def rhoK (h : Matrix (Fin k) (Fin k) ℂ) : T.V →L[ℂ] T.V := HW.torepSig T (kE k r h)

def spanW : Submodule ℂ T.V :=
  sInf {S | T.w ∈ S ∧ ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S}

theorem w_mem_spanW : T.w ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun _ hS => hS.1

theorem spanW_stable {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) {v : T.V}
    (hv : v ∈ spanW (k := k) (r := r) T) : rhoK (k := k) (r := r) T h v ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun S hS => hS.2 h hh v (Submodule.mem_sInf.1 hv S hS)

theorem spanW_le {S : Submodule ℂ T.V} (hw : T.w ∈ S)
    (hS : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S) :
    spanW (k := k) (r := r) T ≤ S :=
  sInf_le ⟨hw, hS⟩

theorem torep_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) (v : T.V) : HW.torepSig T (a * b) v = HW.torepSig T a (HW.torepSig T b v) := by
  rw [(HW.torep_isURepOn T).1.2 a ha b hb]; rfl

theorem spanW_scalar (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (θ : Fin (2 * r + k + 1) → ℝ)
    {x : T.V} (hx : x ∈ spanW (k := k) (r := r) T) :
    HW.torepSig T (dg (th2 θ)) x = Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I) • x := by
  set c := Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I)
  let S : Submodule ℂ T.V := LinearMap.ker ((HW.torepSig T (dg (th2 θ)) : T.V →ₗ[ℂ] T.V) - c • LinearMap.id)
  have hmem : ∀ y, y ∈ S ↔ HW.torepSig T (dg (th2 θ)) y = c • y := by
    intro y
    simp [S, sub_eq_zero]
  have hle : spanW (k := k) (r := r) T ≤ S := by
    refine spanW_le T ((hmem _).2 (HW.torep_wt_w T (th2 θ) (dg_mem _))) ?_
    intro h hh v hv
    rw [hmem] at hv ⊢
    unfold rhoK
    rw [← torep_mul T (dg_mem _) (kE_mem_Kset hε hh), ← central_diagonal_commute, torep_mul T (kE_mem_Kset hε hh) (dg_mem _), hv,
      map_smul]
  exact (hmem x).1 (hle hx)

end Span

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight =====
