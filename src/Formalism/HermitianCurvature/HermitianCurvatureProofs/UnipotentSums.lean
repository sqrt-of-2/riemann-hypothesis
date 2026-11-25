module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianXiVector

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace UnipotentSums

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector

variable {k r : ℕ}

lemma sum_X (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), r ≤ p.val → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (eI k r c) := by
  symm
  refine Fintype.sum_of_injective (eI k r) ?_ (fun c => g (eI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : (eI k r a).val = (eI k r b).val := congrArg Fin.val h
    exact Fin.ext h1
  · intro p hp
    apply hg
    by_contra h
    exact hp ⟨⟨p.val, by omega⟩, Fin.ext rfl⟩

lemma sig_eI (c : Fin r) : GBasic.sig k r (eI k r c) = esI k r c := by
  unfold GBasic.sig
  split_ifs with h
  · rfl
  · exact absurd (Or.inl c.isLt) h

lemma sig_esI (c : Fin r) : GBasic.sig k r (esI k r c) = eI k r c := by
  have hc := c.isLt
  unfold GBasic.sig
  split_ifs with h
  · exact Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
  · exact absurd (Or.inr (by show r + k < 2 * r + k - c.val; omega)) h

lemma sum_Xs (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), p.val ≤ r + k → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (esI k r c) := by
  symm
  refine Fintype.sum_of_injective (esI k r) ?_ (fun c => g (esI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : 2 * r + k - a.val = 2 * r + k - b.val := congrArg Fin.val h
    have := a.isLt
    have := b.isLt
    exact Fin.ext (by omega)
  · intro p hp
    apply hg
    by_contra h
    exact hp ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - p.val) = p.val; omega)⟩

lemma sgn_X (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val) : GBasic.sgn k r p = 1 := by
  unfold GBasic.sgn
  rw [ite_eq_right (show ¬ p.val = r + k by omega)]

lemma mX_apply_X (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (eI k r c) j = if hj : j.val < r then vX c ⟨j.val, hj⟩ else 0 := by
  simp only [C2.mX]
  rw [dite_eq_left (show (eI k r c).val < r from c.isLt)]
  rfl

lemma mX_apply_Xs (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (esI k r c) j = if hj : r + k < j.val then (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ else 0 := by
  have hc := c.isLt
  have h1 : ¬ (esI k r c).val < r := by show ¬ 2 * r + k - c.val < r; omega
  have h2 : r + k < (esI k r c).val := by show r + k < 2 * r + k - c.val; omega
  simp only [C2.mX]
  rw [dite_eq_right h1, dite_eq_left h2]
  by_cases hj : r + k < j.val
  · rw [dite_eq_left hj, dite_eq_left hj]
    have e : (⟨2 * r + k - (esI k r c).val, by omega⟩ : Fin r) = c :=
      Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
    rw [e]
  · rw [dite_eq_right hj, dite_eq_right hj]

lemma unipotent_apply_middle_row (vX : Matrix (Fin r) (Fin r) ℂ) (i j : Fin (2 * r + k + 1)) (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) :
    C2.mX k r vX i j = if i = j then 1 else 0 := by
  simp only [C2.mX]
  rw [dite_eq_right (show ¬ i.val < r by omega), dite_eq_right (show ¬ r + k < i.val by omega)]

lemma mX_col_X (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (c : Fin r) :
    C2.mX k r vX p (eI k r c) = if hp : p.val < r then vX ⟨p.val, hp⟩ c else 0 := by
  have hc := c.isLt
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dite_eq_left h1, dite_eq_left h1, dite_eq_left (show (eI k r c).val < r from hc)]
    rfl
  · rw [dite_eq_right h1, dite_eq_right h1]
    by_cases h2 : r + k < p.val
    · rw [dite_eq_left h2, dite_eq_right (show ¬ r + k < (eI k r c).val from by show ¬ r + k < c.val; omega)]
    · rw [dite_eq_right h2, ite_eq_right]
      intro h
      apply h1
      rw [h]
      exact hc

lemma unipotent_apply_middle_column (vX : Matrix (Fin r) (Fin r) ℂ) (p j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    C2.mX k r vX p j = if p = j then 1 else 0 := by
  have hne : ∀ h : p.val < r ∨ r + k < p.val, p ≠ j := fun h he => by rw [he] at h; omega
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dite_eq_left h1, dite_eq_right (show ¬ j.val < r by omega), ite_eq_right (hne (Or.inl h1))]
  · by_cases h2 : r + k < p.val
    · rw [dite_eq_right h1, dite_eq_left h2, dite_eq_right (show ¬ r + k < j.val by omega), ite_eq_right (hne (Or.inr h2))]
    · rw [dite_eq_right h1, dite_eq_right h2]

end UnipotentSums

namespace UnipotentSums

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector

variable {k r : ℕ}

lemma mX_col_Xs (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (a : Fin r) :
    C2.mX k r vX p (esI k r a) = if hp : r + k < p.val then (vXᴴ)⁻¹ ⟨2 * r + k - p.val, by omega⟩ a else 0 := by
  have ha := a.isLt
  have h1 : ¬ (esI k r a).val < r := by show ¬ 2 * r + k - a.val < r; omega
  have h2 : r + k < (esI k r a).val := by show r + k < 2 * r + k - a.val; omega
  simp only [C2.mX]
  by_cases hp1 : p.val < r
  · rw [dite_eq_left hp1, dite_eq_right h1, dite_eq_right (show ¬ r + k < p.val by omega)]
  · by_cases hp2 : r + k < p.val
    · rw [dite_eq_right hp1, dite_eq_left hp2, dite_eq_left h2, dite_eq_left hp2]
      exact congrArg _ (Fin.ext (by show 2 * r + k - (2 * r + k - a.val) = a.val; omega))
    · rw [dite_eq_right hp1, dite_eq_right hp2, dite_eq_right hp2, ite_eq_right]
      intro h
      apply hp2
      rw [h]
      exact h2

lemma mX_uh (vX : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit vX.det) : C2.mX k r vX ∈ UH (Hpk k r) := by
  have hu' : IsUnit vXᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have hs1 : ∀ c : Fin r, GBasic.sgn k r (eI k r c) = 1 := fun c => sgn_X _ (Or.inl c.isLt)
  have hs2 : ∀ c : Fin r, GBasic.sgn k r (esI k r c) = 1 := fun c =>
    sgn_X _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))
  show (C2.mX k r vX)ᴴ * Hpk k r * C2.mX k r vX = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Hpk_mul_apply, Matrix.conjTranspose_apply]
  have hilt := i.isLt
  have hjlt := j.isLt
  by_cases hi1 : i.val < r
  · obtain ⟨a, rfl⟩ : ∃ a : Fin r, eI k r a = i := ⟨⟨i.val, hi1⟩, Fin.ext rfl⟩
    have ha := a.isLt
    have hea : (eI k r a).val = a.val := rfl
    rw [sum_X _ (fun p hp => by
      rw [mX_col_X, dite_eq_right (show ¬ p.val < r by omega), star_zero, zero_mul])]
    have hcol : ∀ c : Fin r, C2.mX k r vX (eI k r c) (eI k r a) = vX c a := fun c => by
      rw [mX_col_X, dite_eq_left (show (eI k r c).val < r from c.isLt)]
      rfl
    simp only [sig_eI, hs1, one_mul, hcol, mX_apply_Xs]
    by_cases hj : r + k < j.val
    · simp only [dite_eq_left hj]
      have key : ∑ c : Fin r, star (vX c a) * (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ =
          (vXᴴ * (vXᴴ)⁻¹) a ⟨2 * r + k - j.val, by omega⟩ := by
        rw [Matrix.mul_apply]
        simp only [Matrix.conjTranspose_apply]
      rw [key, Matrix.mul_nonsing_inv _ hu', Matrix.one_apply]
      simp only [Hpk, Fin.ext_iff]
      show _ = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega)
    · simp only [dite_eq_right hj, mul_zero, Finset.sum_const_zero]
      simp only [Hpk]
      show (0 : ℂ) = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega)
  · by_cases hi2 : r + k < i.val
    · obtain ⟨a, rfl⟩ : ∃ a : Fin r, esI k r a = i :=
        ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)⟩
      have ha := a.isLt
      have hea : (esI k r a).val = 2 * r + k - a.val := rfl
      rw [sum_Xs _ (fun p hp => by
        rw [mX_col_Xs, dite_eq_right (show ¬ r + k < p.val by omega), star_zero, zero_mul])]
      have hcol : ∀ c : Fin r, C2.mX k r vX (esI k r c) (esI k r a) = (vXᴴ)⁻¹ c a := fun c => by
        have hc := c.isLt
        rw [mX_col_Xs, dite_eq_left (show r + k < (esI k r c).val from by show r + k < 2 * r + k - c.val; omega)]
        have e : (⟨2 * r + k - (esI k r c).val, by show 2 * r + k - (2 * r + k - c.val) < r; omega⟩ : Fin r) = c :=
          Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
        rw [e]
      simp only [sig_esI, hs2, one_mul, hcol, mX_apply_X]
      by_cases hj : j.val < r
      · simp only [dite_eq_left hj]
        have key : ∑ c : Fin r, star ((vXᴴ)⁻¹ c a) * vX c ⟨j.val, hj⟩ =
            (((vXᴴ)⁻¹)ᴴ * vX) a ⟨j.val, hj⟩ := by
          rw [Matrix.mul_apply]
          simp only [Matrix.conjTranspose_apply]
        rw [key, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
          Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
        simp only [Hpk, Fin.ext_iff]
        show _ = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [dite_eq_right hj, mul_zero, Finset.sum_const_zero]
        simp only [Hpk]
        show (0 : ℂ) = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega)
    · rw [Finset.sum_eq_single i (fun p _ hp => by
          rw [unipotent_apply_middle_column vX p i (by omega) (by omega), ite_eq_right hp, star_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [unipotent_apply_middle_column vX i i (by omega) (by omega), ite_eq_left rfl, star_one, one_mul,
        FlagSpanVanishing.sig_fixes_middle_block i ⟨by omega, by omega⟩, unipotent_apply_middle_row vX i j (by omega) (by omega)]
      simp only [GBasic.sgn, Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | omega | simp

lemma mX_mem (vX : Matrix (Fin r) (Fin r) ℂ) (hv : vX ∈ C2.UTset r) : C2.mX k r vX ∈ Nset k r := by
  obtain ⟨hv1, hv2⟩ := hv
  have hdet : vX.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (by intro i j hij; exact hv1 i j hij)]
    simp [hv2]
  refine ⟨mX_uh vX (by rw [hdet]; exact isUnit_one), ?_, ?_⟩
  · intro a i hai
    rw [mX_col_X]
    by_cases hi : i.val < r
    · rw [dite_eq_left hi]
      by_cases he : i = eI k r a
      · rw [ite_eq_left he]
        subst he
        exact hv2 a
      · rw [ite_eq_right he]
        apply hv1
        show a.val < i.val
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
    · rw [dite_eq_right hi, ite_eq_right]
      intro h
      apply hi
      rw [h]
      exact a.isLt
  · intro i j hj1 hj2 _
    exact unipotent_apply_middle_column vX i j hj1 hj2

end UnipotentSums

end Formalism.FourierDecayAlt.P
