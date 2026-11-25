module

public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarInverseSimplification
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation, Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation", "h": "module\n\npublic import Formalism.HermitianCurvature.OperatorsCommuteTranslations\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section dpsi

variable {k r : ℕ}

theorem hpk_col_esI (a : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r l (esI k r a) = if l.val = a.val then 1 else 0 := by
  have ha := a.isLt
  have hl := l.isLt
  unfold Hpk esI
  by_cases hla : l.val = a.val
  · rw [ite_eq_left (by simp only []; omega), ite_eq_left hla]
  · rw [ite_eq_right (by simp only []; omega), ite_eq_right (by simp only []; omega),
      ite_eq_right (by simp only [Fin.ext_iff]; omega), ite_eq_right hla]

theorem hpk_W_row (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w p = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [ite_eq_right hpw]
    unfold Hpk
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (fun h => hpw h.2.2.symm)]

theorem hpk_W_col (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r p w = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [ite_eq_right hpw]
    unfold Hpk
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (fun h => hpw h.2.2)]

theorem hpk_W_sq (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) : Hpk k r w w * Hpk k r w w = 1 := by
  unfold Hpk
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hw.1, hw.2, rfl⟩]
  split_ifs <;> norm_num

theorem herm_Hpk_bvec_eq_star_mul_diag_of_middle (z' : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    herm (Hpk k r) (bvec p) z' = star (z' p) * Hpk k r p p := by
  have hc : ∀ l, Hpk k r l p = if l = p then Hpk k r p p else 0 := fun l => hpk_W_col p l hp
  unfold herm bvec
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_single p]
  · intro l _ hl
    rw [hc l, ite_eq_right hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem unit_entry (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (i j : Fin (2 * r + k + 1)) :
    (∑ l, star (X l i) * Hpk k r l j) + ∑ l, Hpk k r i l * X l j = 0 := by
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h

theorem unit_a (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (a : Fin r) (ha : a.val + 1 < r) :
    X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) = -star (X (eI k r a) (eI k r ⟨a.val + 1, ha⟩)) := by
  have hcol : ∀ l, Hpk k r l (esI k r a) = if l = eI k r a then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r (eI k r ⟨a.val + 1, ha⟩) l = if l = esI k r ⟨a.val + 1, ha⟩ then 1 else 0 := by
    intro l
    unfold Hpk eI esI
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have h := unit_entry X hU (eI k r ⟨a.val + 1, ha⟩) (esI k r a)
  simp only [hcol, hrow, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  linear_combination h

theorem unit_w (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (hr : 1 ≤ r) (w : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r w w * X w (esI k r ⟨r - 1, by omega⟩) = -star (X (eI k r ⟨r - 1, by omega⟩) w) := by
  have hcol : ∀ l, Hpk k r l (esI k r ⟨r - 1, by omega⟩) = if l = eI k r ⟨r - 1, by omega⟩ then 1 else 0 := by
    intro l
    rw [hpk_col_esI]
    simp only [eI, Fin.ext_iff]
  have hrow : ∀ l, Hpk k r w l = if l = w then Hpk k r w w else 0 := fun l => hpk_W_row w l hw
  have h := unit_entry X hU w (esI k r ⟨r - 1, by omega⟩)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [Finset.sum_eq_single w (fun l _ hl => by rw [hrow l, ite_eq_right hl, zero_mul])
    (fun h' => absurd (Finset.mem_univ w) h')] at h
  linear_combination h

end dpsi

theorem dpsi_is_derivation : DpsiDerivation := by
  intro k r z' X hr hz' hU _

  let in1 : Fin (2 * r + k + 1) → ℂ := fun p => if h : p.val + 1 < r then X p ⟨p.val + 1, by omega⟩ else 0
  let in2 : Fin (2 * r + k + 1) → ℂ := fun p => if p.val + 1 = r then (X *ᵥ z') p else 0
  let in3 : Fin (2 * r + k + 1) → ℂ := fun p => -star (X (eI k r ⟨r - 1, by omega⟩) p * z' p)
  let in4 : Fin (2 * r + k + 1) → ℂ := fun p => if h : r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 then X p ⟨p.val + 1, h.2⟩ else 0
  have hrow : ∀ p : Fin (2 * r + k + 1), ∑ q, X p q * dpsiP k r z' p q =
      in1 p + in2 p + (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0)
        + in4 p := by
    intro p
    by_cases h1 : p.val + 1 < r
    · rw [Finset.sum_eq_single ⟨p.val + 1, by omega⟩]
      · rw [dp1 _ _ _ (by omega) (by simp; omega), ite_eq_left (by simp), mul_one]
        simp only [in1, in2, in4, dite_eq_left h1, ite_eq_right (show ¬ p.val + 1 = r by omega), dite_eq_right (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          ite_eq_right (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        ring
      · intro q _ hq
        by_cases hq1 : q.val < r
        · rw [dp1 _ _ _ (by omega) hq1, ite_eq_right, mul_zero]; intro h'; apply hq; ext; simp; omega
        · by_cases hq2 : q.val ≤ r + k
          · rw [dp2 _ _ _ (by omega) (by omega) hq2, ite_eq_right (by omega), mul_zero]
          · rw [dp0 _ _ _ (by omega) (by omega), mul_zero]
      · simp
    · by_cases h2 : p.val + 1 = r
      · have hterm : ∀ q, X p q * dpsiP k r z' p q = X p q * z' q := by
          intro q
          by_cases hq1 : q.val < r
          · rw [dp1 _ _ _ (by omega) hq1, ite_eq_right (by omega), hz' q (by omega)]
          · by_cases hq2 : q.val ≤ r + k
            · rw [dp2 _ _ _ (by omega) (by omega) hq2, ite_eq_left h2]
            · rw [dp0 _ _ _ (by omega) (by omega), hz' q (by omega)]
        simp only [hterm, in1, in2, in4, dite_eq_right h1, ite_eq_left h2, dite_eq_right (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
          ite_eq_right (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
        simp [Matrix.mulVec, dotProduct]
      · by_cases h3 : p.val ≤ r + k
        · rw [Finset.sum_eq_single (esI k r ⟨r - 1, by omega⟩)]
          · rw [dp3 _ _ _ (by omega) h3 (by simp [esI]; omega), ite_eq_left (by simp [esI]; omega)]
            simp only [in1, in2, in4, dite_eq_right h1, ite_eq_right h2, dite_eq_right (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
              ite_eq_left (show r ≤ p.val ∧ p.val ≤ r + k by omega)]
            ring
          · intro q _ hq
            by_cases hq1 : q.val ≤ r + k
            · have : ¬ (r ≤ q.val ∧ q.val ≤ r + k ∧ r + k < q.val) := by omega
              unfold dpsiP; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
            · rw [dp3 _ _ _ (by omega) h3 (by omega), ite_eq_right, mul_zero]
              intro h'; apply hq; ext; simp [esI]; omega
          · simp
        · by_cases h4 : p.val + 1 < 2 * r + k + 1
          · rw [Finset.sum_eq_single ⟨p.val + 1, h4⟩]
            · rw [dp4 _ _ _ (by omega) (by simp; omega), ite_eq_left (by simp), mul_one]
              simp only [in1, in2, in4, dite_eq_right h1, ite_eq_right h2, dite_eq_left (show r + k < p.val ∧ p.val + 1 < 2 * r + k + 1 from ⟨by omega, h4⟩),
                ite_eq_right (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _ hq
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, ite_eq_right, mul_zero]; intro h'; apply hq; ext; simp; omega
              · unfold dpsiP; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
            · simp
          · rw [Finset.sum_eq_zero]
            · simp only [in1, in2, in4, dite_eq_right h1, ite_eq_right h2, dite_eq_right (show ¬ (r + k < p.val ∧ p.val + 1 < 2 * r + k + 1) by omega),
                ite_eq_right (show ¬ (r ≤ p.val ∧ p.val ≤ r + k) by omega)]
              ring
            · intro q _
              by_cases hq1 : r + k < q.val
              · rw [dp4 _ _ _ (by omega) hq1, ite_eq_right (by omega), mul_zero]
              · unfold dpsiP; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]

  have h3eq : ∀ p : Fin (2 * r + k + 1), (if r ≤ p.val ∧ p.val ≤ r + k then X p (esI k r ⟨r - 1, by omega⟩) * herm (Hpk k r) (bvec p) z' else 0) =
      in3 p := by
    intro p
    simp only [in3]
    split_ifs with hp
    · rw [herm_Hpk_bvec_eq_star_mul_diag_of_middle z' p hp]
      have hu := unit_w X hU hr p hp
      rw [star_mul']
      linear_combination (star (z' p)) * hu
        + (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp) - (X p (esI k r ⟨r - 1, by omega⟩) * star (z' p)) * (hpk_W_sq (k := k) p hp)
    · rw [hz' p (by omega)]; simp
  simp_rw [hrow, h3eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  set L1 : ℂ := ∑ a : Fin r, if h : a.val + 1 < r then X (eI k r a) (eI k r ⟨a.val + 1, h⟩) else 0 with hL1
  set M2 : ℂ := (X *ᵥ z') (eI k r ⟨r - 1, by omega⟩) with hM2
  have s2 : ∑ p, in2 p = M2 := by
    rw [Finset.sum_eq_single (eI k r ⟨r - 1, by omega⟩)]
    · simp only [in2]; rw [ite_eq_left (show (eI k r ⟨r - 1, by omega⟩).val + 1 = r by simp [eI]; omega)]
    · intro p _ hp; simp only [in2]; rw [ite_eq_right]; intro h'; apply hp; ext; simp [eI]; omega
    · simp
  have s3 : ∑ p, in3 p = -star M2 := by
    simp only [in3, M2, Matrix.mulVec, dotProduct]
    rw [Finset.sum_neg_distrib, star_sum]
  have e1inj : Function.Injective (eI k r) := fun a b h => by
    have := congrArg Fin.val h; simp [eI] at this; exact Fin.ext this
  have s1 : ∑ p, in1 p = L1 := by
    rw [hL1, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨eI k r, e1inj⟩))]
    · rw [Finset.sum_map]; rfl
    · intro p _ hp
      simp only [in1]
      rw [dite_eq_right]
      intro h'
      apply hp
      exact Finset.mem_map.mpr ⟨⟨p.val, by omega⟩, Finset.mem_univ _, by ext; simp [eI]⟩
  have e4inj : Function.Injective (fun a : Fin r => (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h; have := congrArg Fin.val h; simp at this; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
  have s4 : ∑ p, in4 p = -star L1 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, e4inj⟩))]
    · rw [Finset.sum_map, hL1, star_sum, ← Finset.sum_neg_distrib]
      congr 1; ext a
      have hav := a.isLt
      simp only [in4, Function.Embedding.coeFn_mk]
      by_cases ha : a.val + 1 < r
      · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ha]
        have hu := unit_a X hU a ha
        have e1 : (⟨2 * r + k - 1 - a.val, by omega⟩ : Fin (2 * r + k + 1)) = esI k r ⟨a.val + 1, ha⟩ := by
          ext; simp [esI]; omega
        have e2 : (⟨2 * r + k - 1 - a.val + 1, by omega⟩ : Fin (2 * r + k + 1)) = esI k r a := by
          ext; simp [esI]; omega
        have hx : ∀ p q : Fin (2 * r + k + 1), p = esI k r ⟨a.val + 1, ha⟩ → q = esI k r a →
            X p q = X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) := by
          rintro p q rfl rfl; rfl
        rw [hx _ _ e1 e2, hu]
      · rw [dite_eq_right (by omega), dite_eq_right ha, star_zero, neg_zero]
    · intro p _ hp
      simp only [in4]
      rw [dite_eq_right]
      rintro ⟨h1, h2⟩
      apply hp
      exact Finset.mem_map.mpr ⟨⟨2 * r + k - 1 - p.val, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  rw [s1, s2, s3, s4]
  unfold dEll
  rw [← hL1, ← hM2, star_add]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity", "h": "module\n\npublic import Formalism.HermitianCurvature.OperatorsCommuteTranslations\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarInverseSimplification\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SignPermutationIdentity\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem Formalism.FourierDecayAlt.P.sign_permutation_identity : Formalism.FourierDecayAlt.C3.SignE :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity

theorem Formalism.FourierDecayAlt.P.derivative_leading_zb : Formalism.FourierDecayAlt.C3.DleadZb :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb

theorem Formalism.FourierDecayAlt.P.minors_first_case : Formalism.FourierDecayAlt.C3.MinorsFirstCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case

theorem Formalism.FourierDecayAlt.P.third_polynomial_expansion : Formalism.FourierDecayAlt.C3.MinorsThirdCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion

theorem Formalism.FourierDecayAlt.P.first_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity

theorem Formalism.FourierDecayAlt.P.second_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity

theorem Formalism.FourierDecayAlt.P.third_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_identity

theorem Formalism.FourierDecayAlt.P.first_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity

theorem Formalism.FourierDecayAlt.P.second_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity

theorem Formalism.FourierDecayAlt.P.column_indicator_expansion : Formalism.FourierDecayAlt.C3.ExpansionCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion

alias Formalism.FourierDecayAlt.P.chain_first_identity := _root_.Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity

theorem Formalism.FourierDecayAlt.P.leading_term_identity : Formalism.FourierDecayAlt.C3.LeadAA :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity

theorem Formalism.FourierDecayAlt.P.leading_term_vector_identity : Formalism.FourierDecayAlt.C3.LeadAAv :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity

theorem Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.isotropicNormalFormFull_statement
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity =====
