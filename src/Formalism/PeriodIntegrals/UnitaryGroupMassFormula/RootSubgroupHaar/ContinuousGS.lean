module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.SUpPowEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriShear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupHaar.MatEqZeroOfSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.ContinuousRootCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace PI.AmpRootHaarW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpRootJacW

variable {k r : ℕ}

theorem nset_mul' {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    (hb : b ∈ Nset k r) : a * b ∈ Nset k r := by
  apply PI.AmpOrbQuot.nset_mul <;> assumption

theorem rstab_mul' {g a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (ha : a ∈ RStab k r g) (hb : b ∈ RStab k r g) : a * b ∈ RStab k r g := by
  refine ⟨nset_mul' ha.1 hb.1, ?_⟩
  have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g g⁻¹, uh_mul_inv hg, Matrix.one_mul]
  rw [e]; exact nset_mul' ha.2 hb.2

theorem Fm_row {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (c : Fin r) (j : Fin (r + 1)) : (Fm k r z * M) (eI k r c) j = M (Fin.castSucc c) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hl : Fm k r z (eI k r c) (Fin.last r) = 0 := by
    show fvec k r z (Fin.last r) (eI k r c) = 0
    unfold fvec; rw [dite_eq_right (by simp)]; exact hz _ (Or.inl c.isLt)
  have hc : ∀ d : Fin r, Fm k r z (eI k r c) (Fin.castSucc d) = if d = c then 1 else 0 := fun d => by
    show fvec k r z (Fin.castSucc d) (eI k r c) = _
    rw [fvec_cs, bvec, Pi.single_apply]
    by_cases h : d = c
    · rw [ite_eq_left h, ite_eq_left (by rw [h])]
    · rw [ite_eq_right h, ite_eq_right]
      intro e; apply h; ext; have := congrArg Fin.val e; simp only [eI] at this; omega
  rw [hl, zero_mul, add_zero]
  simp only [hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem flagMat_mul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {a x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r) (hx : x ∈ Nset k r) :
    flagMat k r z (a * x) = flagMat k r z a * flagMat k r z x := by
  have hF : Fm k r z * flagMat k r z (a * x) = Fm k r z * (flagMat k r z a * flagMat k r z x) := by
    rw [← mul_Fm hz (nset_mul' ha hx), Matrix.mul_assoc, mul_Fm hz hx, ← Matrix.mul_assoc a, mul_Fm hz ha,
      Matrix.mul_assoc]
  ext i j
  by_cases hi : i.val < r
  · have e1 := Fm_row hz (flagMat k r z (a * x)) ⟨i.val, hi⟩ j
    have e2 := Fm_row hz (flagMat k r z a * flagMat k r z x) ⟨i.val, hi⟩ j
    have hc : Fin.castSucc (⟨i.val, hi⟩ : Fin r) = i := Fin.ext rfl
    rw [hc] at e1 e2
    rw [← e1, ← e2, hF]
  · have hrow : ∀ (b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (r + 1)),
        flagMat k r z b i c = if i = c then 1 else 0 := fun b c => by
      unfold flagMat; rw [dite_eq_right hi]
    rw [Matrix.mul_apply]
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def gS (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) (v : rootPat p → ℂ) : ℂ :=
  s' q + (vM (rootPat p) s' * vM (rootPat p) v) q.1.1 q.1.2

theorem lm_eq (p : Point ℂ (r + 1)) (s' v : rootPat p → ℂ) (q : rootPat p) :
    ((1 + vM (rootPat p) s') * (1 + vM (rootPat p) v)) q.1.1 q.1.2 = v q + gS p s' q v := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt (rootPat_lt p q.1 q.2)
  rw [add_mul, one_mul, mul_add, mul_one]
  simp only [Matrix.add_apply, Matrix.one_apply, ite_eq_right hne, vM_at, gS]
  ring

theorem gS_dep (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) (v w : rootPat p → ℂ)
    (h : ∀ q', rk (rootPat p) q' < rk (rootPat p) q → v q' = w q') : gS p s' q v = gS p s' q w := by
  unfold gS
  congr 1
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold vM
  by_cases h1 : (q.1.1, c) ∈ rootPat p
  · by_cases h2 : (c, q.1.2) ∈ rootPat p
    · simp only [dite_eq_left h1, dite_eq_left h2]
      rw [h ⟨(c, q.1.2), h2⟩ ?_]
      have a1 : q.1.1.val < c.val := Fin.lt_def.mp (rootPat_lt p _ h1)
      have a2 : c.val < q.1.2.val := Fin.lt_def.mp (rootPat_lt p _ h2)
      show q.1.2.val - c.val < q.1.2.val - q.1.1.val
      omega
    · simp only [dite_eq_right h2, mul_zero]
  · simp only [dite_eq_right h1, zero_mul]

theorem continuous_gS (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) (q : rootPat p) : Continuous (gS p s' q) := by
  unfold gS
  exact continuous_const.add ((continuous_const.matrix_mul (continuous_vM _)).matrix_elem _ _)

theorem lm_mp (p : Point ℂ (r + 1)) (s' : rootPat p → ℂ) :
    MeasurePreserving (fun (v : rootPat p → ℂ) q => v q + gS p s' q v) volume volume :=
  PI.AmpRootCommon.Tri.triShear (rootPat p) (rk (rootPat p)) (gS p s') (fun q => (continuous_gS p s' q).measurable)
    (fun q v w h => gS_dep p s' q v w h)

end PI.AmpRootHaarW
