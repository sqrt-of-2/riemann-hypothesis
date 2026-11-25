module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Mathlib.RingTheory.PicardGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA, Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB, Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso, Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

def LongWeylElementSquare : Prop := ∀ k r : ℕ, w0B k r * w0B k r = 1

end Formalism.L2.SG.Pf.BH.Sw
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB", "h": "module\n\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.PicardGroup\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]

def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]

def tv (k r : ℕ) (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then c ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))⁻¹

def tM (k r : ℕ) (c : Fin r → ℂ) : Mat k r := Matrix.diagonal (tv k r c)

def dv (k r : ℕ) (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then x ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 0
  else -star (x ⟨2 * r + k - i.val, by have := i.isLt; omega⟩)

def tD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal (dv k r x)

def Phi (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r) : Mat k r :=
  w0B k r * NormedSpace.exp X * w0B k r * tM k r (1 + x) * NormedSpace.exp Z * NormedSpace.exp (-X')

def LmL (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →ₗ[ℝ] Mat k r where
  toFun p := w0B k r * p.1 * w0B k r + tD k r p.2.1 + p.2.2.1 - p.2.2.2
  map_add' p q := by
    have : tD k r (p.2.1 + q.2.1) = tD k r p.2.1 + tD k r q.2.1 := by
      unfold tD; rw [Matrix.diagonal_add]; congr 1; funext i; unfold dv
      split_ifs <;> simp [star_add]; ring
    simp only [Prod.fst_add, Prod.snd_add, this, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    have : tD k r (c • p.2.1) = c • tD k r p.2.1 := by
      have hd : ∀ i, dv k r (c • p.2.1) i = (c : ℂ) * dv k r p.2.1 i := by
        intro i; unfold dv; split_ifs <;> simp [Complex.real_smul]
      unfold tD; ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, hd]
      split_ifs <;> simp [Complex.real_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, this, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_sub]

def Lm (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LmL k r)

def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))

def LieG : Prop := ∀ k r : ℕ, Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL

def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ Formalism.FourierDecayAlt.B2.UWb k r) ∧
  Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r).map RL

def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2

end Formalism.L2.SG.Pf.BH.Sw
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwA\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHSwB\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem long_weyl_element_apply (i j : Fin (2 * r + k + 1)) : w0B k r i j = if i = tau k r j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold w0B bigCell
  by_cases h1 : j.val < r
  · rw [dite_eq_left h1]
    have e : (esI k r ⟨j.val, h1⟩ = i) ↔ (i = tau k r j) := by
      constructor
      · intro h; apply Fin.ext; rw [← h]; simp [esI, tau, h1]
      · intro h; apply Fin.ext; rw [h]; simp [esI, tau, h1]
    by_cases h : i = tau k r j
    · rw [ite_eq_left (e.2 h).symm, ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (e.1 h'.symm)), ite_eq_right h]
  · rw [dite_eq_right h1]
    by_cases h2 : j.val ≤ r + k
    · rw [dite_eq_left h2]
      have htj : tau k r j = j := by apply Fin.ext; simp [tau]; omega
      by_cases hi2 : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dite_eq_left hi2, htj, Matrix.one_apply]
        by_cases h : i = j
        · rw [ite_eq_left (by subst h; rfl), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))), ite_eq_right h]
      · rw [dite_eq_right hi2, htj, ite_eq_right]
        intro h; apply hi2; rw [h]; exact ⟨by omega, h2⟩
    · rw [dite_eq_right h2]
      have htj : (tau k r j).val = 2 * r + k - j.val := by simp [tau]; omega
      by_cases h : i.val = 2 * r + k - j.val
      · rw [ite_eq_left h, ite_eq_left (Fin.ext (by rw [htj]; exact h))]; simp
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', htj]))]

theorem w0Sq : LongWeylElementSquare := by
  intro k r
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [long_weyl_element_apply, long_weyl_element_apply, ite_eq_left rfl, mul_one, Matrix.one_apply]
    by_cases h : i = j
    · rw [ite_eq_left (by rw [h, tau_tau]), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (by rw [h', tau_tau])), ite_eq_right h]
  · intro m _ hm
    rw [long_weyl_element_apply m j, ite_eq_right hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem adjoint_long_weyl_element : adjH (w0B k r) = w0B k r := by
  have h1 : adjH (w0B k r) * w0B k r = 1 := (mem_UH_iff _).1 long_weyl_element_mem
  calc adjH (w0B k r) = adjH (w0B k r) * (w0B k r * w0B k r) := by rw [w0Sq k r, Matrix.mul_one]
    _ = (adjH (w0B k r) * w0B k r) * w0B k r := by rw [Matrix.mul_assoc]
    _ = w0B k r := by rw [h1, Matrix.one_mul]

theorem longestWeylElementGL_conj_apply_rev (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (w0B k r * M * w0B k r) i j = M (tau k r i) (tau k r j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r j)]
  · rw [long_weyl_element_apply (tau k r j) j, ite_eq_left rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
    · rw [long_weyl_element_apply, ite_eq_left (tau_tau i).symm, one_mul]
    · intro m _ hm
      rw [long_weyl_element_apply, ite_eq_right (fun h => hm (by rw [h, tau_tau])), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro m _ hm
    rw [long_weyl_element_apply m j, ite_eq_right hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

instance decMid (i : Fin (2 * r + k + 1)) : Decidable (Mid k r i) := by unfold Mid; infer_instance

theorem mid_iff (i : Fin (2 * r + k + 1)) : Mid k r i ↔ dg k r i = r := by
  have := i.isLt
  unfold Mid dg; split_ifs <;> omega

theorem dg_inj {i j : Fin (2 * r + k + 1)} (h : dg k r i = dg k r j) (hm : ¬ Mid k r i) : i = j := by
  have := i.isLt; have := j.isLt
  rw [mid_iff] at hm
  apply Fin.ext
  unfold dg at h hm; split_ifs at h hm <;> omega

theorem mid_tau (i : Fin (2 * r + k + 1)) : Mid k r (tau k r i) ↔ Mid k r i := by
  rw [mid_iff, mid_iff, dg_tau]; have := dg_le (k := k) (r := r) i; omega

def posP (Y : Mat k r) : Mat k r := fun i j => if dg k r i < dg k r j then Y i j else 0

def negP (Y : Mat k r) : Mat k r := fun i j => if dg k r j < dg k r i then Y i j else 0

def middlePart (Y : Mat k r) : Mat k r := fun i j => if Mid k r i ∧ Mid k r j then Y i j else 0

def xOf (Y : Mat k r) (a : Fin r) : ℂ := Y (eI k r a) (eI k r a)

theorem adjH_posP (Y : Mat k r) : adjH (posP Y) = posP (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold posP
  have hi := dg_le (k := k) (r := r) i; have hj := dg_le (k := k) (r := r) j
  by_cases h : dg k r i < dg k r j
  · rw [ite_eq_left (by rw [dg_tau, dg_tau]; omega), ite_eq_left h, adjH_apply]
  · rw [ite_eq_right (by rw [dg_tau, dg_tau]; omega), ite_eq_right h, star_zero, mul_zero, zero_mul]

theorem adjH_negP (Y : Mat k r) : adjH (negP Y) = negP (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold negP
  have hi := dg_le (k := k) (r := r) i; have hj := dg_le (k := k) (r := r) j
  by_cases h : dg k r j < dg k r i
  · rw [ite_eq_left (by rw [dg_tau, dg_tau]; omega), ite_eq_left h, adjH_apply]
  · rw [ite_eq_right (by rw [dg_tau, dg_tau]; omega), ite_eq_right h, star_zero, mul_zero, zero_mul]

theorem adjH_midP (Y : Mat k r) : adjH (middlePart Y) = middlePart (adjH Y) := by
  ext i j
  rw [adjH_apply]
  unfold middlePart
  by_cases h : Mid k r i ∧ Mid k r j
  · rw [ite_eq_left ⟨(mid_tau j).2 h.2, (mid_tau i).2 h.1⟩, ite_eq_left h, adjH_apply]
  · rw [ite_eq_right (fun h' => h ⟨(mid_tau i).1 h'.2, (mid_tau j).1 h'.1⟩), ite_eq_right h, star_zero, mul_zero, zero_mul]

theorem adjH_w0conj (M : Mat k r) : adjH (w0B k r * M * w0B k r) = w0B k r * adjH M * w0B k r := by
  rw [adjH_mul, adjH_mul, adjoint_long_weyl_element, Matrix.mul_assoc]

theorem tD_apply (x : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) :
    tD k r x i j = if i = j then dv k r x i else 0 := by
  unfold tD; rw [Matrix.diagonal_apply]

theorem dv_tau (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : star (dv k r x (tau k r i)) = -dv k r x i := by
  have hi := i.isLt
  unfold dv
  by_cases h1 : i.val < r
  · have hv : (tau k r i).val = 2 * r + k - i.val := by rw [tau_val, ite_eq_left (Or.inl h1)]
    have ht : ¬ (tau k r i).val < r := by omega
    have ht2 : ¬ (tau k r i).val ≤ r + k := by omega
    rw [dite_eq_right ht, dite_eq_right ht2, dite_eq_left h1, star_neg, star_star]
    congr 2; apply Fin.ext; simp only; omega
  · by_cases h2 : i.val ≤ r + k
    · have hv : (tau k r i).val = i.val := by rw [tau_val, ite_eq_right (by omega)]
      have ht : ¬ (tau k r i).val < r := by omega
      have ht2 : (tau k r i).val ≤ r + k := by omega
      rw [dite_eq_right ht, dite_eq_left ht2, dite_eq_right h1, dite_eq_left h2, star_zero, neg_zero]
    · have hv : (tau k r i).val = 2 * r + k - i.val := by rw [tau_val, ite_eq_left (Or.inr (by omega))]
      have ht : (tau k r i).val < r := by omega
      rw [dite_eq_left ht, dite_eq_right h1, dite_eq_right h2, neg_neg]
      congr 2; apply Fin.ext; simp only; omega

theorem adjH_tD (x : Fin r → ℂ) : adjH (tD k r x) = -tD k r x := by
  ext i j
  rw [adjH_apply, Matrix.neg_apply, tD_apply, tD_apply]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, dv_tau]
    calc sgn k r i * -dv k r x i * sgn k r i = -(sgn k r i * sgn k r i) * dv k r x i := by ring
      _ = -dv k r x i := by rw [sgn_mul_self]; ring
  · rw [ite_eq_right (fun h' => h (by rw [← tau_tau i, ← tau_tau j, h'])), ite_eq_right h, star_zero, mul_zero, zero_mul, neg_zero]

theorem lm_mem {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) : Lm k r v ∈ uH k r := by
  obtain ⟨h1, -, h3, h4⟩ : v.1 ∈ lieNS k r ∧ v.2.1 ∈ (⊤ : Submodule ℝ (Fin r → ℂ)) ∧ v.2.2.1 ∈ uWb k r ∧
      v.2.2.2 ∈ lieNS k r := by
    simp only [Vs, Submodule.mem_prod] at hv; exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  show adjH (w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) +
    (w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) = 0
  have a1 : adjH v.1 = -v.1 := eq_neg_of_add_eq_zero_left h1.2
  have a3 : adjH v.2.2.1 = -v.2.2.1 := eq_neg_of_add_eq_zero_left h3.1
  have a4 : adjH v.2.2.2 = -v.2.2.2 := eq_neg_of_add_eq_zero_left h4.2
  rw [adjH_sub, adjH_add, adjH_add, adjH_w0conj, a1, adjH_tD, a3, a4, Matrix.mul_neg, Matrix.neg_mul]
  abel

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem posP_neg (Y : Mat k r) : posP (-Y) = -posP Y := by
  ext i j; simp only [posP, Matrix.neg_apply]; split_ifs <;> simp
theorem negP_neg (Y : Mat k r) : negP (-Y) = -negP Y := by
  ext i j; simp only [negP, Matrix.neg_apply]; split_ifs <;> simp
theorem middlePart_neg (Y : Mat k r) : middlePart (-Y) = -middlePart Y := by
  ext i j; simp only [middlePart, Matrix.neg_apply]; split_ifs <;> simp

theorem long_weyl_conj_conj (M : Mat k r) : w0B k r * (w0B k r * M * w0B k r) * w0B k r = M := by
  simp only [← Matrix.mul_assoc]
  rw [w0Sq k r, Matrix.one_mul, Matrix.mul_assoc, w0Sq k r, Matrix.mul_one]

theorem eI_val' (a : Fin r) : (eI k r a).val = a.val := rfl

theorem diag_star {Y : Mat k r} (hadj : adjH Y = -Y) (i : Fin (2 * r + k + 1)) :
    Y i i = -star (Y (tau k r i) (tau k r i)) := by
  have h := congrFun (congrFun hadj i) i
  rw [adjH_apply, Matrix.neg_apply] at h
  have hs : sgn k r i * star (Y (tau k r i) (tau k r i)) * sgn k r i = star (Y (tau k r i) (tau k r i)) := by
    calc sgn k r i * star (Y (tau k r i) (tau k r i)) * sgn k r i
        = (sgn k r i * sgn k r i) * star (Y (tau k r i) (tau k r i)) := by ring
      _ = star (Y (tau k r i) (tau k r i)) := by rw [sgn_mul_self, one_mul]
  rw [hs] at h
  rw [h, neg_neg]

theorem decomp {Y : Mat k r} (hadj : adjH Y = -Y) : negP Y + tD k r (xOf Y) + middlePart Y + posP Y = Y := by
  ext i j
  simp only [Matrix.add_apply, tD_apply]
  unfold negP middlePart posP
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy (dg k r i) (dg k r j) with h | h | h
  · have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    have hm : ¬ (Mid k r i ∧ Mid k r j) := fun hm => by
      rw [mid_iff, mid_iff] at hm; omega
    rw [ite_eq_right (by omega), ite_eq_right hne, ite_eq_right hm, ite_eq_left h]; ring
  · by_cases hm : Mid k r i
    · have hmj : Mid k r j := by rw [mid_iff] at hm ⊢; omega
      by_cases hij : i = j
      · subst hij
        have h0 : dv k r (xOf Y) i = 0 := by
          have hm2 : r ≤ i.val ∧ i.val ≤ r + k := hm
          unfold dv
          rw [dite_eq_right (by omega), dite_eq_left hm2.2]
        rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_left ⟨hm, hm⟩, h0]; ring
      · rw [ite_eq_right (by omega), ite_eq_right hij, ite_eq_left ⟨hm, hmj⟩, ite_eq_right (by omega)]; ring
    · have hij : i = j := dg_inj h hm
      subst hij
      have hmm : ¬ (Mid k r i ∧ Mid k r i) := fun h' => hm h'.1
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_right hmm]
      have hm' : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := hm
      unfold dv xOf
      by_cases h1 : i.val < r
      · rw [dite_eq_left h1]
        have : eI k r ⟨i.val, h1⟩ = i := Fin.ext rfl
        rw [this]; ring
      · have h2 : ¬ i.val ≤ r + k := fun h2 => hm' ⟨by omega, h2⟩
        rw [dite_eq_right h1, dite_eq_right h2]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = tau k r i := by
          apply Fin.ext; rw [eI_val', tau_val, ite_eq_left (Or.inr (by omega))]
        rw [e, ← diag_star hadj]; ring
  · have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
    have hm : ¬ (Mid k r i ∧ Mid k r j) := fun hm => by
      rw [mid_iff, mid_iff] at hm; omega
    rw [ite_eq_left h, ite_eq_right hne, ite_eq_right hm, ite_eq_right (by omega)]; ring

theorem lm_surj {Y : Mat k r} (hY : Y ∈ uH k r) : ∃ v ∈ Vs k r, Lm k r v = Y := by
  have hadj : adjH Y = -Y := eq_neg_of_add_eq_zero_left hY
  refine ⟨(w0B k r * negP Y * w0B k r, xOf Y, middlePart Y, -posP Y), ?_, ?_⟩
  · have m1 : w0B k r * negP Y * w0B k r ∈ lieNS k r := by
      show w0B k r * negP Y * w0B k r ∈ lieN k r
      refine ⟨?_, ?_⟩
      · intro i j hij
        rw [longestWeylElementGL_conj_apply_rev]
        unfold negP
        rw [ite_eq_right]
        rw [dg_tau, dg_tau]
        have := dg_le (k := k) (r := r) i; have := dg_le (k := k) (r := r) j
        omega
      · rw [adjH_w0conj, adjH_negP, hadj, negP_neg, Matrix.mul_neg, Matrix.neg_mul, neg_add_cancel]
    have m3 : middlePart Y ∈ uWb k r := by
      refine ⟨?_, ?_⟩
      · show adjH (middlePart Y) + middlePart Y = 0
        rw [adjH_midP, hadj, middlePart_neg, neg_add_cancel]
      · intro i j h
        unfold middlePart; rw [ite_eq_right h]
    have m4 : -posP Y ∈ lieNS k r := by
      show -posP Y ∈ lieN k r
      refine ⟨?_, ?_⟩
      · intro i j hij
        rw [Matrix.neg_apply]
        unfold posP
        rw [ite_eq_right (by omega), neg_zero]
      · rw [adjH_neg, adjH_posP, hadj, posP_neg, neg_neg, add_neg_cancel]
    exact Submodule.mem_prod.2 ⟨m1, Submodule.mem_prod.2 ⟨Submodule.mem_top, Submodule.mem_prod.2 ⟨m3, m4⟩⟩⟩
  · show w0B k r * (w0B k r * negP Y * w0B k r) * w0B k r + tD k r (xOf Y) + middlePart Y - -posP Y = Y
    rw [long_weyl_conj_conj, sub_neg_eq_add]
    exact decomp hadj

end Formalism.L2.SG.Pf.BH.Sw

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem RL_sq (M : Mat k r) : ‖RL M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [RL, Formalism.MainNotions.S.realifyFun, WithLp.equiv]
  ring

theorem dv_sq_sum (x : Fin r → ℂ) : ∑ i, ‖dv k r x i‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  let e : Fin r → Fin (2 * r + k + 1) := fun a => ⟨a.val, by omega⟩
  let f : Fin r → Fin (2 * r + k + 1) := fun a => ⟨2 * r + k - a.val, by omega⟩
  have he : Function.Injective e := fun a b h => Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hf : Function.Injective f := fun a b h => by
    have := congrArg Fin.val h; simp [f] at this; exact Fin.ext (by omega)
  have hdisj : Disjoint (Finset.univ.image e) (Finset.univ.image f) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨a, rfl⟩ := hi; obtain ⟨b, hb⟩ := hi'
    have := congrArg Fin.val hb; simp [e, f] at this; omega
  have hsupp : ∀ i ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
      i ∉ Finset.univ.image e ∪ Finset.univ.image f → ‖dv k r x i‖ ^ 2 = 0 := by
    intro i _ hi
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists] at hi
    have h1 : ¬ i.val < r := fun h => hi.1 ⟨i.val, h⟩ (Fin.ext rfl)
    have h2 : i.val ≤ r + k := by
      by_contra h
      exact hi.2 ⟨2 * r + k - i.val, by have := i.isLt; omega⟩ (Fin.ext (by simp [f]; have := i.isLt; omega))
    unfold dv; rw [dite_eq_right h1, dite_eq_left h2]; simp
  rw [← Finset.sum_subset (Finset.subset_univ _) hsupp, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => he h),
    Finset.sum_image (fun a _ b _ h => hf h), two_mul]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    unfold dv; rw [dite_eq_left (show (e a).val < r from a.isLt)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ¬ (f a).val < r := by simp [f]; omega
    have h2 : ¬ (f a).val ≤ r + k := by simp [f]; have := a.isLt; omega
    unfold dv; rw [dite_eq_right h1, dite_eq_right h2, norm_neg, norm_star]
    congr 2; congr 1; apply Fin.ext; simp [f]; omega

theorem tD_sq_sum (x : Fin r → ℂ) : ∑ i, ∑ j, ‖tD k r x i j‖ ^ 2 = 2 * ∑ a, ‖x a‖ ^ 2 := by
  rw [← dv_sq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [tD_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl]
  · intro j _ hj; rw [ite_eq_right (Ne.symm hj), norm_zero]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem conj_sq_sum (X : Mat k r) : ∑ i, ∑ j, ‖(w0B k r * X * w0B k r) i j‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp only [longestWeylElementGL_conj_apply_rev]
  let σ : Equiv.Perm (Fin (2 * r + k + 1)) := Function.Involutive.toPerm (tau k r) tau_tau
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ‖X (tau k r (tau k r i)) (tau k r (tau k r j))‖ ^ 2 = ‖X i j‖ ^ 2
  rw [tau_tau, tau_tau]

theorem lm_norm {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) :
    ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 := by
  obtain ⟨h1, -, h3, h4⟩ : v.1 ∈ lieNS k r ∧ v.2.1 ∈ (⊤ : Submodule ℝ (Fin r → ℂ)) ∧ v.2.2.1 ∈ uWb k r ∧
      v.2.2.2 ∈ lieNS k r := by
    simp only [Vs, Submodule.mem_prod] at hv; exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  have f1 : Fil 1 v.1 := h1.1
  have f4 : Fil 1 v.2.2.2 := h4.1
  have hpt : ∀ i j, ‖(Lm k r v) i j‖ ^ 2 = ‖(w0B k r * v.1 * w0B k r) i j‖ ^ 2 + ‖tD k r v.2.1 i j‖ ^ 2 +
      ‖v.2.2.1 i j‖ ^ 2 + ‖v.2.2.2 i j‖ ^ 2 := by
    intro i j
    show ‖(w0B k r * v.1 * w0B k r + tD k r v.2.1 + v.2.2.1 - v.2.2.2) i j‖ ^ 2 = _
    simp only [Matrix.sub_apply, Matrix.add_apply, longestWeylElementGL_conj_apply_rev, tD_apply]
    have hi := dg_le (k := k) (r := r) i
    have hj := dg_le (k := k) (r := r) j
    rcases lt_trichotomy (dg k r i) (dg k r j) with h | h | h
    · have a0 : v.1 (tau k r i) (tau k r j) = 0 := f1 _ _ (by rw [dg_tau, dg_tau]; omega)
      have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
      have c0 : v.2.2.1 i j = 0 := h3.2 i j (fun hm => by rw [mid_iff, mid_iff] at hm; omega)
      rw [a0, ite_eq_right hne, c0]; simp
    · have a0 : v.1 (tau k r i) (tau k r j) = 0 := f1 _ _ (by rw [dg_tau, dg_tau]; omega)
      have d0 : v.2.2.2 i j = 0 := f4 _ _ (by omega)
      rw [a0, d0]
      by_cases hm : Mid k r i
      · by_cases hij : i = j
        · subst hij
          have h0 : dv k r v.2.1 i = 0 := by
            have hm2 : r ≤ i.val ∧ i.val ≤ r + k := hm
            unfold dv; rw [dite_eq_right (by omega), dite_eq_left hm2.2]
          rw [ite_eq_left rfl, h0]; simp
        · rw [ite_eq_right hij]; simp
      · have hij : i = j := dg_inj h hm
        subst hij
        have c0 : v.2.2.1 i i = 0 := h3.2 i i (fun h' => hm h'.1)
        rw [c0]; simp
    · have d0 : v.2.2.2 i j = 0 := f4 _ _ (by omega)
      have hne : i ≠ j := fun e => by rw [e] at h; exact lt_irrefl _ h
      have c0 : v.2.2.1 i j = 0 := h3.2 i j (fun hm => by rw [mid_iff, mid_iff] at hm; omega)
      rw [d0, ite_eq_right hne, c0]; simp
  rw [RL_sq, RL_sq, RL_sq, RL_sq]
  simp_rw [hpt]
  simp only [Finset.sum_add_distrib]
  rw [conj_sq_sum, tD_sq_sum]

theorem lIso : LIso := fun k r => ⟨fun v hv => lm_mem hv, fun Y hY => lm_surj hY, fun v hv => lm_norm hv⟩

end Formalism.L2.SG.Pf.BH.Sw
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem lieE_G : Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL := by
  have h : Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = ((uH k r : Submodule ℝ (Mat k r)) : Set (Mat k r)) := BH.lieG k r
  unfold Formalism.MainNotions.S.lieE
  rw [h]
  change Submodule.span ℝ (⇑(RL (k := k) (r := r)) '' ↑(uH k r)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem lieG' : LieG := fun k r => lieE_G

theorem mulVec_bvec (X : Mat k r) (j i : Fin (2 * r + k + 1)) : (X *ᵥ bvec j) i = X i j := by
  simp [Formalism.QuantumDeterminants.bvec]

theorem mid_or (j : Fin (2 * r + k + 1)) (h : ¬ Mid k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) := by
  simp only [Mid, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨2 * r + k - j, by omega⟩, Fin.ext ?_⟩
    have hj := j.isLt
    show (j : ℕ) = 2 * r + k - (2 * r + k - j)
    omega

private theorem mul_hpk_apply_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  rw [Matrix.mul_apply]
  simp_rw [Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row]
  rw [Finset.sum_eq_single (tau k r j)]
  · rw [tau_tau, ite_eq_left rfl, sgn_tau]
  · intro m _ hm
    rw [ite_eq_right (fun h => hm (by rw [h, tau_tau])), mul_zero]
  · simp

private theorem adjH_apply_lemma_2 (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Xᴴ * Hpk k r) i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  rw [mul_hpk_apply_lemma, Formalism.QuantumDeterminants.WeylGroupFacts.hpk_mul_apply, Matrix.conjTranspose_apply]

theorem lieWb_set : Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r : Set (Mat k r)) := by
  rw [BH.lieWb k r]
  ext X
  change _ ↔ (adjH X + X = 0 ∧ ∀ i j, ¬(Mid k r i ∧ Mid k r j) → X i j = 0)
  rw [adjH_def]
  constructor
  · rintro ⟨hX, hc⟩
    have hcol : ∀ i j, ¬ Mid k r j → X i j = 0 := by
      intro i j hj
      rcases mid_or j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [← mulVec_bvec X (eI k r a) i, (hc a).1]; rfl
      · rw [← mulVec_bvec X (esI k r a) i, (hc a).2]; rfl
    refine ⟨hX, fun i j hij => ?_⟩
    rcases not_and_or.1 hij with hi | hj
    · have h := congrFun (congrFun hX i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      rw [adjH_apply_lemma_2] at h
      have htau : ¬ Mid k r (tau k r i) := by
        have := tau_out i (by simp only [Mid, not_and_or, not_le] at hi; exact hi)
        simp only [Mid, not_and_or, not_le]; exact this
      rw [hcol _ _ htau, star_zero, mul_zero, zero_mul, zero_add] at h
      exact h
    · exact hcol i j hj
  · rintro ⟨hX, hz⟩
    refine ⟨hX, fun a => ⟨?_, ?_⟩⟩
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h1 : r ≤ (a : ℕ) := h.2.1
      have := a.isLt
      omega
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h2 : 2 * r + k - (a : ℕ) ≤ r + k := h.2.2
      have := a.isLt
      omega

theorem lieWb' : LieWb := by
  intro k r
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have h : Z ∈ Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) := by rw [lieWb_set]; exact hZ
    simpa using h 1
  · unfold Formalism.MainNotions.S.lieE
    rw [lieWb_set]
    have : (fun X => (WithLp.equiv 2 _).symm (Formalism.MainNotions.S.realifyFun X)) '' (uWb k r : Set (Mat k r)) =
        (RL : Mat k r → _) '' (uWb k r : Set (Mat k r)) := rfl
    rw [this, Submodule.span_image, Submodule.span_eq]

def prodEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_prodS {R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) [FiniteDimensional R p] [FiniteDimensional R q] :
    Module.finrank R ↥(p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

private theorem eq_zero_of_RL_lemma_3 (M : Mat k r) (h : ‖RL (k := k) (r := r) M‖ ^ 2 = 0) : M = 0 := by
  rw [RL_sq] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖M i j‖))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖M i j‖)).1 h1 j (Finset.mem_univ _)
  simpa using h2

theorem lm_inj {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (h : Lm k r v = 0) : v = 0 := by
  have hn := lm_norm hv
  rw [h, map_zero, norm_zero] at hn
  have h1 := sq_nonneg ‖RL (k := k) (r := r) v.1‖
  have h2 : 0 ≤ ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have h3 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.1‖
  have h4 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.2‖
  have e1 : ‖RL (k := k) (r := r) v.1‖ ^ 2 = 0 := by nlinarith
  have e2 : ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
  have e3 : ‖RL (k := k) (r := r) v.2.2.1‖ ^ 2 = 0 := by nlinarith
  have e4 : ‖RL (k := k) (r := r) v.2.2.2‖ ^ 2 = 0 := by nlinarith
  have hx : v.2.1 = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v.2.1 a‖)).1 e2 a (Finset.mem_univ _)
    simpa using this
  exact Prod.ext (eq_zero_of_RL_lemma_3 _ e1)
    (Prod.ext hx (Prod.ext (eq_zero_of_RL_lemma_3 _ e3) (eq_zero_of_RL_lemma_3 _ e4)))

def lmEquiv (k r : ℕ) : ↥(Vs k r) ≃ₗ[ℝ] ↥(uH k r) :=
  LinearEquiv.ofBijective ((Lm k r).toLinearMap.restrict fun v hv => lm_mem hv)
    ⟨fun a b hab => by
      have h : Lm k r (a.1 - b.1) = 0 := by
        have := congrArg Subtype.val hab
        simp only [LinearMap.restrict_apply] at this
        rw [map_sub]; exact sub_eq_zero.2 this
      exact Subtype.ext (sub_eq_zero.1 (lm_inj ((Vs k r).sub_mem a.2 b.2) h)),
     fun y => by
      obtain ⟨v, hv, hvy⟩ := lm_surj y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

theorem dimG : Formalism.L2.SG.Pf.BH.DimG := by
  intro k r
  have eG : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (UH (Hpk k r))) = Module.finrank ℝ ↥(uH k r) := by
    rw [lieE_G]; exact ((Submodule.equivMapOfInjective _ RL_injective (uH k r)).finrank_eq).symm
  have eN : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Nset k r)) = Module.finrank ℝ ↥(lieNS k r) := by
    rw [lieE_N]; exact ((Submodule.equivMapOfInjective _ RL_injective (lieNS k r)).finrank_eq).symm
  have eW : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) = Module.finrank ℝ ↥(uWb k r) := by
    rw [(lieWb' k r).2]; exact ((Submodule.equivMapOfInjective _ RL_injective (uWb k r)).finrank_eq).symm
  rw [eG, eN, eW, ← (lmEquiv k r).finrank_eq]
  unfold Vs
  rw [finrank_prodS, finrank_prodS, finrank_prodS, finrank_top, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Formalism.L2.SG.Pf.BH.Sw
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim =====
