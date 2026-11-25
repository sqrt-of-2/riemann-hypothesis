module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsLevPairA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

open Finset PositivityTheory.RgBcC.RealD
open CompanionTheory.D.LK (Pos key)

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

variable {n : ℕ}

theorem key_lt (i : Pos n) : key i < n * n := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have ha := a.isLt
  have hb := b.isLt
  show (a : ℕ) * n + b < n * n
  calc (a : ℕ) * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ ha

theorem keyL_inj {l m : Lt n} (h : keyL l = keyL m) : l = m := by
  obtain ⟨b1, p1⟩ := l
  obtain ⟨b2, p2⟩ := m
  have k1 := key_lt p1
  have k2 := key_lt p2
  have hk : key p1 = key p2 ∧ b1 = b2 := by
    simp only [keyL] at h
    cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨⟨a1, c1⟩, h1⟩ := p1
  obtain ⟨⟨a2, c2⟩, h2⟩ := p2
  have hc1 := c1.isLt
  have hc2 := c2.isLt
  have hn : 0 < n := by omega
  have hk' : (c1 : ℕ) + a1 * n = c2 + a2 * n := by
    have e : (a1 : ℕ) * n + c1 = a2 * n + c2 := hk
    linarith
  have ea : (a1 : ℕ) = a2 := by
    have := congrArg (· / n) hk'
    simpa [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2] using this
  have ec : (c1 : ℕ) = c2 := by
    have := congrArg (· % n) hk'
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] using this
  have e1 : a1 = a2 := Fin.ext ea
  have e2 : c1 = c2 := Fin.ext ec
  subst e1 e2
  rfl

def twL (l m : Lt n) : ℂ := if keyL m < keyL l then -1 else 1

theorem twL_self (l : Lt n) : twL l l = 1 := by simp [twL]

theorem twL_mul_self (l m : Lt n) : twL l m * twL l m = 1 := by
  unfold twL
  split_ifs <;> norm_num

theorem twL_swap {l m : Lt n} (h : l ≠ m) : twL m l = -twL l m := by
  have hk : keyL l ≠ keyL m := fun e => h (keyL_inj e)
  unfold twL
  split_ifs with h1 h2 h2
  · exfalso; omega
  · norm_num
  · norm_num
  · exfalso; omega

theorem sgL_mul_self (l : Lt n) (A : Finset (Lt n)) : sgL l A * sgL l A = 1 := by
  unfold sgL
  rw [← mul_pow]
  norm_num

theorem sgL_ne_zero (l : Lt n) (A : Finset (Lt n)) : sgL l A ≠ 0 := by
  unfold sgL
  exact pow_ne_zero _ (by norm_num)

theorem sgL_insert (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∉ A) :
    sgL l (insert m A) = twL l m * sgL l A := by
  unfold sgL twL
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sgL_erase (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∈ A) :
    sgL l (A.erase m) = twL l m * sgL l A := by
  have h1 := sgL_insert l (Finset.notMem_erase m A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, twL_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annL l x A = if l ∈ A then 0 else sgL l A • x (insert l A) := rfl

theorem creL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creL l x A = if l ∈ A then sgL l A • x (A.erase l) else 0 := rfl

theorem liftL_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cq n V) (A : Finset (Lt n)) :
    liftL n T x A = T (x A) := rfl

theorem annL_annL (i j : Lt n) : (annL i * annL j + annL j * annL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, mul_apply_eq_comp, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, ite_false]
  rw [sgL_insert j hi, sgL_insert i hj, twL_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem creL_creL (i j : Lt n) : (creL i * creL j + creL j * creL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, mul_apply_eq_comp, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, ite_true]
  rw [sgL_erase j hi, sgL_erase i hj, twL_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem annL_creL (i j : Lt n) :
    (annL i * creL j + creL j * annL i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, mul_apply_eq_comp, Pi.add_apply, annL_apply, creL_apply,
      one_apply_eq_self]
    by_cases hi : i ∈ A
    · have h1 : i ∉ A.erase i := Finset.notMem_erase i A
      rw [ite_eq_left hi, ite_eq_left hi, ite_eq_right h1, sgL_erase i hi, twL_self, one_mul, Finset.insert_erase hi,
        smul_smul, sgL_mul_self, one_smul, zero_add]
    · have h1 : i ∈ insert i A := Finset.mem_insert_self i A
      rw [ite_eq_right hi, ite_eq_left h1, ite_eq_right hi, sgL_insert i hi, twL_self, one_mul, Finset.erase_insert hi,
        smul_smul, sgL_mul_self, one_smul, add_zero]
  · rw [ite_eq_right hij]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.zero_apply, Pi.add_apply,
      Pi.zero_apply, annL_apply, creL_apply]
    by_cases hi : i ∈ A
    · have hi' : i ∈ A.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
      simp [hi, hi']
    · by_cases hj : j ∈ A
      · have hj' : j ∈ insert i A := Finset.mem_insert_of_mem hj
        have hi' : i ∉ A.erase j := fun hm => hi (Finset.mem_of_mem_erase hm)
        rw [ite_eq_right hi, ite_eq_left hj', ite_eq_left hj, ite_eq_right hi', sgL_insert j hi, sgL_erase i hj,
          twL_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
        have e : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
        rw [e, zero_smul]
      · have hj' : j ∉ insert i A := by simp [hj, Ne.symm hij]
        simp [hi, hj, hj']

theorem annL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annL i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annL_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]

theorem creL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [creL_apply] at h
  by_cases hi : i ∈ A
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]
  · simp [hi] at h

theorem liftL_annL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * annL l : Module.End ℂ (Cq n V)) = annL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [mul_apply_eq_comp, liftL_apply, annL_apply]
  split_ifs <;> simp

theorem liftL_creL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * creL l : Module.End ℂ (Cq n V)) = creL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [mul_apply_eq_comp, liftL_apply, creL_apply]
  split_ifs <;> simp

def adS (S : Lt n → Prop) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  open Classical in ∑ l : Lt n, ∑ k : Lt n, if S l then adCL s p q l k • (creL k * annL l) else 0

def Lv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (kA E1 E2 p q) : Module.End ℂ (Cq n V)) + adLL lev false p q

end GlobalTheory.CompanionTheory.LvChain
