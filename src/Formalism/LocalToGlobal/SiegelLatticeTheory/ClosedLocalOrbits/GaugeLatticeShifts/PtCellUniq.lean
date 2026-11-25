module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpUMul
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.L2.SG.PtCell

open Matrix

variable {K : Type*} [Field K] {N : ℕ}

def LoU (L : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)

def UpU (U : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)

theorem loU_bt {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : L.BlockTriangular OrderDual.toDual :=
  fun i j hij => (h i j).1 hij

theorem upU_bt {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : U.BlockTriangular id :=
  fun i j hij => (h i j).1 hij

theorem loU_det {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (loU_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem upU_det {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : U.det = 1 := by
  rw [det_of_isUpperTriangular (upU_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem loU_mul {A B : Matrix (Fin N) (Fin N) K} (hA : LoU A) (hB : LoU B) : LoU (A * B) := by
  intro i j
  refine ⟨fun hij => (BlockTriangular.mul (loU_bt hA) (loU_bt hB)) hij, fun hij => ?_⟩
  subst hij
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hB k i).1 h, mul_zero]
    · rw [(hA i k).1 h, zero_mul]
  · simp

theorem upU_mul {A B : Matrix (Fin N) (Fin N) K} (hA : UpU A) (hB : UpU B) : UpU (A * B) := by
  first | (apply UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption)

theorem loU_inv {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : LoU L⁻¹ := by
  have hu : IsUnit L.det := by rw [loU_det h]; exact isUnit_one
  have := invertibleOfIsUnitDet L hu
  have hbt : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular (loU_bt h)
  intro i j
  refine ⟨fun hij => hbt hij, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (mul_nonsing_inv L hu) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [hbt h', mul_zero]
    · rw [(h i k).1 h', zero_mul]
  · simp

theorem upU_inv {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : UpU U⁻¹ := by
  have hu : IsUnit U.det := by rw [upU_det h]; exact isUnit_one
  have := invertibleOfIsUnitDet U hu
  have hbt : U⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular (upU_bt h)
  intro i j
  refine ⟨fun hij => hbt hij, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (mul_nonsing_inv U hu) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [(h i k).1 h', zero_mul]
    · rw [hbt h', mul_zero]
  · simp

theorem eq_self_of_le {f : Fin N → Fin N} (hf : Function.Injective f) (hle : ∀ a, f a ≤ a) (a : Fin N) : f a = a := by
  suffices h : ∀ n (a : Fin N), a.val = n → f a = a from h _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    rcases (hle a).lt_or_eq with hlt | heq
    · have h1 : f (f a) = f a := ih (f a).val (by rw [← ha]; exact hlt) (f a) rfl
      exact absurd (hf h1) (ne_of_lt hlt)
    · exact heq

def mono (π : Fin N → Fin N) (c : Fin N → K) : Matrix (Fin N) (Fin N) K := fun a b => if b = π a then c a else 0

theorem mul_mono_apply (A : Matrix (Fin N) (Fin N) K) {π : Fin N → Fin N} (hπ : ∀ a, π (π a) = a) (c : Fin N → K)
    (a b : Fin N) : (A * mono π c) a b = A a (π b) * c (π b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π b)]
  · simp [mono, hπ]
  · intro k _ hk
    have : b ≠ π k := fun hb => hk (by rw [hb, hπ])
    simp [mono, this]
  · simp

theorem mono_mul_apply (A : Matrix (Fin N) (Fin N) K) (π : Fin N → Fin N) (c : Fin N → K) (a b : Fin N) :
    (mono π c * A) a b = c a * A (π a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π a)]
  · simp [mono]
  · intro k _ hk
    simp [mono, hk]
  · simp

theorem mono_uniq {π ρ : Fin N → Fin N} (hπ : ∀ a, π (π a) = a) (hρ : ∀ a, ρ (ρ a) = a) {c d : Fin N → K}
    (hd : ∀ a, d a ≠ 0) {L₁ L₂ U₁ U₂ : Matrix (Fin N) (Fin N) K} (hL₁ : LoU L₁) (hL₂ : LoU L₂)
    (hU₁ : UpU U₁) (hU₂ : UpU U₂) (h : L₁ * mono π c * U₁ = L₂ * mono ρ d * U₂) : π = ρ ∧ c = d := by
  have hu1 : IsUnit U₁.det := by rw [upU_det hU₁]; exact isUnit_one
  have hu2 : IsUnit L₂.det := by rw [loU_det hL₂]; exact isUnit_one
  have key : L₂⁻¹ * L₁ * mono π c = mono ρ d * (U₂ * U₁⁻¹) := by
    have h' : L₁ * (mono π c * U₁) = L₂ * (mono ρ d * U₂) := by simpa only [Matrix.mul_assoc] using h
    have e1 : L₂⁻¹ * L₁ * mono π c = L₂⁻¹ * ((L₁ * (mono π c * U₁)) * U₁⁻¹) := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu1, Matrix.mul_one]
    have e2 : L₂⁻¹ * ((L₂ * (mono ρ d * U₂)) * U₁⁻¹) = mono ρ d * (U₂ * U₁⁻¹) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc L₂⁻¹ L₂, nonsing_inv_mul _ hu2, Matrix.one_mul]
    rw [e1, h', e2]
  have hL := loU_mul (loU_inv hL₂) hL₁
  have hU := upU_mul hU₂ (upU_inv hU₁)
  have e : ∀ a b, (L₂⁻¹ * L₁) a (π b) * c (π b) = d a * (U₂ * U₁⁻¹) (ρ a) b := by
    intro a b
    have := congrFun (congrFun key a) b
    rwa [mul_mono_apply _ hπ, mono_mul_apply] at this
  have hle : ∀ a, π (ρ a) ≤ a := by
    intro a
    have h1 := e a (ρ a)
    rw [(hU (ρ a) (ρ a)).2 rfl, mul_one] at h1
    by_contra hlt
    push Not at hlt
    rw [(hL a (π (ρ a))).1 hlt, zero_mul] at h1
    exact hd a h1.symm
  have hinj : Function.Injective (fun a => π (ρ a)) := by
    intro a b hab
    have := congrArg π hab
    simp only [hπ] at this
    simpa [hρ] using congrArg ρ this
  have hid : ∀ a, π (ρ a) = a := eq_self_of_le hinj hle
  have hpr : π = ρ := by
    funext a
    simpa only [hρ] using hid (ρ a)
  refine ⟨hpr, ?_⟩
  funext a
  have h2 := e a (π a)
  rw [hπ, (hL a a).2 rfl, one_mul, ← hpr, (hU (π a) (π a)).2 rfl, mul_one] at h2
  exact h2

section Pt

open Formalism.MainNotions.S

def pperm : List (K × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pperm bs (i - s)

def pval : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, i => if i < s then t else pval bs (i - s)

theorem ptEntry_eq (bs : List (K × ℕ)) (i j : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    ptEntry bs i j = if j = pperm bs i then pval bs i else 0 := by
  induction bs generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases his : i < s
    · by_cases hjs : j < s
      · simp only [ptEntry, pperm, pval, his, hjs, and_self, ite_true]
        by_cases h : i + j + 1 = s
        · rw [ite_eq_left h, ite_eq_left (by omega)]
        · rw [ite_eq_right h, ite_eq_right (by omega)]
      · have hn : ¬ (s ≤ i ∧ s ≤ j) := by omega
        simp only [ptEntry, pperm, pval, his, hjs, and_false, ite_false, ite_true, hn]
        rw [ite_eq_right (by omega)]
    · by_cases hjs : s ≤ j
      · have hsi : s ≤ i := by omega
        simp only [ptEntry, pperm, pval, his, false_and, ite_false, hsi, hjs, and_self, ite_true]
        rw [ih (i - s) (j - s) (by omega)]
        by_cases h : j - s = pperm bs (i - s)
        · rw [ite_eq_left h, ite_eq_left (by omega)]
        · rw [ite_eq_right h, ite_eq_right (by omega)]
      · simp only [ptEntry, pperm, pval, his, false_and, ite_false, hjs, and_false]
        rw [ite_eq_right (by omega)]

omit [Field K] in
theorem pperm_lt [Field K] (bs : List (K × ℕ)) (hpos : ∀ b ∈ bs, 1 ≤ b.2) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pperm bs i < (bs.map Prod.snd).sum := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    have hs : 1 ≤ s := hpos (t, s) (by simp)
    have hpos' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb => hpos b (by simp [hb])
    simp only [pperm]
    split_ifs with h
    · omega
    · have := ih hpos' (i - s) (by omega)
      omega

omit [Field K] in
theorem pperm_pperm [Field K] (bs : List (K × ℕ)) (hpos : ∀ b ∈ bs, 1 ≤ b.2) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pperm bs (pperm bs i) = i := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    have hpos' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb => hpos b (by simp [hb])
    by_cases h : i < s
    · simp only [pperm, h, ite_true]
      rw [ite_eq_left (by omega)]
      omega
    · simp only [pperm, h, ite_false]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ih hpos' (i - s) (by omega)]
      omega

theorem pval_ne (bs : List (K × ℕ)) (ht : ∀ b ∈ bs, b.1 ≠ 0) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pval bs i ≠ 0 := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    have ht' : ∀ b ∈ bs, b.1 ≠ 0 := fun b hb => ht b (by simp [hb])
    simp only [pval]
    split_ifs with h
    · exact ht (t, s) (by simp)
    · exact ih ht' (i - s) (by omega)

theorem blocks_eq_of (bs : List (K × ℕ)) (cs : List (K × ℕ)) (hb : ∀ b ∈ bs, 1 ≤ b.2) (hc : ∀ c ∈ cs, 1 ≤ c.2)
    (hsum : (bs.map Prod.snd).sum = (cs.map Prod.snd).sum)
    (hp : ∀ i < (bs.map Prod.snd).sum, pperm bs i = pperm cs i)
    (hv : ∀ i < (bs.map Prod.snd).sum, pval bs i = pval cs i) : bs = cs := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      have : 1 ≤ c.2 := hc c (by simp)
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum
      omega
  | cons b bs ih =>
    cases cs with
    | nil =>
      have : 1 ≤ b.2 := hb b (by simp)
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum
      omega
    | cons c cs =>
      obtain ⟨t, s⟩ := b
      obtain ⟨t', s'⟩ := c
      have hs : 1 ≤ s := hb (t, s) (by simp)
      have hs' : 1 ≤ s' := hc (t', s') (by simp)
      have hb' : ∀ b ∈ bs, 1 ≤ b.2 := fun b h => hb b (by simp [h])
      have hc' : ∀ c ∈ cs, 1 ≤ c.2 := fun c h => hc c (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hsum hp hv
      have h0 := hp 0 (by omega)
      have v0 := hv 0 (by omega)
      simp only [pperm, pval, show 0 < s by omega, show 0 < s' by omega, ite_true] at h0 v0
      have hss : s = s' := by omega
      subst hss
      subst v0
      have htail : bs = cs := by
        refine ih cs hb' hc' (by omega) (fun i hi => ?_) (fun i hi => ?_)
        · have := hp (s + i) (by omega)
          simp only [pperm, show ¬ (s + i < s) by omega, ite_false, Nat.add_sub_cancel_left] at this
          omega
        · have := hv (s + i) (by omega)
          simpa only [pval, show ¬ (s + i < s) by omega, ite_false, Nat.add_sub_cancel_left] using this
      rw [htail]

def pinv (p : Point K N) (a : Fin N) : Fin N :=
  ⟨pperm p.1 a.val, by
    have := pperm_lt p.1 (fun b hb => (p.2.1 b hb).2) a.val (by rw [p.2.2]; exact a.isLt)
    rwa [p.2.2] at this⟩

theorem pinv_pinv (p : Point K N) (a : Fin N) : pinv p (pinv p a) = a := by
  apply Fin.ext
  exact pperm_pperm p.1 (fun b hb => (p.2.1 b hb).2) a.val (by rw [p.2.2]; exact a.isLt)

theorem ptMat_eq_mono (p : Point K N) : ptMat p = mono (pinv p) (fun a => pval p.1 a.val) := by
  funext a b
  simp only [ptMat, mono, pinv]
  rw [ptEntry_eq p.1 a.val b.val (by rw [p.2.2]; exact a.isLt)]
  congr 1
  simp [Fin.ext_iff]

theorem isInCell_uniq {Z : Matrix (Fin N) (Fin N) K} {p q : Point K N} (hp : IsInCell Z p) (hq : IsInCell Z q) :
    p = q := by
  obtain ⟨L₁, U₁, hL₁, hU₁, e₁⟩ := hp
  obtain ⟨L₂, U₂, hL₂, hU₂, e₂⟩ := hq
  rw [ptMat_eq_mono] at e₁ e₂
  obtain ⟨hπ, hc⟩ := mono_uniq (pinv_pinv p) (pinv_pinv q)
    (fun a => pval_ne q.1 (fun b hb => (q.2.1 b hb).1) a.val (by rw [q.2.2]; exact a.isLt))
    hL₁ hL₂ hU₁ hU₂ (e₁.symm.trans e₂)
  apply Subtype.ext
  refine blocks_eq_of p.1 q.1 (fun b hb => (p.2.1 b hb).2) (fun b hb => (q.2.1 b hb).2) (by rw [p.2.2, q.2.2])
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [p.2.2] at hi
    have := congrArg Fin.val (congrFun hπ ⟨i, hi⟩)
    simpa [pinv] using this
  · rw [p.2.2] at hi
    simpa using congrFun hc ⟨i, hi⟩

end Pt

end Formalism.L2.SG.PtCell
