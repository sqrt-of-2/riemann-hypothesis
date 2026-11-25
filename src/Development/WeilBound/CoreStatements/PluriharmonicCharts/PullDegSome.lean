module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section
namespace PositivityTheory.Xgp.c_algsq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def κ₁ (k₀ : K) (k : K) : Option K := if k = k₀ then none else some k

omit [Fintype K] in
theorem κ₁_self [Fintype K] (k₀ : K) : κ₁ k₀ k₀ = none := ite_eq_left rfl

omit [Fintype K] in
theorem κ₁_ne [Fintype K] {k₀ k : K} (h : k ≠ k₀) : κ₁ k₀ k = some k := ite_eq_right h

omit [Fintype K] in
theorem κ₁_inj [Fintype K] (k₀ : K) : Function.Injective (κ₁ k₀) := by
  intro a b h
  unfold κ₁ at h
  split_ifs at h with ha hb hb <;>
    first
    | exact ha.trans hb.symm
    | (cases h; rfl)

omit [(k : K) → Fintype (ι k)] in
theorem isBlockMap_v₁ [(k : K) → Fintype (ι k)] (k₀ : K) :
    IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) (κ₁ k₀) (v₁ k₀) := by
  have h3 : ∀ p : (k : K) × ι k, (v₁ k₀ p).fst = κ₁ k₀ p.fst := fun p => by
    unfold v₁ κ₁
    split_ifs <;> rfl
  refine ⟨κ₁_inj k₀, ?_, h3, ?_⟩
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hfst : κ₁ k₀ a = κ₁ k₀ b := by
      have e := congrArg Sigma.fst h
      rwa [h3, h3] at e
    have hab : a = b := κ₁_inj k₀ hfst
    subst hab
    unfold v₁ at h
    split_ifs at h with ha
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq ((cast_heq _ x).symm.trans (h2.trans (cast_heq _ y)))
      rfl
    · have h2 := (Sigma.mk.inj_iff.mp h).2
      obtain rfl := eq_of_heq h2
      rfl
  · rintro ⟨o, x⟩ ⟨j, hj⟩
    cases o with
    | none =>
      refine ⟨⟨k₀, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_left rfl]
      rfl
    | some k =>
      have hk : k ≠ k₀ := by
        intro hk
        unfold κ₁ at hj
        split_ifs at hj with h1;
          first
          | (cases hj; exact h1 hk)
      refine ⟨⟨k, x⟩, ?_⟩
      unfold v₁
      rw [dite_eq_right hk]

omit [Fintype K] in
theorem pullDeg_some [Fintype K] (xi : K → ℤ) (o : Option K) : pullDeg (some : K → Option K) xi o = o.elim 0 xi := by
  unfold pullDeg
  cases o with
  | none =>
    have hn : ¬∃ a : K, some a = (none : Option K) := by
      rintro ⟨a, ha⟩
      cases ha
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  | some k =>
    exact (Option.some_injective K).extend_apply xi 0 k

theorem pullDeg_κ₁ (k₀ : K) (xi : K → ℤ) (o : Option K) :
    pullDeg (κ₁ k₀) xi o = o.elim (xi k₀) fun k => if k = k₀ then 0 else xi k := by
  unfold pullDeg
  cases o with
  | none =>
    have e := (κ₁_inj k₀).extend_apply xi 0 k₀
    rw [κ₁_self] at e
    exact e
  | some k =>
    by_cases hk : k = k₀
    · have hn : ¬∃ j : K, κ₁ k₀ j = some k := by
        rintro ⟨j, hj⟩
        unfold κ₁ at hj
        split_ifs at hj with h1;
          first
          | (cases hj; exact h1 hk)
      rw [Function.extend_apply' _ _ _ hn]
      simp [hk]
    · have e := (κ₁_inj k₀).extend_apply xi 0 k
      rw [κ₁_ne hk] at e
      rw [e]
      simp [hk]

end PositivityTheory.Xgp.c_algsq
