module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.OnePair.coeff_subst_kill {σ R : Type} [CommRing R] [Finite σ] (p : σ → Prop)
    [DecidablePred p] (c : MvPowerSeries σ R) (γ : σ →₀ ℕ) [Decidable (∀ s, ¬ p s → γ s = 0)] :
    coeff γ (subst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) c) =
      if ∀ s, ¬ p s → γ s = 0 then coeff γ c else 0 := by
  classical
  have hsub : HasSubst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) :=
    hasSubst_of_constantCoeff_zero fun s => by split_ifs <;> simp
  have key : ∀ d : σ →₀ ℕ,
      coeff γ (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
        if d = γ ∧ ∀ s, ¬ p s → γ s = 0 then 1 else 0 := by
    intro d
    by_cases hd : ∀ s, ¬ p s → d s = 0
    · have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
          monomial d 1 := by
        rw [monomial_one_eq]
        refine Finsupp.prod_congr fun s hs => ?_
        have hps : p s := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hs) (hd s h)
        rw [ite_eq_left hps]
      rw [hprod, coeff_monomial]
      by_cases hγ : γ = d
      · subst hγ
        rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hd⟩]
      · rw [ite_eq_right hγ, ite_eq_right fun h => hγ h.1.symm]
    · push Not at hd
      obtain ⟨s, hps, hds⟩ := hd
      have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds) (by rw [ite_eq_right hps, zero_pow hds])
      rw [hprod, map_zero, ite_eq_right]
      rintro ⟨rfl, h⟩
      exact hds (h s hps)
  rw [coeff_subst hsub, finsum_eq_single _ γ]
  · rw [key]
    by_cases h : ∀ s, ¬ p s → γ s = 0 <;> simp [h]
  · intro d hd
    rw [key, ite_eq_right fun h => hd h.1, smul_zero]

end OnePair


open CategoryTheory TensorProduct MvPowerSeries in
theorem _root_.GlobalTheory.coeff_at2_single_X_inl_inr (R : Type) [CommRing R] (d : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (_root_.GlobalTheory.Katz.at2 c
      (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m)))) =
      if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  classical
  have hfun : Sum.elim (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m))) = fun s =>
        if (s = Sum.inl m ∨ s = Sum.inr m) then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0 := by
    funext s
    rcases s with i | i <;> by_cases h : i = m <;> simp [h]
  have hiff : (∀ s, ¬ (s = Sum.inl m ∨ s = Sum.inr m) → γ s = 0) ↔
      γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) := by
    constructor
    · intro h
      ext s
      by_cases hs : s = Sum.inl m ∨ s = Sum.inr m
      · rcases hs with rfl | rfl <;> simp
      · push Not at hs
        rw [h s (not_or.mpr hs)]
        simp [Ne.symm hs.1, Ne.symm hs.2]
    · intro h s hs
      push Not at hs
      rw [h]
      simp [Ne.symm hs.1, Ne.symm hs.2]
  unfold _root_.GlobalTheory.Katz.at2
  rw [hfun, _root_.GlobalTheory.OnePair.coeff_subst_kill]
  by_cases hγ : γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (γ (Sum.inr m))
  · rw [ite_eq_left hγ, ite_eq_left (hiff.mpr hγ)]
  · rw [ite_eq_right hγ, ite_eq_right fun h => hγ (hiff.mp h)]

end GlobalTheory
