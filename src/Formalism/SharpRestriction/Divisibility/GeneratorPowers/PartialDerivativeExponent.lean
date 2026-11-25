module

public import Mathlib.RingTheory.PowerSeries.Exp
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

open MvPowerSeries

variable {σ : Type}

variable {k : Type} [CommRing k]

variable [Algebra ℚ k]

omit [Algebra ℚ k] in
private lemma coeff_XX_pow_lemma (d : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) k) ^ d) =
      if e 0 + e 1 = d then ((d.choose (e 0) : ℕ) : k) else 0 := by

  rw [add_pow, map_sum]
  have key : ∀ m ∈ Finset.range (d + 1),
      coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0 := by
    intro m _
    rw [← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq,
      monomial_mul_monomial, coeff_monomial]
    have hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m) := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> simp [h0, h1]
    by_cases h : e 0 = m ∧ e 1 = d - m
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
      simp
    · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, zero_mul]
  rw [Finset.sum_congr rfl key]
  by_cases hd : e 0 + e 1 = d
  · rw [ite_eq_left hd, Finset.sum_eq_single (e 0)]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [ite_eq_right]
      rintro ⟨h, _⟩
      exact hm h.symm
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [ite_eq_right]
    rintro ⟨h0, h1⟩
    omega

omit [Algebra ℚ k] in
private lemma coeff_substX_lemma_2 (i : Fin 2) (f : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp_rw [coeff_X_pow]
  by_cases h : e = Finsupp.single i (e i)
  · rw [ite_eq_left h, finsum_eq_single _ (e i)]
    · rw [ite_eq_left h, smul_eq_mul, mul_one]
    · intro d hd
      rw [ite_eq_right, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · rw [ite_eq_right h]
    have hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0 := by
      intro d
      rw [ite_eq_right, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]

theorem exp_biv :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  ext e
  have hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k) := by
    rw [PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_XX_pow_lemma, ite_eq_left rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_XX_pow_lemma, ite_eq_right (fun h => hd h.symm), smul_zero]
  have hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k) := by
    rw [coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · rw [coeff_substX_lemma_2, coeff_substX_lemma_2, ite_eq_left (by simp), ite_eq_left (by simp)]
      simp
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [coeff_substX_lemma_2, coeff_substX_lemma_2]
      by_cases h1 : p = Finsupp.single 0 (p 0)
      · by_cases h2 : q = Finsupp.single 1 (q 1)
        · exfalso
          apply hne
          have hq0 : q 0 = 0 := by
            rw [h2]
            simp
          have hp1 : p 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hpq 0
          have c1 := DFunLike.congr_fun hpq 1
          simp only [Finsupp.coe_add, Pi.add_apply] at c0 c1
          rw [Prod.mk.injEq]
          constructor
          · rw [h1]
            congr 1
            omega
          · rw [h2]
            congr 1
            omega
        · rw [ite_eq_right h2, mul_zero]
      · rw [ite_eq_right h1, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      ext i
      fin_cases i <;> simp
  rw [hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  have hle : e 0 ≤ e 0 + e 1 := Nat.le_add_right _ _
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    exact_mod_cast h
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← h']
  field_simp

omit [Algebra ℚ k] in
theorem psubst_comp [Algebra ℚ k] {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hb]

theorem expS_add {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by
  have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have h := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))
  rw [psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp),
    psubst_comp _ hb (X 1) (by simp)] at h
  simpa [subst_add hb, subst_X hb] using h

end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
