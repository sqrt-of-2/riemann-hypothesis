module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

namespace UpperTheory.Reformulated.B.StandardLattice

noncomputable def pZ : ℕ → Ideal ℤ :=
  fun l => Ideal.span {↑l}

theorem aux2 : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)],
  (pZ l).IsPrime := by
  intro l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

@[reducible] noncomputable def Ml : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] → (K : Type) → [inst : Field K] → Submonoid (NumberField.RingOfIntegers K) :=
  fun l [Fact (Nat.Prime l)] K [Field K] => by
    letI := aux2 l
    exact Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K)
      (pZ l).primeCompl

@[reducible] noncomputable def Rl : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] → (K : Type) → [Field K] → Type :=
  fun l [Fact (Nat.Prime l)] K [Field K] => Localization (Ml l K)

theorem aux5 : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (K : Type)
  [inst : Field K],
  IsLocalization (Ml l K)
    (Localization (Ml l K)) := by
  intro l hl K inst
  exact Localization.isLocalization

theorem aux6 : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (K : Type)
  [inst : Field K] [NumberField K] (y : ↥(Ml l K)),
  IsUnit ((Algebra.algebraMap (NumberField.RingOfIntegers K) K) ↑y) := by
  intro l hl K inst _ y
  obtain ⟨y, n, hn, rfl⟩ := y
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine isUnit_iff_ne_zero.mpr ?_
  simpa using hn0

noncomputable def rlToK : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] →
    (K : Type) → [inst : Field K] → [NumberField K] → Rl l K →+* K :=
  fun l [Fact (Nat.Prime l)] K [Field K] [NumberField K] =>
    IsLocalization.lift (aux6 l K)

@[reducible] noncomputable def rlAlgebra : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] →
    (K : Type) → [inst : Field K] → [NumberField K] → Algebra (Rl l K) K :=
  fun l [Fact (Nat.Prime l)] K [Field K] [NumberField K] =>
    (rlToK l K).toAlgebra

attribute [local instance] rlAlgebra

@[reducible] noncomputable def rlModule : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] →
    (K : Type) →
      [inst : Field K] →
        [NumberField K] →
          (V : Type) →
            [inst_2 : AddCommGroup V] → [Module K V] → Module (Rl l K) V :=
  fun l [Fact (Nat.Prime l)] K [Field K] [NumberField K] V [AddCommGroup V] [Module K V] =>
    Module.compHom V (Algebra.algebraMap (Rl l K) K)

attribute [local instance] rlModule

noncomputable def atL : (l : ℕ) →
  [hl : Fact (Nat.Prime l)] →
    (K : Type) →
      [inst : Field K] →
        [inst_1 : NumberField K] →
          {V : Type} →
            [inst_2 : AddCommGroup V] →
              [inst_3 : Module K V] →
                [inst_4 : Module (NumberField.RingOfIntegers K) V] →
                  Submodule (NumberField.RingOfIntegers K) V →
                    Submodule (Rl l K) V :=
  fun l [Fact (Nat.Prime l)] K [Field K] [NumberField K] {V} [AddCommGroup V] [Module K V]
      [Module (NumberField.RingOfIntegers K) V] L =>
    Submodule.span (Rl l K) (↑L : Set V)

theorem mem_atL_iff : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (K : Type)
  [inst : Field K] [inst_1 : NumberField K] {V : Type} [inst_2 : AddCommGroup V] [inst_3 : Module K V]
  [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
  {L : Submodule (NumberField.RingOfIntegers K) V} {x : V},
  x ∈ atL l K L ↔
    ∃ s ∈ Ml l K, s • x ∈ L := by
  intro l hl K inst inst_1 V inst_2 inst_3 inst_4 tower L x
  let := rlModule l K V
  have hact : ∀ (r : NumberField.RingOfIntegers K) (v : V),
      (algebraMap (NumberField.RingOfIntegers K) (Rl l K) r) • v = r • v := by
    intro r v
    change rlToK l K (algebraMap _ _ r) • v = r • v
    unfold rlToK
    rw [IsLocalization.lift_eq, algebraMap_smul]
  have : IsScalarTower (NumberField.RingOfIntegers K) (Rl l K) V :=
    IsScalarTower.of_algebraMap_smul hact
  unfold atL
  rw [IsLocalization.mem_span_iff (Ml l K), Submodule.span_eq]
  constructor
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← hact, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← hact, smul_smul]
    have := IsLocalization.mk'_spec (Rl l K) (1 : NumberField.RingOfIntegers K)
      (⟨s, hs⟩ : Ml l K)
    rw [this, map_one, one_smul]

end UpperTheory.Reformulated.B.StandardLattice
