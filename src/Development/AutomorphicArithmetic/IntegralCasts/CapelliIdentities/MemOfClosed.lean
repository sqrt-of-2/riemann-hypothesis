module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

namespace UpperTheory.Reformulated.B.Qi13

theorem aux1 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K], IsLocalRing ↥(ValuativeRel.valuation K).integer := by
  intro K _ _ _ _
  infer_instance

@[reducible] noncomputable def algRes : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Algebra (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    ZMod.algebra (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l

attribute [local instance] algRes

@[reducible] noncomputable def fdim : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [Fact (Nat.Prime l)] → [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] → ℕ :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    Module.finrank (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

theorem aux4 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Module.Free (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  let := algRes K l
  exact Module.Free.of_divisionRing (ZMod l) _

theorem aux5 : ∀ (l : ℕ) [Fact (Nat.Prime l)], StrongRankCondition (ZMod l) := by
  intro l _
  infer_instance

theorem aux6 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Module.Finite (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) := by
  intro K _ _ _ _ l _ _
  let := algRes K l
  have : Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := inferInstance
  exact Module.Finite.of_finite

attribute [local instance] aux4 aux6

noncomputable def bb : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Module.Basis (Fin (fdim K l)) (ZMod l)
                  (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] =>
    Module.finBasis (ZMod l) (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

theorem aux8 : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l]
  (i : Fin (fdim K l)),
  ∃ a, (IsLocalRing.residue ↥(ValuativeRel.valuation K).integer) a = (bb K l) i := by
  intro K _ _ _ _ l _ _ i
  exact IsLocalRing.residue_surjective _

noncomputable def blift : (K : Type) →
  [inst : Field K] →
    [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] →
        [inst_3 : IsNonarchimedeanLocalField K] →
          (l : ℕ) →
            [inst_4 : Fact (Nat.Prime l)] →
              [inst_5 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] →
                Fin (fdim K l) → ↥(ValuativeRel.valuation K).integer :=
  fun K [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] l [Fact (Nat.Prime l)]
      [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l] i =>
    (aux8 K l i).choose

private theorem key {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    (O : Subring K) {k : Type} [CommRing k] [Algebra (ZMod l) k] (r : O →+* k)
    (hO : ∀ c : ℤ_[l], algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) {ι : Type} [Fintype ι] (x : ι → O)
    (h : LinearIndependent (ZMod l) (fun i => r (x i))) :
    LinearIndependent ℚ_[l] (fun i => (x i : K)) := by
  classical
  let φ : ℤ_[l] →+* O :=
    ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict O hO
  have hφ : ∀ c : ℤ_[l], r (φ c) = algebraMap (ZMod l) k (PadicInt.toZMod c) := by
    intro c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZMod c)
    have hker : c - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
    obtain ⟨d, hd⟩ := hker
    have hl : (l : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod l) k), ZMod.natCast_self, map_zero]
    have hc : c = n + l * d := by rw [← hd]; ring
    rw [← hn, hc]
    simp only [map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖g i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖g m‖ := (norm_pos_iff.mpr hi₀).trans_le (hm i₀ (Finset.mem_univ _))
  have hgm : g m ≠ 0 := norm_pos_iff.mp hpos
  let c : ι → ℤ_[l] := fun i => ⟨g i / g m, by
    rw [PadicInt.mem_subring_iff]
    rw [norm_div]
    exact (div_le_one hpos).mpr (hm i (Finset.mem_univ _))⟩
  have hsum : ∑ i, φ (c i) * x i = 0 := by
    apply Subtype.ext
    have h1 : ∀ i, ((φ (c i) * x i : O) : K) = (g m)⁻¹ • (g i • (x i : K)) := by
      intro i
      change algebraMap ℚ_[l] K (g i / g m) * (x i : K) = _
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul]
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [h1]
    rw [← Finset.smul_sum, hg, smul_zero]
    rfl
  have hred : ∑ i, PadicInt.toZMod (c i) • r (x i) = 0 := by
    have h2 := congrArg r hsum

    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφ, Algebra.smul_def]
  have h3 := h _ hred m
  have h4 : c m = 1 := Subtype.ext (div_self hgm)
  rw [h4, map_one] at h3
  exact one_ne_zero h3

private theorem mem_of_closed {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [TopologicalSpace K] [Algebra ℚ_[l] K] (O : Subring K) (hO : IsClosed (O : Set K))
    (hc : Continuous (algebraMap ℚ_[l] K)) (c : ℤ_[l]) :
    algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O := by
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun c : ℤ_[l] => algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) c ?_ ?_
  · exact hO.preimage (hc.comp continuous_subtypeVal)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem O n

theorem linIndep : ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K]
  [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (l : ℕ) [inst_4 : Fact (Nat.Prime l)]
  [inst_5 : Algebra ℚ_[l] K] [inst_6 : CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l],
  Continuous ⇑(Algebra.algebraMap ℚ_[l] K) →
    LinearIndependent ℚ_[l] fun i => (blift K l i : K) := by
  intro K _ _ _ _ l _ _ _ hc
  let := algRes K l
  refine key (ValuativeRel.valuation K).integer
    (IsLocalRing.residue (ValuativeRel.valuation K).integer)
    (mem_of_closed _ Valuation.isClosed_integer hc)
    (blift K l) ?_
  have h : (fun i => IsLocalRing.residue (ValuativeRel.valuation K).integer
      (blift K l i)) = bb K l :=
    funext fun i => (aux8 K l i).choose_spec
  rw [h]
  exact (bb K l).linearIndependent

end UpperTheory.Reformulated.B.Qi13
