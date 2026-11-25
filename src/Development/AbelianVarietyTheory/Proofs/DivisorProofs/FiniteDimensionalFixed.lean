module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations, Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Module.Constructions\npublic import Mathlib.RepresentationTheory.Semisimple\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.InnerProductSpace.Orthogonal\npublic import Mathlib.Analysis.InnerProductSpace.Projection.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ,
        zero_mem' := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux3 ρ H χ, smul_mem' := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth ρ ∧
        ∀ (K : Subgroup G),
          IsOpen (↑K : Set G) → IsCompact (↑K : Set G) → FiniteDimensional k ↥(UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K)

private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed {H V : Type} [Group H] [AddCommGroup V]
    [_root_.Module ℂ V] {ρ : Representation ℂ H V} {K : Subgroup H} {v : V} :
    v ∈ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h' := (show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v from h) ⟨k, hk⟩
    simpa using h'
  · intro h
    show ∀ h : ↥K, ρ (h : H) v = (↑((1 : ↥K →* ℂˣ) h) : ℂ) • v
    intro k
    simpa using h k k.2

private theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed {H V : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ρ : Representation ℂ H V} (hsm : UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsSmooth ρ)
    (hun : ∀ (g : H) (x y : V), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    {K : Subgroup H} (hK : IsCompact (K : Set H)) (W : Subrepresentation ρ) {u : V}
    (hu : ∀ k ∈ K, ρ k u = u)
    (hperp : ∀ s ∈ W.toSubmodule, (∀ k ∈ K, ρ k s = s) → inner ℂ s u = 0)
    {w : V} (hw : w ∈ W.toSubmodule) : inner ℂ w u = 0 := by
  have hopen : ∀ x : H, IsOpen {g : H | ρ g w = ρ x w} := by
    intro x
    have h1 : IsOpen ((fun g : H => x⁻¹ * g) ⁻¹' {g : H | ρ g w = w}) :=
      (hsm w).preimage (continuous_const.mul continuous_id)
    convert h1 using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul, mul_apply_eq_comp]
    constructor
    · intro h
      rw [h, ← mul_apply_eq_comp, ← map_mul]
      simp
    · intro h
      have h2 := congrArg (ρ x) h
      rw [← mul_apply_eq_comp (ρ x), ← map_mul] at h2
      simpa using h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x : H => {g : H | ρ g w = ρ x w})
    (fun x _ => (hopen x).mem_nhds rfl)
  classical
  have hfin : {y : V | ∃ k ∈ K, ρ k w = y}.Finite := by
    refine (t.image (fun x => ρ x w)).finite_toSet.subset ?_
    rintro y ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hkx⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, hkx.symm⟩)
  have hO : ∀ y, y ∈ hfin.toFinset ↔ ∃ k ∈ K, ρ k w = y := by
    intro y
    simp
  have hsW : (∑ y ∈ hfin.toFinset, y) ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ ?_
    intro y hy
    obtain ⟨k, -, rfl⟩ := (hO y).mp hy
    exact W.apply_mem_toSubmodule k hw
  have hsfix : ∀ k ∈ K, ρ k (∑ y ∈ hfin.toFinset, y) = ∑ y ∈ hfin.toFinset, y := by
    intro k hk

    rw [map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k * l, K.mul_mem hk hl, ?_⟩
      rw [map_mul, mul_apply_eq_comp]
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := (hO y).mp hy
      refine (hO _).mpr ⟨k⁻¹ * l, K.mul_mem (K.inv_mem hk) hl, ?_⟩
      rw [map_mul, mul_apply_eq_comp]
    · intro y _
      show ρ k⁻¹ (ρ k y) = y
      rw [← mul_apply_eq_comp, ← map_mul]
      simp
    · intro y _
      show ρ k (ρ k⁻¹ y) = y
      rw [← mul_apply_eq_comp, ← map_mul]
      simp
    · intro y _
      rfl
  have hsum := hperp _ hsW hsfix
  rw [sum_inner] at hsum
  have hconst : ∀ y ∈ hfin.toFinset, inner ℂ y u = inner ℂ w u := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (hO y).mp hy
    rw [← hun k w u, hu k hk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨w, (hO w).mpr ⟨1, K.one_mem, ?_⟩⟩)
    simp
  exact (mul_eq_zero.mp hsum).resolve_left hcard

theorem UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple :
    ∀ {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [IsTopologicalGroup H] {V : Type}
      [inst_3 : NormedAddCommGroup V] [inst_4 : InnerProductSpace ℂ V] {ρ : Representation ℂ H V},
      UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.IsAdmissible ρ →
        (∀ (g : H) (x y : V),
            Inner.inner ℂ (((ρ : H → V →ₗ[ℂ] V) g : V → V) x) (((ρ : H → V →ₗ[ℂ] V) g : V → V) y) = Inner.inner ℂ x y) →
          ∀ {K₀ : Subgroup H}, IsOpen (↑K₀ : Set H) → IsCompact (↑K₀ : Set H) → ρ.IsSemisimpleRepresentation := by
  intro H _ _ _ V _ _ ρ hadm hun K₀ hK₀o hK₀c
  refine ⟨fun W => ?_⟩
  have hinv : ∀ (g : H) ⦃v : V⦄, v ∈ W.toSubmoduleᗮ → ρ g v ∈ W.toSubmoduleᗮ := by
    intro g v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro w hw
    have h1 : ρ g (ρ g⁻¹ w) = w := by
      rw [← mul_apply_eq_comp, ← map_mul]
      simp
    rw [← h1, hun]
    exact hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
  refine ⟨⟨W.toSubmoduleᗮ, hinv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    exact W.toSubmodule.inf_orthogonal_eq_bot
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule ⊔ W.toSubmoduleᗮ = ⊤
    rw [eq_top_iff]
    intro v _
    let S : Subgroup H :=
      { carrier := {g : H | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          show ρ (a * b) v = v
          rw [map_mul, mul_apply_eq_comp, show ρ b v = v from hb, show ρ a v = v from ha]
        one_mem' := by
          show ρ 1 v = v
          simp
        inv_mem' := by
          intro a ha
          show ρ a⁻¹ v = v
          have h2 : ρ a⁻¹ (ρ a v) = v := by
            rw [← mul_apply_eq_comp, ← map_mul]
            simp
          rwa [show ρ a v = v from ha] at h2 }
    let K : Subgroup H := K₀ ⊓ S
    have hKo : IsOpen (K : Set H) := hK₀o.inter (hadm.1 v)
    have hKc : IsCompact (K : Set H) :=
      hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
    have : FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K) := hadm.2 K hKo hKc
    let A : Submodule ℂ V := W.toSubmodule ⊓ UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.fixed ρ K
    have : FiniteDimensional ℂ ↥A := Submodule.finiteDimensional_inf_right _ _
    have : CompleteSpace ↥A := FiniteDimensional.completeSpace ℂ ↥A
    obtain ⟨a, ha, u, hu, hv⟩ := A.exists_add_mem_mem_orthogonal v
    have hafix : ∀ k ∈ K, ρ k a = a := UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mp ha.2
    have hufix : ∀ k ∈ K, ρ k u = u := by
      intro k hk
      have hvk : ρ k v = v := hk.2
      rw [hv, map_add (f := _), hafix k hk] at hvk
      exact add_left_cancel hvk
    have huW : u ∈ W.toSubmoduleᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      exact UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.inner_eq_zero_of_fixed hadm.1 hun hKc W hufix
        (fun s hs hsf => (Submodule.mem_orthogonal _ _).mp hu s
          ⟨hs, UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.mem_fixed.mpr hsf⟩) hw
    rw [hv]
    exact Submodule.add_mem_sup ha.1 huW
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite\npublic import Mathlib.RepresentationTheory.Semisimple\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem\nimport Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations\nimport Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.CuspMult GlobalTheory.PRep
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDec

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mem_fixed {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X} {K : Subgroup H} {x : X} :
    x ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixed, eig]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ρ : Representation ℂ H V}

theorem isSemisimple (ha : IsAdmissible ρ) (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {K₀ : Subgroup H}
    (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : ρ.IsSemisimpleRepresentation :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc

omit [IsTopologicalGroup H] in
theorem mem_irrSum [IsTopologicalGroup H] {W X : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ H W}
    {ρ : Representation ℂ H X} {C : Submodule ℂ X} (h1 : σ.IsSemisimpleRepresentation) (h2 : IsAdmissible σ)
    {f : W →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  have := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1
  have hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ H) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hs
  refine Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    obtain ⟨U, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m
    have hU : U.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      have : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm
      exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)
    exact GlobalTheory.RepCount.apply_mem_irrSum hU
      (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2)
      (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩
  · simp
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem isDecomp_of_form {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (hC : ∀ g, ∀ x ∈ C, ρ g x ∈ C) (B : X → X → ℂ)
    (hl : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z ∧ B y x = star (B x y))
    (hp : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) (hi : ∀ g, ∀ x ∈ C, ∀ y ∈ C, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ fixed ρ K))
    {K₀ : Subgroup H} (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : IsDecomp ρ C := by
  intro x hx hx'
  let A : Subrepresentation ρ := ⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩
  have hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y) := fun x hx y hy => (hl x hx y hy y hy 0).2
  have h0 : ∀ x ∈ C, B x 0 = 0 := fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1
  let cd : InnerProductSpace.Core ℂ A.toSubmodule :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm
      re_inner_nonneg := fun a => by
        by_cases h : (a : X) = 0
        · simp [h, h0 0 C.zero_mem]
        · exact (hp _ a.2.1 h).le
      add_left := fun a b c => by
        have := (hl _ c.2.1 _ a.2.1 _ b.2.1 1).1
        rw [one_smul, one_mul] at this
        show B (a + b) c = B a c + B b c
        rw [hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]
      smul_left := fun a b r => by
        have := (hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1
        rw [zero_add, h0 _ b.2.1, zero_add] at this
        show B (r • a) b = star r * B a b
        rw [hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]
      definite := fun a h => by
        by_contra hn
        have := hp _ a.2.1 fun e => hn (Subtype.ext e)
        rw [show B a a = 0 from h] at this
        simp at this }
  have ha : IsAdmissible A.toRepresentation := by
    refine ⟨fun v => ?_, fun K hK _ => ?_⟩
    · have : {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v} := by
        ext g
        exact Subtype.ext_iff
      rw [this]
      exact v.2.2
    · have := hf K hK
      refine FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K)
        (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_
      have h' : (a.1 : X) = b.1 := congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
  have hs : A.toRepresentation.IsSemisimpleRepresentation := by
    let := cd.toNormedAddCommGroup
    let := InnerProductSpace.ofCore cd.toCore
    exact isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc
  exact mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩

end Abstract

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : DSModel V S}

theorem finRep_mem (g : GfC V) (T : MMap M) (hT : T ∈ allMaps θ M) : finRep M g T ∈ allMaps θ M := by
  have e : finRep M g T = heckeOn M {(g : GA D V)} T := by
    ext v x
    simp [heckeOn, postOn_apply, heckeLin_apply, finRep_apply]
  rw [e]
  exact Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)

theorem isMultiplicityInner_finRep {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (g : GfC V) {T T' : MMap M} (hT : T ∈ allMaps θ M) (hT' : T' ∈ allMaps θ M)
    {c : ℂ} (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 (finRep M g T) (finRep M g T') c := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  intro v v'
  have := GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by
    rw [(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]
  exact ⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩

theorem finiteDimensional_fixed (hP : GlobalTheory.Published.HarishChandraFinite) (hθ : IsInfFam θ) (K : Subgroup (GfC V))
    (hK : IsOpen (K : Set (GfC V))) : FiniteDimensional ℂ ↥(allMaps θ M ⊓ fixed (finRep M) K) := by
  obtain ⟨N, hN, e⟩ := isOpen_induced_iff.1 hK
  have hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K := fun k => Set.ext_iff.1 e k
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))
  have := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ
    ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_
  have h := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩
  have := congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))
  rw [one_mul]
  exact this

theorem exists_compact_open (V : HSp D) : ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) := by
  obtain ⟨_, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨N, hN, h1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1
  refine ⟨U.subgroupOf (GfC V), hU.preimage continuous_subtypeVal, ?_⟩
  refine ((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset
    ((U.isClosed_of_isOpen hU).preimage continuous_subtypeVal) fun k hk => hUN k hk k.2

theorem cuspDecomp : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, CuspDecomp D := by
  intro hP hQ D θ hθ V S M
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, hF⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2
  have hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕 := GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨K, ho, hc⟩ := exists_compact_open V
  refine isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_)
    (finiteDimensional_fixed hP hθ) ho hc
  have h := isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))
  exact hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h

end GlobalTheory.CuspDec

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed =====
