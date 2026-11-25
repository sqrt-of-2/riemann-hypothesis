module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Group.Units

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct", "h": "module\n\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Basic\npublic import Mathlib.Topology.Algebra.Group.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Topology.Algebra.OpenSubgroup\n\n"}
section -- clump:auto
@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Gwa2.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

noncomputable def UpperTheory.Reformulated.B.Gwa2.twKer :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      Submodule.span k
        {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[k] V) (↑n : G) : V → V) v - (↑((ψ : ↥N → kˣ) n) : k) • v}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa2.TwJacquet :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (N : Subgroup G) → (↥N →* kˣ) → Type :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V) (N : Subgroup G)
        (ψ : ↥N →* kˣ) ↦
      V ⧸ UpperTheory.Reformulated.B.Gwa2.twKer ρ N ψ

theorem UpperTheory.Reformulated.B.Gwa2.aux4 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (m : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m)) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs m
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
  have key : ρ (s m * (n : G) * (s m)⁻¹) (ρ (s m) v) = ρ (s m) (ρ (n : G) v) := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right, map_mul, mul_apply_eq_comp]
  rw [hθ, map_sub, map_smul, ← key]

theorem UpperTheory.Reformulated.B.Gwa2.aux5 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        Submodule.span ℂ
            {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
          Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs 1

theorem UpperTheory.Reformulated.B.Gwa2.aux6 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (1 : M)))
          (UpperTheory.Reformulated.B.Gwa2.aux5 ρ N θ s hs) =
        (1 : UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s 1) v) = Submodule.Quotient.mk v
  rw [map_one, map_one, one_apply_eq_self]

theorem UpperTheory.Reformulated.B.Gwa2.aux7 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G),
      (∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
        ∀ (a b : M),
          Submodule.span ℂ
              {w : V | ∃ (n : ↥N) (v : V), w = ((ρ : G → V →ₗ[ℂ] V) (↑n : G) : V → V) v - (↑((θ : ↥N → ℂˣ) n) : ℂ) • v} ≤
            Submodule.comap ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b))) (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  exact UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs (a * b)

theorem UpperTheory.Reformulated.B.Gwa2.aux8 :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) {M : Type} [inst_3 : Group M] (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n)
      (a b : M),
      (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) (a * b)))
          (UpperTheory.Reformulated.B.Gwa2.aux7 ρ N θ s hs a b) =
        (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) a))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs a) *
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) b))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs b) := by
  intro G V _ _ _ ρ N θ M _ s hs a b
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
  rw [map_mul, map_mul, mul_apply_eq_comp]

noncomputable def UpperTheory.Reformulated.B.Gwa2.twAct :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] →
          [inst_2 : _root_.Module ℂ V] →
            (ρ : Representation ℂ G V) →
              (N : Subgroup G) →
                (θ : ↥N →* ℂˣ) →
                  {M : Type} →
                    [inst_3 : Group M] →
                      (s : M →* G) →
                        (∀ (m : M) (n : ↥N),
                            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
                              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) →
                          Representation ℂ M (UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ) :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (N : Subgroup G)
        (θ : ↥N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
        (hs :
          ∀ (m : M) (n : ↥N),
            ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
              (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n) ↦
      {
        toFun := fun (m : M) ↦
          (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ).mapQ (UpperTheory.Reformulated.B.Gwa2.twKer ρ N θ) ((ρ : G → V →ₗ[ℂ] V) ((s : M → G) m))
            (UpperTheory.Reformulated.B.Gwa2.aux4 ρ N θ s hs m),
        map_one' := UpperTheory.Reformulated.B.Gwa2.aux6 ρ N θ s hs, map_mul' := UpperTheory.Reformulated.B.Gwa2.aux8 ρ N θ s hs :
        M →* UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ →ₗ[ℂ] UpperTheory.Reformulated.B.Gwa2.TwJacquet ρ N θ }

private theorem UpperTheory.Reformulated.B.Gwa2.isOpen_fixer {M W : Type} [Group M] [AddCommGroup W] [_root_.Module ℂ W]
    [TopologicalSpace M] [IsTopologicalGroup M] (τ : Representation ℂ M W) (x : W)
    (h : {m : M | τ m x = x} ∈ nhds (1 : M)) : IsOpen {m : M | τ m x = x} := by
  let H : Subgroup M :=
    { carrier := {m : M | τ m x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : τ a x = x) (hb : τ b x = x) ↦ show τ (a * b) x = x by
        rw [map_mul, mul_apply_eq_comp, hb, ha]
      inv_mem' := fun {a} (ha : τ a x = x) ↦ show τ a⁻¹ x = x by
        conv_lhs => rw [← ha]
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] }
  exact H.isOpen_of_mem_nhds h

theorem UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct :
    ∀ {G M V : Type} [inst : Group G] [inst_1 : Group M] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℂ V]
      [inst_4 : TopologicalSpace G] [inst_5 : TopologicalSpace M] [IsTopologicalGroup M] (ρ : Representation ℂ G V)
      (N : Subgroup G) (θ : ↥N →* ℂˣ) (s : M →* G)
      (hs :
        ∀ (m : M) (n : ↥N),
          ∃ (h : (s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹ ∈ N),
            (θ : ↥N → ℂˣ) (⟨(s : M → G) m * (↑n : G) * ((s : M → G) m)⁻¹, h⟩ : ↥N) = (θ : ↥N → ℂˣ) n),
      Continuous (⇑s : M → G) → UpperTheory.Reformulated.B.Gwa2.IsSmooth ρ → UpperTheory.Reformulated.B.Gwa2.IsSmooth (UpperTheory.Reformulated.B.Gwa2.twAct ρ N θ s hs) := by
  intro G M V _ _ _ _ _ _ _ ρ N θ s hs hc hρ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine UpperTheory.Reformulated.B.Gwa2.isOpen_fixer _ _ ?_
  have hU : IsOpen {m : M | ρ (s m) v = v} := (hρ v).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun m (hm : ρ (s m) v = v) ↦ ?_
  change Submodule.Quotient.mk (ρ (s m) v) = Submodule.Quotient.mk v
  rw [hm]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSmooth

section General

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_twAct [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hc : Continuous s) (hρ : IsSmooth ρ) : IsSmooth (twAct ρ N θ s hs) :=
  _root_.UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct ρ N θ s hs hc hρ

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem continuous_glEmbHom [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j => simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simpa [glEmbMat] using (continuous_id.matrix_elem i j)

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) :=
  Continuous.units_map _ (continuous_glEmbHom n)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) :=
  (continuous_glEmb n).subtype_mk _

theorem smPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SmPhiMinus k := by
  intro ψ n V _ _ τ hτ
  exact isSmooth_twAct τ (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n)
    ((continuous_levi (n + 1)).comp continuous_subtypeVal) hτ

end GlobalTheory.CompanionTheory.BZMirSmooth

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus =====
