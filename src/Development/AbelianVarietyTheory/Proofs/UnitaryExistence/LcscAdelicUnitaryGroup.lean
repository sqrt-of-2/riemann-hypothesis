module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.RingTheory.TensorProduct.Free
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem, Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem", "h": "module\n\npublic import Mathlib.Topology.Algebra.Module.ModuleTopology\npublic import Mathlib.Topology.Instances.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.SetTheory.ZFC.PSet\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.TensorProduct.Free\n\n"}
section -- clump:auto
@[expose] public section

namespace UpperTheory.Reformulated.B.Yzd4

noncomputable def cT : {A : Type} →
  [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
  fun {A} [CommRing A] σ {m p} M => (M.map ⇑σ).transpose

private theorem cT_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (a b : Matrix n n A) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [cT]
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) : cT σ (1 : Matrix n n A) = 1 := by
  simp only [cT]
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem aux2 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A) {a b : GL n A},
  a ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
    b ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
      a * b ∈ {g : GL n A | cT σ g.val * J * g.val = J} := by
  intro A _ n _ _ σ J a b ha hb
  have ha' : cT σ (a : Matrix n n A) * J * (a : Matrix n n A) = J := ha
  have hb' : cT σ (b : Matrix n n A) * J * (b : Matrix n n A) = J := hb
  change cT σ ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((a * b : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  rw [Units.val_mul, cT_mul]
  calc _ = cT σ (b : Matrix n n A) *
        (cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha', hb']

theorem aux3 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A), cT σ (1 : GL n A).val * J * (1 : GL n A).val = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem aux4 : ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n]
  [inst_2 : DecidableEq n] (σ : A →+* A) (J : Matrix n n A) {g : GL n A},
  g ∈ {g : GL n A | cT σ g.val * J * g.val = J} →
    g⁻¹ ∈ {g : GL n A | cT σ g.val * J * g.val = J} := by
  intro A _ n _ _ σ J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) * J *
    ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = J
  have h1 : (g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) = 1 :=
    Units.mul_inv g
  have h2 : cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
      cT σ (g : Matrix n n A) = 1 := by
    rw [← cT_mul, h1, cT_one]
  calc _ = cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        (cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) := by rw [hg']
    _ = (cT σ ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A) *
        cT σ (g : Matrix n n A)) * J *
        ((g : Matrix n n A) * ((g⁻¹ : Matrix.GeneralLinearGroup n A) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UJ : {A : Type} →
  [inst : CommRing A] →
    {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
  fun {A} [inst : CommRing A] {n} [inst_1 : Fintype n] [inst_2 : DecidableEq n] σ J =>
    { carrier := {g : GL n A | cT σ g.val * J * g.val = J},
      mul_mem' := @aux2 A inst n inst_1 inst_2 σ J,
      one_mem' := aux3 σ J,
      inv_mem' := @aux4 A inst n inst_1 inst_2 σ J }

theorem aux6 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], SMulCommClass F F R := by
  intro F _ R _ _
  exact inferInstance

theorem aux7 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], IsScalarTower F F R := by
  intro F _ R _ _
  exact inferInstance

noncomputable def sigR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] → [inst_4 : Algebra F R] → (E →ₐ[F] E) → TensorProduct F R E →+* TensorProduct F R E :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ =>
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom

theorem aux9 : ∀ {F : Type} [inst : Field F] (R : Type) [inst_1 : CommRing R]
  [inst_2 : Algebra F R], SMulCommClass F R R := by
  intro F _ R _ _
  exact inferInstance

theorem laurent_T_neg_one_mul_T_one : ∀ {F : Type} [inst : Field F] (R : Type)
  [inst_1 : CommRing R] [inst_2 : Algebra F R], IsScalarTower F R R := by
  intro F _ R _ _
  exact inferInstance

theorem aux11 : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E], SMulCommClass F E E := by
  intro F E _ _ _
  exact inferInstance

theorem aux12 : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E], IsScalarTower F E E := by
  intro F E _ _ _
  exact inferInstance

noncomputable def inclR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] => Algebra.TensorProduct.includeRight.toRingHom

noncomputable def JR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              {M : ℕ} → Matrix (Fin M) (Fin M) E → Matrix (Fin M) (Fin M) (TensorProduct F R E) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] {M} J =>
    J.map ⇑(inclR R)

noncomputable def HR : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (E →ₐ[F] E) → {M : ℕ} → Matrix (Fin M) (Fin M) E → Subgroup (GL (Fin M) (TensorProduct F R E)) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J =>
    UJ (sigR R σ) (JR R J)

noncomputable def HA : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) → [inst_3 : CommRing R] → [Algebra F R] → (E →ₐ[F] E) → {M : ℕ} → Matrix (Fin M) (Fin M) E → Type :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J =>
    ↥(HR R σ J)

noncomputable def topTens : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] → [TopologicalSpace R] → TopologicalSpace (TensorProduct F R E) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] [TopologicalSpace R] =>
    moduleTopology R (TensorProduct F R E)

noncomputable def d18 : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (σ : E →ₐ[F] E) →
                {M : ℕ} →
                  (J : Matrix (Fin M) (Fin M) E) →
                    [TopologicalSpace R] → Set (HA R σ J) → Prop :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J [TopologicalSpace R] s =>
    letI : TopologicalSpace (TensorProduct F R E) := topTens R
    ∃ t, IsOpen t ∧ Subtype.val ⁻¹' t = s

theorem blockM_one_partner_eq_one : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R], d18 R σ J Set.univ := by
  intro F E _ _ _ R _ _ σ M J _
  let : TopologicalSpace (TensorProduct F R E) := topTens R
  exact ⟨Set.univ, isOpen_univ, rfl⟩

theorem blockM_mul_alt : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R] (s t : Set (HA R σ J)),
  d18 R σ J s →
    d18 R σ J t → d18 R σ J (s ∩ t) := by
  intro F E _ _ _ R _ _ σ M J _ s t hs ht
  let : TopologicalSpace (TensorProduct F R E) := topTens R
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a ∩ b, ha.inter hb, rfl⟩

theorem conj_invariant_character_mem : ∀ {F E : Type} [inst : Field F]
  [inst_1 : Field E] [inst_2 : Algebra F E] (R : Type) [inst_3 : CommRing R] [inst_4 : Algebra F R] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [inst_5 : TopologicalSpace R]
  (s : Set (Set (HA R σ J))),
  (∀ t ∈ s, d18 R σ J t) → d18 R σ J (⋃₀ s) := by
  intro F E _ _ _ R _ _ σ M J _ s hs
  let : TopologicalSpace (TensorProduct F R E) := topTens R
  refine ⟨⋃₀ {u : Set (Matrix.GeneralLinearGroup (Fin M) (TensorProduct F R E)) |
    IsOpen u ∧ Subtype.val ⁻¹' u ∈ s}, isOpen_sUnion (fun u hu => hu.1), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_sUnion]
  constructor
  · rintro ⟨u, ⟨_, hu⟩, hx⟩
    exact ⟨_, hu, hx⟩
  · rintro ⟨t, ht, hx⟩
    obtain ⟨u, hu, rfl⟩ := hs t ht
    exact ⟨u, ⟨hu, ht⟩, hx⟩

@[reducible] noncomputable def instTopologicalSpaceHA : {F E : Type} →
  [inst : Field F] →
    [inst_1 : Field E] →
      [inst_2 : Algebra F E] →
        (R : Type) →
          [inst_3 : CommRing R] →
            [inst_4 : Algebra F R] →
              (σ : E →ₐ[F] E) →
                {M : ℕ} →
                  (J : Matrix (Fin M) (Fin M) E) →
                    [TopologicalSpace R] → TopologicalSpace (HA R σ J) :=
  fun {F E} [Field F] [Field E] [Algebra F E] R [CommRing R] [Algebra F R] σ {M} J [TopologicalSpace R] =>
    { IsOpen := d18 R σ J,
      isOpen_univ := blockM_one_partner_eq_one R σ J,
      isOpen_inter := blockM_mul_alt R σ J,
      isOpen_sUnion := conj_invariant_character_mem R σ J }

attribute [local instance] instTopologicalSpaceHA

private theorem closed_UJ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    (J : Matrix n n A) :
    IsClosed ((UJ σ J : Subgroup (Matrix.GeneralLinearGroup n A)) :
      Set (Matrix.GeneralLinearGroup n A)) := by
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup n A => (g : Matrix n n A)) :=
    Units.continuous_val
  have hc : Continuous (fun g : Matrix.GeneralLinearGroup n A =>
      cT σ (g : Matrix n n A) * J * (g : Matrix n n A)) := by
    simp only [cT]
    exact ((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

private theorem lcsc_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {n : Type} [Fintype n]
    [DecidableEq n] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n A) ∧
      SecondCountableTopology (Matrix.GeneralLinearGroup n A) ∧
      T2Space (Matrix.GeneralLinearGroup n A) := by
  have : LocallyCompactSpace (Matrix n n A) := inferInstanceAs (LocallyCompactSpace (n → n → A))
  have : SecondCountableTopology (Matrix n n A) :=
    inferInstanceAs (SecondCountableTopology (n → n → A))
  have : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have he : Topology.IsClosedEmbedding (Units.embedProduct (Matrix n n A)) :=
    Units.isClosedEmbedding_embedProduct
  exact ⟨he.locallyCompactSpace, he.isEmbedding.secondCountableTopology, he.isEmbedding.t2Space⟩

private theorem lcsc_sub {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    LocallyCompactSpace H ∧ SecondCountableTopology H ∧ T2Space H :=
  ⟨hH.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

private theorem props_of_free {R D : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [Ring D] [Algebra R D]
    {ι : Type} [Fintype ι] (B : Module.Basis ι R D) [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] :
    IsTopologicalRing D ∧ LocallyCompactSpace D ∧ SecondCountableTopology D ∧ T2Space D := by
  have hr := IsModuleTopology.isTopologicalRing R D
  have := IsModuleTopology.toContinuousAdd R D
  let e := B.equivFun
  have c1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have c2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : D ≃ₜ (ι → R) := { toEquiv := e.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  exact ⟨hr, h.isClosedEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology,
    h.isEmbedding.t2Space⟩

private theorem sigR_continuous {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [TopologicalSpace (TensorProduct F R E)]
    [IsModuleTopology R (TensorProduct F R E)] (σ : E →ₐ[F] E) :
    Continuous (sigR R σ) := by
  have := IsModuleTopology.toContinuousAdd R (TensorProduct F R E)
  have h : (⇑(sigR R σ) : TensorProduct F R E → TensorProduct F R E) =
      ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add a b ha hb => simp [map_add (f := _), ha, hb]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

theorem lcsc_HA : ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] [FiniteDimensional F E] (R : Type) [inst_4 : CommRing R] [inst_5 : Algebra F R]
  [inst_6 : TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
  LocallyCompactSpace (HA R σ J) ∧
    SecondCountableTopology (HA R σ J) ∧
      T2Space (HA R σ J) := by
  intro F E _ _ _ _ R _ _ _ _ _ _ _ σ M J
  letI τ : TopologicalSpace (TensorProduct F R E) := topTens R
  haveI hm : IsModuleTopology R (TensorProduct F R E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    props_of_free (Algebra.TensorProduct.basis R (Module.finBasis F E))
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g1, g2, g3⟩ := lcsc_GL (A := TensorProduct F R E) (n := Fin M)
  haveI := g1
  haveI := g2
  haveI := g3
  have hc := closed_UJ (sigR R σ) (sigR_continuous R σ) (JR R J)
  exact lcsc_sub _ hc

end UpperTheory.Reformulated.B.Yzd4
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup", "h": "module\n\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem\npublic import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.Topology.Algebra.Valued.LocallyCompact\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  have : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable (𝓞 F) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  have : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  have := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  have := properSpace_adicCompletion F
  have := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  have : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem lcsc_HA [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) :=
  by apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA

end Tensor

theorem lcsc_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  intro F E _ _ _ _ _ σ M J
  have := locallyCompact_adele F
  have := secondCountable_adele F
  have := t2Space_adeleRing_numberField F
  exact lcsc_HA (AF F) σ M J

end GlobalTheory.AdelicUnitaryTop
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup =====
