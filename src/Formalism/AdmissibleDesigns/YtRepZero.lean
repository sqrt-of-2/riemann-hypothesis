module

public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.TrCMemZ1D
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
public import Formalism.AdmissibleDesigns.TensSubsingleton
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.AdmissibleDesigns.ContOfInjY, Formalism.AdmissibleDesigns.YtRepZero

-- ===== clump member: Formalism.AdmissibleDesigns.ContOfInjY =====
-- clump-header: {"m": "Formalism.AdmissibleDesigns.ContOfInjY", "h": "module\n\npublic import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.AdmissibleDesigns.TrCMemZ1D\n\n"}
section -- clump:auto
@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

theorem baer_of_div {R Q : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup Q] [Module R Q]
    (hdiv : ∀ a : R, a ≠ 0 → ∀ y : Q, ∃ q : Q, a • q = y) : Module.Baer R Q := by
  intro I g
  have ha : Submodule.IsPrincipal.generator I ∈ I := Submodule.IsPrincipal.generator_mem I
  by_cases h0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    have : (⟨s • Submodule.IsPrincipal.generator I, hx⟩ : I) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero, LinearMap.zero_apply]
  · obtain ⟨q, hq⟩ := hdiv _ h0 (g ⟨_, ha⟩)
    refine ⟨LinearMap.toSpanSingleton R Q q, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    rw [LinearMap.toSpanSingleton_apply, smul_assoc, hq, ← map_smul]
    rfl

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOwY (V : Type) [AddCommGroup V] [Module (FractionRing O) V] :
    Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOwY : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

def trY (v : V) : TrV e V := v

variable {e eO}

theorem smul_OwY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • trY e v : TrV e V) = trY e (eO.symm c • v) := by
  show (e.symm (algebraMap Ow LL c)) • v = eO.symm c • v
  conv_lhs => rw [← RingEquiv.apply_symm_apply eO c]
  rw [heO, RingEquiv.symm_apply_apply, algebraMap_smul]

variable {M : Type} [AddCommGroup M] [Module O M]


variable (e eO) in
def latTY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e (MK (O := O) M)) where
  carrier := Set.range fun m : M => trY e (mkK (O := O) m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add (mkK (O := O) (M := M)) a b⟩
  zero_mem' := ⟨0, map_zero (mkK (O := O) (M := M))⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show trY e (mkK (O := O) (eO.symm c • a)) = c • trY e (mkK (O := O) a)
    rw [smul_OwY heO, map_smul]

def MOY (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MOY eO M) := ‹AddCommGroup M›
instance : Module O (MOY eO M) := ‹Module O M›
instance instModMOY : Module Ow (MOY eO M) := Module.compHom M eO.symm.toRingHom

variable (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))

def latMapY : MOY eO M →ₗ[Ow] ↥(latTY e eO (M := M) heO) where
  toFun m := ⟨trY e (mkK (O := O) (show M from m)), m, rfl⟩
  map_add' a b := Subtype.ext (map_add (mkK (O := O) (M := M)) a b)
  map_smul' c a := Subtype.ext (by
    show trY e (mkK (O := O) (eO.symm c • (show M from a))) = c • trY e (mkK (O := O) (show M from a))
    rw [smul_OwY heO, map_smul])

theorem latMapY_bij (hinj : Function.Injective (mkK (O := O) (M := M))) :
    Function.Bijective (latMapY (eO := eO) (M := M) heO) :=
  ⟨fun a b h => hinj (congrArg Subtype.val h : trY e (mkK (O := O) (show M from a)) = trY e (mkK (show M from b))),
    fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def latEquivY (hinj : Function.Injective (mkK (O := O) (M := M))) : MOY eO M ≃ₗ[Ow] ↥(latTY e eO (M := M) heO) :=
  LinearEquiv.ofBijective (latMapY heO) (latMapY_bij heO hinj)

def basMOY [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MOY eO M) := Module.Free.chooseBasis O M

theorem free_MOY [Module.Free O M] : Module.Free Ow (MOY eO M) :=
  Module.Free.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem finite_MOY [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MOY eO M) :=
  Module.Finite.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem mkK_spanY (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  induction v using LocalizedModule.induction_on with
  | h m s =>
    refine ⟨(s : O), nonZeroDivisors.coe_ne_zero s, m, ?_⟩
    rw [LocalizedModule.smul'_mk]
    show LocalizedModule.mk m 1 = _
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem mkK_injY [NoZeroSMulDivisors O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := mkK (O := O) (M := M)) h
  rw [Submonoid.smul_def, Submonoid.smul_def] at hc
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero c) hc

variable {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)

def latY [Module.Finite O M] [Module.Free O M] [NoZeroSMulDivisors O M] (ρM : Representation O Γ M) :
    Lattice (O := Ow) (repL e (locRep ρM) ι) where
  T := latTY e eO heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, (locRep_mkK ρM (ι g) m).symm⟩
  fg := by
    have := finite_MOY (eO := eO) (M := M)
    have : Module.Finite Ow ↥(latTY e eO (M := M) heO) := Module.Finite.equiv (latEquivY heO mkK_injY)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    have := free_MOY (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquivY heO mkK_injY)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := mkK_spanY (O := O) (show MK (O := O) M from v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : (show MK (O := O) M from v) = (algebraMap O (FractionRing O) c)⁻¹ • mkK m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (show MK (O := O) M from v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • trY e (mkK (O := O) m) := by
      show (show MK (O := O) M from v) = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • mkK m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Gen2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N]


variable (e) in
def eLin : TrV e (FractionRing O) →ₗ[LL] LL where
  toFun x := e (show FractionRing O from x)
  map_add' x y := map_add e _ _
  map_smul' c x := by
    show e (e.symm c * (show FractionRing O from x)) = c * e (show FractionRing O from x)
    rw [map_mul, RingEquiv.apply_symm_apply]


variable (e N) in
def pY : TrV e (MK (O := O) (N × O)) →ₗ[LL] LL :=
  eLin e ∘ₗ trL e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O))

theorem pY_mk (m : N × O) : pY e N (trY e (mkK (O := O) m)) = e (algebraMap O (FractionRing O) m.2) := by
  show e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O) (mkK m)) = _
  rw [liftK_mkK]
  rfl

theorem pY_inv (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2) (g : G)
    (v : TrV e (MK (O := O) (N × O))) : pY e N (repL e (locRep ρM) ι g v) = pY e N v := by
  have h := liftK_equiv (Representation.trivial O Γ (FractionRing O)) ρM
    (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O)
    (fun g m => by
      show algebraMap O (FractionRing O) (ρM g m).2 = algebraMap O (FractionRing O) m.2
      rw [h2]) (ι g) (show MK (O := O) (N × O) from v)
  show e (liftK _ (locRep ρM (ι g) (show MK (O := O) (N × O) from v))) = e (liftK _ (show MK (O := O) (N × O) from v))
  rw [h]
  rfl

include heO in
theorem pY_int (v : TrV e (MK (O := O) (N × O))) (hv : ∃ m : N × O, trY e (mkK (O := O) m) = v) :
    pY e N v ∈ Set.range (algebraMap Ow LL) := by
  obtain ⟨m, rfl⟩ := hv
  rw [pY_mk, ← heO]
  exact ⟨_, rfl⟩

theorem pY_zero (m : N × O) (h : pY e N (trY e (mkK (O := O) m)) = 0) : m.2 = 0 := by
  rw [pY_mk] at h
  have h1 : algebraMap O (FractionRing O) m.2 = 0 := by
    rwa [map_eq_zero_iff e e.injective] at h
  exact (IsFractionRing.injective O (FractionRing O)) (h1.trans (map_zero _).symm)


include heO in
theorem div_quot {V : Type} [AddCommGroup V] [Module LL V] [Module Ow V] [IsScalarTower Ow LL V]
    (T : Submodule Ow V) (a : O) (ha : a ≠ 0) (y : V ⧸ T) : ∃ q : V ⧸ T, eO a • q = y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    have hc : algebraMap Ow LL (eO a) ≠ 0 := by
      rw [heO]
      exact (map_ne_zero e).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha))
    refine ⟨Submodule.Quotient.mk ((algebraMap Ow LL (eO a))⁻¹ • v), ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul LL (eO a), smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem nzsd_prod [NoZeroSMulDivisors O N] : NoZeroSMulDivisors O (N × O) :=
  ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1 : c • x.1 = 0 := congrArg Prod.fst h
      have h2 : c * x.2 = 0 := congrArg Prod.snd h
      exact Prod.ext ((smul_eq_zero.1 h1).resolve_left hc) ((mul_eq_zero.1 h2).resolve_left hc)⟩


include heO in
theorem ext_of_baer [IsPrincipalIdealRing O] [NoZeroSMulDivisors O N] {Q : Type} [AddCommGroup Q] [Module Ow Q]
    (hdiv : ∀ a : O, a ≠ 0 → ∀ y : Q, ∃ q : Q, eO a • q = y) (g₀ : N →+ Q)
    (hg : ∀ (a : O) (n : N), g₀ (a • n) = eO a • g₀ n) :
    ∃ φ : TrV e (MK (O := O) (N × O)) →ₗ[Ow] Q, ∀ n : N, φ (trY e (mkK (O := O) (n, (0 : O)))) = g₀ n := by
  let : Module O Q := Module.compHom Q eO.toRingHom
  have hB : Module.Baer O Q := baer_of_div fun a ha y => hdiv a ha y
  let f : N →ₗ[O] MK (O := O) (N × O) := mkK ∘ₗ LinearMap.inl O N O
  have := nzsd_prod (O := O) (N := N)
  have hf : Function.Injective f := mkK_injY.comp LinearMap.inl_injective
  let g : N →ₗ[O] Q := { toFun := g₀, map_add' := g₀.map_add, map_smul' := fun a n => hg a n }
  obtain ⟨h, hh⟩ := hB.extension_property f hf g
  refine ⟨⟨⟨fun v => h (show MK (O := O) (N × O) from v), fun x y => h.map_add _ _⟩, fun c v => ?_⟩,
    fun n => LinearMap.congr_fun hh n⟩
  have hs := smul_OwY (V := MK (O := O) (N × O)) heO c (show MK (O := O) (N × O) from v)
  show h (show MK (O := O) (N × O) from (c • v)) = c • h (show MK (O := O) (N × O) from v)
  have hs' : (show MK (O := O) (N × O) from (c • v)) = eO.symm c • (show MK (O := O) (N × O) from v) := hs
  rw [hs', h.map_smul]
  show eO (eO.symm c) • h _ = _
  rw [RingEquiv.apply_symm_apply]

end Gen2

end Formalism.MainNotions.N.K.TBa

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.AdmissibleDesigns.ContOfInjY =====

-- ===== clump member: Formalism.AdmissibleDesigns.YtRepZero =====
-- clump-header: {"m": "Formalism.AdmissibleDesigns.YtRepZero", "h": "module\n\npublic import Formalism.AdmissibleDesigns.ContOfInjY\npublic import Formalism.AdmissibleDesigns.TrCMemZ1D\npublic import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation\npublic import Formalism.AdmissibleDesigns.TensSubsingleton\nimport Mathlib.Algebra.Module.Torsion.Prod\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Mk

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] [Module.Free O (N × O)] [NoZeroSMulDivisors O (N × O)]
  (Qp : Type) [Field Qp] [Algebra Qp LL]
  (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2)
  [FiniteDimensional LL (TrV e (MK (O := O) (N × O)))]
  (hcont : ∀ x, Continuous fun g => repL e (locRep ρM) ι g x)

def mkYt : YtLat (G := G) (Qp := Qp) LL Ow where
  V := TrV e (MK (O := O) (N × O))
  ρ := repL e (locRep ρM) ι
  L := latY heO ι ρM
  cont := hcont
  p := pY e N
  p_inv g v := pY_inv ι ρM h2 g v
  p_int v hv := pY_int heO v hv
  e₀ := trY e (mkK (O := O) ((0 : N), (1 : O)))
  e₀_mem := ⟨_, rfl⟩
  p_e₀ := by rw [pY_mk]; simp

end Mk

section GenY

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
  (r : GG →* A) (χ : GG →* T'ˣ) (E : A)

theorem nzsdY [NoZeroSMulDivisors O A] : NoZeroSMulDivisors O ↥(Ymod r χ E) :=
  Function.Injective.noZeroSMulDivisors (fun y : ↥(Ymod r χ E) => (y : A)) Subtype.val_injective rfl
    (fun _ _ => rfl)

theorem finY [Module.Finite O A] : Module.Finite O ↥(Ymod r χ E) := by
  have : IsNoetherian O A := isNoetherian_of_isNoetherianRing_of_finite O A
  let f : ↥(Ymod r χ E) →ₗ[O] A :=
    { toFun := fun y => (y : A), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem freeY [Module.Finite O A] [NoZeroSMulDivisors O A] : Module.Free O (↥(Ymod r χ E) × O) := by
  have := finY (O := O) r χ E
  have := nzsdY (O := O) r χ E
  have := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  exact Module.free_of_finite_type_torsion_free'

theorem ytRep_zero (g : GG) (y : ↥(Ymod r χ E)) : ytRep O r χ E g (y, 0) = (uElt r χ g • y, 0) :=
  Prod.ext (by
    show uElt r χ g • y + (0 : O) • yY r χ E g = _
    rw [zero_smul, add_zero]) rfl

theorem ytRep_e (g : GG) : ytRep O r χ E g (0, 1) = (yY r χ E g, 1) :=
  Prod.ext (by
    show uElt r χ g • (0 : ↥(Ymod r χ E)) + (1 : O) • yY r χ E g = _
    rw [smul_zero, one_smul, zero_add]) rfl

end GenY

section GenT

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {Ow : Type} [CommRing Ow] [Algebra Ow LL]
    {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {e : FractionRing O ≃+* LL} {eO : O ≃+* Ow}
    (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : ↥Dw ≃* G)

abbrev ytVG : Representation LL G (TrV e (MK (O := O) (↥(Ymod r χ E) × O))) :=
  repL e (locRep (resRep (ytRep O r χ E) Dw)) eG.symm.toMonoidHom


variable (Qp) in
def ytG [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x) : YtLat (G := G) (Qp := Qp) LL Ow :=
  haveI := finY (O := O) r χ E
  haveI := freeY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  mkYt heO eG.symm.toMonoidHom Qp (resRep (ytRep O r χ E) Dw) (fun _ _ => rfl) hcont

theorem ytG_psi [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] {e' : ℕ}
    (Cd : CoefDict PD LL Ow eO M r χ Dw eG e') :
    PsiExt eO r χ E Dw eG (ytG Qp heO r χ E Dw eG hfd hcont) Cd := by
  intro ψ hψe
  have := nzsdY (O := O) r χ E
  obtain ⟨φ, hφ⟩ := ext_of_baer (e := e) (eO := eO) heO (N := ↥(Ymod r χ E)) (Q := Cd.Ce.V ⧸ Cd.Ce.L.T)
    (div_quot heO Cd.Ce.L.T) (Cd.u.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a n => by
      show Cd.u (ψ (a • n)) = _
      rw [ψ.map_smul, Cd.u_smul]
      rfl)
  refine ⟨φ, ?_, ?_⟩
  · intro g y hy hp
    obtain ⟨⟨n, c0⟩, rfl⟩ := hy
    have hc0 : c0 = 0 := pY_zero (m := (n, c0)) hp
    subst hc0
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm g) (mkK (n, (0 : O))))) =
      actD Cd.Ce.L g (φ (trY e (mkK (n, (0 : O)))))
    rw [locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E ((eG.symm g : ↥Dw) : GG) (n, (0 : O))))) = _
    rw [ytRep_zero, hφ, hφ]
    show Cd.u (ψ _) = _
    rw [hψe _ (eG.symm g).2 n, Cd.u_act (eG.symm g) (ψ n), MulEquiv.apply_symm_apply]
    rfl
  · intro γ
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm (eG γ)) (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [MulEquiv.symm_apply_apply, locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E (γ : GG) ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [ytRep_e]
    have h3 : (mkK (O := O) (yY r χ E (γ : GG), (1 : O)) - mkK (O := O) ((0 : ↥(Ymod r χ E)), (1 : O)) :
          MK (O := O) (↥(Ymod r χ E) × O)) = mkK (O := O) (yY r χ E (γ : GG), (0 : O)) := by
      rw [← map_sub]
      congr 1
      ext <;> simp
    exact (congrArg φ h3).trans (hφ _)

theorem ytG_crys [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL Ow) {ιx : Type} {k : ℕ} (Ms : ιx → G →* Matrix (Fin k) (Fin k) LL)
    (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x))) {m : ℕ} (xs : Fin m → ιx)
    (φ : TrV e (MK (O := O) (↥(Ymod r χ E) × O)) →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ytVG (e := e) r χ E Dw eG g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ ∧
      ∀ τ a, IsJumpV PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  let Ag : GRep G Qp LL Ow :=
    { V := TrV e (MK (O := O) (↥(Ymod r χ E) × O)), ρ := ytVG (e := e) r χ E Dw eG, cont := hcont }
  exact crys_of_inj PD Ms hF hMc hMs Ag xs φ hφ heq

end GenT

end Formalism.MainNotions.N.K.TBa

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.AdmissibleDesigns.YtRepZero =====
