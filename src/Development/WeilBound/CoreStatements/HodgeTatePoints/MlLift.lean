module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Ml

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  let := β.toAlgebra
  have := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem lift_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) {X : Scheme.{0}} (s : X ⟶ Sp O) {K : Type} [Field K]
    (x : Sp K ⟶ X) (hx : Set.range x ⊆ Set.range (pullback.fst s (spMap β))) :
    ∃ y : Sp K ⟶ pullback s (spMap β), y ≫ pullback.fst _ _ = x := by
  have : IsPreimmersion (spMap β) := preimm_frac β h
  obtain ⟨⟨p, a⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective x
  have hp : p ∈ Set.range (pullback.fst s (spMap β)) := by
    apply hx
    exact ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply p _⟩
  obtain ⟨q, rfl⟩ := hp
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    have h1 : Function.Surjective
        (Scheme.Hom.stalkMap (pullback.fst s (spMap β)) q ≫ (pullback s (spMap β)).residue q) :=
      ((pullback s (spMap β)).residue_surjective q).comp
        (Scheme.Hom.stalkMap_surjective (pullback.fst s (spMap β)) q)
    rw [← Scheme.residue_residueFieldMap] at h1
    intro b
    obtain ⟨c, hc⟩ := h1 b
    exact ⟨X.residue _ c, hc⟩
  have : IsIso (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q).hom.injective, hsurj⟩
  refine ⟨Spec.map (inv (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) ≫ a) ≫
    (pullback s (spMap β)).fromSpecResidueField q, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp [Scheme.SpecToEquivOfField]

theorem lift_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  intro E _ _ _ H D l Xo c O _ β Y h K _ x hx
  have : IsPreimmersion (spMap β) := preimm_frac β h
  have := Y.jQ_open
  have hx' : Set.range x ⊆ Set.range (pullback.fst Y.s (spMap β)) := by
    refine hx.trans ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨Y.jQ w, by simp [Model.j]⟩
  obtain ⟨y1, hy1⟩ := lift_frac β h Y.s x hx'
  have hr : Set.range y1 ⊆ Set.range Y.jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hx ⟨z, rfl⟩
    refine ⟨w, (pullback.fst Y.s (spMap β)).isEmbedding.injective ?_⟩
    rw [← hy1] at hw
    simpa [Model.j] using hw
  refine ⟨IsOpenImmersion.lift Y.jQ y1 hr, ?_⟩
  simp [Model.j, hy1]

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  have : IsProper s := projProper O X s hp
  have : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  have : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  have : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO h v hv
  have : IsPreimmersion (spMap β) := preimm_frac β h
  have := Y.flat
  have := Y.jQ_open
  have := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj
  have hβ : Function.Injective β := by
    let := β.toAlgebra
    have := h
    exact IsFractionRing.injective O c.F
  let z0 : Sp c.F := IsLocalRing.closedPoint c.F
  have hgen : (spMap β z0).asIdeal = ⊥ := by
    rw [spMap_field_pt]
    exact (RingHom.injective_iff_ker_eq_bot β).mp hβ
  have hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal := by
    rw [hgen]
    exact bot_le
  have hspec : spMap β z0 ⤳ Y.s v := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback v z0 hv'
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  refine ⟨w, ?_⟩
  rw [← hq, ← hw]
  simp [Model.j]

end PositivityTheory.HtPt.Ml
