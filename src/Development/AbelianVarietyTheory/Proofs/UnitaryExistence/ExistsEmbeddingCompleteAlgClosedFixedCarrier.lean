module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
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
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallClosedField

open Cardinal

theorem mk_le_of_denseRange {A C : Type} [MetricSpace C] (f : A → C) (hf : DenseRange f) :
    #C ≤ #A ^ ℵ₀ := by
  have h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := by
    intro x
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (hxy ▸ hs y)
  simpa using mk_le_of_injective hinj

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  apply _root_.GlobalTheory.ComplexEmbedding.mk_le_continuum_of_finite_residueField

theorem exists_small_closed_subfield {K C : Type} [Field K] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra K C] (hK : #K ≤ 𝔠)
    {x : K} (hx : 1 < ‖algebraMap K C x‖) :
    ∃ L : Subfield C, (∀ y : K, algebraMap K C y ∈ L) ∧ IsClosed (L : Set C) ∧ IsAlgClosed L ∧
      #L ≤ 𝔠 := by
  let A := algebraicClosure K C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : K, algebraMap K C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  let : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  have : CompleteSpace L := hcl.completeSpace_coe
  let : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  have : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  refine ⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩
  have hA : #A ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)
  exact (power_le_power_right hA).trans continuum_power_aleph0.le

theorem exists_scf_isometry {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), ∀ x, ‖e x‖ = ‖x‖ := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  let : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  let : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  let : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  have : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add (f := _)]; exact IsUltrametricDist.norm_add_le_max _ _
  have : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  have : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  have : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩

theorem exists_extension_intO {V W C : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (g : V →+* intO C) (φ : V →+* W)
    (hg : Function.Injective g) (hφ : Function.Injective φ) (hf : φ.Finite) :
    ∃ g' : W →+* intO C, g'.comp φ = g ∧ Function.Injective g' := by
  let : Algebra V W := φ.toAlgebra
  let : Algebra V C := ((intO C).subtype.comp g).toAlgebra
  have : Module.Finite V W := hf
  have hgC : Function.Injective (algebraMap V C) := Subtype.val_injective.comp hg
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ
  have : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC
  let l : W →ₐ[V] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hl : Function.Injective l := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := V) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, l.commutes] at ha
    exact (map_eq_zero_iff _ hgC).1 ha
  have hmem : ∀ a : W, l a ∈ intO C := by
    intro a
    have hO := normIntegers_integers C
    obtain ⟨q, hq, hqa⟩ := (Algebra.IsIntegral.isIntegral (R := V) a).map l
    let g₀ : V →+* normIntegers C := (algebraMap V C).codRestrict (normIntegers C) fun v =>
      mem_normIntegers_iff.2 (g v).2
    have hint : IsIntegral (normIntegers C) (l a) :=
      ⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩
    exact mem_normIntegers_iff.1 (hO.mem_of_integral hint)
  refine ⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩
  ext a
  exact l.commutes a

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem exists_embedding_and_extension :
    ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T p hp hfin hpm
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩
  · obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
      exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm
        (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
    have : Finite (ResidueField T.V) := hfin
    have hK : #T.Fr ≤ 𝔠 :=
      (IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans
        (mk_le_continuum_of_finite_residueField T.V)
    have hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖ := by
      rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
    obtain ⟨L, hKL, hcl, hac, hL⟩ := exists_small_closed_subfield hK hx
    let : NontriviallyNormedField L :=
      { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
    have : CompleteSpace L := hcl.completeSpace_coe
    have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
    let i : T.Fr →+* L := (algebraMap T.Fr C).codRestrict L hKL
    have hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖ := fun _ => rfl
    have : CharZero L := charZero_of_injective_ringHom i.injective
    have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
      rw [← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]
    obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL
    have hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
      rw [RingHom.comp_apply, he, hi]; exact (hC _).2 ⟨a, rfl⟩
    refine ⟨D, e.comp i, hle, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  · obtain ⟨g', hc, hinj⟩ := exists_extension_intO g φ hg hφ hf
    refine ⟨g', hc, hinj, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2)
      ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha
    have := hgm p hpm
    rw [← hc] at this
    exact this

end GlobalTheory.SmallClosedField
