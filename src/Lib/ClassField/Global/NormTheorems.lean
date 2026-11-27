module

import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Sheaves.Presheaf
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import Lib.ClassField.Local.ArtinMap
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.Global.ArtinReciprocity

/-!
# Surjectivity of the Artin map, Hasse's norm theorem and norm groups of cyclic extensions

Global class field theory for cyclic extensions of a number field `K`, using the reciprocity law,
the second inequality `New.second_inequality` and Tau Ceti's cyclic Hasse norm theorem.

* `New.artinMap_surjective`: the Artin map from the finite ideles onto `Γ^ab` is surjective.
* `New.exists_isProGalois_ker_of_isCyclic`: a cyclic extension `L/K` is cut out by a character.
* `New.hasse_norm`: Hasse's norm theorem, for totally positive elements.
* `New.index_ker_abelianLift_comp_artinMap`, `New.abelianLift_artinMap_eq_one_iff`: if `χ` cuts out
  `L`, the kernel of `χ ∘ artinMap` has index `[L : K]` and consists of totally positive elements of
  `Kˣ` times norms from `L`.

Notions from other files:
* `New.Ω` is an algebraic closure of `ℚ`, and `New.EmbeddedNumberField K` is a number field `K`
  with an embedding in `Ω`. `New.IsProGalois Γ K Ω` says that `Γ` is the profinite Galois group of
  `Ω/K`.
* `New.artinMap Γ` is the global Artin map from the finite ideles `(𝔸f K)ˣ` of `K` to the
  topological abelianisation `Γ^ab` of `Γ`, chosen so that a character takes at `artinMap Γ a` the
  product of its values at the local Artin symbols of the components of `a`.
* A `χ : New.QZChar Γ` is a continuous character `Γ → ℚ/ℤ`; `New.QZChar.toHom χ` and
  `New.QZChar.abelianLift χ` are its multiplicative forms on `Γ` and `Γ^ab`. "`χ` cuts out `L`" is
  the instance `IsProGalois (ker χ) L Ω`, with `New.QZChar.ker`.
* `New.IsTotallyPositive x`: every ring homomorphism `K → ℝ` sends `x` to a positive number.

## Relation to the literature

Known; see `Lib.ClassField.Global.AlbertBrauerHasseNoether` for sources.
-/

@[expose] public section

namespace New

open Subgroup QZChar QuotientGroup Set Module Function IsScalarTower Algebra

variable (Γ : Type)
  {K L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  (χ : QZChar Γ) [Field L] [EmbeddedNumberField L] [Algebra K L]

open Pointwise in
/-- The image of the global Artin map from the finite ideles of `K` to `Γ^ab` is closed. -/
lemma isClosed_range_artinMap : IsClosed (artinMap (K := K) Γ).range.carrier := by
  -- `H` is open and contains the totally positive principal ideles, so it has finite index;
  -- thus the range is a finite union of translates of the compact image of the unit ideles.
  let H : Subgroup (𝔸f K)ˣ := idelesUnitOff ∅ ⊔ (artinMap Γ).ker
  have hH_fin : H.FiniteIndex :=
    finiteIndex_idele_subgroup_of_isOpen H (isOpen_mono le_sup_left (isOpen_idelesUnitOff _))
      fun x hx ↦ mem_sup_right (artinMap_principalIdele_eq_one_of_isTotallyPositive hx)
  let C : Set (TopologicalAbelianization Γ) := artinMap Γ '' idelesUnitOff (K := K) ∅
  have h_compact : IsCompact C := isCompact_idelesUnitOff_empty.image (by fun_prop)
  have h_range : (artinMap (K := K) Γ).range.carrier = ⋃ q : (𝔸f K)ˣ ⧸ H, artinMap Γ q.out • C := by
    change range (artinMap (K := K) Γ) = _
    simp [← image_univ, H, C, univ_eq_iUnion_smul H, image_iUnion, image_smul_distrib,
      ← coe_map, Subgroup.map_sup]
  rw [h_range]
  exact (isCompact_iUnion fun q : (𝔸f K)ˣ ⧸ H ↦ h_compact.smul (artinMap Γ q.out)).isClosed

/-- The global Artin map from the finite ideles of `K` to the topological abelianisation `Γ^ab` of
the absolute Galois group `Γ` of `K` is surjective.

A consequence of Artin's global reciprocity law. -/
lemma artinMap_surjective : Surjective (artinMap (K := K) Γ) := by
  -- The range of `artinMap` is closed, so by duality (`mem_of_forall_abelianLift`) it suffices to
  -- show that a character `ψ` killing it is trivial. In the fixed field of `ker ψ` every prime
  -- splits completely, and counting primes of degree one shows that this field is `K`.
  intro σ
  rw [← MonoidHom.mem_range]
  refine mem_of_forall_abelianLift (isClosed_range_artinMap Γ) σ fun ψ hψ ↦ ?_
  let U : Subgroup Γ := ker ψ
  let F : IntermediateField K Ω := fixedFieldOf U
  suffices h_index : U.index = 1 by
    have h_top : U = ⊤ := index_eq_one.mp h_index
    obtain ⟨g, rfl⟩ : ∃ g : Γ, (g : TopologicalAbelianization Γ) = σ :=
      QuotientGroup.mk_surjective σ
    rw [abelianLift_mk, ← QZChar.toHom_apply, ← MonoidHom.mem_ker]
    exact h_top.ge (mem_top g)
  -- `ψ` kills every local symbol, so all decomposition groups lie in `U` and every `v` splits.
  have h_count (v : FinPlace K) :
      {w : FinPlace F | w.below K = v ∧ w.q = v.q}.ncard = finrank K F := by
    have h_dec : decompGroup Γ (placeOver v) ≤ U :=
      (v.isPlaceOver_placeOver.artinAt_trivial_iff_decompGroup_le ψ).mp fun x ↦
        hψ (artinAt Γ v x) (MonoidHom.mem_range.mpr ⟨locIdele v x, artinMap_locIdele v x⟩)
    have h_card :
        {w : FinPlace F | w.below K = v}.ncard * U.relIndex (decompGroup Γ (placeOver v)) =
          finrank K F :=
      v.isPlaceOver_placeOver.ncard_above_mul_relIndex_eq_finrank (L := F) U
    have h_same_q (w : FinPlace F) (hw : w.below K = v) : w.q = v.q :=
      (v.isPlaceOver_placeOver.q_eq_and_comap_ne_self_of_decompGroup_le h_dec w hw).1
    rw [← h_card, relIndex_eq_one.mpr h_dec, mul_one]
    congr! with w
    exact and_iff_left_of_imp (h_same_q w)
  -- The family `v ↦ #{places of F over v with the same norm}` has density `1`
  -- (`hasPrimeDensity_card_degree_one`); by `h_count` it is the constant `[F : K]`, so
  -- `[F : K] ≤ 1`.
  have h_re_le : (finrank K F : ℂ).re ≤ (1 : ℂ).re :=
    (hasPrimeDensity_const (K := K) (finrank K F : ℂ)).re_le_re
      (hasPrimeDensity_card_degree_one F 1) (.of_forall fun v _ ↦ by simp [h_count v])
  -- The degree `[F : K]` is the index of `U` (`finrank_fixedFieldOf`).
  have h_le : finrank K F ≤ 1 := by simpa using h_re_le
  exact (finrank_fixedFieldOf U).symm.trans (h_le.antisymm finrank_pos)

variable {Γ} [IsScalarTower K L Ω] [hχ : IsProGalois (ker χ) L Ω] [IsGalois K L]

/-- Let L/K be a cyclic extension of number fields inside an algebraic closure Ω of ℚ. There is
a continuous character χ : Gal(Ω/K) → ℚ/ℤ whose kernel acts on Ω as the Galois group of Ω/L. -/
lemma exists_isProGalois_ker_of_isCyclic (h_cyc : IsCyclic Gal(L/K)) :
    ∃ χ : QZChar Gal(Ω/K), IsProGalois (ker χ) L Ω := by
  -- Pull back a faithful character `ψ` of the cyclic group `Gal(L/K)` along restriction `φ`.
  obtain ⟨φ, hφ⟩ : ∃ φ : Gal(Ω/K) →ₜ* Gal(L/K),
      ∀ (g : Gal(Ω/K)) (x : L), algebraMap L Ω (φ g • x) = g • algebraMap L Ω x :=
    exists_galois_restrict _ _ (algebraMap L Ω) (by simp [← algebraMap_apply])
  obtain ⟨ψ, hψ⟩ : ∃ ψ : QZChar Gal(L/K), ker ψ = ⊥ :=
    exists_ker_eq_of_isCyclic ⟨⊥, by simp⟩ (quotientBot.isCyclic.mpr h_cyc)
  refine ⟨comap φ ψ, .of_fixingSubgroup_eq (K := K) ?_⟩
  -- `g` fixes `L` pointwise iff `φ g = 1` iff `ψ (φ g)` is trivial.
  ext g
  have h_fix_iff : g ∈ fixingSubgroup Gal(Ω/K) (Set.range (algebraMap L Ω)) ↔ φ g = 1 := by
    simp only [mem_fixingSubgroup_iff, forall_mem_range, AlgEquiv.ext_iff, AlgEquiv.one_apply]
    refine forall_congr' fun x ↦ ?_
    rw [← hφ, (algebraMap L Ω).injective.eq_iff, AlgEquiv.smul_def]
  rw [h_fix_iff, ← Subgroup.mem_bot, ← hψ]
  rfl

open NumberField TauCeti TauCeti.GlobalNumberFields in
open scoped TensorProduct in
omit [EmbeddedNumberField K] [EmbeddedNumberField L] in
variable [NumberField K] [NumberField L] in
/-- Hasse's norm theorem. Let `L / K` be a cyclic extension of number fields. A totally positive `x`
in `K` that is a local norm (a limit of norms from `L` in the completion `LocField v` of `K` at `v`)
at every finite place `v` is a norm.

A case of the Hasse norm theorem, with x assumed totally positive, which is stronger than being a
local norm at each real place. -/
lemma hasse_norm [IsCyclic Gal(L/K)] (x : Kˣ)
    (h_loc : ∀ v : FinPlace K,
      algebraMap K (LocField v) x ∈ closure
        (range fun y : L ↦ algebraMap K (LocField v) (Algebra.norm K y)))
    (hx_pos : IsTotallyPositive x.val) :
    ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  have h_norm : x ∈ normGroup K L := by
    apply (TauCeti.ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere K L x).2
    rw [isLocalNormEverywhere_def]
    have h_degree : finrank K L ≠ 0 := finrank_pos.ne'
    refine ⟨fun v ↦ ?_, fun w ↦ ?_⟩
    · -- The local norm subgroup contains an open subgroup of powers, so it contains the limits.
      rw [isFiniteLocalNorm_def]
      let F := LocField v
      let N := (Algebra.normUnits F (S := F ⊗[K] L)).range
      have hN : IsOpen (N : Set Fˣ) :=
        Subgroup.isOpen_mono (Algebra.range_powMonoidHom_le_range_normUnits_baseChange K L F)
          (TauCeti.isOpen_range_powMonoidHom (Nat.cast_ne_zero.2 h_degree))
      let S := range fun y : L ↦ algebraMap K F (Algebra.norm K y)
      have h_subset : (Units.val : Fˣ → F) ⁻¹' S ⊆ N := by
        intro u hu
        obtain ⟨y, hy⟩ := hu
        have hy0 : y ≠ 0 := by
          rintro rfl
          exact u.ne_zero (by simpa using hy.symm)
        refine ⟨Units.map (Algebra.TensorProduct.includeRight (R := K) (A := F)).toMonoidHom
          (Units.mk0 y hy0), Units.ext ?_⟩
        simpa [TauCeti.Algebra.norm_baseChange_tmul] using hy
      have hx : Units.map (algebraMap K F).toMonoidHom x ∈
          _root_.closure ((Units.val : Fˣ → F) ⁻¹' S) := by
        rw [← IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap.preimage_closure_eq_closure_preimage
          Units.continuous_val]
        exact h_loc v
      exact closure_minimal h_subset (Subgroup.isClosed_of_isOpen N hN) hx
    · -- At infinity, total positivity supplies a root of degree `[L : K]`.
      rw [isInfiniteLocalNorm_def]
      apply Algebra.range_powMonoidHom_le_range_normUnits_baseChange K L w.Completion
      refine InfinitePlace.Completion.mem_range_powMonoidHom h_degree _ fun hw ↦ ?_
      simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, WithAbs.equiv]
        using hx_pos (InfinitePlace.embedding_of_isReal hw)
  obtain ⟨z, hz⟩ := mem_normGroup_iff.1 h_norm
  exact ⟨z, Units.ext hz⟩

omit [IsGalois K L] in
/-- If the kernel of `χ` is the Galois group of `Ω / L`, then the kernel of `χ ∘ artinMap` has index
`[L : K]` in the finite ideles of `K`. -/
lemma index_ker_abelianLift_comp_artinMap :
    ((abelianLift χ).comp (artinMap Γ)).ker.index = finrank K L := by
  -- The index of `(abelianLift χ).ker` is unchanged by pulling back along the surjection
  -- `artinMap Γ`, and along the quotient map from `Γ`, where the kernel becomes the group `ker χ`
  -- fixing `L`.
  calc
    _ = (abelianLift χ).ker.index := index_comap_of_surjective _ (artinMap_surjective _)
    _ = (ker χ).index := (index_comap_of_surjective _ (mk'_surjective _)).symm
    _ = finrank K L := (eq_fixingSubgroup_of_isProGalois (Γ := Γ) (L := L)).right

/-- The norm group of the extension `L / K` cut out by `χ`: a finite idele `a` of `K` is killed by
`χ ∘ artinMap` exactly when it is a totally positive element of `Kˣ` times the norm of a finite
idele of `L`. A case of the Artin reciprocity law. -/
lemma abelianLift_artinMap_eq_one_iff (a : (𝔸f K)ˣ) :
    abelianLift χ (artinMap Γ a) = 1 ↔
      ∃ (x : Kˣ) (y : (𝔸f L)ˣ),
        IsTotallyPositive x.val ∧ a = principalIdele x * Units.map (adeleNorm K L) y := by
  -- Let `W` be the group generated by the totally positive elements and the norms from `L`. It lies
  -- in the kernel of `χ ∘ artinMap`, which has index `[L : K]`, while the second inequality
  -- (`second_inequality`) bounds the index of `W` by `[L : K]`. Hence the two groups are equal.
  let P : Subgroup Kˣ := ⨅ φ : K →+* ℝ, (Units.posSubgroup ℝ).comap (Units.map φ)
  have h_mem_P (x : Kˣ) : x ∈ P ↔ IsTotallyPositive x.val := mem_iInf
  let W : Subgroup (𝔸f K)ˣ := P.map principalIdele ⊔ (Units.map (adeleNorm K L)).range
  -- `W` is open: an idele `b` near `1` is a unit everywhere and `χ` kills its local symbols,
  -- so it is a norm.
  have h_norms_closed :
      IsClosed ((idelesUnitOff ∅).map (Units.map (adeleNorm K L)) : Set (𝔸f K)ˣ) :=
    (isCompact_idelesUnitOff_empty.image (by fun_prop)).isClosed
  have hW_open : IsOpen (W : Set (𝔸f K)ˣ) := by
    refine isOpen_of_mem_nhds _
      ((eventually_artinAt_eq_one χ).mono fun b ⟨hb_unit, hb_loc⟩ ↦ mem_sup_right ?_)
    -- The norms of the unit ideles form a closed group, so it suffices to treat the ideles with a
    -- single component of `b` (`mem_of_locIdele_mem`). Such a component, killed by `χ`, is the
    -- local norm of some `y` (`exists_localNorm_of_abelianLift_artinAt`), and `y` is a unit
    -- because its norm is.
    apply map_le_range _ (idelesUnitOff ∅)
    apply mem_of_locIdele_mem h_norms_closed
    intro v
    obtain ⟨w, rfl⟩ : ∃ w : FinPlace L, w.below K = v :=
      FinPlace.comap_surjective (algebraMap K L) v
    obtain ⟨y, hy_norm⟩ : ∃ y : (LocField w)ˣ, localNorm K w y = ideleAt (w.below K) b :=
      exists_localNorm_of_abelianLift_artinAt (hb_loc (w.below K))
    -- The norm of `y` has absolute value one, as `b` is a unit at every place.
    have h_norm_one : ‖(localNorm K w y).val‖ = 1 ↔ ‖(ideleAt (w.below K) b).val‖ = 1 := by
      rw [hy_norm]
    have hy_unit : Valued.v y.val = 1 := by
      simpa [mem_idelesUnitOff.mp hb_unit, ideleAt, le_antisymm_iff] using h_norm_one
    refine ⟨locIdele w y, locIdele_mem_idelesUnitOff hy_unit, ?_⟩
    rw [← hy_norm]
    exact adeleNorm_locIdele w y
  have hW_pos (x : Kˣ) (hx : IsTotallyPositive x.val) : principalIdele x ∈ W :=
    mem_sup_left ⟨x, (h_mem_P x).mpr hx, rfl⟩
  have hW_norm (y : (𝔸f L)ˣ) : Units.map (adeleNorm K L) y ∈ W := mem_sup_right ⟨y, rfl⟩
  -- `hW_fin` is used below as an instance, by `index_strictAnti`.
  obtain ⟨(hW_fin : W.FiniteIndex), (hW_index : W.index ≤ finrank K L), -⟩ :=
    second_inequality L hW_open hW_pos hW_norm
  -- `N` is the kernel of `χ ∘ artinMap`. Reciprocity puts the totally positive elements in it,
  -- norm compatibility the norms.
  let N : Subgroup (𝔸f K)ˣ := ((abelianLift χ).comp (artinMap Γ)).ker
  have h_pos_le : P.map principalIdele ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    simp [N, artinMap_principalIdele_eq_one_of_isTotallyPositive ((h_mem_P x).mp hx)]
  have h_norm_le : (Units.map (adeleNorm K L)).range ≤ N := by
    rintro _ ⟨y, rfl⟩
    exact abelianLift_artinMap_adeleNorm y
  -- A strict inclusion `W < N` would make the index of `N` smaller than `[L : K]`.
  have hW_eq : W = N := by
    refine eq_of_le_of_not_lt (sup_le h_pos_le h_norm_le) fun hlt ↦ ?_
    have h_lt : N.index < W.index := index_strictAnti hlt
    have h_ker_index : N.index = finrank K L := index_ker_abelianLift_comp_artinMap χ
    omega
  -- Membership in `W`, written out, is the right side.
  change a ∈ N ↔ _
  rw [← hW_eq]
  simp [W, mem_sup, h_mem_P, eq_comm]

end New
