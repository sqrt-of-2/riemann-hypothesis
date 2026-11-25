module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SemiProd

theorem torus_prod_iso : ∀ (S : Scheme.{0}) (X₁ X₂ : Type) [AddCommGroup X₁] [AddCommGroup X₂], IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂)) (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) := by
  intro S X₁ X₂ _ _
  let comb : ∀ {M : Type} [CommGroup M], (Multiplicative X₁ →* M) → (Multiplicative X₂ →* M) →
      (Multiplicative (X₁ × X₂) →* M) := fun u v =>
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X₁ X₂)) *
      v.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X₁ X₂))
  let l : ∀ {Z : Over S}, (Z ⟶ splitTorus S X₁) → (Z ⟶ splitTorus S X₂) → (Z ⟶ splitTorus S (X₁ × X₂)) :=
    fun {Z} f g => (splitTorusPointsEquiv S (X₁ × X₂) Z).symm
      (comb (splitTorusPointsEquiv S X₁ Z f) (splitTorusPointsEquiv S X₂ Z g))
  have f₁ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂) = f := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₁ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have f₂ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂) = g := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₂ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have u : ∀ {Z : Over S} (m : Z ⟶ splitTorus S (X₁ × X₂)),
      m = l (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
        (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    intro Z m
    apply (splitTorusPointsEquiv S (X₁ × X₂) Z).injective
    rw [MulEquiv.apply_symm_apply, SplitTorusPow.points_comp_torusMap,
      SplitTorusPow.points_comp_torusMap]
    refine MonoidHom.ext fun x => ?_
    have hx : x = Multiplicative.ofAdd (AddMonoidHom.inl X₁ X₂ x.toAdd.1) *
        Multiplicative.ofAdd (AddMonoidHom.inr X₁ X₂ x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_lhs => rw [hx]
    rw [map_mul]
    rfl
  have hl : IsLimit (BinaryFan.mk (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) :=
    BinaryFan.IsLimit.mk _ (fun f g => l f g) (fun f g => f₁ f g) (fun f g => f₂ f g)
      (fun f g m h₁ h₂ => by rw [u m]; exact congrArg₂ l h₁ h₂)
  have e : lift (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) =
      (hl.conePointUniqueUpToIso (tensorProductIsBinaryProduct _ _)).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.left⟩).symm
    · rw [lift_snd]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.right⟩).symm
  rw [e]
  infer_instance

theorem tensorHom_prop : ∀ (S : Scheme.{0}) (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange] (A B C D : Over S) (f : A ⟶ B) (g : C ⟶ D), P f.left → P g.left → P (f ⊗ₘ g).left := by
  intro S P _ _ A B C D f g hf hg
  have e : (f ⊗ₘ g).left = pullback.map A.hom C.hom B.hom D.hom f.left g.left (𝟙 S) (by simp) (by simp) := by
    first | rfl
  rw [e]
  exact P.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

theorem kernel_tensor : ∀ (S : Scheme.{0}) (T₁ T₂ G₁ G₂ B₁ B₂ : Over S) [GrpObj B₁] [GrpObj B₂] (i₁ : T₁ ⟶ G₁) (i₂ : T₂ ⟶ G₂) (q₁ : G₁ ⟶ B₁) (q₂ : G₂ ⟶ B₂), IsPullback i₁ (toUnit T₁) q₁ (η : 𝟙_ (Over S) ⟶ B₁) → IsPullback i₂ (toUnit T₂) q₂ (η : 𝟙_ (Over S) ⟶ B₂) → IsPullback (i₁ ⊗ₘ i₂) (toUnit (T₁ ⊗ T₂)) (q₁ ⊗ₘ q₂) (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
  intro S T₁ T₂ G₁ G₂ B₁ B₂ _ _ i₁ i₂ q₁ q₂ h₁ h₂
  have e₁ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ fst _ _ = η := by simp [MonObj.tensorObj.one_def]
  have e₂ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ snd _ _ = η := by simp [MonObj.tensorObj.one_def]
  have c₁ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ fst _ _) ≫ q₁ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ fst _ _) h
    simp only [Category.assoc, tensorHom_fst, e₁] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have c₂ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ snd _ _) ≫ q₂ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ snd _ _) h
    simp only [Category.assoc, tensorHom_snd, e₂] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have w : (i₁ ⊗ₘ i₂) ≫ (q₁ ⊗ₘ q₂) = toUnit (T₁ ⊗ T₂) ≫ (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, e₁, tensorHom_fst_assoc]
      rw [h₁.w, ← Category.assoc, toUnit_unique (fst T₁ T₂ ≫ toUnit T₁) (toUnit _)]
    · simp only [Category.assoc, tensorHom_snd, e₂, tensorHom_snd_assoc]
      rw [h₂.w, ← Category.assoc, toUnit_unique (snd T₁ T₂ ≫ toUnit T₂) (toUnit _)]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (h₁.lift (s.fst ≫ fst _ _) (toUnit _) (c₁ _ _ s.condition))
      (h₂.lift (s.fst ≫ snd _ _) (toUnit _) (c₂ _ _ s.condition)))
    (fun s => ?_) (fun s => toUnit_unique _ _) (fun s m hm _ => ?_)⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, h₂.lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← tensorHom_fst, ← Category.assoc, hm]
      · exact toUnit_unique _ _
    · rw [lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← tensorHom_snd, ← Category.assoc, hm]
      · exact toUnit_unique _ _

variable {S : Scheme.{0}}

theorem isAbelianScheme_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  have := hA.comm; have := hB.comm; have := hA.smooth; have := hB.smooth
  have := hA.proper; have := hB.proper; have := hA.geomConnected; have := hB.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · show Smooth (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show IsProper (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom); exact GeometricallyConnected.comp _ _

theorem torusExtension_of_prod {K : Type} [Field K] {G G₁ G₂ : Over (Spec (.of K))} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] (a₁ : G ⟶ G₁) (a₂ : G ⟶ G₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)]
    (E₁ : TorusExtension G₁) (E₂ : TorusExtension G₂) : Nonempty (TorusExtension G) := by
  let := E₁.addCommGroup; have := E₁.free; have := E₁.finite; let := E₁.grpB
  let := E₂.addCommGroup; have := E₂.free; have := E₂.finite; let := E₂.grpB
  have := E₁.q_hom; have := E₂.q_hom; have := E₁.i_hom; have := E₂.i_hom
  have := torus_prod_iso (Spec (.of K)) E₁.X E₂.X
  have hmon : ∀ {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X'),
      IsMonHom (SplitTorusPow.torusMap (Spec (.of K)) φ) := by
    intro X X' _ _ φ
    constructor
    · have h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus _ X') ≫ SplitTorusPow.torusMap _ φ = 1 := by
        apply (splitTorusPointsEquiv _ X _).injective
        rw [SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h : ∀ {Z : Over (Spec (.of K))} (a b : Z ⟶ splitTorus _ X'),
          (a * b) ≫ SplitTorusPow.torusMap _ φ = (a ≫ SplitTorusPow.torusMap _ φ) * (b ≫ SplitTorusPow.torusMap _ φ) := by
        intro Z a b
        apply (splitTorusPointsEquiv _ X Z).injective
        rw [map_mul, SplitTorusPow.points_comp_torusMap, SplitTorusPow.points_comp_torusMap,
          SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus _ X') (splitTorus _ X')) (snd _ _)
  have := hmon (AddMonoidHom.inl E₁.X E₂.X)
  have := hmon (AddMonoidHom.inr E₁.X E₂.X)
  have key := kernel_tensor _ _ _ _ _ _ _ E₁.i E₂.i E₁.q E₂.q E₁.isKernel E₂.isKernel
  have : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a₁ a₂)))
  have : IsMonHom (inv (lift a₁ a₂)) := inferInstanceAs (IsMonHom (asIso (lift a₁ a₂)).inv)
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P E₁.q.left → P E₂.q.left → P (lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)).left := by
    intro P _ _ h₁ h₂
    rw [Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _) (tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂)
  refine ⟨{ X := E₁.X × E₂.X
            B := E₁.B ⊗ E₂.B
            isAbelian := isAbelianScheme_tensor E₁.isAbelian E₂.isAbelian
            q := lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)
            q_hom := inferInstance
            q_flat := hP @Flat E₁.q_flat E₂.q_flat
            q_surjective := hP @Surjective E₁.q_surjective E₂.q_surjective
            q_quasiCompact := hP @QuasiCompact E₁.q_quasiCompact E₂.q_quasiCompact
            i := lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
                (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)) ≫ (E₁.i ⊗ₘ E₂.i) ≫ inv (lift a₁ a₂)
            i_hom := inferInstance
            isKernel := ?_ }⟩
  refine IsPullback.of_iso key (asIso (lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
    (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)))).symm (asIso (lift a₁ a₂)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, asIso_inv]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact toUnit_unique _ _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem isSemiAbelian_tensor : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  intro S G₁ G₂ _ _ h₁ h₂
  have := h₁.comm; have := h₂.comm; have := h₁.smooth; have := h₂.smooth
  have := h₁.separated; have := h₂.separated; have := h₁.quasiCompact; have := h₂.quasiCompact
  have := h₁.geomConnected; have := h₂.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, fun Ω _ _ p => ?_⟩
  · show Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show QuasiCompact (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show GeometricallyConnected (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); exact GeometricallyConnected.comp _ _
  · obtain ⟨E₁⟩ := h₁.fibres Ω p
    obtain ⟨E₂⟩ := h₂.fibres Ω p
    have : IsIso (lift ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂))) :=
      isIso_prodComparison_of_preservesLimit_pair (Over.pullback p) G₁ G₂
    exact torusExtension_of_prod ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂)) E₁ E₂

end GlobalTheory.SemiProd
