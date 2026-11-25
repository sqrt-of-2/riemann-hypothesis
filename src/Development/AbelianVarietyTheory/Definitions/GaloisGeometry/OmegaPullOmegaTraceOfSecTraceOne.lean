module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

section Sec

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (f : X' ⟶ X)

abbrev secAlg (U : X.Opens) : Algebra (Sec s U) (Sec s' (f ⁻¹ᵁ U)) := (appSec s s' f U).toAlgebra

variable {s s' f}

theorem sec_isScalarTower (hf : f ≫ s = s') (U : X.Opens) :
    letI := secAlg s s' f U
    IsScalarTower k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) :=
  letI := secAlg s s' f U
  .of_algebraMap_eq fun r ↦ ((semiHom_appSec hf U).map_algebraMap r).symm

theorem sec_finite [IsFinite f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := secAlg s s' f U
    Module.Finite (Sec s U) (Sec s' (f ⁻¹ᵁ U)) :=
  f.finite_app U hU

theorem sec_etale [IsFinite f] [Etale f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := secAlg s s' f U
    Algebra.Etale (Sec s U) (Sec s' (f ⁻¹ᵁ U)) := by
  have h := HasRingHomProperty.appLE @Etale f inferInstance ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

variable [IsFinite f] [Etale f]


variable (s s') in
def secTrace {U : X.Opens} (hU : IsAffineOpen U) : Sec s' (f ⁻¹ᵁ U) →+ Sec s U :=
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  (etTrace (Sec s U) (Sec s' (f ⁻¹ᵁ U))).toAddMonoidHom

theorem secTrace_res {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (b' : Sec s' (f ⁻¹ᵁ U)) :
    Sec.res s h (secTrace s s' hU b') = secTrace s s' hV (Sec.res s' (f.preimage_mono h) b') := by
  let : Algebra (Sec s U) (Sec s V) := (Sec.res s h : Sec s U →+* Sec s V).toAlgebra
  let : Algebra (Sec s' (f ⁻¹ᵁ U)) (Sec s' (f ⁻¹ᵁ V)) :=
    (Sec.res s' (f.preimage_mono h) : Sec s' (f ⁻¹ᵁ U) →+* Sec s' (f ⁻¹ᵁ V)).toAlgebra
  let := secAlg s s' f U
  let := secAlg s s' f V
  let : Algebra (Sec s U) (Sec s' (f ⁻¹ᵁ V)) :=
    ((appSec s s' f V).comp (Sec.res s h : Sec s U →+* Sec s V)).toAlgebra
  have : IsScalarTower (Sec s U) (Sec s V) (Sec s' (f ⁻¹ᵁ V)) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Sec s U) (Sec s' (f ⁻¹ᵁ U)) (Sec s' (f ⁻¹ᵁ V)) :=
    .of_algebraMap_eq fun b ↦ ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) b
  have : Algebra.IsPushout (Sec s U) (Sec s' (f ⁻¹ᵁ U)) (Sec s V) (Sec s' (f ⁻¹ᵁ V)) :=
    CommRingCat.isPushout_iff_isPushout.1 (GlobalTheory.FiniteAmple.isPushout_app f hU hV h)
  have := this.symm
  have := sec_finite (s := s) (s' := s') (f := f) hU
  have := sec_etale (s := s) (s' := s') (f := f) hU
  have := sec_finite (s := s) (s' := s') (f := f) hV
  have := sec_etale (s := s) (s' := s') (f := f) hV
  have := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  have := projective_of_etale (Sec s V) (Sec s' (f ⁻¹ᵁ V))
  change Sec.res s h (algTrace (Sec s U) (Sec s' (f ⁻¹ᵁ U)) b') =
    algTrace (Sec s V) (Sec s' (f ⁻¹ᵁ V)) (algebraMap (Sec s' (f ⁻¹ᵁ U)) (Sec s' (f ⁻¹ᵁ V)) b')
  exact (algTrace_of_isPushout (C := Sec s V) (C' := Sec s' (f ⁻¹ᵁ V)) b').symm

end Sec

section Forms

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

def formTraceU (hf : f ≫ s = s') {U : X.Opens} (hU : IsAffineOpen U) (j : ℕ) :
    OmU s' (f ⁻¹ᵁ U) j →+ OmU s U j :=
  letI := secAlg s s' f U
  haveI := sec_isScalarTower hf U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  (formTrace k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) j).toAddMonoidHom

theorem formTraceU_smul_formPull (hf : f ≫ s = s') {U : X.Opens} (hU : IsAffineOpen U) {j : ℕ}
    (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    formTraceU hf hU j (b' • formPull hf U j x) = secTrace s s' hU b' • x := by
  let := secAlg s s' f U
  have := sec_isScalarTower hf U
  have := sec_finite (s := s) (s' := s') (f := f) hU
  have := sec_etale (s := s) (s' := s') (f := f) hU
  exact formTrace_smul_formLin k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) b' x

theorem formTraceU_smul (hf : f ≫ s = s') {U : X.Opens} (hU : IsAffineOpen U) {j : ℕ}
    (b : Sec s U) (y : OmU s' (f ⁻¹ᵁ U) j) :
    formTraceU hf hU j (appSec s s' f U b • y) = b • formTraceU hf hU j y := by
  let := secAlg s s' f U
  have := sec_isScalarTower hf U
  have := sec_finite (s := s) (s' := s') (f := f) hU
  have := sec_etale (s := s) (s' := s') (f := f) hU
  have e : appSec s s' f U b • y = b • y := algebraMap_smul (Sec s' (f ⁻¹ᵁ U)) b y
  rw [e]
  change formTrace k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) j (b • y) = b • formTrace k _ _ j y
  exact (formTrace k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) j).map_smul b y

theorem formOm_induction (hf : f ≫ s = s') {U : X.Opens} (hU : IsAffineOpen U) {j : ℕ}
    {P : OmU s' (f ⁻¹ᵁ U) j → Prop} (h0 : P 0) (ha : ∀ y z, P y → P z → P (y + z))
    (hm : ∀ (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j), P (b' • formPull hf U j x))
    (y : OmU s' (f ⁻¹ᵁ U) j) : P y := by
  let := secAlg s s' f U
  have := sec_isScalarTower hf U
  have := sec_etale (s := s) (s' := s') (f := f) hU
  have hb := isBaseChange_formLin k (Sec s U) (Sec s' (f ⁻¹ᵁ U)) j
  obtain ⟨z, rfl⟩ := hb.equiv.surjective y
  induction z using TensorProduct.induction_on with
  | zero => rw [hb.equiv.map_zero]; exact h0
  | add a b ha' hb' => rw [hb.equiv.map_add]; exact ha _ _ ha' hb'
  | tmul b' x => rw [hb.equiv_tmul]; exact hm b' x

theorem formTraceU_res (hf : f ≫ s = s') {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U) {j : ℕ} (y : OmU s' (f ⁻¹ᵁ U) j) :
    formRes s h j (formTraceU hf hU j y) =
      formTraceU hf hV j (formRes s' (f.preimage_mono h) j y) := by
  refine formOm_induction (P := fun y ↦ formRes s h j (formTraceU hf hU j y) =
      formTraceU hf hV j (formRes s' (f.preimage_mono h) j y)) hf hU ?_ (fun y z hy hz ↦ ?_)
    (fun b' x ↦ ?_) y
  · simp only [map_zero]
  · simp only [map_add (f := _), hy, hz]
  · rw [formTraceU_smul_formPull, formRes_smul, formRes_smul, formRes_formPull,
      formTraceU_smul_formPull, secTrace_res hU hV h]

end Forms

section Omega

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

def omegaTraceU (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Γ((Scheme.Modules.pushforward f).obj (Omega s' j), U) →ₗ[Γ(X, U)] Γ(Omega s j, U) where
  toFun y := toOm s j U (formTraceU hf hU j ((toOmEquiv s' j (hU.preimage f)).symm y))
  map_add' y z := ((toOm s j U).toAddMonoidHom.comp ((formTraceU hf hU j).comp
    (toOmEquiv s' j (hU.preimage f)).symm.toLinearMap.toAddMonoidHom)).map_add y z
  map_smul' r y := by
    change toOm s j U (formTraceU hf hU j ((toOmEquiv s' j (hU.preimage f)).symm
      (appSec s s' f U (show Sec s U from r) • (show Γ(Omega s' j, f ⁻¹ᵁ U) from y)))) = _
    rw [LinearEquiv.map_smul, formTraceU_smul, LinearMap.map_smul]
    rfl

theorem omegaTraceU_toOm (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (y : OmU s' (f ⁻¹ᵁ U) j) :
    omegaTraceU hf j hU (toOm s' j (f ⁻¹ᵁ U) y) = toOm s j U (formTraceU hf hU j y) :=
  congrArg (fun z ↦ toOm s j U (formTraceU hf hU j z))
    ((toOmEquiv s' j (hU.preimage f)).symm_apply_apply y)

theorem omegaTraceU_res (hf : f ≫ s = s') (j : ℕ) {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (h : V ≤ U)
    (y : Γ((Scheme.Modules.pushforward f).obj (Omega s' j), U)) :
    (Omega s j).presheaf.map (homOfLE h).op (omegaTraceU hf j hU y) =
      omegaTraceU hf j hV (((Scheme.Modules.pushforward f).obj (Omega s' j)).presheaf.map
        (homOfLE h).op y) := by
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage f) y
  have e : ((Scheme.Modules.pushforward f).obj (Omega s' j)).presheaf.map (homOfLE h).op
      (toOm s' j (f ⁻¹ᵁ U) z) = toOm s' j (f ⁻¹ᵁ V) (formRes s' (f.preimage_mono h) j z) :=
    res_toOm s' j (f.preimage_mono h) z
  rw [e, omegaTraceU_toOm, omegaTraceU_toOm, res_toOm, formTraceU_res hf hU hV h]

def omegaTrace (hf : f ≫ s = s') (j : ℕ) :
    (Scheme.Modules.pushforward f).obj (Omega s' j) ⟶ Omega s j :=
  homOfAffine (fun U ↦ omegaTraceU hf j U.2) (fun U V h ↦ omegaTraceU_res hf j U.2 V.2 h)

theorem omegaTrace_app_toOm (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (y : OmU s' (f ⁻¹ᵁ U) j) :
    (omegaTrace hf j).app U (toOm s' j (f ⁻¹ᵁ U) y) = toOm s j U (formTraceU hf hU j y) :=
  (homOfAffine_app _ _ ⟨U, hU⟩ _).trans (omegaTraceU_toOm hf j hU y)

theorem omegaTrace_toOm_smul_formPull (hf : f ≫ s = s') (j : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j) :
    (omegaTrace hf j).app U (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x)) =
      toOm s j U (secTrace s s' hU b' • x) := by
  rw [omegaTrace_app_toOm hf j hU, formTraceU_smul_formPull]

theorem omegaTrace_ext (hf : f ≫ s = s') (j : ℕ)
    (T : (Scheme.Modules.pushforward f).obj (Omega s' j) ⟶ Omega s j)
    (hT : ∀ (U : X.Opens) (hU : IsAffineOpen U) (b' : Sec s' (f ⁻¹ᵁ U)) (x : OmU s U j),
      T.app U (toOm s' j (f ⁻¹ᵁ U) (b' • formPull hf U j x)) =
        toOm s j U (secTrace s s' hU b' • x)) : T = omegaTrace hf j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage f) y
  refine formOm_induction (P := fun z ↦ T.app U (toOm s' j (f ⁻¹ᵁ U) z) =
      (omegaTrace hf j).app U (toOm s' j (f ⁻¹ᵁ U) z)) hf hU ?_ (fun y z hy hz ↦ ?_)
    (fun b' x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · rw [hT U hU, omegaTrace_toOm_smul_formPull]

end Omega

section Hodge

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

def hodgeTrace (hf : f ≫ s = s') (j q : ℕ) : hodgeH s' j q →ₗ[k] hodgeH s j q :=
  letI := algΓ s; letI := algΓ s'
  cohOn.map k (omegaTrace hf j) ⊤ q ∘ₗ
    (coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q).symm.toLinearMap

theorem hodgeTrace_hodgePull (hf : f ≫ s = s') (j q : ℕ) (x : hodgeH s j q) :
    letI := algΓ s
    hodgeTrace hf j q (hodgePull hf j q x) = cohOn.map k (omegaPull hf j ≫ omegaTrace hf j) ⊤ q x := by
  letI := algΓ s; letI := algΓ s'
  have e : hodgePull hf j q x = coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q
      (cohOn.map k (omegaPull hf j) ⊤ q x) := by
    have e' := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hf)
      (𝟙 ((Scheme.Modules.pushforward f).obj (Omega s' j))) (omegaPull hf j) (le_refl (f ⁻¹ᵁ ⊤))
      (n := q) x
    rw [Category.comp_id] at e'
    exact e'.symm
  change cohOn.map k (omegaTrace hf j) ⊤ q
    ((coh.pushforwardEquiv k (appTop_algebraMap hf) (Omega s' j) q).symm (hodgePull hf j q x)) = _
  rw [e, LinearEquiv.symm_apply_apply, cohOn.map_comp]
  rfl

end Hodge

section Identity

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

theorem secTrace_appSec_of_bijective {U : X.Opens} (hU : IsAffineOpen U)
    (h : Function.Bijective (appSec s s' f U)) (b : Sec s U) :
    secTrace s s' hU (appSec s s' f U b) = b := by
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  exact algTrace_algebraMap_of_bijective h b


variable (s) in
theorem secTrace_id {U : X.Opens} (hU : IsAffineOpen U) (b : Sec s U) :
    secTrace (f := 𝟙 X) s s hU b = b := by
  have h : Function.Bijective (appSec s s (𝟙 X) U) :=
    ConcreteCategory.bijective_of_isIso (Scheme.Hom.app (𝟙 X) U)
  have e : appSec s s (𝟙 X) U b = b := by
    change (Scheme.Hom.app (𝟙 X) U).hom b = b
    rw [Scheme.Hom.id_app]; rfl
  conv_lhs => rw [← e]
  exact secTrace_appSec_of_bijective hU h b


variable (s) in
theorem omegaTrace_id (j : ℕ) :
    omegaTrace (f := 𝟙 X) (Category.id_comp s) j =
      (Scheme.Modules.pushforwardId X).hom.app (Omega s j) := by
  refine (omegaTrace_ext (Category.id_comp s) j _ fun U hU b' x ↦ ?_).symm
  change toOm s j U (b' • formPull (f := 𝟙 X) (Category.id_comp s) U j x) =
    toOm s j U (secTrace s s hU b' • x)
  congr 1
  erw [secTrace_id s hU, formPull_id]
  rfl


variable (s) in
theorem hodgeTrace_id (j q : ℕ) (x : hodgeH s j q) :
    hodgeTrace (f := 𝟙 X) (Category.id_comp s) j q x = x := by
  letI := algΓ s
  have e := hodgeTrace_hodgePull (f := 𝟙 X) (Category.id_comp s) j q x
  rw [hodgePull_id, omegaPull_id, omegaTrace_id, Iso.inv_hom_id_app] at e
  exact e.trans (LinearMap.congr_fun (cohOn.map_id k _ ⊤ q) x)

end Identity

section Degree

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

end Degree

end GlobalTheory.HodgeCoh
