module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Algebra.Star.Subsemiring
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.UniformSpace.Uniformizable
import TauCeti.NumberTheory.NumberField.Countable
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ResidueField
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.BorelSpace
public import Lib.Speed

/-!
# Finite adeles of number fields: topology, idempotents, functoriality and base change

This file develops the finite adeles `New.𝔸f E` of a number field `E` and their subring `New.Ô E` of
integral adeles. The valuation `Valued.v` of a completion, written `v`, is multiplicative with
values in `ℤᵐ⁰` (the integers, written multiplicatively by `exp`, with a zero adjoined), so that
integral elements have `v ≤ 1`. The file covers the topology of completions and finite adeles, and
the idempotents `New.idem` of sets of places. It also covers functoriality along embeddings of
number fields through `New.adeleMap`, and base change along an extension `L / K`. For CM fields,
complex conjugation `star` is extended to places and finite adeles, and commutes with
`New.adeleMap`; it induces maps `New.conjLoc` between the completions at conjugate places.

## Main definitions and results

* `New.FinPlace`, `New.LocField`, `New.LocInt`, `New.ResField`: finite places, completions, their
  integers and residue fields; `New.𝔸f`, `New.Ô`: finite adeles and integral finite adeles;
  `New.evalAt w` is the ring homomorphism taking a finite adele to its component in the completion
  `New.LocField w`.
* `New.isCompact_Ô`, `New.isOpen_Ô`: the integral adeles `New.Ô E` are compact and open.
* `New.denseRange_algebraMap_Ô`, `New.denseRange_algebraMap_finAdele`: `𝓞 E` is dense in `Ô E` and
  `E` is dense in the finite adeles (strong approximation), which are a Polish space.
* `New.adeleCombination`: for a basis `b` of `L / K`, the map `(a i) ↦ ∑ a i • b i` from `ι → 𝔸f K`
  to `𝔸f L`.
* `New.isHomeomorph_adeleCombination`: this map is a homeomorphism.
* `New.mem_range_finAdeleIncl_iff`: for `L / K` Galois, the adeles fixed by `Gal(L/K)` are those
  from `K`.

## Relation to the literature

Known result: the topology of the finite adeles of a number field, strong approximation and base
change. Base change is proved for finite adeles only, and the full adeles are those of totally
complex fields with chosen embeddings.

Source: J. W. S. Cassels, Global Fields, in Cassels-Fröhlich, Algebraic Number Theory, 1967, ch. II
§§14-16; A. Weil, Basic Number Theory, ch. IV.
-/

@[expose] public section

noncomputable section

/-!
## Places, completions, adeles and CM fields

* `New.𝔸`: the adeles with one factor `ℂ` for each infinite place (meant for totally complex
  fields). The diagonal embedding `New.toAdele` depends on the choice of embeddings
  `New.PlaceEmbedding`; `New.CMType` is a CM number field with such a choice.
* For a CM field, `star` is complex conjugation on the integers and the places, and `New.conjLoc`
  is the map that it induces between the completions at conjugate places;
  `New.HasPrimitiveRoot5040` is the class of CM fields that contain a primitive root of unity of
  order `5040`.
-/

section AdeleDefs

open NumberField Ideal IsDedekindDomain Filter Valued IsCMField RestrictedProduct Set
  IsLocalRing HeightOneSpectrum WithZeroTopology WithZero adicCompletion UniformSpace.Completion
open scoped Classical

namespace New

variable (E : Type*) [Field E]

/-- A choice, for each infinite place w of E, of a complex embedding Φ w of E that induces w. -/
class PlaceEmbedding where
  /-- For each infinite place w, a complex embedding of E. -/
  Φ : InfinitePlace E → E →+* ℂ
  /-- The embedding Φ w induces the place w. -/
  mk_Φ (w : InfinitePlace E) : InfinitePlace.mk (Φ w) = w

export PlaceEmbedding (Φ mk_Φ)

attribute [simp] mk_Φ

instance (priority := low) : PlaceEmbedding E where
  Φ := InfinitePlace.embedding
  mk_Φ := InfinitePlace.mk_embedding

/-- A CM number field E together with a choice, for each infinite place w of E, of a complex
embedding of E that induces w.
So `[CMType E]` includes the hypothesis that E is a CM number field. -/
class CMType extends NumberField E, IsCMField E, PlaceEmbedding E

variable [NumberField E]

/-- A number field is integral over `ℚ`. The instance `Star E` on a CM field needs this fact, and
instance search is too slow to find it. -/
instance isIntegral_rat : Algebra.IsIntegral ℚ E := .of_finite ℚ E

/-- The set of finite places of E, that is, nonzero prime ideals of its ring of integers. -/
abbrev FinPlace : Type _ := HeightOneSpectrum (𝓞 E)

/-- The ring of finite adeles of the number field E. -/
abbrev 𝔸f : Type _ := FiniteAdeleRing (𝓞 E) E

instance : DecidableEq (InfinitePlace E) := Classical.decEq _

/-- The product of one copy of ℂ for each infinite place of E with the finite adeles of E. It is the
adele ring of E when E is totally complex. -/
abbrev 𝔸 : Type _ := (InfinitePlace E → ℂ) × 𝔸f E

variable {E} (w : FinPlace E)

/-- The diagonal embedding of E in its adeles, given at the infinite places by the embeddings chosen
in `New.PlaceEmbedding`. -/
@[simps! apply_fst apply_snd]
def toAdele [PlaceEmbedding E] : E →+* 𝔸 E := RingHom.prod (RingHom.pi Φ) (algebraMap E (𝔸f E))

-- An element of `E` is read as an adele and as a finite adele, by the diagonal embeddings.
instance [PlaceEmbedding E] : Coe E (𝔸 E) := ⟨toAdele⟩

instance : Coe E (𝔸f E) := ⟨algebraMap E (𝔸f E)⟩

/-- The completion E_w of E at the finite place w. -/
abbrev LocField : Type _ := w.adicCompletion E

/-- The ring of integers of the completion E_w of E at the finite place w. -/
abbrev LocInt : ValuationSubring (adicCompletion E w) := w.adicCompletionIntegers E

instance : CommSemiring (LocInt w) := CommRing.toCommSemiring

/-- The residue field of the completion E_w of E at the finite place w. -/
@[instance_reducible]
def ResField : Type _ := IsLocalRing.ResidueField (LocInt w)
  deriving Field, Algebra (𝓞 E)

/-- The absolute norm of the prime ideal w, that is, the order of its residue field. -/
abbrev FinPlace.q : ℕ := w.asIdeal.absNorm

@[simp] lemma FinPlace.one_lt_q : 1 < w.q := one_lt_absNorm w

lemma FinPlace.q_sub_one_pos : 0 < w.q - 1 := Nat.sub_pos_of_lt w.one_lt_q

lemma FinPlace.one_le_q : 1 ≤ w.q := w.one_lt_q.le

lemma FinPlace.q_pos : 0 < w.q := zero_lt_one.trans w.one_lt_q

lemma FinPlace.q_ne_zero : w.q ≠ 0 := w.q_pos.ne'

/-- The four consequences of `1 < w.q` for the order `w.q` of the residue field at `w`, collected
for `simp`. -/
@[simp] lemma FinPlace.q_bounds : 0 < w.q - 1 ∧ w.q ≠ 0 ∧ 1 ≤ w.q ∧ 0 < w.q :=
  ⟨w.q_sub_one_pos, w.q_ne_zero, w.one_le_q, w.q_pos⟩

/-- A chosen uniformiser of the completion of E at the finite place w. -/
def uniformizer : (adicCompletion E w)ˣ :=
  -- an element of valuation `exp (-1)`, which is not zero
  Units.mk0 (w.valuedAdicCompletion_surjective E (exp (-1))).choose (by grind [exp_pos])

/-- The chosen uniformiser at w has valuation exp (-1), the largest value less than 1. -/
@[simp] lemma v_uniformizer : v (uniformizer w).val = exp (-1) := by
  simpa [uniformizer] using (w.valuedAdicCompletion_surjective E (exp (-1))).choose_spec

/-- The ring homomorphism sending a finite adele to its component in E_w. -/
def evalAt : 𝔸f E →+* LocField w := evalRingHom (fun v ↦ LocField v) w

@[simp] lemma evalAt_apply (x : 𝔸f E) : evalAt w x = x w := rfl

/-- The map sending a in E_w to the finite adele with component a at w and 0 elsewhere, a ring
homomorphism that does not preserve 1. -/
def singleAdele : LocField w →ₙ+* 𝔸f E :=
  letI : (i : FinPlace E) → AddCommGroup (LocField i) := fun i ↦
    (inferInstance : Field (LocField i)).toAddCommGroup
  { toFun := RestrictedProduct.single LocInt w
    map_mul' := fun x y ↦ Subtype.ext (Pi.single_mul w x y)
    map_zero' := single_zero LocInt w
    map_add' := single_add LocInt w }

@[simp] lemma singleAdele_same (x : LocField w) : singleAdele w x w = x := dite_eq_left rfl

@[simp]
lemma singleAdele_of_ne {v w : FinPlace E} (hv : v ≠ w) (x : LocField w) : singleAdele w x v = 0 :=
  dite_eq_right hv

variable (E) in
/-- The subring Ô of finite adeles of E that are integral at every finite place: Tau Ceti's
integral adeles `FiniteAdeleRing.integralAdeles`, as a subring. -/
def Ô : Subring (𝔸f E) := (FiniteAdeleRing.integralAdeles (𝓞 E) E).toSubring

/-- A finite adele x is integral if and only if each of its components has valuation at most 1. -/
lemma mem_Ô {x : 𝔸f E} : x ∈ Ô E ↔ ∀ w : HeightOneSpectrum (𝓞 E), v (x w) ≤ 1 :=
  FiniteAdeleRing.mem_integralAdeles.trans (forall_congr' fun _ ↦ mem_adicCompletionIntegers ..)

/-- Reduction modulo w: the ring homomorphism from the integral finite adeles to the residue
field at w. -/
def reduceAt : Ô E →+* ResField w :=
  (residue (LocInt w)).comp
    (((evalAt w).domRestrict (Ô E)).codRestrict (LocInt w) fun x ↦ mem_Ô.1 x.property w)

instance : MeasurableSpace (LocField w) := borel _

instance : BorelSpace (LocField w) := ⟨rfl⟩

-- The finite adeles `𝔸f E` carry Tau Ceti's Borel σ-algebra, local compactness and Polish
-- structure (`FiniteAdeleRing.instMeasurableSpace`, `instBorelSpace`, `instLocallyCompactSpace`,
-- `instPolishSpace`); the last two use the instance `finite_quotient_asIdeal`.

/-- Tau Ceti's Polish structure, as a shortcut: found through `instPolishSpace` inside products
such as `(n → InfinitePlace E → ℂ) × (n → 𝔸f E)`, the instance term exceeds
`synthInstance.maxSize`. -/
instance : PolishSpace (𝔸f E) := inferInstance

/-- Tau Ceti's second countability, as a shortcut, for the same reason. -/
instance : SecondCountableTopology (𝔸f E) := inferInstance

/-- The structure of ring with involution on a commutative ring R given by a ring endomorphism
whose square is the identity. -/
abbrev starRingOfInvolution {R : Type*} [CommRing R] (star : R →+* R)
    (star_involutive : Function.Involutive star) : StarRing R where
  star := star
  star_involutive := star_involutive
  star_mul := by grind
  star_add := by grind

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] (f : K →+* L)
  {w : FinPlace K} (x : 𝓞 K)

/-! ### Valuations on the completions -/

/-- The valuation v of the completion at w extends the w-adic valuation of K. -/
@[local simp]
lemma v_algebraMap_eq_valuation {w : FinPlace K} (x : K) :
    v (algebraMap K (LocField w) x) = w.valuation K x :=
  valued_coe ..

lemma mem_LocInt {w : FinPlace K} {x : adicCompletion K w} : x ∈ LocInt w ↔ v x ≤ 1 := .rfl

/-- On the ring of integers of K, the valuation of the completion at w is the w-adic valuation. -/
lemma v_algebraMap_eq_intValuation : v (algebraMap K (LocField w) x) = w.intValuation x := by
  simp [valuation_of_algebraMap]

lemma v_algebraMap_eq_one {w : FinPlace K} {x : 𝓞 K} (hx : x ∉ w.asIdeal) :
    v (algebraMap K (LocField w) x) = 1 :=
  (v_algebraMap_eq_intValuation x).trans (intValuation_eq_one_iff.2 hx)

@[local fun_prop] lemma continuous_v {w : FinPlace K} : Continuous (v : LocField w → ℤᵐ⁰) :=
  continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective K)

/-- Only finitely many finite places of K divide a given nonzero natural number n. -/
lemma finite_natCast_mem (n : ℕ) [NeZero n] : {v : FinPlace K | (n : 𝓞 K) ∈ v.asIdeal}.Finite := by
  simp [← dvd_span_singleton, finite_factors, NeZero.ne]

/-! ### Functoriality in the number field -/

/-- For f: K → L and a finite place w of L, the finite place of K below w: the preimage under f
of the prime ideal w. -/
def FinPlace.comap (w : FinPlace L) : FinPlace K :=
  let := f.toAlgebra
  w.under (𝓞 K)

/-- For an extension L/K, the finite place of K below the finite place w of L. -/
abbrev FinPlace.below (K : Type*) [Field K] [Algebra K L] (w : FinPlace L) : FinPlace K :=
  comap (algebraMap K L) w

/-- Let `e` be a map with dense range in a space `X`. Two maps `f`, `g` from `X` to a Hausdorff
space that are continuous (hypotheses `hf_cont`, `hg_cont`) and agree at every point `e i`
(hypothesis `h_agree`) agree at every point `x`. This is the pointwise form of
`DenseRange.equalizer`; by default continuity is proved by `fun_prop`. -/
lemma _root_.DenseRange.eq {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {e : ι → X} (he : DenseRange e) {f g : X → Y} (h_agree : ∀ i : ι, f (e i) = g (e i))
    (hf_cont : Continuous f := by fun_prop) (hg_cont : Continuous g := by fun_prop) (x : X) :
    f x = g x :=
  he.induction_on x (isClosed_eq hf_cont hg_cont) h_agree

variable {u : FinPlace K} {w : FinPlace L}

/-- For a finite place w of L above the finite place u of K, the continuous extension of
`f : K → L` to a homomorphism of the completions at u and at w. -/
def locMap (h : w.comap f = u) : adicCompletion K u →+* adicCompletion L w :=
  let := f.toAlgebra
  have : w.asIdeal.LiesOver u.asIdeal := .mk (congrArg HeightOneSpectrum.asIdeal h).symm
  -- `f` is uniformly continuous for the valuations at `u` and `w`, so it extends to the completions
  (equiv L w).symm.toRingHom.comp
    ((mapRingHom _ (uniformContinuous_algebraMap_liesOver K L u w).continuous).comp
      (equiv K u).toRingHom)

@[fun_prop] lemma continuous_locMap {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u) :
    Continuous (locMap f hw) :=
  continuous_induced_rng.mpr (continuous_map.comp (by fun_prop))

/-- For a finite place `w` of `L` above the place `u` of `K`, the map of completions `locMap f hw`
extends the field homomorphism `f : K →+* L`. -/
@[simp] lemma locMap_algebraMap {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u) (x : K) :
    locMap f hw (algebraMap K (adicCompletion K u) x) =
      algebraMap L (adicCompletion L w) (f x) := by
  let : Algebra K L := f.toAlgebra
  have : w.asIdeal.LiesOver u.asIdeal := .mk (congrArg HeightOneSpectrum.asIdeal hw).symm
  let φ : WithVal (u.valuation K) →+* WithVal (w.valuation L) := algebraMap _ _
  have hφ : Continuous φ := (uniformContinuous_algebraMap_liesOver K L u w).continuous
  let x' : WithVal (u.valuation K) := algebraMap K _ x
  -- Through `equiv`, the map `locMap f hw` is the extension of `φ` to the uniform completions.
  change (equiv L w).symm (mapRingHom φ hφ x') = (equiv L w).symm (φ x')
  rw [mapRingHom_coe]

attribute [irreducible] locMap

/-- Let `f : K →+* L` be an embedding of number fields and `w` a finite place of `L` above the place
`u` of `K`. Along the induced map `locMap f hw` of completions, the valuation `v` is raised to some
nonzero power `e`. -/
lemma exists_v_locMap_eq_pow {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u) :
    ∃ e : ℕ, e ≠ 0 ∧ ∀ x : adicCompletion K u, v (locMap f hw x) = v x ^ e := by
  let : Algebra K L := f.toAlgebra
  have : w.asIdeal.LiesOver u.asIdeal := .mk (congrArg HeightOneSpectrum.asIdeal hw).symm
  -- Take for `e` the ramification index of `w` over `u`. Both sides are continuous in `x`, so it
  -- suffices to treat elements of `K`, which is dense in its completion.
  refine ⟨w.asIdeal.ramificationIdx (𝓞 K), (w.asIdeal.ramificationIdx_pos (𝓞 K)).ne',
    (denseRange_algebraMap K u).eq fun x : K ↦ ?_⟩
  simpa only [locMap_algebraMap, v_algebraMap_eq_valuation] using!
    (valuation_liesOver L u w x).symm

/-- The map of completions induced by a field homomorphism preserves and reflects integrality. -/
@[simp] lemma v_locMap_le_one_iff {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u)
    {x : adicCompletion K u} : v (locMap f hw x) ≤ 1 ↔ v x ≤ 1 := by
  obtain ⟨e, he, h_pow⟩ := exists_v_locMap_eq_pow f hw
  rw [h_pow x, pow_le_one_iff he]

/-- The pullback of the valuation at w along the map of completions is equivalent to the valuation
at the place u below w. -/
lemma isEquiv_comap_locMap {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u) :
    (v.comap (locMap f hw)).IsEquiv v :=
  Valuation.isEquiv_of_val_le_one (by simp)

/-- If some value `log v (locMap f hw z)` is `±1`, then the map of completions `locMap f hw` induced
by f: K → L at a place w above u preserves the valuation. -/
lemma v_locMap_eq_of_isUnit_log {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u)
    (h_unit : ∃ z : adicCompletion K u, IsUnit (v (locMap f hw z)).log) (x : adicCompletion K u) :
    v (locMap f hw x) = v x := by
  -- the valuation is raised to a power `e` that divides a unit of `ℤ`, so `e = 1`
  obtain ⟨e, -, h_pow⟩ := exists_v_locMap_eq_pow f hw
  obtain ⟨z, hz⟩ := h_unit
  have h_mul : IsUnit (e * (v z).log) := by simpa [h_pow] using hz
  obtain rfl : e = 1 := by simpa [Int.ofNat_isUnit] using isUnit_of_mul_isUnit_left h_mul
  rw [h_pow, pow_one]

/-- For a surjective field homomorphism f, the map of completions preserves the valuation. -/
lemma v_locMap_eq_of_surjective {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u)
    (hf : Function.Surjective f) : ∀ x : adicCompletion K u, v (locMap f hw x) = v x := by
  -- as `f` is onto, `v ∘ locMap f hw` takes the value `exp 1`, whose logarithm is a unit of `ℤ`
  obtain ⟨a, ha⟩ : ∃ a : K, w.valuation L (f a) = exp 1 := (w.valuation_surjective L).comp hf _
  exact v_locMap_eq_of_isUnit_log f hw ⟨algebraMap K (adicCompletion K u) a, by simp [ha]⟩

omit [NumberField K] in
/-- The map taking a place of L to the place of K below it along f: K → L tends to the cofinite
filter along the cofinite filter, as its fibres are finite. -/
lemma tendsto_place_comap_cofinite : Tendsto (FinPlace.comap f) cofinite cofinite := by
  -- the places above `u` divide the nonzero ideal generated by `u`, so they are finitely many
  let : Algebra K L := f.toAlgebra
  refine .cofinite_of_finite_preimage_singleton fun u ↦
    (finite_factors (map_ne_bot_of_ne_bot (S := 𝓞 L) u.ne_bot)).subset ?_
  rintro w rfl
  change w.asIdeal ∣ (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))).map (algebraMap (𝓞 K) (𝓞 L))
  exact dvd_iff_le.2 map_comap_le

/-- For an embedding f: K → L of number fields, the induced ring homomorphism from the finite
adeles of K to those of L; it gives base change and the Galois action. -/
def adeleMap : 𝔸f K →+* 𝔸f L :=
  mapAlongRingHom LocField LocField (FinPlace.comap f) (tendsto_place_comap_cofinite f)
    (fun _ ↦ locMap f rfl) (by simp [MapsTo, mem_LocInt])

variable (K L) in
/-- For an extension of number fields L over K, the inclusion of the finite adeles of K in those
of L. -/
abbrev finAdeleIncl [Algebra K L] : 𝔸f K →+* 𝔸f L := adeleMap (algebraMap K L)

/-- The component at w of the image of a finite adele x is the image of the component of x at the
place u below w. -/
lemma adeleMap_apply {u : FinPlace K} {w : FinPlace L} (hw : w.comap f = u) (x : 𝔸f K) :
    adeleMap f x w = locMap f hw (x u) := by
  subst hw
  rfl

@[fun_prop] lemma continuous_adeleMap : Continuous (adeleMap f) :=
  mapAlong_continuous LocField LocField (FinPlace.comap f) (tendsto_place_comap_cofinite f) _
    (by simp [MapsTo, mem_LocInt]) fun _ ↦ continuous_locMap f rfl

/-- The homomorphism of finite adeles induced by f extends f. -/
@[simp] lemma adeleMap_algebraMap (x : K) : adeleMap f x = f x := by
  ext1 w
  exact (adeleMap_apply f rfl _).trans (locMap_algebraMap f rfl x)

/-! ### CM fields: complex conjugation and roots of unity -/

variable [IsCMField E]

instance : StarRing (𝓞 E) := starRingOfInvolution (ringOfIntegersComplexConj E) (by aesop_cat)

@[simp, norm_cast] lemma coe_star_ringOfIntegers (x : 𝓞 E) : star x = star x.val := rfl

/-- A complex embedding φ of a CM field E commutes with complex conjugation: φ (x̄) is the complex
conjugate of φ x. -/
@[simp] lemma map_star_complex (φ : E →+* ℂ) (x : E) : φ (star x) = star (φ x) :=
  complexEmbedding_complexConj ..

/-- An embedding f : K → L of CM fields commutes with complex conjugation. -/
lemma map_star_CM [IsCMField K] [IsCMField L] (x : K) : f (star x) = star (f x) := by
  -- apply a complex embedding `φ` of `L`; `map_star_complex` holds for `φ ∘ f` and for `φ`
  let φ : L →+* ℂ := Φ Classical.ofNonempty
  exact φ.injective ((map_star_complex (φ.comp f) x).trans (map_star_complex φ (f x)).symm)

instance : InvolutiveStar (FinPlace E) where
  star := comap (starRingEnd (𝓞 E)) star_involutive.surjective
  star_involutive w := by aesop

/-- The finite place w of the CM field E is split over the maximal real subfield: it differs
from its complex conjugate. -/
abbrev FinPlace.IsSplit (w : FinPlace E) : Prop := star w ≠ w

@[simp]
lemma mem_star_place {w : FinPlace E} {x : 𝓞 E} : x ∈ (star w).asIdeal ↔ star x ∈ w.asIdeal := .rfl

variable {u w : FinPlace E} (h : star u = w)

variable (E) in
/-- The CM field `E` contains a primitive root of unity of order `7! = 5040`. Then the integers of
`E` contain an element `i` with `i² = -1` and `ī = -i`
(`New.HasPrimitiveRoot5040.exists_mul_self_eq_neg_one`), and an element `ω` with `ω + ω̄ = 1` and
`ω ω̄ = 2` (`New.HasPrimitiveRoot5040.exists_add_star_eq_one_mul_star_eq_two`).
So `y = i ω` has `y - ȳ = i`, a unit
(`New.HasPrimitiveRoot5040.exists_isUnit_sub_star`), and `E` is unramified at the finite places
over its maximal real subfield `E⁺`. In the comments such a field `E` is called stably unramified.
A place over `2` divides exactly one of `ω`, `ω̄`, so it is not fixed by conjugation. -/
class HasPrimitiveRoot5040 [IsCMField E] : Prop where
  /-- `E` contains a primitive root of unity of order `7! = 5040`. -/
  exists_primitive_root : ∃ ζ : E, IsPrimitiveRoot ζ 5040

/-- Complex conjugation `star` inverts the roots of unity in the ring of integers `𝓞 E` of a CM
number field `E`. -/
lemma star_mul_self_of_isPrimitiveRoot {n : ℕ} {y : 𝓞 E} (hn : n ≠ 0)
    (hy : IsPrimitiveRoot y n) : star y * y = 1 := by
  let u : (𝓞 E)ˣ := (hy.isUnit hn).unit
  have hu : IsOfFinOrder u := (hy.isUnit_unit hn).isOfFinOrder hn
  have h_conj : unitsComplexConj E u = u⁻¹ := unitsComplexConj_torsion E ⟨u, hu⟩
  calc star y * y = (unitsComplexConj E u * u : (𝓞 E)ˣ) := rfl
    _ = 1 := by rw [h_conj, inv_mul_cancel, Units.val_one]

/-- If the CM field `E` contains a primitive 5040-th root of unity, then its integers contain a
primitive `n`-th root of unity for each divisor `n` of `5040`. -/
lemma HasPrimitiveRoot5040.exists_isPrimitiveRoot_of_dvd [HasPrimitiveRoot5040 E] {n : ℕ}
    (hn : n ∣ 5040) : ∃ y : 𝓞 E, IsPrimitiveRoot y n := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, IsPrimitiveRoot ζ 5040 := exists_primitive_root
  obtain ⟨d, hd⟩ : ∃ d : ℕ, 5040 = d * n := exists_eq_mul_left_of_dvd hn
  exact ⟨hζ.toInteger ^ d, hζ.toInteger_isPrimitiveRoot.pow (by norm_num) hd⟩

/-- If the CM field `E` contains a primitive 5040-th root of unity, then its integers contain a
square root of `-1`, and conjugation negates it. -/
lemma HasPrimitiveRoot5040.exists_mul_self_eq_neg_one [HasPrimitiveRoot5040 E] :
    ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i := by
  obtain ⟨i, hi⟩ : ∃ i : 𝓞 E, IsPrimitiveRoot i 4 := exists_isPrimitiveRoot_of_dvd (by norm_num)
  have hi_sq : i ^ 2 = -1 := (hi.pow (by norm_num) rfl).eq_neg_one_of_two_right
  have h_inv : star i * i = 1 := star_mul_self_of_isPrimitiveRoot (by norm_num) hi
  exact ⟨i, by grind, by grind⟩

/-- If the CM field `E` contains a primitive 5040-th root of unity, then its integers contain an
element of trace `1` and norm `2` over the maximal real subfield, that is, one of the numbers
`(1 ± √-7) / 2`. -/
lemma HasPrimitiveRoot5040.exists_add_star_eq_one_mul_star_eq_two [HasPrimitiveRoot5040 E] :
    ∃ ω : 𝓞 E, ω + star ω = 1 ∧ ω * star ω = 2 := by
  -- `ω = -(η + η ^ 2 + η ^ 4)`, minus a Gaussian period of a primitive 7th root of unity `η`.
  obtain ⟨η, hη⟩ : ∃ η : 𝓞 E, IsPrimitiveRoot η 7 := exists_isPrimitiveRoot_of_dvd (by norm_num)
  have h_pow : η ^ 7 = 1 := hη.pow_eq_one
  have h_sum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 + η ^ 6 = 0 := by
    simpa [Finset.sum_range_succ] using hη.geom_sum_eq_zero (by norm_num)
  have h_inv : star η * η = 1 := star_mul_self_of_isPrimitiveRoot (by norm_num) hη
  have h_star : star η = η ^ 6 := by linear_combination η ^ 6 * h_inv - star η * h_pow
  have h_conj : star (-(η + η ^ 2 + η ^ 4)) = -(η ^ 3 + η ^ 5 + η ^ 6) := by
    simp only [star_neg, star_add, star_pow, h_star]
    linear_combination (-η ^ 5 - η ^ 3 * (η ^ 14 + η ^ 7 + 1)) * h_pow
  refine ⟨-(η + η ^ 2 + η ^ 4), ?_, ?_⟩
  · linear_combination h_conj - h_sum
  · linear_combination -(η + η ^ 2 + η ^ 4) * h_conj + h_sum + (3 + η + η ^ 2 + η ^ 3) * h_pow

/-- If the CM field `E` contains a primitive 5040-th root of unity, then its ring of integers `𝓞 E`
contains a square root `i` of `-1`, negated by complex conjugation `star`, and an element `ω` of
trace `1` and norm `2` over the maximal real subfield of `E`. -/
lemma HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two [HasPrimitiveRoot5040 E] :
    ∃ i ω : 𝓞 E, i * i = -1 ∧ star i = -i ∧ ω + star ω = 1 ∧ ω * star ω = 2 := by
  obtain ⟨i, hi_sq, hi_star⟩ := exists_mul_self_eq_neg_one (E := E)
  obtain ⟨ω, hω_trace, hω_norm⟩ := exists_add_star_eq_one_mul_star_eq_two (E := E)
  exact ⟨i, ω, hi_sq, hi_star, hω_trace, hω_norm⟩

/-- If the CM field `E` contains a primitive 5040-th root of unity, then some algebraic integer `y`
of `E` differs from its complex conjugate `star y` by a unit. -/
lemma HasPrimitiveRoot5040.exists_isUnit_sub_star [HasPrimitiveRoot5040 E] :
    ∃ y : 𝓞 E, IsUnit (y - star y) := by
  obtain ⟨i, hi_sq, hi_star⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i := exists_mul_self_eq_neg_one
  obtain ⟨ω, hω_trace : ω + star ω = 1, -⟩ := exists_add_star_eq_one_mul_star_eq_two (E := E)
  -- `i * ω - star (i * ω) = i * (ω + star ω) = i`, with inverse `-i`
  have h_sub : i * ω - star (i * ω) = i := by
    rw [star_mul', hi_star]
    linear_combination i * hω_trace
  exact ⟨i * ω, .of_mul_eq_one (-i) (by rw [h_sub, mul_neg, hi_sq, neg_neg])⟩

/-- For finite places u, w with ū = w, the homomorphism E_u → E_w of completions induced by
complex conjugation. -/
def conjLoc : adicCompletion E u →+* adicCompletion E w :=
  locMap (starRingEnd E) (star_eq_iff_star_eq.mp h)

@[simp] lemma v_conjLoc {u w : FinPlace E} (h : star u = w) (x : adicCompletion E u) :
    v (conjLoc h x) = v x :=
  v_locMap_eq_of_surjective _ _ starRingAut.surjective x

/-- The valuation of x̄ at the conjugate place w̄ equals the valuation of x at w. -/
@[simp] lemma valuation_star (w : FinPlace E) (x : E) :
    (star w).valuation E (star x) = w.valuation E x := by
  have h_map : conjLoc (rfl : star w = star w) (algebraMap E (LocField w) x) =
      algebraMap E (LocField (star w)) (star x) := locMap_algebraMap (starRingEnd E) _ x
  rw [← v_algebraMap_eq_valuation (star x), ← h_map, v_conjLoc, v_algebraMap_eq_valuation]

end New

end AdeleDefs

/-!
## Topology of local fields and finite adeles

* Local fields: the residue field has order `w.q` (`New.card_ResField`), so `New.LocField w` is
  proper and its ring of integers `New.LocInt w` is compact.
* `New.mem_nhds_zero_finAdele_iff`: the sets `N * Ô E`, for `N ≠ 0` natural, are a basis of
  neighbourhoods of `0`.
-/

namespace New

open NumberField IsDedekindDomain HeightOneSpectrum WithZero WithZeroTopology IsTopologicalAddGroup
  Valued integer RestrictedProduct Nat Set Fact IsRightUniformAddGroup IsIntegralClosure IsLocalRing

variable {E : Type*} [Field E] [NumberField E] (w : FinPlace E)

/-- Two elements of the valuation ring of v have the same residue exactly when the valuation of
their difference is less than 1. -/
lemma residue_eq_iff_valuation_sub_lt_one {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation F Γ} {a b : v.valuationSubring} :
    residue v.valuationSubring a = residue v.valuationSubring b ↔ v (a - b) < 1 :=
  Ideal.Quotient.eq.trans v.mem_maximalIdeal_iff

/-! ### The completions at finite places -/

/-- An algebraic integer x maps to 0 in the residue field at w exactly when x lies in w. -/
@[simp] lemma algebraMap_ResField_eq_zero {w : FinPlace E} {x : 𝓞 E} :
    algebraMap (𝓞 E) (ResField w) x = 0 ↔ x ∈ w.asIdeal :=
  residue_eq_iff_valuation_sub_lt_one.trans (by simp [valuation_lt_one_iff_mem])

lemma isOpen_v_lt (γ : WithZero (Multiplicative ℤ)) : IsOpen {x : LocField w | v x < γ} :=
  isOpen_lt continuous_v (by fun_prop)

/-- Every element of the residue field at w is the residue of an algebraic integer of E. -/
lemma algebraMap_ResField_surjective : Function.Surjective (algebraMap (𝓞 E) (ResField w)) :=
  residue_algebraMap_adicCompletionIntegers_surjective (K := E) w

/-- The residue field at w has `w.q` elements, the absolute norm of w. -/
lemma card_ResField : Nat.card (ResField w) = w.q := by
  have h_ker : w.asIdeal = RingHom.ker (algebraMap (𝓞 E) (ResField w)) := Ideal.ext (by simp)
  rw [FinPlace.q, Ideal.absNorm_eq_natCard, h_ker]
  exact (card_congr
    (RingHom.quotientKerEquivOfSurjective (algebraMap_ResField_surjective w)).toEquiv).symm

/-- The residue field at a finite place is finite. -/
instance instFiniteResField : Finite (ResField w) :=
  finite_of_card_ne_zero (by simp [card_ResField, w.ne_bot])

instance : ProperSpace (LocField w) :=
  properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, v.valuationSubring_isDiscreteValuationRing, instFiniteResField w⟩

/-- The ring of integers of the completion at a finite place is compact. -/
instance compactSpace_LocInt : CompactSpace (LocInt w) :=
  properSpace_iff_compactSpace_integer.mp inferInstance

lemma isCompact_LocInt : IsCompact (LocInt w : Set (LocField w)) :=
  isCompact_iff_compactSpace.mpr (compactSpace_LocInt w)

instance : CharZero (LocField w) := algebraRat.charZero _

deriving instance PolishSpace for LocField

/-! ### The topology of the finite adeles -/

instance : Fact (∀ w : FinPlace E, IsOpen (LocInt w).carrier) :=
  ⟨fun w ↦ isOpen_integer (LocField w)⟩

lemma isCompact_Ô : IsCompact (Ô E : Set (𝔸f E)) :=
  FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 E) (K := E)

lemma isOpen_Ô : IsOpen (Ô E : Set (𝔸f E)) := FiniteAdeleRing.isOpen_integralAdeles (𝓞 E) E

@[fun_prop]
lemma continuous_evalAt : Continuous (evalAt w) := continuous_eval w

/-- The map sending a in E_w to the finite adele with component a at w and 0 elsewhere is
continuous. -/
@[fun_prop]
lemma continuous_singleAdele : Continuous (singleAdele w) := by
  classical
  -- `singleAdele w` factors through the adeles integral outside `w`, which carry the product
  -- topology.
  let single' (x : LocField w) : Πʳ u : FinPlace E, [LocField u, LocInt u]_[.principal {w}ᶜ] :=
    ⟨singleAdele w x, by aesop⟩
  have h_cont : Continuous single' := continuous_rng_of_principal.2 (_root_.continuous_single w)
  exact (continuous_inclusion (𝓕 := .cofinite) (by simp)).comp h_cont

/-- An element of `E` that lies in `Ô E`, the finite adeles integral at every finite place, is an
algebraic integer, and conversely. -/
@[simp]
lemma algebraMap_mem_Ô {x : E} : ↑x ∈ Ô E ↔ IsIntegral ℤ x := by
  have key : (∀ w : FinPlace E, w.valuation E x ≤ 1) ↔ IsIntegral ℤ x :=
    ⟨fun h ↦ isIntegral_iff.2 (mem_integers_of_valuation_le_one E x h),
      fun hx w ↦ w.valuation_le_one ⟨x, hx⟩⟩
  simpa [mem_Ô] using key

/-- The image of an algebraic integer in the finite adeles is integral at every finite place. -/
lemma coe_mem_Ô (a : 𝓞 E) : ↑a ∈ Ô E := algebraMap_mem_Ô.2 a.isIntegral_coe

lemma isUnit_natCast_finAdele {d : ℕ} (hd : d ≠ 0) : IsUnit (d : 𝔸f E) :=
  mod_cast (cast_ne_zero.mpr hd).isUnit.map (algebraMap E (𝔸f E))

variable (E) in
/-- Let M be a module over the finite adeles of E with a topology making scalar multiplication
continuous. For K compact and U a neighbourhood of 0 in M, some nonzero natural number N has
Nx in U for all x in K. -/
lemma exists_natCast_smul_mem_of_isCompact {M : Type*} [AddCommMonoid M] [Module (𝔸f E) M]
    [TopologicalSpace M] [ContinuousSMul (𝔸f E) M] {K U : Set M} (hK : IsCompact K)
    (hU : U ∈ nhds 0) : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ K, (N : 𝔸f E) • x ∈ U := by
  -- Small elements `a` of `Ô E` satisfy `a • K ⊆ U`, and in the compact group `Ô E` the multiples
  -- `N • 1` come close to `0` for arbitrarily large `N`.
  have : CompactSpace (Ô E) := isCompact_iff_compactSpace.1 isCompact_Ô
  have h_cont : Continuous fun p : Ô E × M ↦ (p.1 : 𝔸f E) • p.2 := by fun_prop
  have h_small : ∀ᶠ a : Ô E in nhds 0, ∀ x ∈ K, a.val • x ∈ U :=
    hK.eventually_forall_of_forall_eventually fun x _ ↦ h_cont.tendsto' (0, x) 0 (by simp) hU
  have h_freq : ∃ᶠ N : ℕ in .atTop, ∀ x ∈ K, (N • (1 : Ô E)).val • x ∈ U :=
    (mapClusterPt_zero_atTop_nsmul _).frequently h_small
  obtain ⟨N, hN, hN_mem⟩ := h_freq.forall_exists_of_atTop 1
  exact ⟨N, one_le_iff_ne_zero.1 hN, fun x hx ↦ by simpa using hN_mem x hx⟩

/-- A set `U` is a neighbourhood of `0` in the finite adeles `𝔸f E` exactly when it contains
`N * Ô E` for some nonzero natural number `N`, where `Ô E` is the ring of integral finite adeles. -/
lemma mem_nhds_zero_finAdele_iff {U : Set (𝔸f E)} :
    U ∈ nhds 0 ↔ ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ Ô E, (N : 𝔸f E) * x ∈ U := by
  refine ⟨exists_natCast_smul_mem_of_isCompact (E := E) isCompact_Ô, fun ⟨N, hN, hU⟩ ↦ ?_⟩
  -- `N` is a unit of the finite adeles, so `N * Ô E` is an open set that contains `0`.
  have h_nhds : (fun x : 𝔸f E ↦ (N : 𝔸f E) • x) '' Ô E ∈ nhds 0 :=
    ((isUnit_natCast_finAdele hN).isOpenMap_smul _ isOpen_Ô).mem_nhds ⟨0, zero_mem _, smul_zero _⟩
  exact Filter.mem_of_superset h_nhds (forall_mem_image.2 hU)

/-- Finitely many finite adeles are carried into Ô E by one nonzero natural number. -/
lemma exists_forall_mul_mem_Ô {ι : Sort*} [Finite ι] (x : ι → 𝔸f E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i : ι, (N : 𝔸f E) * x i ∈ Ô E := by
  simpa using exists_natCast_smul_mem_of_isCompact E (finite_range x).isCompact
    (isOpen_Ô.mem_nhds (zero_mem _))

/-- Let `c ≠ 0` be a natural number. Every finite adele `y₀` of a number field `E` has a
neighbourhood `U` such that `(x - x') / c` is integral for any two elements `x`, `x'` of `E` whose
images lie in `U`. -/
lemma exists_mem_nhds_isIntegral_sub_div {E : Type*} [Field E] [NumberField E] (y₀ : 𝔸f E) {c : ℕ}
    (hc : c ≠ 0) :
    ∃ U ∈ nhds y₀, ∀ x x' : E, algebraMap E (𝔸f E) x ∈ U → algebraMap E (𝔸f E) x' ∈ U →
      IsIntegral ℤ ((x - x') / c) := by
  -- Take for `U` the adeles `y₀ + c z` with `z` integral.
  let U : Set (𝔸f E) := {y | ∃ z ∈ Ô E, y - y₀ = c * z}
  have h_zero : {y : 𝔸f E | ∃ z ∈ Ô E, y = c * z} ∈ nhds 0 :=
    mem_nhds_zero_finAdele_iff.mpr ⟨c, hc, fun z hz ↦ ⟨z, hz, rfl⟩⟩
  have hU : U ∈ nhds y₀ := (continuous_sub_right y₀).tendsto' y₀ 0 (sub_self y₀) h_zero
  refine ⟨U, hU, fun x x' ⟨z, hz, hx⟩ ⟨z', hz', hx'⟩ ↦ algebraMap_mem_Ô.mp ?_⟩
  have h_mul : (c : 𝔸f E) * algebraMap E (𝔸f E) ((x - x') / c) = c * (z - z') := by
    rw [← map_natCast (algebraMap E (𝔸f E)), ← map_mul, mul_div_cancel₀ _ (mod_cast hc)]
    simp [mul_sub, ← hx, ← hx']
  rw [(isUnit_natCast_finAdele hc).mul_left_cancel h_mul]
  exact sub_mem hz hz'

@[simp]
lemma finAdele_mul_apply (x y : 𝔸f E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

/-- A finite adele x equals c y for some y in `Ô E`, that is, integral at every finite place, if and
only if v (x w) ≤ v (c w) at every finite place w. -/
lemma exists_eq_mul_iff_v_le {x c : 𝔸f E} :
    (∃ y ∈ Ô E, x = c * y) ↔ ∀ w : HeightOneSpectrum (𝓞 E), v (x w) ≤ v (c w) := by
  refine ⟨?_, fun h_le ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩ w
    simpa using mul_le_of_le_one_right' (a := v (c w)) (mem_Ô.1 hy w)
  -- At each place the inequality gives a local integer `a w` with `a w * c w = x w`.
  have h_local (w : FinPlace E) : ∃ a : LocInt w, (a : LocField w) * c w = x w :=
    (v.isEquiv_valuation_valuationSubring (x w) (c w)).1 (h_le w)
  choose a ha using h_local
  refine ⟨structureMap LocField (fun w ↦ LocInt w) .cofinite a,
    mem_Ô.2 fun w ↦ (a w).property, ext _ _ fun w ↦ ?_⟩
  exact ((mul_comm _ _).trans (ha w)).symm

/-- The algebra structure of the subalgebra `FiniteAdeleRing.integralAdeles`. -/
instance : Algebra (𝓞 E) (Ô E) :=
  inferInstanceAs (Algebra (𝓞 E) (FiniteAdeleRing.integralAdeles (𝓞 E) E))

@[simp]
lemma coe_algebraMap_Ô (x : 𝓞 E) : (algebraMap (𝓞 E) (Ô E) x).val = ↑x := rfl

/-! ### Density of `𝓞 E` and `E`, and complex conjugation -/

/-- The algebraic integers of `E` are dense in `Ô E`, the ring of finite adeles that are integral at
every finite place. -/
lemma denseRange_algebraMap_Ô : DenseRange (algebraMap (𝓞 E) (Ô E)) :=
  FiniteAdeleRing.denseRange_algebraMap_integralAdeles (𝓞 E) E

/-- For a nonzero algebraic integer a, every integral finite adele x (an element of the ring `Ô E`
of finite adeles integral at every finite place) is congruent modulo a to an algebraic integer b. -/
lemma exists_dvd_algebraMap_sub {a : 𝓞 E} (ha : a ≠ 0) (x : Ô E) :
    ∃ b : 𝓞 E, algebraMap (𝓞 E) (Ô E) a ∣ algebraMap (𝓞 E) (Ô E) b - x := by
  -- `a` is a unit of the finite adeles, so `x + a Ô` is open; `𝓞 E` is dense in `Ô E`.
  have h_unit : IsUnit (a : 𝔸f E) :=
    (Ne.isUnit (by simpa using ha : (a : E) ≠ 0)).map (algebraMap E (𝔸f E))
  have h_open : IsOpen {y : Ô E | y.val - x.val ∈ (fun t : 𝔸f E ↦ (a : 𝔸f E) • t) '' Ô E} :=
    ((h_unit.isOpenMap_smul _ isOpen_Ô).preimage (continuous_sub_right _)).preimage
      continuous_subtypeVal
  obtain ⟨b, z, hz, hb⟩ :=
    denseRange_algebraMap_Ô.exists_mem_open h_open ⟨x, 0, zero_mem _, by simp⟩
  exact ⟨b, ⟨z, hz⟩, Subtype.ext (by simpa [smul_eq_mul] using hb.symm)⟩

/-- The number field `E` is dense in its ring `𝔸f E` of finite adeles (strong approximation). -/
lemma denseRange_algebraMap_finAdele : DenseRange ((↑) : E → 𝔸f E) :=
  FiniteAdeleRing.denseRange_algebraMap (𝓞 E) E

/-- Every finite adele is the sum of an element of `E` and an integral finite adele. -/
lemma exists_sub_mem_Ô (x : 𝔸f E) : ∃ a : E, x - a ∈ Ô E :=
  denseRange_algebraMap_finAdele.exists_mem_open (isOpen_Ô.preimage (by fun_prop)) ⟨x, by simp⟩

variable [IsCMField E]

instance : StarRing (𝔸f E) :=
  -- conjugation is an involution on `E`, which is dense
  starRingOfInvolution (adeleMap (starRingEnd E))
    (denseRange_algebraMap_finAdele.eq fun x : E ↦ by simp)

/-- For a CM field `E`, the component of `star x` at the finite place `w` is the conjugate, by the
map of completions `conjLoc`, of the component of `x` at the conjugate place `star w`. -/
@[simp]
lemma finAdele_star_apply (x : 𝔸f E) : star x w = conjLoc (star_star w) (x (star w)) := rfl

instance : ContinuousStar (𝔸f E) := ⟨continuous_adeleMap _⟩

/-- Complex conjugation of finite adeles extends that of `E`. -/
@[simp]
lemma star_algebraMap_finAdele (x : E) : star (x : 𝔸f E) = ↑(star x) :=
  adeleMap_algebraMap (starRingEnd E) x

/-- Complex conjugation of adeles, given by that of `ℂ` at the infinite places and by `star` on the
finite adeles, extends that of the CM field `E` along the diagonal embedding `toAdele`. -/
@[simp]
lemma star_toAdele [PlaceEmbedding E] (x : E) : star (toAdele (x : E)) = ↑(star x) := by aesop

/-- The integral finite adeles are stable under complex conjugation. -/
lemma star_mem_Ô {x : 𝔸f E} (h_mem : x ∈ Ô E) : star x ∈ Ô E :=
  mem_Ô.2 fun w ↦ by simpa using mem_Ô.1 h_mem (star w)

end New

/-!
## Idempotents of sets of places and units of the integral adeles

* `New.idem`: the idempotent of a set of places; `New.isUnit_Ô`: a unit of the integral adeles is
  an element with valuation `1` at every place.
* For a CM field, complex conjugation `star` acts on places and on adeles (through `New.conjLoc`).
  It carries the valuation at a place to that at the conjugate place, keeps the order of the residue
  field and permutes the idempotents (`New.v_star_apply`, `New.q_star`, `New.star_idem`).
-/

section AdeleIdempotent

open NumberField RestrictedProduct Valued StarSubsemiring Ideal

namespace New

variable {E : Type*} [Field E] [NumberField E] (S : Set (FinPlace E)) (x y : 𝔸f E) (w : FinPlace E)

/-! ### Components of finite adeles -/

@[simp]
lemma finAdele_add_apply : (x + y) w = x w + y w := rfl

@[simp]
lemma finAdele_sub_apply : (x - y) w = x w - y w := rfl

@[simp]
lemma finAdele_neg_apply : (-x) w = -x w := rfl

@[simp]
lemma finAdele_one_apply : (1 : 𝔸f E) w = 1 := rfl

@[simp]
lemma finAdele_pow_apply (k : ℕ) : (x ^ k) w = x w ^ k := rfl

@[simp]
lemma finAdele_natCast_apply (k : ℕ) : (k : 𝔸f E) w = k := rfl

@[simp]
lemma finAdele_zero_apply : (0 : 𝔸f E) w = 0 := rfl

/-- The component of the inverse of a finite idele is the inverse of its component, which is
nonzero. -/
lemma idele_inv_apply_and_ne_zero (x : (𝔸f E)ˣ) : x⁻¹.val w = (x.val w)⁻¹ ∧ x.val w ≠ 0 := by
  simp [← evalAt_apply, (x.isUnit.map (evalAt w)).ne_zero]

/-! ### Idempotents, reduction and units -/

open scoped Classical in
/-- The finite adele with component 1 at the places in S and 0 at the other places. -/
noncomputable def idem : 𝔸f E := ⟨fun w ↦ if w ∈ S then 1 else 0, by simp [ite_mem]⟩

/-- Reduction at `w` of integral finite adeles extends reduction of algebraic integers
modulo `w`. -/
@[simp]
lemma reduceAt_algebraMap (x : 𝓞 E) :
    reduceAt w (algebraMap (𝓞 E) (Ô E) x) = algebraMap (𝓞 E) (ResField w) x := rfl

open scoped Classical in
@[local simp]
lemma idem_apply : idem S w = if w ∈ S then 1 else 0 := rfl

/-- The adele `idem S`, with components 1 and 0, is integral at every finite place. -/
@[simp]
lemma idem_mem_Ô : idem S ∈ Ô E := mem_Ô.2 fun w ↦ by by_cases hw : w ∈ S <;> simp [hw]

open scoped Classical in
/-- The integral adele `idem S`, with component 1 on the set of places `S` and 0 elsewhere, is sent
by `reduceAt w`, reduction to the residue field at `w`, to 1 if `w` is in `S` and to 0 otherwise. -/
@[simp]
lemma reduceAt_idem : reduceAt w ⟨idem S, idem_mem_Ô S⟩ = if w ∈ S then 1 else 0 := by
  -- the component of `idem S` at `w` is `1` or `0` before reduction
  change IsLocalRing.residue (LocInt w) ⟨idem S w, mem_Ô.1 (idem_mem_Ô S) w⟩ = _
  have h_comp : (⟨idem S w, mem_Ô.1 (idem_mem_Ô S) w⟩ : LocInt w) = if w ∈ S then 1 else 0 :=
    Subtype.ext (by simp [apply_ite Subtype.val])
  rw [h_comp, apply_ite (IsLocalRing.residue (LocInt w)), map_one, map_zero]

lemma idem_mul_self : idem S * idem S = idem S := by aesop

lemma idem_compl : idem Sᶜ = 1 - idem S := by aesop

/-- For a finitely supported family of integers `d` on the finite places of `E` there is a finite
idele (a unit of the finite adeles `𝔸f E`) whose component at each place `w` is the chosen
uniformiser `uniformizer w` of the completion at `w` to the power `-d w`. -/
lemma exists_idele_eq_uniformizer_zpow (d : FinPlace E → ℤ) (hd : d.HasFiniteSupport) :
    ∃ x : (𝔸f E)ˣ, ∀ w : FinPlace E, x.val w = ↑((uniformizer w)⁻¹ ^ d w) := by
  let t (w : FinPlace E) : (LocField w)ˣ := (uniformizer w)⁻¹ ^ d w
  -- Outside the support of `d` the component `t w` is `1`, a unit of the local integers.
  have h_unit : ∀ᶠ w : FinPlace E in .cofinite, t w ∈ (Submonoid.ofClass (LocInt w)).units := by
    filter_upwards [hd.compl_mem_cofinite] with w hw
    simp only [t, Function.notMem_support.1 hw, zpow_zero, one_mem]
  exact ⟨mkUnit t h_unit, fun _ ↦ rfl⟩

variable {S x w}

@[simp]
lemma idem_of_mem (hw : w ∈ S) : idem S w = 1 := ite_eq_left hw

@[simp]
lemma idem_of_notMem (hw : w ∉ S) : idem S w = 0 := ite_eq_right hw

/-- The product `idem S * x` is an integral finite adele if and only if `x` is integral at every
place in `S`. -/
lemma idem_mul_mem_Ô : idem S * x ∈ Ô E ↔ ∀ w ∈ S, v (x w) ≤ 1 := by
  refine mem_Ô.trans (forall_congr' fun w ↦ ?_)
  by_cases hw : w ∈ S <;> simp [hw]

/-- The reduction at `w` of an integral finite adele vanishes if and only if its component at `w`
has valuation less than 1. -/
@[simp]
lemma reduceAt_eq_zero {x : Ô E} : reduceAt w x = 0 ↔ v (x.val w) < 1 := by
  have h_residue : reduceAt w x = 0 ↔ v (x.val w - 0) < 1 := residue_eq_iff_valuation_sub_lt_one
  rwa [sub_zero] at h_residue

/-- An element `x` of `Ô E`, the ring of finite adeles integral at every finite place, is a unit of
`Ô E` if and only if its component has valuation 1 at every finite place. -/
@[simp]
lemma isUnit_Ô {x : Ô E} :
    IsUnit x ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), v (x.val w) = 1 := by
  calc IsUnit x
    _ ↔ ∃ y ∈ Ô E, 1 = x.val * y := by simp [isUnit_iff_dvd_one, dvd_def, Subtype.ext_iff]
    _ ↔ ∀ w : FinPlace E, 1 ≤ v (x.val w) := by simp [exists_eq_mul_iff_v_le]
    _ ↔ ∀ w : FinPlace E, v (x.val w) = 1 := by simp [le_antisymm_iff, mem_Ô.1 x.property]

variable [IsCMField E] (x : 𝔸f E) (w : FinPlace E)

noncomputable instance : StarRing (Ô E) := starRing ⟨_, star_mem_Ô⟩

/-! ### Complex conjugation -/

@[simp, norm_cast]
lemma coe_star_Ô (x : Ô E) : (star x : Ô E) = star x.val := rfl

/-- The valuation of a conjugate adele at a place is that of the adele at the conjugate place. -/
@[simp]
lemma v_star_apply : v (star x w) = v (x (star w)) := by simp

/-- Conjugate places have residue fields of the same order. -/
@[simp]
lemma q_star : (star w).q = w.q := by
  -- conjugation of `𝓞 E` induces a bijection of the quotients by the two prime ideals
  rw [FinPlace.q, FinPlace.q, Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_eq_of_bijective _
    ⟨quotientMap_injective, quotientMap_surjective starRingAut.surjective⟩

/-- Complex conjugation carries the idempotent of a set of places to that of its conjugate. -/
lemma star_idem (S : Set (FinPlace E)) : star (idem S : 𝔸f E) = idem (star ⁻¹' S) := by aesop

/-- If `w` is the conjugate of the place `u`, complex conjugation carries the adele supported at
`u` with component `x` to the adele supported at `w` with component the conjugate of `x`. -/
lemma star_singleAdele {u w : FinPlace E} (huw : star u = w) (x : LocField u) :
    star (singleAdele u x) = singleAdele w (conjLoc huw x) := by
  -- Write `u` as `star w` and compare components.
  obtain rfl : star w = u := by rw [← huw, star_star]
  ext v
  obtain rfl | hv := eq_or_ne v w
  · simp
  · simp [hv, star_injective.ne hv]

end New

end AdeleIdempotent

/-!
## Functoriality under embeddings of number fields

* `New.FinPlace.comap_surjective`: every place has a place above it.

Identities between adelic maps are checked on the field, which is dense
(`New.denseRange_algebraMap_finAdele`).
-/

section AdeleMap

open NumberField

namespace New

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [Field M]
  [NumberField M] (g : L →+* M) (f : K →+* L)

omit [NumberField K] in
/-- An integer of `K` lies in the place below `w` if and only if its image lies in `w`. -/
@[simp]
lemma FinPlace.mem_comap {w : FinPlace L} {x : 𝓞 K} :
    x ∈ (comap f w).asIdeal ↔ RingOfIntegers.mapRingHom f x ∈ w.asIdeal := .rfl

/-- The maps of finite adeles induced by embeddings of number fields compose as the embeddings
do. -/
@[simp]
lemma adeleMap_adeleMap [NumberField L] :
    ∀ x : 𝔸f K, adeleMap g (adeleMap f x) = adeleMap (g.comp f) x :=
  denseRange_algebraMap_finAdele.eq fun x : K ↦ by simp

@[simp]
lemma adeleMap_id : ∀ x : 𝔸f K, adeleMap (RingHom.id K) x = x :=
  denseRange_algebraMap_finAdele.eq fun x : K ↦ by simp

omit [NumberField K] in
/-- For an embedding `f: K →+* L`, every finite place of `K` has a place of `L` above it. -/
lemma FinPlace.comap_surjective : Function.Surjective (comap f) := by
  -- Lying over: some prime `P` of `𝓞 L` lies over the given prime `p` of `𝓞 K`.
  rintro ⟨p, p_prime, p_ne_bot⟩
  let : Algebra K L := f.toAlgebra
  obtain ⟨P, P_prime, P_over⟩ := p.nonempty_primesOver (S := 𝓞 L)
  exact ⟨⟨P, P_prime, Ideal.ne_bot_of_liesOver_of_ne_bot p_ne_bot P⟩,
    IsDedekindDomain.HeightOneSpectrum.ext P_over.over.symm⟩

variable [NumberField L]

open scoped Pointwise in
/-- In a Galois extension `L / K`, two finite places `u`, `v` of `L` that lie above the same place
of `K` (`u.below K` is the place below `u`) are conjugate: `v` is the preimage of `u` under an
element of the Galois group. -/
lemma FinPlace.exists_gal_comap_eq [Algebra K L] [IsGalois K L] {u v : FinPlace L}
    (h_below : u.below K = v.below K) : ∃ g : Gal(L/K), u.comap g = v := by
  -- The Galois group is transitive on the primes above a given prime.
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(L/K), u.asIdeal = σ • v.asIdeal :=
    IsGaloisGroup.isInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) Gal(L/K) v.asIdeal u.asIdeal
      (congr_arg IsDedekindDomain.HeightOneSpectrum.asIdeal h_below.symm)
  use σ
  ext x
  rw [mem_comap, hσ]
  exact Ideal.smul_mem_pointwise_smul_iff

/-- A finite adele of `K` is integral if and only if its image in the finite adeles of `L` is. -/
@[simp]
lemma adeleMap_mem_Ô {x : 𝔸f K} : adeleMap f x ∈ Ô L ↔ x ∈ Ô K := by
  simp [mem_Ô, adeleMap_apply, (FinPlace.comap_surjective f).forall]

variable [IsCMField K] [IsCMField L]

/-- Complex conjugation of the finite adeles of a CM field is the map induced by complex conjugation
of the field. -/
lemma star_eq_adeleMap (x : 𝔸f K) : star x = adeleMap (starRingEnd K) x := rfl

/-- For CM fields, the place below the conjugate of `u` is the conjugate of the place below `u`. -/
lemma below_star [Algebra K L] (u : FinPlace L) : (star u).below K = star (u.below K) := by
  ext x
  have h_star : RingOfIntegers.mapRingHom (algebraMap K L) (star x) =
      star (RingOfIntegers.mapRingHom (algebraMap K L) x) :=
    RingOfIntegers.ext (map_star_CM (algebraMap K L) x)
  simp [h_star]

/-- For CM fields, the map of finite adeles induced by an embedding commutes with complex
conjugation. -/
lemma adeleMap_star : ∀ x : 𝔸f K, adeleMap f (star x) = star (adeleMap f x) :=
  denseRange_algebraMap_finAdele.eq (by simp [map_star_CM])

end New

end AdeleMap

/-!
## Base change of finite adeles and Galois descent

Base change of finite adeles along an extension `L / K` of number fields.
-/

section AdeleBaseChange

open Algebra Module Basis IsTopologicalAddGroup IsRightUniformAddGroup

namespace New

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The map of finite adeles induced by an embedding of number fields is injective. -/
lemma adeleMap_injective (f : K →+* L) : Function.Injective (adeleMap f) := by
  -- Every place of `K` lies under a place of `L`, and maps of completions are injective.
  intro x y hxy
  ext1 u
  obtain ⟨w, hw⟩ := FinPlace.comap_surjective f u
  exact (locMap f hw).injective (by rw [← adeleMap_apply, ← adeleMap_apply, hxy])

variable [Algebra K L] {ι : Type*} [Fintype ι] (b : Basis ι K L)

/-- The finite adeles `𝔸f L` are an algebra over `𝔸f K`, via the inclusion `finAdeleIncl K L`. -/
instance (priority := low) adeleAlgebra : Algebra (𝔸f K) (𝔸f L) := (finAdeleIncl K L).toAlgebra

@[local simp]
lemma algebraMap_eq_finAdeleIncl : algebraMap (𝔸f K) (𝔸f L) = finAdeleIncl K L := rfl

attribute [local instance] rightUniformSpace isUniformAddGroup_of_addCommGroup
  completeSpace_of_weaklyLocallyCompactSpace

/-- For a finite basis b of L over K, the linear map sending a family (a_i) of finite adeles of
K to the finite adele ∑ a_i b_i of L. -/
abbrev adeleCombination : (ι → 𝔸f K) →ₗ[𝔸f K] 𝔸f L :=
  Fintype.linearCombination (𝔸f K) ((↑) ∘ b : ι → 𝔸f L)

/-- On the coordinates of `x : L` in the basis `b`, viewed as adeles of `K`, the map
`New.adeleCombination` returns `x`, viewed as an adele of `L`. -/
lemma adeleCombination_repr (x : L) :
    adeleCombination b (Pi.map (fun _ : ι ↦ ((↑) : K → 𝔸f K)) (b.repr x)) = (x : 𝔸f L) := by
  conv_rhs => rw [← b.sum_repr x]
  simp [smul_def, Fintype.linearCombination]

lemma continuous_adeleCombination : Continuous (adeleCombination b) := by
  change Continuous fun a : ι → 𝔸f K ↦ ∑ i : ι, finAdeleIncl K L (a i) * (b i : 𝔸f L)
  exact continuous_finsetSum _ fun i _ ↦
    ((continuous_adeleMap _).comp (continuous_apply i)).mul_const _

/-- Let `b` be a basis of `L / K` with dual basis `b.traceDual` for the trace form, and let `U` be a
closed set of finite adeles of `K` that contains `N * Ô K`, with `N ≠ 0` (`Ô K` is the ring of
integral finite adeles). If `(∑ a j • b j) * (b.traceDual i / N)` is integral, then `a i ∈ U`. -/
lemma apply_mem_of_adeleCombination_mul_traceDual_mem_Ô [DecidableEq ι] {U : Set (𝔸f K)}
    (hU : IsClosed U) {N : ℕ} (hN : N ≠ 0) (h_sub : ∀ x ∈ Ô K, (N : 𝔸f K) * x ∈ U)
    (i : ι) (a : ι → 𝔸f K)
    (ha_int : adeleCombination b a * algebraMap L (𝔸f L) (b.traceDual i / N) ∈ Ô L) : a i ∈ U := by
  let d : L := b.traceDual i / N
  have h_closed : IsClosed {a : ι → 𝔸f K | adeleCombination b a * d ∈ Ô L → a i ∈ U} :=
    isClosed_imp (isOpen_Ô.preimage ((continuous_adeleCombination b).mul_const _))
      (hU.preimage (continuous_apply i))
  -- By density it suffices to look at the coordinates of an element `x` of `L`.
  refine isClosed_property (DenseRange.piMap fun _ : ι ↦ denseRange_algebraMap_finAdele) h_closed
    (fun c hc ↦ ?_) a ha_int
  obtain ⟨x, rfl⟩ := b.equivFun.surjective c
  have h_int : IsIntegral ℤ (x * d) := by
    simpa [adeleCombination_repr, ← map_mul, algebraMap_mem_Ô] using hc
  -- The `i`-th coordinate of `x` is the trace of `x * b.traceDual i`.
  have h_trace : b.repr x i = N * trace K L (x * d) := by
    rw [← nsmul_eq_mul, ← map_nsmul]
    simp [d, ← mul_div_assoc, ← traceForm_apply, ← Basis.traceDual_repr_apply, hN]
  simpa [h_trace] using h_sub _ (algebraMap_mem_Ô.2 (isIntegral_trace h_int))

/-- For a finite basis `b` of `L / K`, the topology on families of finite adeles of `K` is induced
from the finite adeles of `L` by the map `adeleCombination b`, `(a i) ↦ ∑ a i • b i`. -/
lemma isInducing_adeleCombination : Topology.IsInducing (adeleCombination b) := by
  classical
  -- The map is continuous, so it suffices that each coordinate is small where the sum is small.
  refine IsTopologicalAddGroup.isInducing_iff_nhds_zero.2
    (le_antisymm ((continuous_adeleCombination b).tendsto' 0 0 (map_zero _)).le_comap ?_)
  rw [nhds_pi, Filter.le_pi]
  intro i
  refine (closed_nhds_basis (0 : 𝔸f K)).tendsto_right_iff.2 fun U ⟨hU, hU_closed⟩ ↦ ?_
  obtain ⟨N, hN, h_sub⟩ := mem_nhds_zero_finAdele_iff.1 hU
  have h_nhds : {z : 𝔸f L | z * algebraMap L (𝔸f L) (b.traceDual i / N) ∈ Ô L} ∈ nhds 0 :=
    (isOpen_Ô.preimage (continuous_mul_const _)).mem_nhds (by simp)
  -- Where the sum lies in this neighbourhood of `0`, the `i`-th coordinate lies in `U`.
  filter_upwards [Filter.preimage_mem_comap h_nhds] with a ha
  exact apply_mem_of_adeleCombination_mul_traceDual_mem_Ô b hU_closed hN h_sub i a ha

/-- For a finite basis `b` of `L` over `K`, the map `adeleCombination b`, `(a i) ↦ ∑ a i • b i`,
from families of finite adeles of `K` to the finite adeles of `L` is a homeomorphism.

Known result: base change for the finite adeles of a number field. -/
lemma isHomeomorph_adeleCombination : IsHomeomorph (adeleCombination b) := by
  have h_ind : Topology.IsInducing (adeleCombination b) := isInducing_adeleCombination b
  -- The range is complete, hence closed, and it contains the dense image of `L`.
  have h_closed : IsClosed (Set.range (adeleCombination b)) :=
    (AddMonoidHom.isUniformInducing_of_isInducing h_ind).isComplete_range.isClosed
  have h_surj : Function.Surjective (adeleCombination b) :=
    isClosed_property denseRange_algebraMap_finAdele h_closed fun x ↦ ⟨_, adeleCombination_repr b x⟩
  exact isHomeomorph_iff_isEmbedding_surjective.2 ⟨h_ind.isEmbedding, h_surj⟩

/-- A finite basis of L over K, viewed as a basis of the finite adeles of L over the finite
adeles of K. -/
def adeleBasis : Basis ι (𝔸f K) (𝔸f L) :=
  ofEquivFun
    (LinearEquiv.ofBijective (adeleCombination b) (isHomeomorph_adeleCombination b).bijective).symm

/-- For `L / K` Galois, a finite adele of `L` comes from one of `K` if and only if it is fixed by
the action of the Galois group on finite adeles. -/
lemma mem_range_finAdeleIncl_iff [IsGalois K L] {y : 𝔸f L} :
    y ∈ (finAdeleIncl K L).range ↔ ∀ σ : Gal(L/K), adeleMap σ y = y := by
  have h_fix (σ : Gal(L/K)) : (σ : L →+* L).comp (algebraMap K L) = algebraMap K L :=
    RingHom.ext σ.commutes
  refine ⟨fun ⟨x, hx⟩ σ ↦ by rw [← hx, adeleMap_adeleMap, h_fix], fun hy ↦ ?_⟩
  -- Take `c` of trace one and write `y * c = ∑ a i • e i` in a basis `e`, with adelic `a i`.
  -- Summing over the Galois group gives `y = y * trace c = ∑ trace (e i) • a i`.
  obtain ⟨c, hc⟩ := trace_surjective K L 1
  let e : Basis (Fin (finrank K L)) K L := finBasis K L
  obtain ⟨a, ha⟩ := (isHomeomorph_adeleCombination e).surjective (y * c)
  refine ⟨∑ i, trace K L (e i) • a i, ?_⟩
  calc finAdeleIncl K L (∑ i, trace K L (e i) • a i)
    _ = ∑ i, finAdeleIncl K L (a i) * ∑ σ : Gal(L/K), (σ (e i) : 𝔸f L) := by
      simp [← map_sum (algebraMap L (𝔸f L)), ← trace_eq_sum_automorphisms, smul_def, mul_comm]
    _ = ∑ σ : Gal(L/K), adeleMap (σ : L →+* L) (adeleCombination e a) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [Fintype.linearCombination, smul_def, h_fix]
    _ = ∑ σ : Gal(L/K), y * σ c := by simp [ha, hy]
    _ = y := by simp [← map_sum _, ← Finset.mul_sum, ← trace_eq_sum_automorphisms, hc]

end New

end AdeleBaseChange

end
