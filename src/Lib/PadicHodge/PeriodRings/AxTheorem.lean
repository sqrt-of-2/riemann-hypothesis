module

public import Lib.General.Algebra.AbsIntegrallyClosed
public import Lib.General.Algebra.AdicCompletion
public import TauCeti.Analysis.Normed.Ring.Ultra

import TauCeti.RingTheory.RootsOfUnity.Ultrametric
public import Lib.ClassField.Places.GaloisDefs
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.NumberTheory.Padics.AlgebraicClosure.Basic
public import TauCeti.Topology.Algebra.UniformMulAction
public import TauCeti.Topology.MetricSpace.IsometricSMul
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.Complex.FixedPoints

/-!
# Tilting, Fontaine's θ, the ring O_C and Ax's theorem on Galois invariants in ℂ_p

This file studies the absolute Galois group `New.Gp` of `ℚ_p`, its action on `ℂ_p`, and its
invariants. For `p`-adically complete rings in which `p` is not a unit, the untilt and Fontaine's
`θ` are natural, and they are onto if the ring is also absolutely integrally closed. Ax's theorem
then describes the elements of `ℂ_p` fixed by a subgroup `J` of `New.Gp` as limits of algebraic
elements fixed by `J`.

## Main definitions and results

* Tilting for a ring `R` in which `p` is not a unit. `New.Variety.tiltMap` makes Mathlib's
  `PreTilt R p` functorial. For `p`-adically complete `R`, the untilt `x ↦ x^♯` and Fontaine's `θ`
  are natural in `R` (`New.Variety.untilt_tiltMap`, `New.Variety.fontaineTheta_map_tiltMap`). Both
  are onto if `R` is absolutely integrally closed
  (`New.Variety.fontaineTheta_surjective_of_isAbsIntegrallyClosed`). The tilt of a `p`-adically
  complete valuation ring is a valuation ring.
* The Galois group `New.Gp` of `ℚ̄_p / ℚ_p` and its cyclotomic character `New.cyclotomicGp`.
* The continuous isometric action of `New.Gp` on `ℂ_p` (Tau Ceti's
  `UniformSpace.Completion.instMulSemiringAction`), which restricts to an action by ring
  automorphisms on the ring of integers `New.OC`.
* `O_C` is absolutely integrally closed, with `O_C[1/p] = ℂ_p`.
* `New.Period.ax_mem_closure_fixedField`: Ax's theorem; an element fixed by a subgroup `J` is a
  limit of algebraic elements fixed by `J` (Tau Ceti's
  `PadicComplex.fixedPoints_eq_closure_fixedField`).
* `New.Period.exists_algebraic_of_fixed_near_one`: an element fixed by a neighbourhood of `1` is
  algebraic.

Notions from other files:
* `New.cyclotomicChar`: the ℓ-adic cyclotomic character Γ → ℤ_ℓ^× of a group Γ that acts on a
  field Ω by ring automorphisms; `New.cyclotomicGp` is the case Γ = `New.Gp p`, Ω = ℚ̄_p, ℓ = p.

## Relation to the literature

Known; see `Lib.PadicHodge.PeriodRings.DeRhamPeriods` and `Lib.PadicHodge.TateSen` for sources.
-/

@[expose] public section

open TauCeti (IsAbsolutelyIntegrallyClosed)

noncomputable section

/-! ## Functorial tilting, Fontaine's θ and the Galois action on ℂ_p -/

section CpIntegers

open Ideal WittVector Metric Perfection PadicComplex RingHom Valuation Valued ValuationRing

namespace New.Variety

variable {p : ℕ} [Fact p.Prime]
  {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Fact ¬IsUnit (p : R)]
  [Fact ¬IsUnit (p : R')] [Fact ¬IsUnit (p : R'')]
  (f : R →+* R') (g : R' →+* R'') (x : PreTilt R p)

/-! ### Functoriality of the tilt and of `θ` -/

/-- The tilt `PreTilt R p` is the inverse limit of `R / p` along `x ↦ x ^ p`. A ring homomorphism
`f : R → R'` induces the ring homomorphism `tiltMap f` between the tilts, which applies `f` modulo
`p` to each component. -/
def tiltMap : PreTilt R p →+* PreTilt R' p := map p (quotientMap _ f (by simp))

/-- If `y ∈ R` lifts the `n`-th component of `x` in `R / p`, then `f y` lifts the `n`-th component
of `tiltMap f x` in `R' / p`. -/
lemma coeff_tiltMap {x : PreTilt R p} {n : ℕ} {y : R}
    (hy : y = Perfection.coeff (ModP R p) p n x) :
    f y = Perfection.coeff (ModP R' p) p n (tiltMap f x) := by
  -- `tiltMap f` acts on each component by the map `R / p → R' / p` that `f` induces
  change _ = quotientMap (span {(p : R')}) f (by simp) (Perfection.coeff (ModP R p) p n x)
  rw [← hy, quotientMap_mk]

/-- The identity of `R` induces the identity of its tilt. -/
lemma tiltMap_id : tiltMap (RingHom.id R) x = x := by
  -- a lift `y ∈ R` of the `n`-th component of `x` also lifts the `n`-th component of the left side
  refine ext fun n ↦ ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff (ModP R p) p n x)
  exact (coeff_tiltMap (RingHom.id R) hy).symm.trans hy

/-- The map of tilts induced by a composite is the composite of the induced maps. -/
lemma tiltMap_comp : tiltMap (g.comp f) x = tiltMap g (tiltMap f x) := by
  -- if `y ∈ R` lifts the `n`-th component of `x`, then `g (f y)` lifts that of both sides
  refine ext fun n ↦ ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff (ModP R p) p n x)
  rw [← coeff_tiltMap (g.comp f) hy, ← coeff_tiltMap g (coeff_tiltMap f hy), RingHom.comp_apply]

/-- Let b be a perfect ring of characteristic p and R a p-adically separated commutative ring.
Two ring homomorphisms W(b) → R that agree on all Teichmüller lifts are equal. -/
lemma wittVector_ringHom_ext_of_teichmuller {b R : Type*} [CommRing b] [CharP b p] [PerfectRing b p]
    [CommRing R] [IsHausdorff (span {(p : R)}) R] {f g : WittVector p b →+* R}
    (h_teichmuller : ∀ x : b, f (WittVector.teichmuller p x) = g (WittVector.teichmuller p x)) :
    f = g := by
  -- modulo `p ^ (n + 1)` every Witt vector is a finite sum of terms `teichmuller p _ * p ^ i`, on
  -- which `f` and `g` agree
  refine Adic.ringHom_ext_of_approx (p := p) fun x n ↦ ?_
  let approx : WittVector p b := ∑ (i ≤ n),
    WittVector.teichmuller p (((_root_.frobeniusEquiv b p).symm ^ i) (x.coeff i)) * p ^ i
  have h_dvd : (p : WittVector p b) ^ (n + 1) ∣ x - approx :=
    dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
  exact ⟨approx, by simp [approx, h_teichmuller], (pow_dvd_pow _ n.le_succ).trans h_dvd⟩

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : R')}) R']

/-- The untilt commutes with the maps of tilts: `(tiltMap f x)^♯ = f (x^♯)` for `p`-adically
complete `R` and `R'`. -/
@[simp]
lemma untilt_tiltMap : (tiltMap f x).untilt = f x.untilt := by
  -- The `n`-th component of `tiltMap f x` lifts to `f` of the untilt of the `p ^ n`-th root `root`
  -- of `x`, and the `p ^ n`-th power of this lift is `f x.untilt`.
  refine teichmuller_spec fun n ↦ ?_
  let root : PreTilt R p := (powMulEquiv _ p).symm^[n] x
  have h_root_lift : (root.untilt : ModP R p) = Perfection.coeff (ModP R p) p n x := by aesop
  have h_pow : f root.untilt ^ p ^ n = f x.untilt := by simp [root, ← map_pow]
  exact ⟨f root.untilt, coeff_tiltMap f h_root_lift, by rw [h_pow]⟩

/-- Fontaine's `θ` is natural: it commutes with a ring map `f` and the map of Witt vectors of
the tilts that `f` induces. -/
lemma fontaineTheta_map_tiltMap (x : WittVector p (PreTilt R p)) :
    fontaineTheta R' p (WittVector.map (tiltMap f) x) = f (fontaineTheta R p x) := by
  -- both sides are ring maps that agree on Teichmüller lifts, where `θ [y] = y^♯`
  have h_maps_eq :
      (fontaineTheta R' p).comp (WittVector.map (tiltMap f)) = f.comp (fontaineTheta R p) :=
    wittVector_ringHom_ext_of_teichmuller fun y ↦ by simp [untilt_tiltMap]
  exact RingHom.congr_fun h_maps_eq x

/-- Let R be a p-adically complete, integrally closed domain in which p is not a unit. For x, y
in the tilt of R, x^♯ divides y^♯ in R if and only if x divides y. -/
lemma untilt_dvd_iff [IsDomain R] [IsIntegrallyClosed R] {x y : PreTilt R p} :
    x.untilt ∣ y.untilt ↔ x ∣ y := by
  -- The tilt is the multiplicative monoid of sequences `(xₙ)` in `R` with `xₙ₊₁ ^ p = xₙ`, and
  -- `untilt` is `x₀`. If `x₀ ∣ y₀` then `xₙ ∣ yₙ` for all `n` as `R` is integrally closed, and the
  -- quotients form such a sequence.
  obtain ⟨x, rfl⟩ := (quotientMulEquiv p (span {(p : R)})).surjective x
  obtain ⟨y, rfl⟩ := (quotientMulEquiv p (span {(p : R)})).surjective y
  refine ⟨fun h_untilt_dvd ↦ map_dvd _ ?_, map_dvd _⟩
  have h_untilt (z : Perfection R p) :
      PreTilt.untilt (quotientMulEquiv p (span {(p : R)}) z) = coeffMonoidHom R p 0 z :=
    teichmuller₀_mapMonoidHom_idealQuotientMk
  rw [h_untilt, h_untilt] at h_untilt_dvd
  have hp_pow (n : ℕ) : p ^ n ≠ 0 := pow_ne_zero n (NeZero.ne p)
  have h_dvd (n : ℕ) : ∃ e : R, coeffMonoidHom R p n y = coeffMonoidHom R p n x * e := by
    -- `xₙ ^ p ^ n = x₀`, and in an integrally closed domain `a ^ m ∣ b ^ m` implies `a ∣ b`
    refine (IsIntegrallyClosed.pow_dvd_pow_iff (hp_pow n)).mp ?_
    rwa [coeffMonoidHom_pow_p_pow_self, coeffMonoidHom_pow_p_pow_self]
  choose e hy_eq using h_dvd
  -- as `zₙ ^ p ^ n = z₀`, the term `zₙ` is zero if and only if `z₀` is
  have h_zero_iff (z : Perfection R p) (n : ℕ) :
      coeffMonoidHom R p n z = 0 ↔ coeffMonoidHom R p 0 z = 0 := by
    rw [← coeffMonoidHom_pow_p_pow_self z n, pow_eq_zero_iff (hp_pow n)]
  by_cases hx_zero : coeffMonoidHom R p 0 x = 0
  · -- every `xₙ` is zero, hence so is every `yₙ = xₙ * eₙ`, and `y = x * 1`
    refine ⟨1, extMonoid fun n ↦ ?_⟩
    rw [mul_one, hy_eq, (h_zero_iff x n).mpr hx_zero, zero_mul]
  · -- cancel `xₙ` in `yₙ₊₁ ^ p = yₙ` to get `eₙ₊₁ ^ p = eₙ`; then `y = x * e`
    have he_pow (n : ℕ) : e (n + 1) ^ p = e n := by
      refine mul_left_cancel₀ ((h_zero_iff x n).not.mpr hx_zero) ?_
      rw [← hy_eq, ← coeffMonoidHom_pow_p' y n, hy_eq (n + 1), mul_pow, coeffMonoidHom_pow_p' x n]
    exact ⟨⟨e, he_pow⟩, extMonoid hy_eq⟩

/-- Let R be a p-adically complete, integrally closed domain in which p is not a unit. An element
x of the tilt of R has untilt x^♯ = 0 exactly when x = 0. -/
lemma untilt_eq_zero_iff [IsDomain R] [IsIntegrallyClosed R] {x : PreTilt R p} :
    x.untilt = 0 ↔ x = 0 := by
  -- `x = 0` means `0 ∣ x`, which `untilt_dvd_iff` carries over to `R`, where `0^♯ = 0`
  rw [← zero_dvd_iff (a := x), ← untilt_dvd_iff, ← zero_dvd_iff (a := x.untilt)]
  simp [← fontaineTheta_teichmuller]

/-- Let R be a p-adically complete ring in which p is not a unit. If R is absolutely integrally
closed (every monic polynomial of positive degree over R has a root in R), then every element of R
is the untilt x^♯ of an element x of the tilt. -/
lemma untilt_surjective_of_isAbsIntegrallyClosed [h : IsAbsolutelyIntegrallyClosed R] :
    (PreTilt.untilt : PreTilt R p → R).Surjective := by
  -- choose successive `p`-th roots of `r`; the untilt of this sequence is its first term `r`
  intro r
  let pthRoot : R → R := Function.surjInv (h.exists_pow_eq p)
  have h_roots (n : ℕ) : pthRoot^[n + 1] r ^ p = pthRoot^[n] r := by
    rw [Function.iterate_succ_apply', Function.surjInv_eq (h.exists_pow_eq p)]
  let seq : Perfection R p := ⟨fun n ↦ pthRoot^[n] r, h_roots⟩
  exact ⟨quotientMulEquiv p (span {(p : R)}) seq, teichmuller₀_mapMonoidHom_idealQuotientMk⟩

/-- Let R be a p-adically complete ring in which p is not a unit. If R is absolutely integrally
closed, then Fontaine's `θ : W(tilt R) → R` is onto. -/
lemma fontaineTheta_surjective_of_isAbsIntegrallyClosed [IsAbsolutelyIntegrallyClosed R] :
    (⇑(fontaineTheta R p)).Surjective := by
  -- every `r ∈ R` is an untilt `y^♯`, and `θ` maps the Teichmüller lift `[y]` to `y^♯`
  intro r
  obtain ⟨y, rfl⟩ := untilt_surjective_of_isAbsIntegrallyClosed (p := p) r
  exact ⟨teichmuller p y, fontaineTheta_teichmuller y⟩

variable [IsDomain R] [ValuationRing R]

/-- The tilt of a `p`-adically complete valuation ring is an integral domain. -/
instance : IsDomain (PreTilt R p) := by
  have h_nontrivial : Nontrivial (PreTilt R p) := (coeff _ p 0).domain_nontrivial
  -- the untilt is multiplicative, and it maps only `0` to `0` in the domain `R`
  have h_noZeroDivisors : NoZeroDivisors (PreTilt R p) :=
    ⟨fun h_mul ↦ by simpa only [← untilt_eq_zero_iff, map_mul, mul_eq_zero] using h_mul⟩
  exact NoZeroDivisors.to_isDomain _

/-- The tilt of a `p`-adically complete valuation ring is a valuation ring. -/
instance : ValuationRing (PreTilt R p) := by
  -- divisibility in the tilt is divisibility of the untilts in the valuation ring `R`
  refine iff_dvd_total.mpr ⟨fun a b ↦ ?_⟩
  simpa only [← untilt_dvd_iff] using dvd_total a.untilt b.untilt

end Variety

/-! ### The Galois group of `ℚ_p` and its action on `ℂ_p` -/

/-- The absolute Galois group G_p = Gal(Q̄_p over Q_p). -/
abbrev Gp (p : ℕ) [Fact p.Prime] : Type := Gal(PadicAlgCl p/ℚ_[p])

/-- The ring of integers `valRingCp p` of `ℂ_p` (its elements of norm at most `1`) as a type, for
the prime `p` fixed by the class `ThePrime p`. -/
abbrev OC {p : ℕ} [ThePrime p] : Type := ↥(valRingCp p)

/-- The valuation ring of ℚ̄_p. -/
abbrev intQpBar (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) :=
  (PadicAlgCl.valued p).v.valuationSubring

variable {p : ℕ} [Fact p.Prime] (g : Gp p)

open UniformSpace.Completion Variety IsLocalization

/-- The valuation of the valuation ring `intQpBar p` of `ℚ̄_p` orders elements as the norm does. -/
lemma Selmer.valuation_intQpBar_le_iff (x y : PadicAlgCl p) :
    intQpBar p x ≤ intQpBar p y ↔ ‖x‖ ≤ ‖y‖ :=
  v.isEquiv_valuation_valuationSubring.symm x y

@[simp]
lemma Selmer.valuation_intQpBar_lt_one_iff {z : PadicAlgCl p} : intQpBar p z < 1 ↔ ‖z‖ < 1 := by
  simpa using (valuation_intQpBar_le_iff 1 z).not

/-! The isometric, jointly continuous action of `Gp p` on `ℚ̄_p` and `ℂ_p` by ring automorphisms is
Tau Ceti's (`TauCeti.NumberTheory.Padics.Complex.GaloisAction`). -/

instance : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun a ↦ uniformContinuous_const_smul a.val⟩

variable {p : ℕ} [ThePrime p] (g : Gp p) (x : OC)

instance : MulSemiringAction (Gp p) OC := (IsInvariantSubring.mk (by simp)).toMulSemiringAction

@[simp]
lemma OC.coe_smul : (g • x).val = g • x := rfl

/-- The p-adic cyclotomic character of the absolute Galois group of Q_p, obtained from its
action on the algebraic closure of Q_p. -/
abbrev cyclotomicGp : Gp p →* ℤ_[p]ˣ := cyclotomicChar (Γ := Gp p) (PadicAlgCl p) p

/-- `p` is not a unit in `O_C`, as `‖p‖ < 1`. -/
instance : Fact ¬IsUnit (p : OC) :=
  ⟨by simpa [isUnit_iff_dvd_one, valRingCp.dvd_iff_norm_le] using PadicComplex.norm_p_lt_one p⟩

/-- In `O_C`, a nonzero element `t` divides some power of any non-unit `s`. -/
lemma OC.exists_dvd_pow {s t : OC} (hs_nonunit : ¬IsUnit s) (ht_ne_zero : t ≠ 0) :
    ∃ n : ℕ, t ∣ s ^ n := by
  -- `‖s‖ < 1` and `0 < ‖t‖`, so `‖s‖ ^ n < ‖t‖` for some `n`
  have hs_lt : ‖s.val‖ < 1 := by
    simpa [isUnit_iff_dvd_one, valRingCp.dvd_iff_norm_le] using hs_nonunit
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖s.val‖ ^ n < ‖t.val‖ :=
    exists_pow_lt_of_lt_one (by simpa using ht_ne_zero) hs_lt
  exact ⟨n, by simpa [valRingCp.dvd_iff_norm_le] using hn.le⟩

/-- `ℂ_p` is the localization `O_C[1/p]`. -/
instance : Away (p : OC) ℂ_[p] := by
  -- if `‖z‖ < p ^ n` then `z * p ^ n` has norm at most `1`, because `‖p‖ = p⁻¹`
  have hp_one_lt : 1 < (p : ℝ) := by simp [Fact.out]
  refine .mk _ (by simp [NeZero.ne])
    (fun z ↦ (pow_unbounded_of_one_lt ‖z‖ hp_one_lt).imp fun n hz_lt ↦ ?_) (by simp)
  have h_norm_le : ‖z‖ * ((p : ℝ) ^ n)⁻¹ ≤ 1 :=
    (div_le_one (pow_pos (zero_lt_one.trans hp_one_lt) n)).mpr hz_lt.le
  simpa [norm_p_eq_inv] using h_norm_le

/-- `O_C` is absolutely integrally closed: every monic polynomial of positive degree over `O_C`
has a root in `O_C`. -/
instance : IsAbsolutelyIntegrallyClosed OC := .of_isIntegrallyClosedIn ℂ_[p]

end New

end CpIntegers

/-!
## Ax's theorem on invariants of subgroups of the Galois group

Ax's theorem is Tau Ceti's Ax–Sen–Tate theorem `PadicComplex.fixedPoints_eq_closure_fixedField`.
The norm estimates below are used elsewhere.
-/

section AxTheorem

open Polynomial Finset IsAlgClosed IsPrimitiveRoot IsUltrametricDist Multiset Nat PadicComplex Real
  UniformSpace.Completion IntermediateField InfiniteGalois Padic

namespace New.Period

variable {p : ℕ} [Fact p.Prime]
  {F : Type*} [NormedField F] [IsUltrametricDist F] {ζ : F}

/-- If `ζ` is a primitive `p ^ (m + 1)`-th root of unity in an ultrametric normed field `F`, then
`‖ζ - 1‖ ^ φ (p ^ (m + 1)) = ‖p‖`, where `φ (p ^ (m + 1)) = p ^ m (p - 1)`. -/
lemma norm_zeta_sub_one_pow {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) :
    ‖ζ - 1‖ ^ φ (p ^ (m + 1)) = ‖(p : F)‖ :=
  hζ.norm'_sub_one_pow_totient_prime_pow

/-- Let K be algebraically closed, L a normed field over K, f in K[X] with leading coefficient
a, x in L, r ≥ 0. If ‖x − w‖ ≥ r for every root w of f, then ‖f(x)‖ ≥ ‖a‖ r^(deg f). -/
lemma pow_le_norm_aeval {K L : Type*} [Field K] [IsAlgClosed K] [NormedField L] [Algebra K L]
    (f : K[X]) (x : L) {r : ℝ} (hr_nonneg : 0 ≤ r)
    (h_roots_far : ∀ w ∈ f.roots, r ≤ ‖x - algebraMap K L w‖) :
    ‖algebraMap K L f.leadingCoeff‖ * r ^ f.natDegree ≤ ‖aeval x f‖ := by
  -- Factor `f` into linear factors and bound each of the `deg f` factors `x - w` below by `r`.
  have h_norm_aeval : ‖aeval x f‖ = ‖algebraMap K L f.leadingCoeff‖ *
      (f.roots.map fun w : K ↦ ‖x - algebraMap K L w‖).prod := by
    nth_rw 1 [(splits f).eq_prod_roots]
    simp [← normHom_apply, map_multiset_prod]
  have h_prod : r ^ f.roots.card ≤ (f.roots.map fun w : K ↦ ‖x - algebraMap K L w‖).prod := by
    simpa using prod_map_le_prod_map₀ (fun _ ↦ r) _ (fun _ _ ↦ hr_nonneg) h_roots_far
  grw [h_norm_aeval, ← card_roots_eq_natDegree, h_prod]

/-- Ax's theorem (a known result), the nontrivial inclusion of the Ax–Sen–Tate theorem: let `J` be
a subgroup of `G_p`. Every `x ∈ ℂ_p` fixed by `J` lies in the closure of the image, under the
inclusion `coe'` of `ℚ̄_p` into its completion `ℂ_p`, of the fixed field of `J` in `ℚ̄_p`. -/
lemma ax_mem_closure_fixedField (J : Subgroup (Gp p)) {x : ℂ_[p]} (hx : ∀ g ∈ J, g • x = x) :
    x ∈ closure (coe' '' fixedField J) := by
  -- this is Tau Ceti's `PadicComplex.fixedPoints_eq_closure_fixedField`
  have hx_fixed : x ∈ MulAction.fixedPoints J ℂ_[p] := fun g ↦ hx g g.property
  rw [PadicComplex.fixedPoints_eq_closure_fixedField] at hx_fixed
  simpa [Set.image_eq_range] using hx_fixed

/-- If `x ∈ ℂ_p` is fixed by every `g` in some neighbourhood of the identity of `G_p`, then `x` is
the image `coe' y` of an element `y` of `ℚ̄_p` under the inclusion of `ℚ̄_p` into `ℂ_p`. -/
lemma exists_algebraic_of_fixed_near_one {x : ℂ_[p]} (hx : ∀ᶠ g : Gp p in nhds 1, g • x = x) :
    ∃ y : PadicAlgCl p, x = coe' y := by
  -- `x` is fixed by the subgroup of a finite extension `E`, so it lies in the closure of `E`, and
  -- the finite-dimensional space `E` is closed.
  obtain ⟨E, h_findim, hE⟩ : ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] E ∧ (E.fixingSubgroup : Set (Gp p)) ⊆ {g : Gp p | g • x = x} :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) {g : Gp p | g • x = x}).mp hx
  have h_closure : x ∈ closure (coe' '' (E : Set (PadicAlgCl p))) := by
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using
      ax_mem_closure_fixedField E.fixingSubgroup hE
  obtain ⟨y, -, hy⟩ : ∃ y ∈ E.toSubmodule, (toComplL y : ℂ_[p]) = x :=
    (E.toSubmodule.map toComplL.toLinearMap).isClosed_of_finiteDimensional.closure_subset h_closure
  exact ⟨y, hy.symm⟩

end New.Period

end AxTheorem

end
