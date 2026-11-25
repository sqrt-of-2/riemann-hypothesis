module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemLevelFunOfIsAutFun
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

section Generic

variable {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra F K] (τ : E →ₐ[F] K)
  {l m : Type} [Fintype l] [Fintype m]

theorem map_dot (φ : E →+* K) (x : l → E) (M : Matrix l m E) (y : m → E) :
    φ (x ⬝ᵥ M *ᵥ y) = (φ ∘ x) ⬝ᵥ M.map φ *ᵥ (φ ∘ y) := by simp [dotProduct, mulVec]

end Generic

section Coef


variable (D v) in
def locIdeal : Ideal (AE D) where
  carrier := {z | tensAt D.host.E v (compFin D.host.F D.host.E v z) = z}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change tensAt _ v _ = _
    rw [map_add (f := _), map_add (f := _), ha, hb]
  smul_mem' := fun a z hz => by
    change tensAt _ v (compFin _ _ v (a * z)) = a * z
    rw [map_mul, mul_comm, ← GlobalTheory.EmbChart.tensAt_mul_right, hz, mul_comm]

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

def hQ (V : HSp D) (x y : Fin V.rank → D.host.E) : D.host.E := star y ⬝ᵥ V.gram *ᵥ x

def hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) : AE D := ratV (star y) ⬝ᵥ (gA V * mt V g) *ᵥ ratV x

variable (V : HSp D)

theorem cA_ratV {m : ℕ} (x : Fin m → D.host.E) : cA D ∘ ratV x = ratV (star x) := rfl

theorem gA_mul_mt_inv (g : GA D V) : gA V * mt V g⁻¹ = adj (mt V g) * gA V := by rw [mt_inv, gA_giA_cancel]

theorem cA_hA (g : GA D V) (x y : Fin V.rank → D.host.E) : cA D (hA V g x y) = hA V g⁻¹ y x := by
  have h : adj (gA V * mt V g) = gA V * mt V g⁻¹ := by rw [gA_mul_mt_inv, adj_mul, adj_gA]
  rw [hA, hA, ← h, adj, dotProduct_mulVec (ratV (star x)), vecMul_transpose, dotProduct_comm _ (ratV y), map_dot,
    cA_ratV, cA_ratV, star_star]

theorem incA_hQ (x y : Fin V.rank → D.host.E) : incA D (hQ V x y) = hA V 1 x y := by
  rw [hA, mt_one, mul_one, gA, ← ratV_mulVec, hQ, RingHom.map_dotProduct]; rfl

theorem star_hQ (x y : Fin V.rank → D.host.E) : star (hQ V x y) = hQ V y x :=
  incA_injective (by rw [incA_hQ, ← inv_one, ← cA_hA, ← incA_hQ]; rfl)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Coef

section Frames

open GlobalTheory.RootEx (N embX)

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def ent {k : Type} [Field k] (g : GL (n ⊕ Fin c) k) (i : ℕ) : k :=
  if h : i + 1 < c then g.val (.inr ⟨i, by omega⟩) (.inr ⟨i + 1, h⟩) else 0

theorem simpleSum_eq_sum_ent {k : Type} [Field k] (g : GL (n ⊕ Fin c) k) :
    GlobalTheory.RootEx.simpleSum g = ∑ i ∈ Finset.range (c - 1), ent g i := by
  have h : ∑ i ∈ Finset.range (c - 1), ent g i = ∑ i ∈ Finset.range c, ent g i :=
    Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi =>
      dite_eq_right (by rw [Finset.mem_range] at hi; omega)
  rw [h, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ent
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i + 1, hi⟩, ite_eq_left rfl]
    · exact fun j _ hj => ite_eq_right fun e => hj (Fin.ext e)
    · exact fun e => absurd (Finset.mem_univ _) e
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)

theorem ent_inv {k : Type} [Field k] {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) (i : ℕ) :
    ent g⁻¹ i = -ent g i := by
  unfold ent
  split_ifs with hi
  · have h := GlobalTheory.RootEx.Radical.Uni.mul_apply_succ (b := GlobalTheory.RootEx.lev p) ((GlobalTheory.RootEx.Radical.mem_N_iff _).1 (inv_mem hg))
      ((GlobalTheory.RootEx.Radical.mem_N_iff _).1 hg) (r := .inr ⟨i, by omega⟩) (s := .inr ⟨i + 1, hi⟩) rfl
    rw [Units.inv_mul, Matrix.one_apply_ne (by simp)] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  · exact neg_zero.symm

variable (V X : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
  (jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E) (a : ℕ → Fin V.rank → D.host.E)
  (γ : LatFrame (Fv D.host.F v) n (Fin X.rank)) (β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank))

def IsScaled (t : ℕ → Fv D.host.F v) : Prop :=
  (∀ r, vec β (.inl r) = jX.map τ *ᵥ vec γ r) ∧ ∀ i : Fin c, vec β (.inr i) = t i • (τ ∘ a i)


variable (c) in
structure IsHermitianAuxiliaryVectorSystem (κ : ℕ → D.host.E) : Prop where
  iso : jXᴴ * V.gram * jX = X.gram
  perp : ∀ i < c, star (a i) ᵥ* V.gram ᵥ* jX = 0
  pair : ∀ i < c, ∀ l < c, hQ V (a l) (a (c - 1 - i)) = if l = i then κ i else 0
  ne : ∀ i < c, κ i ≠ 0
  card : X.rank + c = V.rank

variable {V X τ jX a γ β} {κ : ℕ → D.host.E} {t : ℕ → Fv D.host.F v}

end Frames

section Global

open GlobalTheory.RootEx (N embX)

def colN {m ρ : ℕ} (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : ℕ) : Fin m → D.host.E :=
  if h : i < ρ then fun y => M y ⟨i, h⟩ else 0

theorem colN_fin {m ρ : ℕ} (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : Fin ρ) : colN M i = fun y => M y i := dite_eq_left i.2

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  (ζ : Fin L.rank → D.host.E)

def besselAuxiliaryVectors (z : Fin V₀.rank → D.host.E) (i : ℕ) : Fin V.rank → D.host.E :=
  if i < ρ then colN d.e i else if i = ρ then d.i₀ *ᵥ z else colN d.e' (2 * ρ - i)

def fourierJacobiVectors (i : ℕ) : Fin V.rank → D.host.E := if i < ρ then colN d.e i else colN d.e' (2 * ρ - 1 - i)

variable (ψv : AddChar (Fv D.host.F v) Circle) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank))

theorem hQ_colN {k l : ℕ} (M : Matrix (Fin V.rank) (Fin k) D.host.E) (M' : Matrix (Fin V.rank) (Fin l) D.host.E) {i j : ℕ}
    (hi : i < k) (hj : j < l) : hQ V (colN M i) (colN M' j) = (M'ᴴ * V.gram * M) ⟨j, hj⟩ ⟨i, hi⟩ := by
  rw [colN, colN, dite_eq_left hi, dite_eq_left hj, Matrix.mul_assoc]; rfl

theorem hQ_mulVec {k l : ℕ} (M : Matrix (Fin V.rank) (Fin k) D.host.E) (M' : Matrix (Fin V.rank) (Fin l) D.host.E) (x y) :
    hQ V (M *ᵥ x) (M' *ᵥ y) = star y ⬝ᵥ (M'ᴴ * V.gram * M) *ᵥ x := by
  rw [hQ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem colN_eq_mulVec {m k : ℕ} (M : Matrix (Fin m) (Fin k) D.host.E) {i : ℕ} (hi : i < k) :
    colN M i = M *ᵥ Pi.single ⟨i, hi⟩ 1 := by
  rw [colN, dite_eq_left hi, mulVec_single_one]; rfl

theorem perp_of_gram {k l : ℕ} {M : Matrix (Fin V.rank) (Fin k) D.host.E} {J : Matrix (Fin V.rank) (Fin l) D.host.E}
    (h : Jᴴ * V.gram * M = 0) (x) : star (M *ᵥ x) ᵥ* V.gram ᵥ* J = 0 := by
  have h1 := congrArg conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero] at h1
  rw [star_mulVec, vecMul_vecMul, vecMul_vecMul, h1, vecMul_zero]

theorem hQ_XX {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e i) (colN d.e j) = 0 := by
  rw [hQ_colN _ _ hi hj, d.ee]; rfl

theorem hQ_YY {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e' i) (colN d.e' j) = 0 := by
  rw [hQ_colN _ _ hi hj, d.e'e']; rfl

theorem hQ_XY {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e i) (colN d.e' j) = if i = j then 1 else 0 := by
  rw [hQ_colN _ _ hi hj, d.e'e, Matrix.one_apply]
  simp only [Fin.mk.injEq, eq_comm]

theorem hQ_YX {i j : ℕ} (hi : i < ρ) (hj : j < ρ) : hQ V (colN d.e' i) (colN d.e j) = if j = i then 1 else 0 := by
  rw [← star_hQ, hQ_XY d hj hi]
  split_ifs <;> simp

theorem wittDecomposition_hermitian_e_anisotropicPart {i : ℕ} (hi : i < ρ) (z) : hQ V (colN d.e i) (d.i₀ *ᵥ z) = 0 := by
  rw [colN_eq_mulVec _ hi, hQ_mulVec, d.i₀e, zero_mulVec, dotProduct_zero]

theorem wittDecomposition_hermitian_dual_anisotropicPart {i : ℕ} (hi : i < ρ) (z) : hQ V (colN d.e' i) (d.i₀ *ᵥ z) = 0 := by
  rw [colN_eq_mulVec _ hi, hQ_mulVec, d.i₀e', zero_mulVec, dotProduct_zero]

theorem hQ_0X {i : ℕ} (hi : i < ρ) (z) : hQ V (d.i₀ *ᵥ z) (colN d.e i) = 0 := by
  rw [← star_hQ, wittDecomposition_hermitian_e_anisotropicPart d hi, star_zero]

theorem hQ_0Y {i : ℕ} (hi : i < ρ) (z) : hQ V (d.i₀ *ᵥ z) (colN d.e' i) = 0 := by
  rw [← star_hQ, wittDecomposition_hermitian_dual_anisotropicPart d hi, star_zero]

theorem hQ_vecB : hQ V (d.i₀ *ᵥ vecB o ζ) (d.i₀ *ᵥ vecB o ζ) = hQ L ζ ζ := by
  rw [hQ_mulVec, d.iso, ← hQ, vecB, hQ_mulVec, o.isoB, hQ]

variable {ζ} in
theorem isHermitianAuxiliaryVectorSystem_besselVectors (hζ : IsLineVec L ζ) : IsHermitianAuxiliaryVectorSystem (2 * ρ + 1) V A (d.i₀ * o.iA) (besselAuxiliaryVectors d (vecB o ζ))
    (fun i => if i = ρ then hQ L ζ ζ else 1) := by
  refine { iso := ?iso, perp := ?perp, pair := ?pair, ne := ?ne, card := ?card }
  case iso =>
    rw [conjTranspose_mul, Matrix.mul_assoc o.iAᴴ, Matrix.mul_assoc o.iAᴴ, ← Matrix.mul_assoc _ d.i₀, d.iso,
      ← Matrix.mul_assoc, o.isoA]
  case perp =>
    intro i hi
    unfold besselAuxiliaryVectors
    split_ifs with h1 h2
    · rw [colN_eq_mulVec _ h1, ← vecMul_vecMul, perp_of_gram d.i₀e, zero_vecMul]
    · rw [vecB, mulVec_mulVec]
      refine perp_of_gram ?_ _
      rw [conjTranspose_mul, Matrix.mul_assoc o.iAᴴ, Matrix.mul_assoc o.iAᴴ, ← Matrix.mul_assoc _ d.i₀, d.iso,
        ← Matrix.mul_assoc, o.orth']
    · rw [colN_eq_mulVec _ (show 2 * ρ - i < ρ by omega), ← vecMul_vecMul, perp_of_gram d.i₀e', zero_vecMul]
  case pair =>
    intro i hi l hl
    unfold besselAuxiliaryVectors
    rcases lt_trichotomy l ρ with h | h | h <;> rcases lt_trichotomy i ρ with h' | h' | h'
    · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_right (by omega), hQ_XY d h (by omega), ite_eq_right h'.ne]
      exact if_congr (by omega) rfl rfl
    · rw [ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), wittDecomposition_hermitian_e_anisotropicPart d h, ite_eq_right (by omega)]
    · rw [ite_eq_left h, ite_eq_left (by omega), hQ_XX d h (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right (by omega), ite_eq_right (by omega), hQ_0Y d (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right (by omega), ite_eq_left (by omega), hQ_vecB, ite_eq_left (by omega), ite_eq_left h']
    · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_left (by omega), hQ_0X d (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hQ_YY d (by omega) (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), wittDecomposition_hermitian_dual_anisotropicPart d (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), hQ_YX d (by omega) (by omega), ite_eq_right h'.ne']
      exact if_congr (by omega) rfl rfl
  case ne =>
    intro i _
    split_ifs
    exacts [hζ.2, one_ne_zero]
  case card =>
    have := d.rank_add
    have := o.rank_add
    have := hζ.1
    omega

variable {β}


end Global

section Table

open GlobalTheory.RootEx (N embX)
open Finset (range)

variable {V X : HSp D} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {γ : LatFrame (Fv D.host.F v) n (Fin X.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank)}
  {κ : ℕ → D.host.E} {t : ℕ → Fv D.host.F v}

variable (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  {ζ : Fin L.rank → D.host.E}

theorem blockX_apply (g : GA D V) (i j : Fin ρ) : blockX d g i j = hA V g (colN d.e j) (colN d.e' i) := by
  rw [blockX, d.pX_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), colN_fin, colN_fin]; rfl

theorem coefX_apply (z : Fin V₀.rank → D.host.E) (g : GA D V) (i : Fin ρ) :
    coefX d z g i = hA V g (d.i₀ *ᵥ z) (colN d.e' i) := by
  rw [coefX, d.pX_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← mulVec_mulVec, ← mulVec_mulVec, hA, ratV_mulVec,
    colN_fin]
  rfl

theorem upSum_blockX (g : GA D V) :
    upSum (blockX d g) = ∑ i ∈ range (ρ - 1), hA V g (colN d.e (i + 1)) (colN d.e' i) := by
  have h : ∑ i ∈ range (ρ - 1), hA V g (colN d.e (i + 1)) (colN d.e' i) =
      ∑ i ∈ range ρ, if i + 1 < ρ then hA V g (colN d.e (i + 1)) (colN d.e' i) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.ext fun i => ?_) fun _ _ => rfl
    simp only [Finset.mem_range, Finset.mem_filter]; omega
  rw [h, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i + 1, hi⟩, ite_eq_left rfl, blockX_apply]
    · exact fun j _ hj => ite_eq_right fun e => hj (Fin.ext e)
    · exact fun e => absurd (Finset.mem_univ _) e
  · exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)

theorem ell_dot {σ : ℕ} (x : Fin (σ + 1) → AE D) : ell D (σ + 1) ⬝ᵥ x = x (Fin.last σ) := by
  rw [dotProduct, Finset.sum_eq_single (Fin.last σ), show ell D (σ + 1) (Fin.last σ) = 1 from ite_eq_left rfl, one_mul]
  · intro j _ hj
    rw [show ell D (σ + 1) j = 0 from ite_eq_right fun e => hj (Fin.ext (Nat.succ_injective e)), zero_mul]
  · exact fun e => absurd (Finset.mem_univ _) e

theorem simpleSum_eq_sum_hA (z : Fin V₀.rank → D.host.E) (g : GA D V) : GlobalTheory.MixPer.simpleSum d z g =
    ∑ i ∈ range ρ, hA V g (besselAuxiliaryVectors d z (i + 1)) (besselAuxiliaryVectors d z (2 * ρ + 1 - 1 - i)) := by
  rw [GlobalTheory.MixPer.simpleSum, upSum_blockX]
  cases ρ with
  | zero => simp [dotProduct]
  | succ σ =>
    rw [Finset.sum_range_succ, ell_dot, coefX_apply]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [besselAuxiliaryVectors, besselAuxiliaryVectors, ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 2; omega
    · rw [besselAuxiliaryVectors, besselAuxiliaryVectors, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 2; simp; omega

theorem cmHost_imaginaryGenerator_ne_zero : D.host.xi0 ≠ 0 := fun h => by
  have := HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D)
  rw [h, map_zero, zero_mul] at this
  exact zero_ne_one (incA_injective ((map_zero _).trans (this.trans (map_one _).symm)))

end Table

section Normal

open GlobalTheory.RootEx (N)
open Finset (range)

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

variable {V X : HSp D} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v}
  {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {γ : LatFrame (Fv D.host.F v) n (Fin X.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank)}
  {κ t : ℕ → Fv D.host.F v} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {θ : Fv D.host.F v}
  {U : Subgroup (GL (n ⊕ Fin c) (Fv D.host.F v))} {χ : GA D V → ℂ}

variable {V₀ A L L' : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) {ζ : Fin L.rank → D.host.E}

section Bes

variable {γ : LatFrame (Fv D.host.F v) n (Fin A.rank)}

end Bes

section FJ

variable {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)}

end FJ

end Normal

end GlobalTheory.LocFrame

end
