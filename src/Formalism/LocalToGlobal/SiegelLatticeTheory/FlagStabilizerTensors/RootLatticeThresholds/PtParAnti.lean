module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LastDiagMulVec
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

theorem ptPar_anti {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x y : ℕ), y < (bs.map Prod.snd).sum →
    x < y → blkOf bs x = blkOf bs y → ptPar bs y < ptPar bs x
  | [], _, y, hy, _, _ => by simp at hy
  | (t, s) :: bs, x, y, hy, hxy, h => by
    simp only [List.map_cons, List.sum_cons] at hy
    simp only [blkOf] at h
    rw [ptPar_cons, ptPar_cons]
    by_cases hys : y < s
    · rw [ite_eq_left hys, ite_eq_left (by omega)]; omega
    · by_cases hxs : x < s
      · rw [ite_eq_left hxs, ite_eq_right hys] at h; omega
      · rw [ite_eq_right hxs, ite_eq_right hys] at h ⊢
        have := ptPar_anti bs (x - s) (y - s) (by omega) (by omega) (by omega)
        omega

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hee_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.eX b)
  rw [X.ee a b] at key
  simpa [HidaSetting.eR] using key

theorem hez_v (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.zu w)
  rw [(X.zu_orth w a).1] at key
  simpa [HidaSetting.eR, HidaSetting.zR] using key

theorem hef_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.eX a) (X.fY b)
  rw [X.ef a b] at key
  split_ifs at key ⊢ <;> simpa [HidaSetting.eR, HidaSetting.fR] using key

theorem hfe_v (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_conj, hef_v X v b a]
  split_ifs <;> simp

theorem hfz_v (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR w)) = 0 := by
  have key := Formalism.L2.SG.Pf.hJ_crd (X := X) v (X.fY a) (X.zu w)
  rw [(X.zu_orth w a).2] at key
  simpa [HidaSetting.fR, HidaSetting.zR] using key

theorem hJs_l {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    hJ ε (c • x) y = starRingEnd ℂ c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul, starRingEnd_apply]

theorem gram_frm (v : InfinitePlace X.B.I.F) (w : D.what₂.Word) (sc : ℝ) (a b : Fin (D.R.rS + 1)) :
    hJ (X.B.I.ε v) (frm X w sc v a) (frm X w sc v b) = lastDiag (-((Tw w : ℝ) : ℂ)) a b := by
  have h0 : ∀ i j : Fin (D.R.rS + 1),
      hJ (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) i)
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) j) =
        lastDiag (-((Tw w : ℝ) : ℂ)) i j := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fam, Fin.snoc_last, lastDiag, Matrix.of_apply]
        try simp only [and_self, ite_true]
        exact Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg (X := X) v w
      | cast j =>
        simp only [fam, Fin.snoc_last, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [ite_eq_right (fun h => (Fin.castSucc_lt_last j).ne h.2), Formalism.L2.SG.PoincareInHH.Cut.hJ_conj,
          hez_v X v w j, map_zero]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fam, Fin.snoc_last, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [ite_eq_right (fun h => (Fin.castSucc_lt_last i).ne h.1), hez_v X v w i]
      | cast j =>
        simp only [fam, Fin.snoc_castSucc, lastDiag, Matrix.of_apply]
        rw [ite_eq_right (fun h => (Fin.castSucc_lt_last i).ne h.1), hee_v X v i j]
  simp only [frm, famSc, hJs_l, _root_.Formalism.L2.SG.Pf.Carrier.JointQuot.hJ_smul_r, h0]
  by_cases ha : a = Fin.last _
  · by_cases hb : b = Fin.last _
    · subst ha
      subst hb
      simp
    · simp [lastDiag, hb]
  · simp [lastDiag, ha]

end Formalism.L2.S.L6.UnitaryStandardVectors
