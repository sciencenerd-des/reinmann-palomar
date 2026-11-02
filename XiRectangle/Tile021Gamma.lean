/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile021Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6063/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((3/4), (6063/640))
  have he : value ((3/4), (6063/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21913600/329854369), (-7760640/329854369)), 0, by norm_num⟩
  | 1 => ⟨((-209989165875200/108803904748388161), (170063560704000/108803904748388161)), 0, by norm_num⟩
  | 2 => ⟨((402167889/8796093022208), (-5251126113/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-721566205/1125899906842624), (6792802255/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-511553425/36028797018963968), (-3881819315/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((501256109/288230376151711744), (1966798961/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-3611995977/36893488147419103232), (-3426434219/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((5129204519/1180591620717411303424), (570604641/295147905179352825856)), (13/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1577815875/9444732965739290427392), (-247626799/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((3447484759/604462909807314587353088), (-462345305/302231454903657293676544)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-3316402267/19342813113834066795298816), (2280666509/19342813113834066795298816)), (23/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((2666625573/618970019642690137449562112), (-3672651925/618970019642690137449562112)), (17/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1451949201/19807040628566084398385987584), (4907656509/19807040628566084398385987584)), (25/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (6063/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (6063/1280)))⁻¹=value ((21913600/329854369), (-7760640/329854369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/329854369), (-7760640/329854369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2848063195/1073741824), (730927495/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((10956800/329854369), (-3880320/329854369)), 0, by norm_num⟩
  | 2 => ⟨((-52497291468800/108803904748388161), (42515890176000/108803904748388161)), 0, by norm_num⟩
  | 3 => ⟨((134055963/17592186044416), (-1750375371/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-721566205/9007199254740992), (6792802255/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-102310685/72057594037927936), (-776363863/72057594037927936)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((2673365915/18446744073709551616), (5244797229/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-2063997701/295147905179352825856), (-1957962411/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((5129204519/18889465931478580854784), (570604641/4722366482869645213696)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-175312875/18889465931478580854784), (-110056355/151115727451828646838272)), (19/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((2757987807/9671406556917033397649408), (-92469061/1208925819614629174706176)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-4823857843/618970019642690137449562112), (207333319/38685626227668133590597632)), (17/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((888875191/4951760157141521099596496896), (-4896869233/19807040628566084398385987584)), (23/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (129/20480)), 0, by norm_num⟩
  | 45 => ⟨((99962393297/4080638361600), (-256323/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-46403137619671/1915179604377600), (5125178380571/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((847688361/34359738368), (-590408511/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-3479076639/137438953472), (1197543131/137438953472)), (1/137438953472), by norm_num⟩
  | 41 => ⟨((3568429045/137438953472), (-306608723/34359738368)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-3658339405/137438953472), (157203409/17179869184)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3751957871/137438953472), (-644681139/68719476736)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-1925330499/68719476736), (661142037/68719476736)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3954859895/137438953472), (-1356905865/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-2032443909/68719476736), (1393433557/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((4181203971/137438953472), (-1431999589/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4304364731/137438953472), (368190409/34359738368)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4434998007/137438953472), (-378977569/34359738368)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4573806617/137438953472), (390415667/34359738368)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((2360791237/68719476736), (-201282813/17179869184)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4879223037/137438953472), (1661984207/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((2523874901/68719476736), (-1717138487/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-5228330375/137438953472), (1776078729/137438953472)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((2711152737/68719476736), (-919604287/68719476736)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-1407805557/34359738368), (1906991157/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((183027359/4294967296), (-1979960481/137438953472)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-3050679725/68719476736), (2058735513/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((6367132763/137438953472), (-2144037777/137438953472)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-1664275345/34359738368), (139794595/8589934592)), (1/34359738368), by norm_num⟩
  | 21 => ⟨((3487362543/68719476736), (-1168880935/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-3662077989/68719476736), (306046375/17179869184)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((1927605167/34359738368), (-642491263/34359738368)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-4069831601/68719476736), (169016611/8589934592)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4309736833/68719476736), (-89167955/4294967296)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4579669971/68719476736), (754970793/34359738368)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((4885640015/68719476736), (-801756415/34359738368)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5235372537/68719476736), (213680655/8589934592)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5638969319/68719476736), (-1830361313/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-6109897293/68719476736), (492420471/17179869184)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((3333257931/34359738368), (-266494375/8589934592)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-458407405/4294967296), (1161681017/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((4075498661/34359738368), (-1276261767/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-1146443245/8589934592), (1415917379/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2620856141/17179869184), (-1589893749/34359738368)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-764488939/4294967296), (906312123/17179869184)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3669360601/17179869184), (-526992053/8589934592)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4584945127/17179869184), (157401855/2147483648)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((3053028231/8589934592), (-1563939657/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4564356543/8589934592), (1032125429/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((4516609423/4294967296), (-760293827/4294967296)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-2063700427/17179869184), (5847419959/17179869184)), (3/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (6063/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (6063/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (6063/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2848063195/1073741824), (730927495/2147483648)), (1/2147483648), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (6063/1280))) (z:=((-21/128), (6063/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2848063195/1073741824), (730927495/2147483648))) (r:=(1/2147483648)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4367214331/134217728), (2274477511/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((7772276895/4294967296), (94523741/536870912)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((929785733299200/108803904748388161), (-341243071367520/108803904748388161)), 0, by norm_num⟩
  | 3 => ⟨((-740858487/8796093022208), (2510220351/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((139693199/140737488355328), (-1962650441/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1052195245/144115188075855872), (1552651417/36028797018963968)), (35/144115188075855872), by norm_num⟩
  | 6 => ⟨((-879827725/4611686018427387904), (-4796206921/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((510909273/36893488147419103232), (1743258795/73786976294838206464)), (77/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-338143533/590295810358705651712), (-2243264731/4722366482869645213696)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5961795903/302231454903657293676544), (2138872857/302231454903657293676544)), (273/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5867003505/9671406556917033397649408), (17695915/9671406556917033397649408)), (373/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5217583091/309485009821345068724781056), (-1905336897/309485009821345068724781056)), (125/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-1026195105/2475880078570760549798248448), (429471589/1237940039285380274899124224)), (339/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2572052219/134217728), (819362941/67108864)), (5/268435456), by norm_num⟩
  | 1 => ⟨((5624793247/4294967296), (94523741/536870912)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((929785733299200/108803904748388161), (-341243071367520/108803904748388161)), 0, by norm_num⟩
  | 3 => ⟨((-740858487/8796093022208), (2510220351/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((139693199/140737488355328), (-1962650441/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1052195245/144115188075855872), (1552651417/36028797018963968)), (35/144115188075855872), by norm_num⟩
  | 6 => ⟨((-879827725/4611686018427387904), (-4796206921/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((510909273/36893488147419103232), (1743258795/73786976294838206464)), (77/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-338143533/590295810358705651712), (-2243264731/4722366482869645213696)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5961795903/302231454903657293676544), (2138872857/302231454903657293676544)), (273/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5867003505/9671406556917033397649408), (17695915/9671406556917033397649408)), (373/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5217583091/309485009821345068724781056), (-1905336897/309485009821345068724781056)), (125/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-1026195105/2475880078570760549798248448), (429471589/1237940039285380274899124224)), (339/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2695390061/134217728), (819362941/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((5624793247/4294967296), (94523741/536870912)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((929785733299200/108803904748388161), (-341243071367520/108803904748388161)), 0, by norm_num⟩
  | 3 => ⟨((-740858487/8796093022208), (2510220351/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((139693199/140737488355328), (-1962650441/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1052195245/144115188075855872), (1552651417/36028797018963968)), (35/144115188075855872), by norm_num⟩
  | 6 => ⟨((-879827725/4611686018427387904), (-4796206921/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((510909273/36893488147419103232), (1743258795/73786976294838206464)), (77/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-338143533/590295810358705651712), (-2243264731/4722366482869645213696)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5961795903/302231454903657293676544), (2138872857/302231454903657293676544)), (273/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5867003505/9671406556917033397649408), (17695915/9671406556917033397649408)), (373/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5217583091/309485009821345068724781056), (-1905336897/309485009821345068724781056)), (125/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-1026195105/2475880078570760549798248448), (429471589/1237940039285380274899124224)), (339/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((419978331750400/108803904748388161), (-340127121408000/108803904748388161)), 0, by norm_num⟩
  | 1 => ⟨((-402167889/2199023255552), (5251126113/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((270587327/70368744177664), (-5094601691/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((511553425/4503599627370496), (3881819315/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-2506280545/144115188075855872), (-2458498701/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((1354498491/1152921504606846976), (20076763/18014398509481984)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-2244026977/36893488147419103232), (-1997116243/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((6311263499/2361183241434822606848), (247626799/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-3878420353/37778931862957161709568), (1040276937/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4145502833/1208925819614629174706176), (-2850833137/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1833305081/19342813113834066795298816), (2524948199/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((272240475/154742504910672534362390528), (-1840371191/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((30884303/2475880078570760549798248448), (1170639487/4951760157141521099596496896)), (9/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((402167889/2199023255552), (-5251126113/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-270587327/35184372088832), (5094601691/140737488355328)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-95916267/281474976710656), (-5822728973/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((78321267/1125899906842624), (2458498701/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((-846561557/144115188075855872), (-100383815/18014398509481984)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((3366040465/9223372036854775808), (1497837183/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-5522355561/295147905179352825856), (-216673449/147573952589676412928)), (11/295147905179352825856), by norm_num⟩
  | 7 => ⟨((3878420353/4722366482869645213696), (-1040276937/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4663690687/151115727451828646838272), (3207187279/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((2291631351/2417851639229258349412352), (-98630789/75557863725914323419136)), (15/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-374330653/19342813113834066795298816), (5061020775/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-370611637/2475880078570760549798248448), (-3511918461/1237940039285380274899124224)), (39/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1772161195/39614081257132168796771975168), (4273763149/39614081257132168796771975168)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((721566205/140737488355328), (-6792802255/281474976710656)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((31972089/70368744177664), (3881819315/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-78321267/562949953421312), (-4916997403/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2257497485/144115188075855872), (2141521387/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((-5610067441/4611686018427387904), (-312049413/576460752303423488)), (5/2305843009213693952), by norm_num⟩
  | 5 => ⟨((5522355561/73786976294838206464), (433346899/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-4524823745/1180591620717411303424), (606828213/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((3109127125/18889465931478580854784), (-534531213/4722366482869645213696)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1718723513/302231454903657293676544), (295892367/37778931862957161709568)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((311942211/2417851639229258349412352), (-16474677/37778931862957161709568)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((169863667/154742504910672534362390528), (3219258589/154742504910672534362390528)), (31/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-1772161195/4951760157141521099596496896), (-1068440787/1237940039285380274899124224)), (13/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2182829017/79228162514264337593543950336), (2422294157/79228162514264337593543950336)), (11/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-511553425/2251799813685248), (-3881819315/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((78321267/562949953421312), (2458498701/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-3386246227/144115188075855872), (-3212282081/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((5610067441/2305843009213693952), (2496395305/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-6902944451/36893488147419103232), (-541683623/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 5 => ⟨((3393617809/295147905179352825856), (-910242319/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-1360243117/2361183241434822606848), (935429623/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((3437447027/151115727451828646838272), (-4734277871/151115727451828646838272)), (5/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-1403739949/2417851639229258349412352), (148272093/75557863725914323419136)), (5/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-424659167/77371252455336267181195264), (-1006018309/9671406556917033397649408)), (37/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((2436721643/1237940039285380274899124224), (5876424329/1237940039285380274899124224)), (17/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-3274243525/19807040628566084398385987584), (-3633441235/19807040628566084398385987584)), (31/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((25250611/2475880078570760549798248448), (219133281/39614081257132168796771975168)), (27/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-501256109/9007199254740992), (-1966798961/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((1354498491/72057594037927936), (20076763/1125899906842624)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-3366040465/1152921504606846976), (-1497837183/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 3 => ⟨((5522355561/18446744073709551616), (433346899/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-212101113/9223372036854775808), (910242319/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 5 => ⟨((3264583481/2361183241434822606848), (-2245031095/2361183241434822606848)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-2406212919/37778931862957161709568), (1656997255/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((140373995/75557863725914323419136), (-948941395/151115727451828646838272)), (17/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((191096625/9671406556917033397649408), (7243331825/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-2436721643/309485009821345068724781056), (-5876424329/309485009821345068724781056)), (35/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1800833939/2475880078570760549798248448), (3996785359/4951760157141521099596496896)), (33/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-1939246925/39614081257132168796771975168), (-2103679497/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((6962265441/2535301200456458802993406410752), (549723689/1267650600228229401496703205376)), (7/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3611995977/576460752303423488), (-3426434219/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((4488053953/2305843009213693952), (1997116243/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-5522355561/18446744073709551616), (-433346899/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 3 => ⟨((4524823745/147573952589676412928), (-1213656425/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-1360243117/590295810358705651712), (1870859245/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((2406212919/18889465931478580854784), (-1656997255/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-655078643/151115727451828646838272), (4428393177/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-63698875/1208925819614629174706176), (-4828887883/4835703278458516698824704)), (25/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((114221327/4835703278458516698824704), (4407318247/77371252455336267181195264)), (7/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-1500694949/618970019642690137449562112), (-1665327233/618970019642690137449562112)), (29/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((3555286029/19807040628566084398385987584), (241046609/2475880078570760549798248448)), (15/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-6962265441/633825300114114700748351602688), (-549723689/316912650057057350374175801344)), (57/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((732599279/1267650600228229401496703205376), (-136145471/1267650600228229401496703205376)), (27/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5129204519/9223372036854775808), (-570604641/2305843009213693952)), (13/9223372036854775808), by norm_num⟩
  | 1 => ⟨((3155631749/18446744073709551616), (247626799/18446744073709551616)), (19/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3878420353/147573952589676412928), (130034617/18446744073709551616)), (7/73786976294838206464), by norm_num⟩
  | 3 => ⟨((3109127125/1180591620717411303424), (-534531213/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-3437447027/18889465931478580854784), (4734277871/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((140373995/18889465931478580854784), (-948941395/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((63698875/604462909807314587353088), (4828887883/2417851639229258349412352)), (27/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-1044309275/19342813113834066795298816), (-5036935139/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((3858929869/618970019642690137449562112), (1070567507/154742504910672534362390528)), (41/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-5078980041/9903520314283042199192993792), (-2754818389/9903520314283042199192993792)), (23/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((2735175709/79228162514264337593543950336), (863851511/158456325028528675187087900672)), (49/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-5023537913/2535301200456458802993406410752), (58348059/158456325028528675187087900672)), (25/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((3949087101/40564819207303340847894502572032), (-1141342861/20282409603651670423947251286016)), (25/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1577815875/36893488147419103232), (-247626799/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 1 => ⟨((30300159/2305843009213693952), (-130034617/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-4663690687/2361183241434822606848), (1603593639/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((3437447027/18889465931478580854784), (-4734277871/18889465931478580854784)), (29/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((-701869975/75557863725914323419136), (4744706975/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-382193249/2417851639229258349412352), (-7243331825/2417851639229258349412352)), (23/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((1827541231/19342813113834066795298816), (2203659123/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-964732467/77371252455336267181195264), (-1070567507/77371252455336267181195264)), (23/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((2856926273/2475880078570760549798248448), (24212271/38685626227668133590597632)), (29/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-854742409/9903520314283042199192993792), (-1079814389/79228162514264337593543950336)), (67/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((3453682315/633825300114114700748351602688), (-641828649/633825300114114700748351602688)), (75/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-2961815325/10141204801825835211973625643008), (428003573/2535301200456458802993406410752)), (41/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((260810601/20282409603651670423947251286016), (-2445603659/162259276829213363391578010288128)), (43/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3447484759/1180591620717411303424), (462345305/590295810358705651712)), (15/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((259093927/295147905179352825856), (-178177071/295147905179352825856)), (13/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-2291631351/18889465931478580854784), (3156185247/18889465931478580854784)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((311942211/37778931862957161709568), (-4217517311/151115727451828646838272)), (29/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((212329583/1208925819614629174706176), (1006018309/302231454903657293676544)), (57/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-1218360821/9671406556917033397649408), (-5876424329/19342813113834066795298816)), (51/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((3001389897/154742504910672534362390528), (1665327233/77371252455336267181195264)), (5/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-634872505/309485009821345068724781056), (-1377409195/1237940039285380274899124224)), (29/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((854742409/4951760157141521099596496896), (539907195/19807040628566084398385987584)), (19/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-1918712397/158456325028528675187087900672), (713142943/316912650057057350374175801344)), (47/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((3619996509/5070602400912917605986812821504), (-261557739/633825300114114700748351602688)), (55/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-2781979743/81129638414606681695789005144064), (1630402439/40564819207303340847894502572032)), (31/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((1513400053/1298074214633706907132624082305024), (-987286331/324518553658426726783156020576256)), (17/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3316402267/18889465931478580854784), (2280666509/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((1833305081/37778931862957161709568), (-1262474099/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-1497322613/302231454903657293676544), (5061020773/302231454903657293676544)), (41/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-339727333/2417851639229258349412352), (-6438517177/2417851639229258349412352)), (55/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((1218360821/9671406556917033397649408), (5876424329/19342813113834066795298816)), (59/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-3601667877/154742504910672534362390528), (-3996785359/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((888821507/309485009821345068724781056), (1928372873/1237940039285380274899124224)), (23/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-5470351417/19807040628566084398385987584), (-107981439/2475880078570760549798248448)), (69/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((3453682315/158456325028528675187087900672), (-80228581/19807040628566084398385987584)), (3/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-3619996509/2535301200456458802993406410752), (261557739/316912650057057350374175801344)), (63/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((1530088859/20282409603651670423947251286016), (-3586885365/40564819207303340847894502572032)), (77/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-1816080063/649037107316853453566312041152512), (1184743597/162259276829213363391578010288128)), (45/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((33563455/2596148429267413814265248164610048), (-5244177965/10384593717069655257060992658440192)), (51/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/989563107), (-646720/329854369)), 0, by norm_num⟩
  | 1 => ⟨((-52497291468800/326411714245164483), (14171963392000/108803904748388161)), 0, by norm_num⟩
  | 2 => ⟨((134055963/35184372088832), (-1750375371/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-962088273/18014398509481984), (4528534837/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-682071233/576460752303423488), (-5175759087/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((2673365915/18446744073709551616), (5244797229/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1203998659/147573952589676412928), (-2284289479/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((3419469679/9444732965739290427392), (190201547/1180591620717411303424)), (9/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-525938625/37778931862957161709568), (-330169065/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((4596646345/9671406556917033397649408), (-1232920813/9671406556917033397649408)), (21/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-4421869689/309485009821345068724781056), (3040888679/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((888875191/2475880078570760549798248448), (-4896869233/9903520314283042199192993792)), (23/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-483983067/79228162514264337593543950336), (1635885503/79228162514264337593543950336)), (67/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133115/134217728), (409615683/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((5624102481/4294967296), (378374679/2147483648)), (3/4294967296), by norm_num⟩
  | 2 => ⟨((2350021431/274877906944), (-1727624859/549755813888)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2965313027/35184372088832), (1259532573/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((2232426843/2251799813685248), (-3945518691/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-515654787/72057594037927936), (3125790323/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 6 => ⟨((-917452683/4611686018427387904), (-75498421/72057594037927936)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1048533153/73786976294838206464), (3510292783/147573952589676412928)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-86590331/147573952589676412928), (-2248423623/4722366482869645213696)), (99/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6105441101/302231454903657293676544), (1050172041/151115727451828646838272)), (275/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-6005186933/9671406556917033397649408), (56361843/4835703278458516698824704)), (375/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2664346245/154742504910672534362390528), (-2058364061/309485009821345068724781056)), (503/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4165278303/9903520314283042199192993792), (113758075/309485009821345068724781056)), (681/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2287888435/4503599627370496), (3734134125/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((769670619/36028797018963968), (-3622827869/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((272828493/288230376151711744), (2070303635/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-891121971/4611686018427387904), (-1748265743/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((1203998659/73786976294838206464), (2284289479/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-2393628775/2361183241434822606848), (-2130257327/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((3927008399/75557863725914323419136), (154078897/37778931862957161709568)), (17/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-5515975613/2417851639229258349412352), (1479504977/2417851639229258349412352)), (15/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((1658201133/19342813113834066795298816), (-1140333255/19342813113834066795298816)), (13/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-3259209033/1237940039285380274899124224), (4488796797/1237940039285380274899124224)), (11/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((532381373/9903520314283042199192993792), (-3598948107/19807040628566084398385987584)), (9/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((263546053/633825300114114700748351602688), (2497364239/316912650057057350374175801344)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-315050879/2535301200456458802993406410752), (-1519560231/5070602400912917605986812821504)), (3/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133047/134217728), (1638462843/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((5624102573/4294967296), (378374463/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((2350021691/274877906944), (-863810455/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-1482659913/17592186044416), (78720369/1099511627776)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1116231793/1125899906842624), (-986370959/562949953421312)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((-515727835/72057594037927936), (1562878909/36028797018963968)), (37/144115188075855872), by norm_num⟩
  | 6 => ⟨((-917212997/4611686018427387904), (-603985017/576460752303423488)), (29/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1048364819/73786976294838206464), (3510383085/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1385242879/2361183241434822606848), (-2248702025/4722366482869645213696)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1526161349/75557863725914323419136), (525359995/75557863725914323419136)), (69/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-6004667029/9671406556917033397649408), (110966387/9671406556917033397649408)), (47/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((5328821175/309485009821345068724781056), (-2055925229/309485009821345068724781056)), (63/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-2083254485/4951760157141521099596496896), (3637290509/9903520314283042199192993792)), (341/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-831477313/4611686018427387904), (-6309496791/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((509212555/4611686018427387904), (249752249/1152921504606846976)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-1375998467/73786976294838206464), (-652654137/36893488147419103232)), (3/73786976294838206464), by norm_num⟩
  | 3 => ⟨((569911613/295147905179352825856), (1014408251/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-2805005999/18889465931478580854784), (-440225421/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((5515975613/604462909807314587353088), (-92469061/37778931862957161709568)), (1/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-552733711/1208925819614629174706176), (3040888679/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((2793607743/154742504910672534362390528), (-3847540111/154742504910672534362390528)), (17/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-285204307/618970019642690137449562112), (964003957/618970019642690137449562112)), (17/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-345119831/79228162514264337593543950336), (-6540715863/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((1980319811/1267650600228229401496703205376), (4775760725/1267650600228229401496703205376)), (29/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-665243129/5070602400912917605986812821504), (-738222981/5070602400912917605986812821504)), (13/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((5253409659/649037107316853453566312041152512), (1424714157/324518553658426726783156020576256)), (45/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133047/134217728), (1638462843/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((5624102573/4294967296), (756748927/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((1175010843/137438953472), (-215952615/68719476736)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-1482659879/17592186044416), (1259525919/17592186044416)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((558115813/562949953421312), (-1972741931/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1031454355/144115188075855872), (6251515283/144115188075855872)), (19/72057594037927936), by norm_num⟩
  | 6 => ⟨((-458607553/2305843009213693952), (-2415939343/2305843009213693952)), (59/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1048366151/73786976294838206464), (438797427/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-1385243967/2361183241434822606848), (-1124347335/2361183241434822606848)), (101/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6104644079/302231454903657293676544), (2101415029/302231454903657293676544)), (277/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-375290745/604462909807314587353088), (111002823/9671406556917033397649408)), (377/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1332195143/77371252455336267181195264), (-2055970287/309485009821345068724781056)), (505/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4166428809/9903520314283042199192993792), (909333497/2475880078570760549798248448)), (683/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((550399387/147573952589676412928), (1044246619/295147905179352825856)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-2735575743/2361183241434822606848), (-2434579801/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((3366007199/18889465931478580854784), (528270505/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-5515975613/302231454903657293676544), (1479504975/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((1658201133/1208925819614629174706176), (-570166627/604462909807314587353088)), (7/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-1466644065/19342813113834066795298816), (4039917117/38685626227668133590597632)), (5/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((199643015/77371252455336267181195264), (-5398422159/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((38825981/1237940039285380274899124224), (1471661069/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-556964947/39614081257132168796771975168), (-5372730815/158456325028528675187087900672)), (35/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((3658837209/2535301200456458802993406410752), (4060226397/2535301200456458802993406410752)), (9/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-4334062969/40564819207303340847894502572032), (-1175389179/20282409603651670423947251286016)), (19/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((4243666555/649037107316853453566312041152512), (335069677/324518553658426726783156020576256)), (9/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-3572293627/10384593717069655257060992658440192), (663871249/10384593717069655257060992658440192)), (67/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133047/134217728), (1638462843/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((5624102573/4294967296), (756748927/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((1175010843/137438953472), (-215952615/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2965319759/35184372088832), (1259525919/17592186044416)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((2232463255/2251799813685248), (-493185483/281474976710656)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((-515727183/72057594037927936), (3125757649/72057594037927936)), (39/144115188075855872), by norm_num⟩
  | 6 => ⟨((-458607547/2305843009213693952), (-2415939363/2305843009213693952)), (15/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2096732307/147573952589676412928), (219398719/9223372036854775808)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-43288875/73786976294838206464), (-1124347415/2361183241434822606848)), (51/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((6104644515/302231454903657293676544), (2101415513/302231454903657293676544)), (139/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-6004652953/9671406556917033397649408), (111002263/9671406556917033397649408)), (189/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((1332195649/77371252455336267181195264), (-2055969967/309485009821345068724781056)), (253/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-520804027/1237940039285380274899124224), (3637334621/9903520314283042199192993792)), (171/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1360002909/37778931862957161709568), (-53360657/18889465931478580854784)), (9/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((6686031045/604462909807314587353088), (-448334841/151115727451828646838272)), (29/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-4019881535/2417851639229258349412352), (2764444253/2417851639229258349412352)), (23/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((2962917303/19342813113834066795298816), (-510090545/2417851639229258349412352)), (13/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-1209957667/154742504910672534362390528), (1022428439/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-329432565/2475880078570760549798248448), (-6243410597/2475880078570760549798248448)), (41/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((787627197/9903520314283042199192993792), (118715643/618970019642690137449562112)), (31/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-831553911/79228162514264337593543950336), (-1845557453/158456325028528675187087900672)), (41/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((4925071555/5070602400912917605986812821504), (667834761/1267650600228229401496703205376)), (51/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-5893981325/81129638414606681695789005144064), (-930749103/81129638414606681695789005144064)), (59/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((5953822711/1298074214633706907132624082305024), (-553226041/649037107316853453566312041152512)), (33/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((-638236299/2596148429267413814265248164610048), (2951351237/20769187434139310514121985316880384)), (9/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((3596903103/332306998946228968225951765070086144), (-2107995073/166153499473114484112975882535043072)), (75/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133047/134217728), (1638462843/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((5624102573/4294967296), (756748927/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((1175010843/137438953472), (-215952615/68719476736)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2965319759/35184372088832), (1259525919/17592186044416)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((2232463255/2251799813685248), (-493185483/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-515727183/72057594037927936), (3125757649/72057594037927936)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-458607547/2305843009213693952), (-4831878725/4611686018427387904)), (61/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2096732305/147573952589676412928), (1755189751/73786976294838206464)), (41/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2770487995/4722366482869645213696), (-562173707/1180591620717411303424)), (103/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6104644493/302231454903657293676544), (1050707755/151115727451828646838272)), (279/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-6004652909/9671406556917033397649408), (111002255/9671406556917033397649408)), (379/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((666097815/38685626227668133590597632), (-2055969923/309485009821345068724781056)), (507/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4166432109/9903520314283042199192993792), (3637334495/9903520314283042199192993792)), (685/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((813989199/2417851639229258349412352), (-279887323/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-3599781725/38685626227668133590597632), (2478927941/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((367508021/38685626227668133590597632), (-155274297/4835703278458516698824704)), (41/154742504910672534362390528), by norm_num⟩
  | 3 => ⟨((83383847/309485009821345068724781056), (3160583679/618970019642690137449562112)), (55/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-1196154711/4951760157141521099596496896), (-5769319337/9903520314283042199192993792)), (59/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((884005773/19807040628566084398385987584), (3923939077/79228162514264337593543950336)), (55/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-3490486609/633825300114114700748351602688), (-236653241/79228162514264337593543950336)), (23/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((2685323799/5070602400912917605986812821504), (424053383/5070602400912917605986812821504)), (69/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-6781469495/162259276829213363391578010288128), (630130539/81129638414606681695789005144064)), (95/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((3554017663/1298074214633706907132624082305024), (-2054324245/1298074214633706907132624082305024)), (63/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((-3004402251/20769187434139310514121985316880384), (1760755005/10384593717069655257060992658440192)), (77/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((1782979791/332306998946228968225951765070086144), (-4652600807/332306998946228968225951765070086144)), (45/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-131806881/5316911983139663491615228241121378304), (5148596433/5316911983139663491615228241121378304)), (101/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696133047/134217728), (1638462843/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((5624102573/4294967296), (756748927/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((1175010843/137438953472), (-215952615/68719476736)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2965319759/35184372088832), (1259525919/17592186044416)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((2232463255/2251799813685248), (-493185483/281474976710656)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((-515727183/72057594037927936), (3125757649/72057594037927936)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-458607547/2305843009213693952), (-4831878725/4611686018427387904)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2096732305/147573952589676412928), (1755189751/73786976294838206464)), (83/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2770487995/4722366482869645213696), (-562173707/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((3052322247/151115727451828646838272), (1050707755/151115727451828646838272)), (35/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-3002326455/4835703278458516698824704), (111002257/9671406556917033397649408)), (95/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((2664391261/154742504910672534362390528), (-2055969927/309485009821345068724781056)), (127/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-4166432109/9903520314283042199192993792), (3637334505/9903520314283042199192993792)), (343/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((32500792579899/65536), (-390128709497555/2097152)), (102545075/2097152), by norm_num⟩
  | 1 => ⟨((5457357943/8), (-312435811/2)), 74, by norm_num⟩
  | 2 => ⟨((7424891647/16), (-725319287/16)), (451/8), by norm_num⟩
  | 3 => ⟨((6679981247/32), (41594045/8)), (923/32), by norm_num⟩
  | 4 => ⟨((4479123103/64), (160315077/16)), (715/64), by norm_num⟩
  | 5 => ⟨((1195201741/64), (622959593/128)), (895/256), by norm_num⟩
  | 6 => ⟨((529152629/128), (805130359/512)), (943/1024), by norm_num⟩
  | 7 => ⟨((799769445/1024), (1617653257/4096)), (215/1024), by norm_num⟩
  | 8 => ⟨((2105914977/16384), (673835703/8192)), (173/4096), by norm_num⟩
  | 9 => ⟨((2452149639/131072), (1931038179/131072)), (125/16384), by norm_num⟩
  | 10 => ⟨((638591133/262144), (609102451/262144)), (1311/1048576), by norm_num⟩
  | 11 => ⟨((2400824941/8388608), (1376404513/4194304)), (789/4194304), by norm_num⟩
  | 12 => ⟨((2048439159/67108864), (2820860925/67108864)), (879/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805071156421593/5070602400912917605986812821504), (-116867434455/2535301200456458802993406410752)), (21837/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((906779327520577/316912650057057350374175801344), (-573460974395/633825300114114700748351602688)), (53607/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1928922322187787/39614081257132168796771975168), (-646829511805/39614081257132168796771975168)), (60469/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1931185379738991/2475880078570760549798248448), (-172174785405/618970019642690137449562112)), (128771/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1812895632219285/154742504910672534362390528), (-86289200929/19342813113834066795298816)), (64539/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1588698659244601/9671406556917033397649408), (-324444720495/4835703278458516698824704)), (121339/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1293087722014349/604462909807314587353088), (-142376182627/151115727451828646838272)), (26625/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1943616266044199/75557863725914323419136), (-29021725283/2361183241434822606848)), (173681/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1339485103807647/4722366482869645213696), (-43711132997/295147905179352825856)), (130805/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1679249742059297/590295810358705651712), (-966311511475/590295810358705651712)), (180745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((473979243169783/18446744073709551616), (-1214932250625/73786976294838206464)), (28409/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1904417498776521/9223372036854775808), (-1376553052517/9223372036854775808)), (257539/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1675996627493141/1152921504606846976), (-86803266085/72057594037927936)), (129941/576460752303423488), by norm_num⟩
  | 5 => ⟨((1266714810477239/144115188075855872), (-614614999029/72057594037927936)), (115031/72057594037927936), by norm_num⟩
  | 4 => ⟨((800297237928529/18014398509481984), (-936093497237/18014398509481984)), (175247/18014398509481984), by norm_num⟩
  | 3 => ⟨((1626792377036773/9007199254740992), (-2390684425241/9007199254740992)), (55967/1125899906842624), by norm_num⟩
  | 2 => ⟨((1253547372884891/2251799813685248), (-617023763565/562949953421312)), (462501/2251799813685248), by norm_num⟩
  | 1 => ⟨((661309596949585/562949953421312), (-3901878725115/1125899906842624)), (182967/281474976710656), by norm_num⟩
  | 0 => ⟨((770505048154127/562949953421312), (-4320545764321/562949953421312)), (1623663/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((770505048154127/562949953421312), (-4320545764321/562949953421312)), (6193782810691451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054550868167489/562949953421312), (-2956748021701/140737488355328)), (558689/140737488355328), by norm_num⟩
  | 2 => ⟨((987599029943261/281474976710656), (-22155015196555/281474976710656)), (8466453/562949953421312), by norm_num⟩
  | 3 => ⟨((1731701003476101/140737488355328), (-19433584978131/35184372088832)), (7593069/70368744177664), by norm_num⟩
  | 4 => ⟨((664523044999421/4398046511104), (-119560036920659/8796093022208)), (24405665/8796093022208), by norm_num⟩
  | 5 => ⟨((389037448236871/17179869184), (-282264522137011/68719476736)), (62801669/68719476736), by norm_num⟩
  | 6 => ⟨((32500792579899/65536), (-390128709497555/2097152)), (102545075/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2696133047/134217728), (1638462843/134217728)), (9/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2252800/39857569), (-7760640/39857569)), 0, by norm_num⟩
  | 1 => ⟨((27576212684800/1588625806589761), (17483169792000/1588625806589761)), 0, by norm_num⟩
  | 2 => ⟨((-3434812925/2199023255552), (1516138207/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-198136257/2199023255552), (-1680356315/8796093022208)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((11624271/549755813888), (-949440721/281474976710656)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((-303056973/1125899906842624), (4850003039/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((-910082451/4503599627370496), (-1568577249/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((2044690515/144115188075855872), (-2480592659/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 8 => ⟨((2939408135/2305843009213693952), (4306612105/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-2009353095/9223372036854775808), (1315660029/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-29028929/36893488147419103232), (-6854738365/295147905179352825856)), (37/295147905179352825856), by norm_num⟩
  | 11 => ⟨((168475929/73786976294838206464), (684441645/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-1142506847/9444732965739290427392), (1944703291/9444732965739290427392)), (39/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (6063/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (6063/1280)))⁻¹=value ((2252800/39857569), (-7760640/39857569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/39857569), (-7760640/39857569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3891200/46001569), (-7760640/46001569)), 0, by norm_num⟩
  | 1 => ⟨((22543047884800/2116144350461761), (30198202368000/2116144350461761)), 0, by norm_num⟩
  | 2 => ⟨((-1818911021/1099511627776), (1297584503/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1586111123/35184372088832), (-668594753/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((384094615/35184372088832), (2880103907/281474976710656)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-5966433243/4503599627370496), (137381183/281474976710656)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((66931745/4503599627370496), (-4769974957/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((1518839499/144115188075855872), (987635529/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((-1180376439/1152921504606846976), (1381531869/2305843009213693952)), (21/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-133509349/18446744073709551616), (-128782401/1152921504606846976)), (11/18446744073709551616), by norm_num⟩
  | 10 => ⟨((5742570465/590295810358705651712), (2428359351/590295810358705651712)), (23/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-3581713737/4722366482869645213696), (1526764887/2361183241434822606848)), (3/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-848682427/37778931862957161709568), (-1725084027/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (6063/1280)))⁻¹=value ((3891200/46001569), (-7760640/46001569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/46001569), (-7760640/46001569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-51461437849600/1833510710525761), (-47681372160000/1833510710525761)), 0, by norm_num⟩
  | 1 => ⟨((3686467273/549755813888), (-897523891/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((203009117/2199023255552), (2383484163/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1189072809/8796093022208), (-343166809/8796093022208)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((2878869833/281474976710656), (-957386157/70368744177664)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((1188551337/1125899906842624), (3750953575/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((-244253549/1125899906842624), (816410229/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 7 => ⟨((1051702033/288230376151711744), (-867057047/36028797018963968)), (19/288230376151711744), by norm_num⟩
  | 8 => ⟨((1325040253/576460752303423488), (2925080237/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-3885196841/18446744073709551616), (3376178445/18446744073709551616)), (3/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-387939583/36893488147419103232), (-1008614755/36893488147419103232)), (27/147573952589676412928), by norm_num⟩
  | 11 => ⟨((7182086597/2361183241434822606848), (-157881597/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-1860672481/18889465931478580854784), (5614490609/18889465931478580854784)), (15/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((614400/6158041), (-2586880/18474123)), 0, by norm_num⟩
  | 1 => ⟨((1647280947200/341293220619129), (529793024000/37921468957681)), 0, by norm_num⟩
  | 2 => ⟨((-670110941/549755813888), (-1578987861/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((3023870743/35184372088832), (-2372525571/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((15260275/35184372088832), (5281086363/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-1527713171/2251799813685248), (-985429661/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((4646559253/72057594037927936), (-462412575/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1636760629/1152921504606846976), (835188043/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((-48268099/144115188075855872), (-3583272049/9223372036854775808)), (3/1152921504606846976), by norm_num⟩
  | 9 => ⟨((809967079/18446744073709551616), (-150112119/36893488147419103232)), (47/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-562417085/295147905179352825856), (3868989663/1180591620717411303424)), (23/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-634619927/4722366482869645213696), (-5608252703/18889465931478580854784)), (89/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1038577179/37778931862957161709568), (816361133/151115727451828646838272)), (43/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (6063/1280)))⁻¹=value ((614400/6158041), (-2586880/18474123)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/6158041), (-2586880/18474123))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7082828303/1099511627776), (367111879/274877906944)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((483423887/1099511627776), (-489937949/274877906944)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((4641549581/17592186044416), (945197981/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-103704113/2199023255552), (1603565217/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-71804887/562949953421312), (-8138210707/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((3832606125/4503599627370496), (1666474451/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-3014143951/36028797018963968), (2738985133/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1197583561/288230376151711744), (-3620675675/288230376151711744)), (13/288230376151711744), by norm_num⟩
  | 8 => ⟨((6888624307/4611686018427387904), (647730357/4611686018427387904)), (7/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-1470860207/18446744073709551616), (5361640801/36893488147419103232)), (17/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-3268609491/295147905179352825856), (-4157925151/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 11 => ⟨((4327816751/2361183241434822606848), (-1192839035/2361183241434822606848)), (43/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-917042679/37778931862957161709568), (3720809889/18889465931478580854784)), (91/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7168000/68119969), (-7760640/68119969)), 0, by norm_num⟩
  | 1 => ⟨((4423654604800/4640330176560961), (55628267520000/4640330176560961)), 0, by norm_num⟩
  | 2 => ⟨((-805973961/1099511627776), (-1267565469/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((5024444327/70368744177664), (-804190205/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-218542277/70368744177664), (1314073969/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-923549649/9007199254740992), (-3805848815/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((4246135395/144115188075855872), (2362066601/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 7 => ⟨((-5727242425/2305843009213693952), (470388787/576460752303423488)), (27/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1553189289/18446744073709551616), (-3401883753/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 9 => ⟨((224127147/36893488147419103232), (4279326159/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-2704796115/2361183241434822606848), (-246025495/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 11 => ⟨((1586920261/18889465931478580854784), (-818374179/18889465931478580854784)), (71/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-1180020981/604462909807314587353088), (2135247357/302231454903657293676544)), (63/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (6063/1280)))⁻¹=value ((7168000/68119969), (-7760640/68119969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/68119969), (-7760640/68119969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2312016363/4398046511104), (3845751159/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-393507677/2199023255552), (-2758405659/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((5596105767/70368744177664), (-2502777/2199023255552)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((-1825497889/281474976710656), (3479156269/281474976710656)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((-675409433/562949953421312), (-3976262489/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((5321711757/18014398509481984), (-602629509/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 6 => ⟨((-496452743/36028797018963968), (1301296379/36028797018963968)), (17/144115188075855872), by norm_num⟩
  | 7 => ⟨((-461276761/144115188075855872), (-2037021543/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 8 => ⟨((5007099571/9223372036854775808), (-175016839/1152921504606846976)), (27/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-433446827/36893488147419103232), (4669726143/73786976294838206464)), (1/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-3398412957/590295810358705651712), (-77838775/18446744073709551616)), (37/590295810358705651712), by norm_num⟩
  | 11 => ⟨((801125451/1180591620717411303424), (-108587695/295147905179352825856)), (43/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((388500913/75557863725914323419136), (1539556855/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/1955683), (-180480/1955683)), 0, by norm_num⟩
  | 1 => ⟨((-108953600/88946418523), (36962304000/3824695996489)), 0, by norm_num⟩
  | 2 => ⟨((-2855733821440000/7479892940501596987), (-4207714762752000/7479892940501596987)), 0, by norm_num⟩
  | 3 => ⟨((6466512019/140737488355328), (833019241/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-415463111/140737488355328), (1689172341/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((768699093/9007199254740992), (-967237281/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((784194145/144115188075855872), (4376293725/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-4544865045/4611686018427387904), (-1254195565/2305843009213693952)), (13/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1414853831/18446744073709551616), (-626970199/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-1907747003/590295810358705651712), (2614366993/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-331891697/9444732965739290427392), (-7197342631/18889465931478580854784)), (29/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((2934870809/151115727451828646838272), (2769807057/151115727451828646838272)), (47/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-4503618713/2417851639229258349412352), (-2401399/37778931862957161709568)), (75/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (6063/1280)))⁻¹=value ((204800/1955683), (-180480/1955683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((204800/1955683), (-180480/1955683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((902314815/35184372088832), (4928743771/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1952239215/35184372088832), (-1581687973/70368744177664)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((3424232121/281474976710656), (-155541907/17592186044416)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((523571207/2251799813685248), (6568915841/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 4 => ⟨((-980385839/2251799813685248), (-973733367/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((4368263915/72057594037927936), (-2848723477/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((155705151/288230376151711744), (1429794091/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((-5291272505/4611686018427387904), (-2625043371/4611686018427387904)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((4765962819/36893488147419103232), (-1644222401/18446744073709551616)), (37/36893488147419103232), by norm_num⟩
  | 9 => ⟨((578174861/295147905179352825856), (5412843177/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-4583282811/2361183241434822606848), (-1842793355/2361183241434822606848)), (27/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3301064883/18889465931478580854784), (-1415316743/9444732965739290427392)), (63/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((880133599/151115727451828646838272), (905583417/37778931862957161709568)), (69/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3481600/34448523), (-2586880/34448523)), 0, by norm_num⟩
  | 1 => ⟨((-904931737600/395566912293843), (9006481408000/1186700736881529)), 0, by norm_num⟩
  | 2 => ⟨((-744850593/4398046511104), (-4129056999/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3685015725/140737488355328), (2443540849/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-4447423815/2251799813685248), (238097095/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((1726427823/18014398509481984), (-2864311033/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-66938041/36028797018963968), (2195102357/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-110717505/576460752303423488), (-4193040753/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((3951281931/147573952589676412928), (2325994481/147573952589676412928)), (25/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-4592092793/2361183241434822606848), (493097441/2361183241434822606848)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1708316651/18889465931478580854784), (-3157397733/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-865649063/604462909807314587353088), (2302707295/302231454903657293676544)), (37/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-1033404087/4835703278458516698824704), (-4243674931/9671406556917033397649408)), (53/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (6063/1280)))⁻¹=value ((3481600/34448523), (-2586880/34448523)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/34448523), (-2586880/34448523))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3690507821/281474976710656), (3442988639/281474976710656)), (7/281474976710656), by norm_num⟩
  | 1 => ⟨((-592330269/70368744177664), (995940817/562949953421312)), (5/281474976710656), by norm_num⟩
  | 2 => ⟨((260224041/281474976710656), (-4982291841/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((2512290469/9007199254740992), (3818075871/9007199254740992)), (11/9007199254740992), by norm_num⟩
  | 4 => ⟨((-3251571093/36028797018963968), (-7604993/72057594037927936)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((278237595/36028797018963968), (-3438925457/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 6 => ⟨((494227879/576460752303423488), (4277385637/2305843009213693952)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-5011612839/18446744073709551616), (-37952113/1152921504606846976)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1573689317/73786976294838206464), (-4020877077/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1795021795/1180591620717411303424), (4585469431/1180591620717411303424)), (53/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-563679461/1180591620717411303424), (-170710689/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((2512381957/75557863725914323419136), (-803592535/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1393719721/604462909807314587353088), (1627071129/302231454903657293676544)), (43/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12083200/125873569), (-7760640/125873569)), 0, by norm_num⟩
  | 1 => ⟨((-42888094515200/15844155372797761), (93773365248000/15844155372797761)), 0, by norm_num⟩
  | 2 => ⟨((-924066387/17592186044416), (-6465421695/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((487326209/35184372088832), (563673831/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2609076345/2251799813685248), (-770047695/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((595868609/9007199254740992), (-43470055/2251799813685248)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-743676733/288230376151711744), (3419482601/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((298922337/9223372036854775808), (-4093245137/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((389952003/73786976294838206464), (3438317185/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-2893761695/4722366482869645213696), (-935566251/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((3145193225/75557863725914323419136), (2412349/18889465931478580854784)), (51/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-2420135351/1208925819614629174706176), (1543905807/1208925819614629174706176)), (65/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((2194110481/38685626227668133590597632), (-4758695209/38685626227668133590597632)), (83/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (6063/1280)))⁻¹=value ((12083200/125873569), (-7760640/125873569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/125873569), (-7760640/125873569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4532353537/2251799813685248), (823786459/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3633717783/4503599627370496), (3302459557/4503599627370496)), (7/2251799813685248), by norm_num⟩
  | 2 => ⟨((-284146247/9007199254740992), (-2967553365/9007199254740992)), (19/18014398509481984), by norm_num⟩
  | 3 => ⟨((4653493231/72057594037927936), (345297149/9007199254740992)), (19/72057594037927936), by norm_num⟩
  | 4 => ⟨((-3732991457/288230376151711744), (822166527/144115188075855872)), (17/288230376151711744), by norm_num⟩
  | 5 => ⟨((1041072847/2305843009213693952), (-1322712039/576460752303423488)), (15/1152921504606846976), by norm_num⟩
  | 6 => ⟨((141656239/576460752303423488), (2299046325/9223372036854775808)), (11/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-3511380051/73786976294838206464), (678955823/73786976294838206464)), (63/147573952589676412928), by norm_num⟩
  | 8 => ⟨((698882253/295147905179352825856), (-3446799857/590295810358705651712)), (21/295147905179352825856), by norm_num⟩
  | 9 => ⟨((2133432463/4722366482869645213696), (1493125939/2361183241434822606848)), (53/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-6911165093/75557863725914323419136), (229389031/37778931862957161709568)), (127/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((2884566403/604462909807314587353088), (-43658319/4722366482869645213696)), (19/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1472959907/2417851639229258349412352), (4668773393/4835703278458516698824704)), (11/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13721600/151678369), (-7760640/151678369)), 0, by norm_num⟩
  | 1 => ⟨((-64027386675200/23006327622500161), (106488397824000/23006327622500161)), 0, by norm_num⟩
  | 2 => ⟨((131428777/17592186044416), (-4935717981/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((962587283/140737488355328), (3625878613/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1438718369/2251799813685248), (-1836109893/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((11070387/281474976710656), (151036163/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1056430489/576460752303423488), (2101430187/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((549520983/9223372036854775808), (-406315625/4611686018427387904)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-520583039/1180591620717411303424), (3252194355/590295810358705651712)), (31/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-571406289/4722366482869645213696), (-4920447301/18889465931478580854784)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((3668196315/302231454903657293676544), (656369079/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-58272069/75557863725914323419136), (-797285447/9671406556917033397649408)), (3/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((5724452701/154742504910672534362390528), (-1238020231/77371252455336267181195264)), (55/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (6063/1280)))⁻¹=value ((13721600/151678369), (-7760640/151678369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/151678369), (-7760640/151678369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3617351789/18014398509481984), (-314748847/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((-385214819/9007199254740992), (4176392701/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 2 => ⟨((-1494615633/72057594037927936), (-4976058681/144115188075855872)), (13/72057594037927936), by norm_num⟩
  | 3 => ⟨((2774286071/288230376151711744), (688848859/576460752303423488)), (7/144115188075855872), by norm_num⟩
  | 4 => ⟨((-1551489193/1152921504606846976), (1580591201/1152921504606846976)), (25/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-234083053/4611686018427387904), (-6034193733/18446744073709551616)), (45/18446744073709551616), by norm_num⟩
  | 6 => ⟨((1684125973/36893488147419103232), (1732095035/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-479584579/73786976294838206464), (31112919/9223372036854775808)), (25/295147905179352825856), by norm_num⟩
  | 8 => ⟨((581560389/4722366482869645213696), (-571552151/590295810358705651712)), (69/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((872923483/9444732965739290427392), (382694205/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-4297068217/302231454903657293676544), (1187212093/302231454903657293676544)), (27/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1212077389/2417851639229258349412352), (-980393355/604462909807314587353088)), (65/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((596378257/4835703278458516698824704), (688414417/4835703278458516698824704)), (153/19342813113834066795298816), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5120000/60253323), (-2586880/60253323)), 0, by norm_num⟩
  | 1 => ⟨((-1084580659200/403384770282481), (13244825600000/3630462932542329)), 0, by norm_num⟩
  | 2 => ⟨((631906703/17592186044416), (-3742238351/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1711536269/562949953421312), (5521999753/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-382515275/1125899906842624), (-1582989857/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((6335341277/288230376151711744), (2202340865/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5063174873/4611686018427387904), (678838233/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 7 => ⟨((3208770053/73786976294838206464), (-2200506361/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-178188625/147573952589676412928), (1299001925/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 9 => ⟨((153453945/37778931862957161709568), (-563932397/4722366482869645213696)), (13/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1445220781/604462909807314587353088), (3119580697/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-4107859429/19342813113834066795298816), (-3248588413/19342813113834066795298816)), (7/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((3908292151/309485009821345068724781056), (398732085/154742504910672534362390528)), (29/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (6063/1280)))⁻¹=value ((5120000/60253323), (-2586880/60253323)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/60253323), (-2586880/60253323))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4053279165/288230376151711744), (-524575595/36028797018963968)), (25/288230376151711744), by norm_num⟩
  | 1 => ⟨((609715081/576460752303423488), (3633644753/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 2 => ⟨((-4105001697/1152921504606846976), (-2947362181/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((2479609561/2305843009213693952), (-644528585/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-438939815/4611686018427387904), (3859638545/18446744073709551616)), (33/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-693778273/36893488147419103232), (-5393831875/147573952589676412928)), (15/36893488147419103232), by norm_num⟩
  | 6 => ⟨((1909711481/295147905179352825856), (87371889/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-1671245563/2361183241434822606848), (3089744477/4722366482869645213696)), (35/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-569638591/37778931862957161709568), (-616534637/4722366482869645213696)), (99/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((4465841539/302231454903657293676544), (2460597563/302231454903657293676544)), (1/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-4453862729/2417851639229258349412352), (2213546837/2417851639229258349412352)), (5/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((305377013/9671406556917033397649408), (-287464965/1208925819614629174706176)), (97/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((3149738619/154742504910672534362390528), (1360404967/77371252455336267181195264)), (231/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((83/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16998400/213118369), (-7760640/213118369)), 0, by norm_num⟩
  | 1 => ⟨((-114359034675200/45419439205220161), (131918462976000/45419439205220161)), 0, by norm_num⟩
  | 2 => ⟨((836152091/17592186044416), (-5688370967/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((590053459/562949953421312), (1029206035/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1575806159/9007199254740992), (-4909964827/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((3441349019/288230376151711744), (1107422467/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2841089361/4611686018427387904), (-821458935/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1932503413/73786976294838206464), (-282789851/36893488147419103232)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-4273336841/4722366482869645213696), (1847717841/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((51568693/2361183241434822606848), (-900723135/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1688765/604462909807314587353088), (1389838011/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-1615226499/38685626227668133590597632), (-3549295683/38685626227668133590597632)), (9/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4129241223/1237940039285380274899124224), (897100641/309485009821345068724781056)), (17/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (6063/1280)))⁻¹=value ((16998400/213118369), (-7760640/213118369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/213118369), (-7760640/213118369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((681891889/1152921504606846976), (-3858573327/2305843009213693952)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((2537870605/4611686018427387904), (4816935913/4611686018427387904)), (5/576460752303423488), by norm_num⟩
  | 2 => ⟨((-3855778695/9223372036854775808), (-976587385/9223372036854775808)), (17/4611686018427387904), by norm_num⟩
  | 3 => ⟨((3475069185/36893488147419103232), (-149516313/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-752116703/295147905179352825856), (225559717/9223372036854775808)), (77/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-3747768049/1180591620717411303424), (-1919727889/590295810358705651712)), (71/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((3518204369/4722366482869645213696), (-654271257/9444732965739290427392)), (29/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1153746409/18889465931478580854784), (1781033389/18889465931478580854784)), (87/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-791497941/151115727451828646838272), (-2226904945/151115727451828646838272)), (31/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((2360085233/1208925819614629174706176), (364865063/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-978900563/4835703278458516698824704), (2931820751/19342813113834066795298816)), (13/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-127991539/154742504910672534362390528), (-288653847/9671406556917033397649408)), (1/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((3515968265/1237940039285380274899124224), (568341515/309485009821345068724781056)), (307/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((91/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18636800/248753569), (-7760640/248753569)), 0, by norm_num⟩
  | 1 => ⟨((-143551390515200/61878338090237761), (144633495552000/61878338090237761)), 0, by norm_num⟩
  | 2 => ⟨((1774812827/35184372088832), (-2176989007/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((179099/4398046511104), (1526296105/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-48476313/562949953421312), (-3647795887/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((920098041/144115188075855872), (3598395747/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-3104006493/9223372036854775808), (-619092757/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((4338935791/295147905179352825856), (-16293413/73786976294838206464)), (15/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1292171841/2361183241434822606848), (1121995463/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1268934347/75557863725914323419136), (-2634997595/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1726912857/4835703278458516698824704), (553185297/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-17370171/19342813113834066795298816), (-1541747189/38685626227668133590597632)), (69/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1622475611/2475880078570760549798248448), (3661599947/2475880078570760549798248448)), (15/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (6063/1280)))⁻¹=value ((18636800/248753569), (-7760640/248753569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/248753569), (-7760640/248753569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-291271913/36893488147419103232), (-5306153855/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 1 => ⟨((2817029341/36893488147419103232), (2447919871/36893488147419103232)), (37/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-1421093969/36893488147419103232), (562993573/147573952589676412928)), (65/147573952589676412928), by norm_num⟩
  | 3 => ⟨((59189971/9223372036854775808), (-1260342923/147573952589676412928)), (41/295147905179352825856), by norm_num⟩
  | 4 => ⟨((548813691/1180591620717411303424), (5505659669/2361183241434822606848)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-3712556625/9444732965739290427392), (-1061170505/4722366482869645213696)), (75/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1357882255/18889465931478580854784), (-987799181/37778931862957161709568)), (31/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-74037063/18889465931478580854784), (1672914939/151115727451828646838272)), (3/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-132683065/151115727451828646838272), (-856221557/604462909807314587353088)), (139/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((4256973697/19342813113834066795298816), (114530545/4835703278458516698824704)), (187/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-2948052899/154742504910672534362390528), (3128454921/154742504910672534362390528)), (241/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-368169033/618970019642690137449562112), (-2020821353/618970019642690137449562112)), (299/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((3399783425/9903520314283042199192993792), (401091899/2475880078570760549798248448)), (181/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((99/8), (6063/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2252800/31962841), (-2586880/95888523)), 0, by norm_num⟩
  | 1 => ⟨((-19492011212800/9194608843121529), (5827723264000/3064869614373843)), 0, by norm_num⟩
  | 2 => ⟨((107883727/2199023255552), (-1681901201/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-247302917/562949953421312), (2269238269/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-350313045/9007199254740992), (-2665789379/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((1940785109/576460752303423488), (2703812271/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-3355736739/18446744073709551616), (-1105689503/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1184708343/147573952589676412928), (1045296421/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5795227505/18889465931478580854784), (866716771/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((192538023/18889465931478580854784), (-108715705/18889465931478580854784)), (17/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-680800219/2417851639229258349412352), (1645666955/4835703278458516698824704)), (7/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((1650282161/309485009821345068724781056), (-2443566263/154742504910672534362390528)), (45/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((124240807/4951760157141521099596496896), (6223606699/9903520314283042199192993792)), (71/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (6063/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (6063/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (6063/1280)))⁻¹=value ((2252800/31962841), (-2586880/95888523)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/31962841), (-2586880/95888523))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-654715075/147573952589676412928), (-1464518323/147573952589676412928)), (67/590295810358705651712), by norm_num⟩
  | 1 => ⟨((4404740867/590295810358705651712), (1715695833/590295810358705651712)), (61/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-215024699/73786976294838206464), (771088369/590295810358705651712)), (57/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((1449683363/4722366482869645213696), (-2031598763/2361183241434822606848)), (37/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1822036773/18889465931478580854784), (1759240269/9444732965739290427392)), (75/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-5996157729/151115727451828646838272), (-793101639/75557863725914323419136)), (71/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((3567037721/604462909807314587353088), (-2386136145/604462909807314587353088)), (15/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-639809285/4835703278458516698824704), (2671047243/2417851639229258349412352)), (189/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-266780529/2417851639229258349412352), (-1130261177/9671406556917033397649408)), (35/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((6689655867/309485009821345068724781056), (-506899771/309485009821345068724781056)), (381/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-1902726447/1237940039285380274899124224), (708164019/309485009821345068724781056)), (125/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-2113435717/19807040628566084398385987584), (-6247820713/19807040628566084398385987584)), (313/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((5796540109/158456325028528675187087900672), (1875117913/158456325028528675187087900672)), (765/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2224480025/549755813888), (-2251910751/549755813888)), (215/274877906944), by norm_num⟩
  | 1 => ⟨((-368924461/1099511627776), (-6622894565/1099511627776)), (1909/1099511627776), by norm_num⟩
  | 2 => ⟨((1007974341/549755813888), (-329467413/137438953472)), (2157/1099511627776), by norm_num⟩
  | 3 => ⟨((1020669817/1099511627776), (-974797495/4398046511104)), (3291/2199023255552), by norm_num⟩
  | 4 => ⟨((215379359/1099511627776), (741917673/8796093022208)), (15293/17592186044416), by norm_num⟩
  | 5 => ⟨((2837662453/140737488355328), (4189473873/140737488355328)), (57729/140737488355328), by norm_num⟩
  | 6 => ⟨((765184727/1125899906842624), (5459116913/1125899906842624)), (184277/1125899906842624), by norm_num⟩
  | 7 => ⟨((-518791459/4503599627370496), (5288714037/9007199254740992)), (63915/1125899906842624), by norm_num⟩
  | 8 => ⟨((-149890467/4503599627370496), (562896529/9007199254740992)), (629153/36028797018963968), by norm_num⟩
  | 9 => ⟨((-809889161/144115188075855872), (3010153043/576460752303423488)), (1394785/288230376151711744), by norm_num⟩
  | 10 => ⟨((-2988751241/4611686018427387904), (695672359/2305843009213693952)), (5640595/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4418498157/73786976294838206464), (258339309/18446744073709551616)), (21017193/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-6515088261/1180591620717411303424), (137721581/590295810358705651712)), (36382473/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2224480025/549755813888), (-2251910751/549755813888)), (431/549755813888), by norm_num⟩
  | 1 => ⟨((-368924461/1099511627776), (-6622894565/1099511627776)), (955/549755813888), by norm_num⟩
  | 2 => ⟨((1007974341/549755813888), (-329467413/137438953472)), (1079/549755813888), by norm_num⟩
  | 3 => ⟨((1020669817/1099511627776), (-974797495/4398046511104)), (6583/4398046511104), by norm_num⟩
  | 4 => ⟨((215379359/1099511627776), (741917673/8796093022208)), (7647/8796093022208), by norm_num⟩
  | 5 => ⟨((2837662453/140737488355328), (4189473873/140737488355328)), (57735/140737488355328), by norm_num⟩
  | 6 => ⟨((765184727/1125899906842624), (5459116913/1125899906842624)), (184323/1125899906842624), by norm_num⟩
  | 7 => ⟨((-518791459/4503599627370496), (5288714037/9007199254740992)), (511681/9007199254740992), by norm_num⟩
  | 8 => ⟨((-149890467/4503599627370496), (562896529/9007199254740992)), (1261189/72057594037927936), by norm_num⟩
  | 9 => ⟨((-809889161/144115188075855872), (3010153043/576460752303423488)), (2812629/576460752303423488), by norm_num⟩
  | 10 => ⟨((-2988751241/4611686018427387904), (695672359/2305843009213693952)), (5825063/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4418498157/73786976294838206464), (258339309/18446744073709551616)), (23968673/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-6515088261/1180591620717411303424), (137721581/590295810358705651712)), (119988611/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile021Gamma
