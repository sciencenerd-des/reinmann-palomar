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
namespace Reinmann.XiRectangle.Tile028Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7473/640))
  have he : value ((7/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((22016000/351685729), (-9565440/351685729)), 0, by norm_num⟩
  | 1 => ⟨((-196603306803200/123682851982261441), (210592727040000/123682851982261441)), 0, by norm_num⟩
  | 2 => ⟨((935879881/35184372088832), (-1317873541/17592186044416)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((419260605/2251799813685248), (6094596859/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1536097407/36028797018963968), (-2961012553/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((2827165429/1152921504606846976), (1148666565/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1915753057/18446744073709551616), (-535364457/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((537960025/147573952589676412928), (-297467267/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-4051754409/37778931862957161709568), (1234390115/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((2983957573/1208925819614629174706176), (-2118015525/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1145354821/38685626227668133590597632), (2770731177/19342813113834066795298816)), (9/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-158041067/154742504910672534362390528), (-23628457/4835703278458516698824704)), (53/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((1949370053/19807040628566084398385987584), (2754240693/19807040628566084398385987584)), (39/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (7473/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (7473/1280)))⁻¹=value ((22016000/351685729), (-9565440/351685729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((22016000/351685729), (-9565440/351685729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1441234743/536870912), (440094641/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((11008000/351685729), (-4782720/351685729)), 0, by norm_num⟩
  | 2 => ⟨((-49150826700800/123682851982261441), (52648181760000/123682851982261441)), 0, by norm_num⟩
  | 3 => ⟨((1247839841/281474976710656), (-3514329443/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((419260605/18014398509481984), (6094596859/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2457755851/576460752303423488), (-4737620085/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((3769553905/18446744073709551616), (382888855/2305843009213693952)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-2189432065/295147905179352825856), (-1223690187/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((537960025/2361183241434822606848), (-297467267/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-3601559475/604462909807314587353088), (548617829/151115727451828646838272)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1193583029/9671406556917033397649408), (-423603105/2417851639229258349412352)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-208246331/154742504910672534362390528), (4030154439/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-842885691/19807040628566084398385987584), (-4032589995/19807040628566084398385987584)), (9/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (159/20480)), 0, by norm_num⟩
  | 45 => ⟨((95555160977/4080638361600), (-628209/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-52113646127557/2298215525253120), (6053475781381/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((795796061/34359738368), (-170251089/17179869184)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-205323501/8589934592), (1379654513/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((6591573/268435456), (-1419696639/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-432305757/17179869184), (364710979/34359738368)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((886411541/34359738368), (-1495604269/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-3638937061/137438953472), (1533310341/137438953472)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((934467815/34359738368), (-196673795/17179869184)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-3842273687/137438953472), (1615909781/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((3952557901/137438953472), (-830407601/68719476736)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4069329871/137438953472), (1708248977/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4193218011/137438953472), (-879227509/68719476736)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4324890183/137438953472), (452925423/34359738368)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((34883565/1073741824), (-934137839/68719476736)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4614691603/137438953472), (964248267/68719476736)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((298415743/8589934592), (-1992727489/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-4946092923/137438953472), (2061382799/137438953472)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5130296021/137438953472), (-2134935937/137438953472)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5328740289/137438953472), (2213930275/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5543142475/137438953472), (-2298992553/137438953472)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-2887753327/68719476736), (2390849575/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((6028186895/137438953472), (-2490349015/137438953472)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-1575991773/34359738368), (162405351/8589934592)), (1/34359738368), by norm_num⟩
  | 21 => ⟨((1651540921/34359738368), (-679108629/34359738368)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-3469379641/68719476736), (177849629/8589934592)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3653289321/68719476736), (-1493820719/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-964440433/17179869184), (393075721/17179869184)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((510805645/8589934592), (-829741379/34359738368)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4343904087/68719476736), (1756890045/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((1158981425/17179869184), (-1866435283/68719476736)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-2484979073/34359738368), (497634039/17179869184)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5355751585/68719476736), (-2132297647/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-5806320565/68719476736), (2295774799/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1584858125/17179869184), (-621591491/17179869184)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-1744997731/17179869184), (1355709459/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((1941002487/17179869184), (-1490598785/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-2186393111/17179869184), (1655243515/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2502438511/17179869184), (-116293427/2147483648)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-5849231663/34359738368), (1062122193/17179869184)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((879202209/4294967296), (-618638059/8589934592)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4406733339/17179869184), (740707473/8589934592)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((5891831629/17179869184), (-230655269/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4430116543/8589934592), (305676587/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((2213322243/2147483648), (-906170355/4294967296)), (1/2147483648), by norm_num⟩
  | 0 => ⟨((-47287493/536870912), (7041514259/17179869184)), (3/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (7473/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (7473/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (7473/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((1441234743/536870912), (440094641/1073741824)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (7473/1280))) (z:=((-41/256), (7473/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((1441234743/536870912), (440094641/1073741824))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2170159543/67108864), (703824749/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((980650617/536870912), (454696901/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((992414539558400/123682851982261441), (-446827683330720/123682851982261441)), 0, by norm_num⟩
  | 3 => ⟨((-2408333213/35184372088832), (2715805711/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1221636053/2251799813685248), (-973810437/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((642627967/144115188075855872), (2733939999/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1054849069/2305843009213693952), (-1770651123/2305843009213693952)), (45/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1350694409/73786976294838206464), (1903310325/147573952589676412928)), (67/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5454784179/9444732965739290427392), (-537478277/4722366482869645213696)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((4725883377/302231454903657293676544), (-1077448523/302231454903657293676544)), (115/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3478039101/9671406556917033397649408), (2602783263/9671406556917033397649408)), (309/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1944367101/309485009821345068724781056), (-868034623/77371252455336267181195264)), (207/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-689204255/19807040628566084398385987584), (3694917119/9903520314283042199192993792)), (1109/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1268384183/67108864), (2031698151/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((712215161/536870912), (454696901/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((992414539558400/123682851982261441), (-446827683330720/123682851982261441)), 0, by norm_num⟩
  | 3 => ⟨((-2408333213/35184372088832), (2715805711/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1221636053/2251799813685248), (-973810437/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((642627967/144115188075855872), (2733939999/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1054849069/2305843009213693952), (-1770651123/2305843009213693952)), (45/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1350694409/73786976294838206464), (1903310325/147573952589676412928)), (67/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5454784179/9444732965739290427392), (-537478277/4722366482869645213696)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((4725883377/302231454903657293676544), (-1077448523/302231454903657293676544)), (115/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3478039101/9671406556917033397649408), (2602783263/9671406556917033397649408)), (309/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1944367101/309485009821345068724781056), (-868034623/77371252455336267181195264)), (207/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-689204255/19807040628566084398385987584), (3694917119/9903520314283042199192993792)), (1109/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((83128319/4194304), (2031698151/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((712215161/536870912), (454696901/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((992414539558400/123682851982261441), (-446827683330720/123682851982261441)), 0, by norm_num⟩
  | 3 => ⟨((-2408333213/35184372088832), (2715805711/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1221636053/2251799813685248), (-973810437/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((642627967/144115188075855872), (2733939999/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1054849069/2305843009213693952), (-1770651123/2305843009213693952)), (45/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1350694409/73786976294838206464), (1903310325/147573952589676412928)), (67/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5454784179/9444732965739290427392), (-537478277/4722366482869645213696)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((4725883377/302231454903657293676544), (-1077448523/302231454903657293676544)), (115/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3478039101/9671406556917033397649408), (2602783263/9671406556917033397649408)), (309/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1944367101/309485009821345068724781056), (-868034623/77371252455336267181195264)), (207/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-689204255/19807040628566084398385987584), (3694917119/9903520314283042199192993792)), (1109/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((393206613606400/123682851982261441), (-421185454080000/123682851982261441)), 0, by norm_num⟩
  | 1 => ⟨((-935879881/8796093022208), (1317873541/4398046511104)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-157222727/140737488355328), (-1142736911/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1536097407/4503599627370496), (2961012553/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1766978393/72057594037927936), (-717916603/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((2873629585/2305843009213693952), (803046685/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-3765720175/73786976294838206464), (520567717/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((4051754409/2361183241434822606848), (-1234390115/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1678476135/37778931862957161709568), (4765534931/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((1431693527/2417851639229258349412352), (-3463413971/1208925819614629174706176)), (7/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((217306467/9671406556917033397649408), (259913027/2417851639229258349412352)), (11/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-1462027539/618970019642690137449562112), (-4131361039/1237940039285380274899124224)), (33/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2560289039/19807040628566084398385987584), (3104363389/39614081257132168796771975168)), (25/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((935879881/8796093022208), (-1317873541/4398046511104)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((157222727/70368744177664), (1142736911/35184372088832)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-2304146111/2251799813685248), (-4441518829/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((1766978393/18014398509481984), (717916603/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-3592036981/576460752303423488), (-250952089/144115188075855872)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((2824290131/9223372036854775808), (-97606447/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-886321277/73786976294838206464), (2160182701/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1678476135/4722366482869645213696), (-2382767465/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-805327609/151115727451828646838272), (3896340717/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-543266167/2417851639229258349412352), (-1299565135/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1005143933/38685626227668133590597632), (1420155357/38685626227668133590597632)), (17/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-1920216779/1237940039285380274899124224), (-1164136271/1237940039285380274899124224)), (13/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((5669861803/79228162514264337593543950336), (192722597/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-419260605/281474976710656), (-6094596859/281474976710656)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((1536097407/1125899906842624), (2961012553/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1766978393/9007199254740992), (-717916603/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2394691321/144115188075855872), (669205571/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-2353575109/2305843009213693952), (650709647/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((3545285107/73786976294838206464), (-2160182701/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-1958222157/1180591620717411303424), (173743461/73786976294838206464)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1073770145/37778931862957161709568), (-1298780239/9444732965739290427392)), (15/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((814899251/604462909807314587353088), (3898695405/604462909807314587353088)), (7/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-104702493/604462909807314587353088), (-4733851191/19342813113834066795298816)), (23/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((880099357/77371252455336267181195264), (1067124915/154742504910672534362390528)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5669861803/9903520314283042199192993792), (-192722597/2475880078570760549798248448)), (33/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((1879541481/79228162514264337593543950336), (-33110883/4951760157141521099596496896)), (27/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1536097407/2251799813685248), (-2961012553/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1766978393/9007199254740992), (717916603/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-3592036981/144115188075855872), (-250952089/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((2353575109/1152921504606846976), (-325354823/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-276975399/2305843009213693952), (337528547/4611686018427387904)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((734333309/147573952589676412928), (-521230383/73786976294838206464)), (3/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-939548877/9444732965739290427392), (1136432709/2361183241434822606848)), (13/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-814899251/151115727451828646838272), (-974673851/37778931862957161709568)), (7/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((942322437/1208925819614629174706176), (2662791295/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-4400496785/77371252455336267181195264), (-2667812287/77371252455336267181195264)), (23/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((3898029989/1237940039285380274899124224), (264993571/618970019642690137449562112)), (21/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-1409656111/9903520314283042199192993792), (1589322385/39614081257132168796771975168)), (9/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((3304082901/633825300114114700748351602688), (-1348574413/316912650057057350374175801344)), (31/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2827165429/36028797018963968), (-1148666565/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((2873629585/144115188075855872), (803046685/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-5648580261/2305843009213693952), (97606447/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((3545285107/18446744073709551616), (-2160182701/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-734333309/73786976294838206464), (521230383/36893488147419103232)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((1127458653/4722366482869645213696), (-5454877003/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((1140858951/75557863725914323419136), (2729086783/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-3015431799/1208925819614629174706176), (-4260466071/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((1980223553/9671406556917033397649408), (1200515529/9671406556917033397649408)), (23/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-3898029989/309485009821345068724781056), (-264993571/154742504910672534362390528)), (11/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((775310861/1237940039285380274899124224), (-1748254623/9903520314283042199192993792)), (39/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-3964899481/158456325028528675187087900672), (3236578591/158456325028528675187087900672)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((907669081/1267650600228229401496703205376), (-3518487723/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1915753057/288230376151711744), (-535364457/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((7531440349/4611686018427387904), (-520567717/2305843009213693952)), (17/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-3545285107/18446744073709551616), (2160182701/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 3 => ⟨((1958222157/147573952589676412928), (-173743461/9223372036854775808)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-939548877/2361183241434822606848), (1136432709/590295810358705651712)), (17/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-1140858951/37778931862957161709568), (-2729086783/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((3518003765/604462909807314587353088), (2485271875/302231454903657293676544)), (27/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-2640298071/4835703278458516698824704), (-400171843/1208925819614629174706176)), (31/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((730880623/19342813113834066795298816), (99372589/19342813113834066795298816)), (35/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-5168739073/2475880078570760549798248448), (364219713/618970019642690137449562112)), (9/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((3634491191/39614081257132168796771975168), (-741715927/9903520314283042199192993792)), (35/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-907669081/316912650057057350374175801344), (3518487723/633825300114114700748351602688)), (33/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((430652795/20282409603651670423947251286016), (-1617822837/5070602400912917605986812821504)), (15/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-537960025/1152921504606846976), (297467267/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 1 => ⟨((4051754409/36893488147419103232), (-2468780229/36893488147419103232)), (15/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3356952269/295147905179352825856), (2382767465/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 3 => ⟨((1073770145/2361183241434822606848), (-1298780239/590295810358705651712)), (23/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((814899251/18889465931478580854784), (974673851/4722366482869645213696)), (19/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-3015431799/302231454903657293676544), (-4260466071/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((2640298071/2417851639229258349412352), (400171843/604462909807314587353088)), (35/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-1670584281/19342813113834066795298816), (-908549385/77371252455336267181195264)), (43/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((6645521665/1237940039285380274899124224), (-936564977/618970019642690137449562112)), (49/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-162254071/618970019642690137449562112), (2119188363/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((1426337127/158456325028528675187087900672), (-691131517/39614081257132168796771975168)), (7/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-46141371/633825300114114700748351602688), (1386705289/1267650600228229401496703205376)), (55/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-1618279965/81129638414606681695789005144064), (-1131381601/20282409603651670423947251286016)), (53/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4051754409/147573952589676412928), (1234390115/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((1678476135/295147905179352825856), (-2382767465/295147905179352825856)), (25/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-805327609/2361183241434822606848), (3896340717/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-814899251/18889465931478580854784), (-974673851/4722366482869645213696)), (23/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((942322437/75557863725914323419136), (1331395647/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-1980223553/1208925819614629174706176), (-1200515529/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((730880623/4835703278458516698824704), (99372589/4835703278458516698824704)), (43/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-6645521665/618970019642690137449562112), (936564977/309485009821345068724781056)), (55/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((1460286639/2475880078570760549798248448), (-2384086909/4951760157141521099596496896)), (17/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-27858147/1237940039285380274899124224), (3455657585/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((63444385/316912650057057350374175801344), (-7626879089/2535301200456458802993406410752)), (83/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((606854987/10141204801825835211973625643008), (3394144803/20282409603651670423947251286016)), (11/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-2243955227/324518553658426726783156020576256), (-1196443621/162259276829213363391578010288128)), (11/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2983957573/2361183241434822606848), (2118015525/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 1 => ⟨((178961691/1180591620717411303424), (-6926827941/9444732965739290427392)), (5/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((543266167/18889465931478580854784), (5198260539/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-104702493/9444732965739290427392), (-2366925595/151115727451828646838272)), (11/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((275031049/151115727451828646838272), (1333906143/1208925819614629174706176)), (43/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-3898029989/19342813113834066795298816), (-529987141/19342813113834066795298816)), (9/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((5168739073/309485009821345068724781056), (-1456878853/309485009821345068724781056)), (51/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-162254071/154742504910672534362390528), (2119188363/2475880078570760549798248448)), (35/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((27858147/618970019642690137449562112), (-1727828793/19807040628566084398385987584)), (11/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-70493761/158456325028528675187087900672), (4237155049/633825300114114700748351602688)), (53/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-741711651/5070602400912917605986812821504), (-1037099801/2535301200456458802993406410752)), (15/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((2991940303/162259276829213363391578010288128), (1595258161/81129638414606681695789005144064)), (65/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-3837089171/2596148429267413814265248164610048), (-1656946809/2596148429267413814265248164610048)), (17/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1145354821/37778931862957161709568), (2770731177/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-869225867/75557863725914323419136), (-259913027/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((1005143933/151115727451828646838272), (1420155357/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-880099357/604462909807314587353088), (-2134249829/2417851639229258349412352)), (21/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((3898029989/19342813113834066795298816), (529987141/19342813113834066795298816)), (11/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-6202486887/309485009821345068724781056), (54632957/9671406556917033397649408)), (19/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((1817245595/1237940039285380274899124224), (-2966863709/2475880078570760549798248448)), (59/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-2852674253/39614081257132168796771975168), (691131517/4951760157141521099596496896)), (21/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((507555079/633825300114114700748351602688), (-3813439545/316912650057057350374175801344)), (55/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((741711651/2535301200456458802993406410752), (1037099801/1267650600228229401496703205376)), (69/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-1645567167/40564819207303340847894502572032), (-1754783977/40564819207303340847894502572032)), (41/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((4604507005/1298074214633706907132624082305024), (1988336171/1298074214633706907132624082305024)), (23/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-2510410845/10384593717069655257060992658440192), (5607639/10384593717069655257060992658440192)), (25/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504000/1055057187), (-797120/351685729)), 0, by norm_num⟩
  | 1 => ⟨((-49150826700800/371048555946784323), (17549393920000/123682851982261441)), 0, by norm_num⟩
  | 2 => ⟨((1247839841/562949953421312), (-3514329443/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((139753535/9007199254740992), (4063064573/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-512032469/144115188075855872), (-3948016737/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((3769553905/18446744073709551616), (382888855/2305843009213693952)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-5108674819/590295810358705651712), (-178454819/73786976294838206464)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((5738240267/18889465931478580854784), (-793246045/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1350584803/151115727451828646838272), (1645853487/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((1989305049/9671406556917033397649408), (-706005175/2417851639229258349412352)), (17/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-763569881/309485009821345068724781056), (923577059/77371252455336267181195264)), (25/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-842885691/9903520314283042199192993792), (-4032589995/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2599160071/316912650057057350374175801344), (918080231/79228162514264337593543950336)), (53/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((332600799/16777216), (2031393937/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((5697152357/4294967296), (56875201/268435456)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4412385171/549755813888), (-497382191/137438953472)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2407787301/35184372088832), (340467673/4398046511104)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((606817773/1125899906842624), (-488832961/281474976710656)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((672077607/144115188075855872), (5491810551/144115188075855872)), (29/144115188075855872), by norm_num⟩
  | 6 => ⟨((-537402415/1152921504606846976), (-444056959/576460752303423488)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((686554705/36893488147419103232), (948556545/73786976294838206464)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-5539195729/9444732965739290427392), (-1023523633/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((598506145/37778931862957161709568), (-582849585/151115727451828646838272)), (231/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-875475165/2417851639229258349412352), (2718230395/9671406556917033397649408)), (311/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1918026923/309485009821345068724781056), (-3598156929/309485009821345068724781056)), (13/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-526756751/19807040628566084398385987584), (952419287/2475880078570760549798248448)), (1113/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-332757291/1125899906842624), (468577259/562949953421312)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((-27950707/4503599627370496), (-1625225829/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((1638503901/576460752303423488), (1579206695/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-2513035937/9223372036854775808), (-2042073893/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5108674817/295147905179352825856), (1427638551/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-2008384093/2361183241434822606848), (69409029/590295810358705651712)), (7/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((5042183265/151115727451828646838272), (-3072259841/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-2387166059/2417851639229258349412352), (3388824839/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((572677411/38685626227668133590597632), (-5541462353/77371252455336267181195264)), (9/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((772645215/1237940039285380274899124224), (924135207/309485009821345068724781056)), (15/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-714769019/9903520314283042199192993792), (-4039553015/39614081257132168796771975168)), (25/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((2730974975/633825300114114700748351602688), (827830237/316912650057057350374175801344)), (5/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-4031901727/20282409603651670423947251286016), (-34261795/1267650600228229401496703205376)), (15/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((166300397/8388608), (2031394049/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((2848576165/2147483648), (910002829/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((2206193367/274877906944), (-248690719/68719476736)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2407796887/35184372088832), (1361866797/17592186044416)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((606837261/1125899906842624), (-977663199/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((671955025/144115188075855872), (5491827497/144115188075855872)), (15/72057594037927936), by norm_num⟩
  | 6 => ⟨((-2149455785/4611686018427387904), (-1776274715/2305843009213693952)), (47/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2746073119/147573952589676412928), (1897319927/147573952589676412928)), (69/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5539055915/9444732965739290427392), (-1024200081/9444732965739290427392)), (89/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2394118897/151115727451828646838272), (-582398347/151115727451828646838272)), (29/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-3502598677/9671406556917033397649408), (169827761/604462909807314587353088)), (39/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((1919360407/309485009821345068724781056), (-3597348501/309485009821345068724781056)), (417/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-530694155/19807040628566084398385987584), (7618818955/19807040628566084398385987584)), (557/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2496767849/4611686018427387904), (-1203205101/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 1 => ⟨((2872041071/18446744073709551616), (2333798735/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2919242753/147573952589676412928), (-1631586915/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 3 => ⟨((3825493511/2361183241434822606848), (-66103837/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-1800779737/18889465931478580854784), (2194471315/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((1193583029/302231454903657293676544), (-3388824839/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-763569881/9671406556917033397649408), (3694308235/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-10347927/2417851639229258349412352), (-6336927133/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((3063295795/4951760157141521099596496896), (2164046259/2475880078570760549798248448)), (3/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-223517297/4951760157141521099596496896), (-2168126811/79228162514264337593543950336)), (19/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((6335845569/2535301200456458802993406410752), (430719709/1267650600228229401496703205376)), (35/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-4582501135/40564819207303340847894502572032), (322909945/10141204801825835211973625643008)), (31/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((2685222929/649037107316853453566312041152512), (-1095984285/324518553658426726783156020576256)), (13/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((166300397/8388608), (2031394049/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((5697152331/4294967296), (455001415/2147483648)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4412386723/549755813888), (-1989525755/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-1203898415/17592186044416), (1361866793/17592186044416)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((1213674307/2251799813685248), (-3910652665/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((335977797/72057594037927936), (5491826689/144115188075855872)), (31/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2149456149/4611686018427387904), (-888136917/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((2746072487/147573952589676412928), (1897316905/147573952589676412928)), (35/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-692381259/1180591620717411303424), (-512095913/4722366482869645213696)), (179/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((598528019/37778931862957161709568), (-1164804965/302231454903657293676544)), (233/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-875643627/2417851639229258349412352), (1358623731/4835703278458516698824704)), (313/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1919325445/309485009821345068724781056), (-3597338647/309485009821345068724781056)), (209/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-33163263/1237940039285380274899124224), (7618752061/19807040628566084398385987584)), (1115/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2335394203/590295810358705651712), (1305269533/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-4590592213/4722366482869645213696), (158649209/1180591620717411303424)), (11/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((4321871369/37778931862957161709568), (-1316682789/18889465931478580854784)), (1/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-1193583029/151115727451828646838272), (3388824839/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((1145354821/4835703278458516698824704), (-346341397/302231454903657293676544)), (11/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((347690347/19342813113834066795298816), (3326886745/38685626227668133590597632)), (27/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-2144307057/618970019642690137449562112), (-1514832381/309485009821345068724781056)), (17/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((3218649077/9903520314283042199192993792), (975657065/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-3563913133/158456325028528675187087900672), (-60569959/19807040628566084398385987584)), (11/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((1575234765/1267650600228229401496703205376), (-222000587/633825300114114700748351602688)), (45/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-4430617833/81129638414606681695789005144064), (3616748139/81129638414606681695789005144064)), (11/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((138311479/81129638414606681695789005144064), (-4289204081/1298074214633706907132624082305024)), (41/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-65623283/5192296858534827628530496329220096), (3944406155/20769187434139310514121985316880384)), (37/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((166300397/8388608), (2031394049/134217728)), (5/67108864), by norm_num⟩
  | 1 => ⟨((5697152331/4294967296), (455001415/2147483648)), (1/536870912), by norm_num⟩
  | 2 => ⟨((4412386723/549755813888), (-1989525755/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-1203898415/17592186044416), (1361866793/17592186044416)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((303418577/562949953421312), (-977663167/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((671955597/144115188075855872), (5491826701/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2149456165/4611686018427387904), (-3552547691/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2746072535/147573952589676412928), (948658467/73786976294838206464)), (71/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1384762571/2361183241434822606848), (-1024191855/9444732965739290427392)), (45/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((299264033/18889465931478580854784), (-1164805071/302231454903657293676544)), (117/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-875643759/2417851639229258349412352), (2717247893/9671406556917033397649408)), (157/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((1919325973/309485009821345068724781056), (-1798669835/154742504910672534362390528)), (419/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-265306229/9903520314283042199192993792), (7618755823/19807040628566084398385987584)), (279/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3492421309/151115727451828646838272), (2127972185/151115727451828646838272)), (15/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((2893534617/604462909807314587353088), (-513458309/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-1388308875/4835703278458516698824704), (209903877/151115727451828646838272)), (9/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-1404809483/38685626227668133590597632), (-6720983323/38685626227668133590597632)), (41/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((1624475043/154742504910672534362390528), (4590401153/309485009821345068724781056)), (37/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-1706859359/1237940039285380274899124224), (-258696949/309485009821345068724781056)), (29/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((2519938579/19807040628566084398385987584), (171308975/9903520314283042199192993792)), (19/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-2864063209/316912650057057350374175801344), (1614549725/633825300114114700748351602688)), (49/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((157337281/316912650057057350374175801344), (-1027485267/2535301200456458802993406410752)), (31/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-768397105/40564819207303340847894502572032), (2978613945/81129638414606681695789005144064)), (35/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((218744277/1298074214633706907132624082305024), (-6574010259/2596148429267413814265248164610048)), (73/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((2092321571/41538374868278621028243970633760768), (2925592827/20769187434139310514121985316880384)), (77/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((-967091815/166153499473114484112975882535043072), (-4125112013/664613997892457936451903530140172288)), (77/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((166300397/8388608), (2031394049/134217728)), (11/134217728), by norm_num⟩
  | 1 => ⟨((5697152331/4294967296), (455001415/2147483648)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((4412386723/549755813888), (-1989525755/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-1203898415/17592186044416), (1361866793/17592186044416)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((303418577/562949953421312), (-977663167/562949953421312)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((671955597/144115188075855872), (5491826701/144115188075855872)), (33/144115188075855872), by norm_num⟩
  | 6 => ⟨((-537364041/1152921504606846976), (-3552547691/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1373036267/73786976294838206464), (948658467/73786976294838206464)), (9/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-5539050279/9444732965739290427392), (-1024191859/9444732965739290427392)), (181/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2394112261/151115727451828646838272), (-291201265/75557863725914323419136)), (235/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1751287517/4835703278458516698824704), (2717247869/9671406556917033397649408)), (315/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1919325989/309485009821345068724781056), (-1798669813/154742504910672534362390528)), (105/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-530612573/19807040628566084398385987584), (1904688925/4951760157141521099596496896)), (1117/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((562239667/9671406556917033397649408), (-1360115613/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((853383167/38685626227668133590597632), (4082812727/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-1973647921/154742504910672534362390528), (-2788542591/154742504910672534362390528)), (1/4835703278458516698824704), by norm_num⟩
  | 3 => ⟨((432029237/154742504910672534362390528), (1047675263/618970019642690137449562112)), (21/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-956745911/2475880078570760549798248448), (-65040935/1237940039285380274899124224)), (11/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((6089439007/158456325028528675187087900672), (-858195277/79228162514264337593543950336)), (19/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((-111507755/39614081257132168796771975168), (728197251/316912650057057350374175801344)), (59/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((1400340395/10141204801825835211973625643008), (-5428278425/20282409603651670423947251286016)), (21/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((-498304269/324518553658426726783156020576256), (7487869927/324518553658426726783156020576256)), (109/324518553658426726783156020576256), by norm_num⟩
  | 9 => ⟨((-1456386105/2596148429267413814265248164610048), (-4072789575/2596148429267413814265248164610048)), (69/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((3231149401/41538374868278621028243970633760768), (3445601803/41538374868278621028243970633760768)), (41/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-70634129/10384593717069655257060992658440192), (-976048161/332306998946228968225951765070086144)), (91/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((2464655549/5316911983139663491615228241121378304), (-5505433/5316911983139663491615228241121378304)), (99/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((166300397/8388608), (2031394049/134217728)), (3/33554432), by norm_num⟩
  | 1 => ⟨((5697152331/4294967296), (455001415/2147483648)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((4412386723/549755813888), (-1989525755/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-1203898415/17592186044416), (1361866793/17592186044416)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((303418577/562949953421312), (-977663167/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((671955597/144115188075855872), (5491826701/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 6 => ⟨((-537364041/1152921504606846976), (-3552547691/4611686018427387904)), (51/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1373036267/73786976294838206464), (948658467/73786976294838206464)), (73/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5539050279/9444732965739290427392), (-1024191859/9444732965739290427392)), (91/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2394112261/151115727451828646838272), (-291201265/75557863725914323419136)), (59/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-3502575033/9671406556917033397649408), (1358623935/4835703278458516698824704)), (79/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((1919325987/309485009821345068724781056), (-3597339627/309485009821345068724781056)), (421/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-132653141/4951760157141521099596496896), (1904688925/4951760157141521099596496896)), (559/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22419463709833/65536), (462784396275653/2097152)), (224090383/2097152), by norm_num⟩
  | 1 => ⟨((-4004265637/8), (1761876323/8)), (1327/8), by norm_num⟩
  | 2 => ⟨((-5715998303/16), (1536815433/16)), (519/4), by norm_num⟩
  | 3 => ⟨(-166884812, (626659023/32)), (2183/32), by norm_num⟩
  | 4 => ⟨((-7376134213/128), (-86617843/64)), (217/8), by norm_num⟩
  | 5 => ⟨((-4026278441/256), (-644168503/256)), (2229/256), by norm_num⟩
  | 6 => ⟨((-3624004327/1024), (-269436283/256)), (301/128), by norm_num⟩
  | 7 => ⟨((-1383936903/2048), (-2439416767/8192)), (1125/2048), by norm_num⟩
  | 8 => ⟨((-3661927109/32768), (-2179976729/32768)), (3713/32768), by norm_num⟩
  | 9 => ⟨((-2129559645/131072), (-3271738199/262144)), (687/32768), by norm_num⟩
  | 10 => ⟨((-1100446743/524288), (-1066036713/524288)), (1847/524288), by norm_num⟩
  | 11 => ⟨((-254469809/1048576), (-19264303/65536)), (1139/2097152), by norm_num⟩
  | 12 => ⟨((-845746633/33554432), (-5139174697/134217728)), (10395/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402449864935119/2535301200456458802993406410752), (1673005672891/5070602400912917605986812821504)), (116463/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1813129924034093/633825300114114700748351602688), (4102945458495/633825300114114700748351602688)), (71697/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1928437781746945/39614081257132168796771975168), (578456526965/4951760157141521099596496896)), (80901/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1930668815761065/2475880078570760549798248448), (4927059181689/2475880078570760549798248448)), (86159/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1812377130196265/154742504910672534362390528), (4938452202937/154742504910672534362390528)), (172769/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1588210496356307/9671406556917033397649408), (4641939178299/9671406556917033397649408)), (40613/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((646329251180373/302231454903657293676544), (4073878796423/604462909807314587353088)), (35657/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((485728717086507/18889465931478580854784), (6642983538559/75557863725914323419136)), (232679/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1338955607968901/4722366482869645213696), (1250597865071/1180591620717411303424)), (43827/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((209814505354103/73786976294838206464), (6911207106899/590295810358705651712)), (121177/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1894991314167487/73786976294838206464), (8688684503913/73786976294838206464)), (304915/73786976294838206464), by norm_num⟩
  | 7 => ⟨((475841070492819/2305843009213693952), (76902816653/72057594037927936)), (345763/9223372036854775808), by norm_num⟩
  | 6 => ⟨((104683026316865/72057594037927936), (9930284156937/1152921504606846976)), (174607/576460752303423488), by norm_num⟩
  | 5 => ⟨((632881510875185/72057594037927936), (4393791808909/72057594037927936)), (154745/72057594037927936), by norm_num⟩
  | 4 => ⟨((1599131955683517/36028797018963968), (1672640813753/4503599627370496)), (472205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1624901840125611/9007199254740992), (4270465092763/2251799813685248)), (302235/4503599627370496), by norm_num⟩
  | 2 => ⟨((625780174581501/1125899906842624), (17627017993053/2251799813685248)), (156583/562949953421312), by norm_num⟩
  | 1 => ⟨((1319386977332495/1125899906842624), (108774532715/4398046511104)), (996093/1125899906842624), by norm_num⟩
  | 0 => ⟨((191684221537255/140737488355328), (15395086223215/281474976710656)), (34853/17592186044416), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((191684221537255/140737488355328), (15395086223215/281474976710656)), (132953643865936989/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1042610296519467/562949953421312), (1310505090311/8796093022208)), (1543/274877906944), by norm_num⟩
  | 2 => ⟨((959234170651407/281474976710656), (155335567433147/281474976710656)), (790425/35184372088832), by norm_num⟩
  | 3 => ⟨((1591617603287991/140737488355328), (529365650690041/140737488355328)), (12519533/70368744177664), by norm_num⟩
  | 4 => ⟨((500270625584269/4398046511104), (748332674240145/8796093022208)), (47168883/8796093022208), by norm_num⟩
  | 5 => ⟨((391758629052049/68719476736), (665012676192707/34359738368)), (146535995/68719476736), by norm_num⟩
  | 6 => ⟨((-22419463709833/65536), (462784396275653/2097152)), (224090383/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((166300397/8388608), (2031394049/134217728)), (3/33554432), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2355200/59231329), (-9565440/59231329)), 0, by norm_num⟩
  | 1 => ⟨((42975337676800/3508350335106241), (22528524288000/3508350335106241)), 0, by norm_num⟩
  | 2 => ⟨((-1675746099/2199023255552), (59197217/68719476736)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-1914284309/35184372088832), (-691888237/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((4184459083/562949953421312), (-398195725/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((726700727/9007199254740992), (1478187821/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1967526111/36028797018963968), (-235500359/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((930126967/576460752303423488), (-2467019103/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((2891373675/9223372036854775808), (1986434859/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-3486112795/147573952589676412928), (3103602153/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1450369437/1180591620717411303424), (-5491121979/2361183241434822606848)), (7/590295810358705651712), by norm_num⟩
  | 11 => ⟨((4008474503/18889465931478580854784), (-1000426863/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((17391335/302231454903657293676544), (5496959583/302231454903657293676544)), (19/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (7473/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (7473/1280)))⁻¹=value ((2355200/59231329), (-9565440/59231329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2355200/59231329), (-9565440/59231329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/21860043), (-3188480/21860043)), 0, by norm_num⟩
  | 1 => ⟨((1399051878400/159287159987283), (4244504576000/477861479961849)), 0, by norm_num⟩
  | 2 => ⟨((-125785975/137438953472), (813866869/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((15396567/17592186044416), (-5489816557/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((3187951031/562949953421312), (1373173947/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-3155396567/9007199254740992), (3050954271/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1011423951/72057594037927936), (-5168278643/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((3508093413/1152921504606846976), (157438831/2305843009213693952)), (19/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1800900111/18446744073709551616), (2027570467/9223372036854775808)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-3854476421/295147905179352825856), (-1019242057/73786976294838206464)), (29/295147905179352825856), by norm_num⟩
  | 10 => ⟨((3317543459/2361183241434822606848), (-627872587/1180591620717411303424)), (25/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-150922111/37778931862957161709568), (2241453769/18889465931478580854784)), (21/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-2578723841/302231454903657293676544), (-2360053417/604462909807314587353088)), (35/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (7473/1280)))⁻¹=value ((1331200/21860043), (-3188480/21860043)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((1331200/21860043), (-3188480/21860043))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27363971891200/1294799398887147), (-20243021824000/1294799398887147)), 0, by norm_num⟩
  | 1 => ⟨((3811168377/1099511627776), (-676444213/274877906944)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((673659003/4398046511104), (1080444075/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-7780309773/140737488355328), (-22644669/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((996508051/562949953421312), (-185372303/35184372088832)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((242631081/562949953421312), (715449253/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-2923628271/72057594037927936), (2113138605/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-205979935/144115188075855872), (-5012757621/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((7583647461/18446744073709551616), (-41135609/9223372036854775808)), (25/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-194859323/18446744073709551616), (5142086267/147573952589676412928)), (3/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-3109141167/1180591620717411303424), (-1058844201/590295810358705651712)), (21/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((2041967779/9444732965739290427392), (-3241880633/18889465931478580854784)), (9/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1298057589/151115727451828646838272), (1669246573/75557863725914323419136)), (31/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((55/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/75205729), (-9565440/75205729)), 0, by norm_num⟩
  | 1 => ⟨((29889109196800/5655901674421441), (53872558080000/5655901674421441)), 0, by norm_num⟩
  | 2 => ⟨((-3534361613/4398046511104), (-181024679/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1104773013/35184372088832), (-1771033079/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((570096411/281474976710656), (1092581565/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-5813091773/18014398509481984), (-18620825/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((59153065/4503599627370496), (-1434114701/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((1784446423/2305843009213693952), (3644432035/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-4777359259/36893488147419103232), (-183838443/18446744073709551616)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((101132849/18446744073709551616), (-4640794015/590295810358705651712)), (39/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1391631753/4722366482869645213696), (3036636651/4722366482869645213696)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-3923577229/75557863725914323419136), (-403242427/75557863725914323419136)), (53/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((2760936279/1208925819614629174706176), (-937686043/302231454903657293676544)), (87/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (7473/1280)))⁻¹=value ((5632000/75205729), (-9565440/75205729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5632000/75205729), (-9565440/75205729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3926541385/1099511627776), (1668183111/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-142410217/8796093022208), (-1999092099/2199023255552)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((2328897181/17592186044416), (442642073/8796093022208)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-1742195129/140737488355328), (1902461061/140737488355328)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((-525625079/562949953421312), (-1076983833/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((4130947977/18014398509481984), (-338123859/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1931510559/288230376151711744), (6526326451/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-2131854841/1152921504606846976), (-3269261019/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((3497933971/18446744073709551616), (-1080312649/9223372036854775808)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1177426419/295147905179352825856), (3010185939/147573952589676412928)), (31/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-2210002479/1180591620717411303424), (-182664163/590295810358705651712)), (29/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1589251153/18889465931478580854784), (-349009063/2361183241434822606848)), (27/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((91641767/9444732965739290427392), (3459663479/302231454903657293676544)), (23/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((71/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/88108129), (-9565440/88108129)), 0, by norm_num⟩
  | 1 => ⟨((19319463116800/7763042395880641), (69544574976000/7763042395880641)), 0, by norm_num⟩
  | 2 => ⟨((-5180563349/8796093022208), (-2062862205/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((5211501193/140737488355328), (-784411947/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-357593185/1125899906842624), (6597553009/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-2628988137/18014398509481984), (-2488211807/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((1948271361/144115188075855872), (-640770221/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1007860471/2305843009213693952), (3807212969/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-987993727/36893488147419103232), (-4263962423/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((312984151/73786976294838206464), (1098606733/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-4259945307/18889465931478580854784), (453011407/2361183241434822606848)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-167726685/151115727451828646838272), (-6092227363/302231454903657293676544)), (9/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1378163767/1208925819614629174706176), (1865170499/2417851639229258349412352)), (7/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (7473/1280)))⁻¹=value ((7270400/88108129), (-9565440/88108129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7270400/88108129), (-9565440/88108129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1143197221/8796093022208), (1127874467/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-2155207311/17592186044416), (-1785133121/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((3792843945/140737488355328), (-1784987951/140737488355328)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((25493487/1125899906842624), (1251312797/281474976710656)), (7/1125899906842624), by norm_num⟩
  | 4 => ⟨((-4746717207/9007199254740992), (-2149876283/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 5 => ⟨((3716995787/72057594037927936), (-814301809/18014398509481984)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((1285908095/576460752303423488), (261605475/36028797018963968)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-7311235249/9223372036854775808), (-218450547/2305843009213693952)), (27/9223372036854775808), by norm_num⟩
  | 8 => ⟨((3008937105/73786976294838206464), (-1279679635/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 9 => ⟨((170700913/36893488147419103232), (1867044381/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-852785705/1180591620717411303424), (1585371409/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((54714191/4722366482869645213696), (-5097637187/75557863725914323419136)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1579954021/302231454903657293676544), (1996945089/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((87/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2969600/34762443), (-3188480/34762443)), 0, by norm_num⟩
  | 1 => ⟨((74882252800/134269715925361), (9468510208000/1208427443328249)), 0, by norm_num⟩
  | 2 => ⟨((-421288903/1099511627776), (-2718826827/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((4298294265/140737488355328), (-614995163/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-2486203831/2251799813685248), (1787137335/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-461817071/18014398509481984), (-2133495307/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((1881114993/288230376151711744), (1119169483/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-4213562825/9223372036854775808), (1230943101/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1976330307/147573952589676412928), (-983260551/36893488147419103232)), (25/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1535338797/2361183241434822606848), (4138040997/2361183241434822606848)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-2042825707/18889465931478580854784), (-1701360171/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((2020284169/302231454903657293676544), (-917617747/302231454903657293676544)), (37/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-707345001/4835703278458516698824704), (527384875/1208925819614629174706176)), (53/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (7473/1280)))⁻¹=value ((2969600/34762443), (-3188480/34762443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((2969600/34762443), (-3188480/34762443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2529162235/70368744177664), (980506781/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-6717112735/281474976710656), (258410037/140737488355328)), (7/281474976710656), by norm_num⟩
  | 2 => ⟨((291885351/140737488355328), (-665434803/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((605671473/1125899906842624), (3038830341/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2176736931/18014398509481984), (857375323/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 5 => ⟨((1248105891/288230376151711744), (-545864907/36028797018963968)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((3150765133/2305843009213693952), (2908574607/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((-888292477/4611686018427387904), (1354023439/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((584865839/295147905179352825856), (-3192797511/147573952589676412928)), (37/295147905179352825856), by norm_num⟩
  | 9 => ⟨((555775189/295147905179352825856), (166902991/147573952589676412928)), (19/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1686899669/9444732965739290427392), (17508823/147573952589676412928)), (19/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-909944009/302231454903657293676544), (-6070266567/302231454903657293676544)), (9/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((4350439429/2417851639229258349412352), (631701855/1208925819614629174706176)), (17/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((103/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10547200/123743329), (-9565440/123743329)), 0, by norm_num⟩
  | 1 => ⟨((-9872892723200/15312411472002241), (100888608768000/15312411472002241)), 0, by norm_num⟩
  | 2 => ⟨((-1998266811/8796093022208), (-2689069657/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((6051009559/281474976710656), (1195746619/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1216373459/1125899906842624), (2926625007/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((188477883/9007199254740992), (-5004441969/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((2066624729/1152921504606846976), (4344854267/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-2048031119/9223372036854775808), (-210580015/2305843009213693952)), (17/18446744073709551616), by norm_num⟩
  | 8 => ⟨((3834796565/295147905179352825856), (-346077667/73786976294838206464)), (23/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-879395307/2361183241434822606848), (3315386347/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-850975187/75557863725914323419136), (-6696655005/151115727451828646838272)), (41/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((165680169/75557863725914323419136), (1756896503/1208925819614629174706176)), (55/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-1447023561/9671406556917033397649408), (882668435/38685626227668133590597632)), (9/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (7473/1280)))⁻¹=value ((10547200/123743329), (-9565440/123743329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10547200/123743329), (-9565440/123743329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4149976929/562949953421312), (555144427/281474976710656)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((-2569863933/1125899906842624), (77478543/35184372088832)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((-12424031/70368744177664), (-1678470001/2251799813685248)), (7/4503599627370496), by norm_num⟩
  | 3 => ⟨((4840267111/36028797018963968), (1472553323/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 4 => ⟨((-1135967987/72057594037927936), (2135704209/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 5 => ⟨((-1621024373/2305843009213693952), (-6610794799/2305843009213693952)), (13/1152921504606846976), by norm_num⟩
  | 6 => ⟨((6543852431/18446744073709551616), (1787483511/18446744073709551616)), (33/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1092307077/36893488147419103232), (1107063/36028797018963968)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1687492321/1180591620717411303424), (-1313726039/295147905179352825856)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((2270874331/4722366482869645213696), (402749669/4722366482869645213696)), (43/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-563702591/18889465931478580854784), (2936968869/75557863725914323419136)), (11/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1232956313/604462909807314587353088), (-324078891/75557863725914323419136)), (85/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((2158948799/4835703278458516698824704), (45480643/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((119/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12185600/146476129), (-9565440/146476129)), 0, by norm_num⟩
  | 1 => ⟨((-28495602483200/21455256366824641), (116560625664000/21455256366824641)), 0, by norm_num⟩
  | 2 => ⟨((-2148774199/17592186044416), (-4738373745/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1952775053/140737488355328), (1015481681/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-3660311343/4503599627370496), (344350937/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((64883189/2251799813685248), (-2370610659/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 6 => ⟨((-143344301/1152921504606846976), (5324845611/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-2591058019/36893488147419103232), (-923409729/9223372036854775808)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((3654104105/590295810358705651712), (1104594803/590295810358705651712)), (13/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-3009002855/9444732965739290427392), (2347736881/18889465931478580854784)), (31/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((2778657489/302231454903657293676544), (-4706484567/302231454903657293676544)), (75/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((152379601/1208925819614629174706176), (572997255/604462909807314587353088)), (91/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-1400231279/38685626227668133590597632), (-683090295/19342813113834066795298816)), (109/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (7473/1280)))⁻¹=value ((12185600/146476129), (-9565440/146476129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12185600/146476129), (-9565440/146476129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3341997673/4503599627370496), (-1429137683/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-1199523793/18014398509481984), (1664888963/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-2618060705/36028797018963968), (-612776509/9007199254740992)), (11/36028797018963968), by norm_num⟩
  | 3 => ⟨((2751068155/144115188075855872), (-44278019/9007199254740992)), (21/288230376151711744), by norm_num⟩
  | 4 => ⟨((-140837629/144115188075855872), (3562678911/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 5 => ⟨((-1410979107/4611686018427387904), (-814067533/2305843009213693952)), (23/9223372036854775808), by norm_num⟩
  | 6 => ⟨((4434135341/73786976294838206464), (-768096087/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-48260693/18446744073709551616), (4064108707/590295810358705651712)), (9/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1240950719/2361183241434822606848), (-3063665589/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((836980445/9444732965739290427392), (-1094305679/75557863725914323419136)), (21/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1908597443/604462909807314587353088), (655729451/75557863725914323419136)), (87/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-2910215101/4835703278458516698824704), (-3325544497/4835703278458516698824704)), (43/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((6595437605/77371252455336267181195264), (-187797873/9671406556917033397649408)), (167/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((135/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1536000/19165081), (-3188480/57495243)), 0, by norm_num⟩
  | 1 => ⟨((-5533629644800/3305702967629049), (1632501760000/367300329736561)), 0, by norm_num⟩
  | 2 => ⟨((-987979099/17592186044416), (-3949864819/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2385821403/281474976710656), (523550287/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-4917605723/9007199254740992), (-568515921/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((3405224855/144115188075855872), (-1817189103/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1377116367/2305843009213693952), (5351705005/4611686018427387904)), (7/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-304185161/36893488147419103232), (-2326625363/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 8 => ⟨((2454487209/1180591620717411303424), (1356801135/590295810358705651712)), (19/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-86800849/590295810358705651712), (-1301866559/37778931862957161709568)), (21/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((2069707747/302231454903657293676544), (-407470797/151115727451828646838272)), (47/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1930953021/9671406556917033397649408), (1440741471/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-80624189/309485009821345068724781056), (-5408357971/309485009821345068724781056)), (57/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (7473/1280)))⁻¹=value ((1536000/19165081), (-3188480/57495243)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((1536000/19165081), (-3188480/57495243))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((377184191/9007199254740992), (-4797992539/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 1 => ⟨((138104279/9007199254740992), (5353928699/144115188075855872)), (5/36028797018963968), by norm_num⟩
  | 2 => ⟨((-3240053395/288230376151711744), (-2799275/1125899906842624)), (7/144115188075855872), by norm_num⟩
  | 3 => ⟨((2048422405/1152921504606846976), (-3838488593/2305843009213693952)), (29/2305843009213693952), by norm_num⟩
  | 4 => ⟨((627232817/9223372036854775808), (3853801111/9223372036854775808)), (13/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-4309944589/73786976294838206464), (-1932171475/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | 6 => ⟨((4312550731/590295810358705651712), (-2796321999/590295810358705651712)), (45/590295810358705651712), by norm_num⟩
  | 7 => ⟨((50632653/4722366482869645213696), (1286001481/1180591620717411303424)), (57/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-128369211/1180591620717411303424), (-156316819/2361183241434822606848)), (65/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((3775525885/302231454903657293676544), (-1945544093/302231454903657293676544)), (71/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-227001037/2417851639229258349412352), (7132637559/4835703278458516698824704)), (147/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-4777970049/38685626227668133590597632), (-807104393/9671406556917033397649408)), (149/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((2014500199/154742504910672534362390528), (-1969576193/309485009821345068724781056)), (147/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((151/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15462400/201772129), (-9565440/201772129)), 0, by norm_num⟩
  | 1 => ⟨((-73794085683200/40711992041192641), (147904659456000/40711992041192641)), 0, by norm_num⟩
  | 2 => ⟨((-586237655/35184372088832), (-3204711209/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((697555079/140737488355328), (3707050425/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3116508565/9007199254740992), (-1214447669/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((2371206713/144115188075855872), (-218712071/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2575609819/4611686018427387904), (583733001/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((693473667/73786976294838206464), (-4816561661/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 8 => ⟨((488214051/1180591620717411303424), (3478869553/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1917998887/37778931862957161709568), (-881225933/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((230534781/75557863725914323419136), (353080775/604462909807314587353088)), (19/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-5058274973/38685626227668133590597632), (241497313/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2368328937/618970019642690137449562112), (-1551406541/309485009821345068724781056)), (19/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (7473/1280)))⁻¹=value ((15462400/201772129), (-9565440/201772129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15462400/201772129), (-9565440/201772129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((60462101/1152921504606846976), (-255367137/36028797018963968)), (9/288230376151711744), by norm_num⟩
  | 1 => ⟨((3576566469/1152921504606846976), (2758813545/1152921504606846976)), (11/576460752303423488), by norm_num⟩
  | 2 => ⟨((-5326022367/4611686018427387904), (747621671/2305843009213693952)), (33/4611686018427387904), by norm_num⟩
  | 3 => ⟨((865190411/9223372036854775808), (-4641149175/18446744073709551616)), (35/18446744073709551616), by norm_num⟩
  | 4 => ⟨((2020954099/73786976294838206464), (1500069341/36893488147419103232)), (33/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-2281730023/295147905179352825856), (-10796865/73786976294838206464)), (23/295147905179352825856), by norm_num⟩
  | 6 => ⟨((1499284641/2361183241434822606848), (-4188775325/4722366482869645213696)), (31/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((1857096251/37778931862957161709568), (4987009109/37778931862957161709568)), (39/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-4981839767/302231454903657293676544), (-1151916033/302231454903657293676544)), (23/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((3322306129/2417851639229258349412352), (-3216238007/2417851639229258349412352)), (103/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((201220855/4835703278458516698824704), (3888356713/19342813113834066795298816)), (55/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1530433283/77371252455336267181195264), (-1122850041/154742504910672534362390528)), (7/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4025414263/2475880078570760549798248448), (-1603989925/1237940039285380274899124224)), (7/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((167/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17100800/234335329), (-9565440/234335329)), 0, by norm_num⟩
  | 1 => ⟨((-100469859123200/54913046417538241), (163576676352000/54913046417538241)), 0, by norm_num⟩
  | 2 => ⟨((104880003/17592186044416), (-2569043559/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((777706039/281474976710656), (383518129/70368744177664)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3819958233/18014398509481984), (-2566546585/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((6136470467/576460752303423488), (250936761/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3746398657/9223372036854775808), (855451059/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1628465765/147573952589676412928), (-2222242691/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-900089731/9444732965739290427392), (3658287095/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-931895283/75557863725914323419136), (-1141347545/37778931862957161709568)), (17/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((161184137/151115727451828646838272), (257083931/302231454903657293676544)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-4354444421/77371252455336267181195264), (-717055995/77371252455336267181195264)), (59/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1388154993/618970019642690137449562112), (-501673321/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (7473/1280)))⁻¹=value ((17100800/234335329), (-9565440/234335329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((17100800/234335329), (-9565440/234335329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1316616131/4611686018427387904), (-4790460985/9223372036854775808)), (17/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1591390279/4611686018427387904), (1127429135/18446744073709551616)), (11/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-1565818541/18446744073709551616), (1394869253/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-69017607/36893488147419103232), (-7874853865/295147905179352825856)), (19/73786976294838206464), by norm_num⟩
  | 4 => ⟨((5042595347/1180591620717411303424), (3287361607/1180591620717411303424)), (37/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-924183313/1180591620717411303424), (685836927/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((154729851/4722366482869645213696), (-2214311335/18889465931478580854784)), (75/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((3074486929/302231454903657293676544), (3799841357/302231454903657293676544)), (3/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-4802475157/2417851639229258349412352), (43395293/302231454903657293676544)), (29/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((2234475341/19342813113834066795298816), (-3848052591/19342813113834066795298816)), (33/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((857856023/77371252455336267181195264), (1747652915/77371252455336267181195264)), (9/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-6450306265/2475880078570760549798248448), (-792272591/2475880078570760549798248448)), (297/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((414337789/2475880078570760549798248448), (-2004642529/9903520314283042199192993792)), (301/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((183/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((6246400/90058443), (-3188480/90058443)), 0, by norm_num⟩
  | 1 => ⟨((-1602839347200/901169239509361), (19916521472000/8110523155584249)), 0, by norm_num⟩
  | 2 => ⟨((640765579/35184372088832), (-4104134433/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1613791603/1125899906842624), (4917541567/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-2288280361/18014398509481984), (-1135768665/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((3826184877/576460752303423488), (1224590501/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-4939807993/18446744073709551616), (50527543/1152921504606846976)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2511997209/295147905179352825856), (-1847717745/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-870503905/4722366482869645213696), (3473484343/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-17775495/151115727451828646838272), (-4840934891/302231454903657293676544)), (31/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((2781711833/9671406556917033397649408), (5352091123/9671406556917033397649408)), (53/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-382426335/19342813113834066795298816), (-2181860457/154742504910672534362390528)), (23/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((4631147585/4951760157141521099596496896), (172061753/1237940039285380274899124224)), (39/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (7473/1280)))⁻¹=value ((6246400/90058443), (-3188480/90058443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((6246400/90058443), (-3188480/90058443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2817948877/73786976294838206464), (-1912280637/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 1 => ⟨((4114576065/147573952589676412928), (-1144510477/147573952589676412928)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-74523481/18446744073709551616), (665002037/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-2582711345/2361183241434822606848), (-5120023457/2361183241434822606848)), (75/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((4449927205/9444732965739290427392), (923192411/9444732965739290427392)), (75/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-1172688335/18889465931478580854784), (124699315/2361183241434822606848)), (29/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-49840263/75557863725914323419136), (-7387245749/604462909807314587353088)), (163/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1680302605/1208925819614629174706176), (1117073835/1208925819614629174706176)), (107/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-3815199905/19342813113834066795298816), (44029831/604462909807314587353088)), (131/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((252223073/38685626227668133590597632), (-3699273097/154742504910672534362390528)), (19/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((1092992167/618970019642690137449562112), (655675359/309485009821345068724781056)), (169/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-2879654581/9903520314283042199192993792), (551228369/19807040628566084398385987584)), (177/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((2223455305/158456325028528675187087900672), (-2066026289/79228162514264337593543950336)), (363/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((199/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20377600/309292129), (-9565440/309292129)), 0, by norm_num⟩
  | 1 => ⟨((-161874469683200/95661621061352641), (194920710144000/95661621061352641)), 0, by norm_num⟩
  | 2 => ⟨((852699331/35184372088832), (-3282351397/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((45333095/70368744177664), (1941022899/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-335695261/4503599627370496), (-3733360079/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((4678375341/1152921504606846976), (2606640421/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-1555393269/9223372036854775808), (-432800265/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3386330015/590295810358705651712), (-1311191551/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-2920897061/18889465931478580854784), (764463987/4722366482869645213696)), (17/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((195744615/75557863725914323419136), (-1167199841/151115727451828646838272)), (27/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((164875537/4835703278458516698824704), (5696517049/19342813113834066795298816)), (43/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-878506197/154742504910672534362390528), (-2839332975/309485009821345068724781056)), (17/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1628574647/4951760157141521099596496896), (2123672277/9903520314283042199192993792)), (27/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (7473/1280)))⁻¹=value ((20377600/309292129), (-9565440/309292129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20377600/309292129), (-9565440/309292129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1958403299/590295810358705651712), (-310716449/590295810358705651712)), (23/590295810358705651712), by norm_num⟩
  | 1 => ⟨((2024167935/1180591620717411303424), (-1661349071/1180591620717411303424)), (67/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-209316711/9444732965739290427392), (7476398541/9444732965739290427392)), (55/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-2845489665/18889465931478580854784), (-1279349437/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((1553539837/37778931862957161709568), (-906463191/151115727451828646838272)), (137/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-2247876323/604462909807314587353088), (3767612881/604462909807314587353088)), (7/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-955776417/2417851639229258349412352), (-5065988699/4835703278458516698824704)), (5/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((2889294133/19342813113834066795298816), (1790817607/38685626227668133590597632)), (107/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-2534517175/154742504910672534362390528), (452004535/38685626227668133590597632)), (67/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((121571683/2475880078570760549798248448), (-2989438567/1237940039285380274899124224)), (315/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((4309749269/19807040628566084398385987584), (1636872489/9903520314283042199192993792)), (89/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-4439989753/158456325028528675187087900672), (692934913/79228162514264337593543950336)), (95/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((1148266455/1267650600228229401496703205376), (-3642516779/1267650600228229401496703205376)), (197/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5502435763/4398046511104), (-303492081/549755813888)), (119/274877906944), by norm_num⟩
  | 1 => ⟨((3299697963/2199023255552), (1726477693/4398046511104)), (2233/2199023255552), by norm_num⟩
  | 2 => ⟨((286107967/549755813888), (185721619/274877906944)), (5051/4398046511104), by norm_num⟩
  | 3 => ⟨((84494741/17592186044416), (5317793547/17592186044416)), (7595/8796093022208), by norm_num⟩
  | 4 => ⟨((-1538571031/35184372088832), (1127086143/17592186044416)), (8643/17592186044416), by norm_num⟩
  | 5 => ⟨((-3995220583/281474976710656), (103589283/17592186044416)), (63785/281474976710656), by norm_num⟩
  | 6 => ⟨((-2745197295/1125899906842624), (-93767607/281474976710656)), (99471/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2467525149/9007199254740992), (-105983727/562949953421312)), (67413/2251799813685248), by norm_num⟩
  | 8 => ⟨((-3072975627/144115188075855872), (-601704049/18014398509481984)), (648229/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1071610397/1152921504606846976), (-2438634359/576460752303423488)), (2806157/1152921504606846976), by norm_num⟩
  | 10 => ⟨((457673185/9223372036854775808), (-4025246177/9223372036854775808)), (5533739/9223372036854775808), by norm_num⟩
  | 11 => ⟨((2512657659/147573952589676412928), (-1376363327/36893488147419103232)), (5018775/36893488147419103232), by norm_num⟩
  | 12 => ⟨((2739452905/1180591620717411303424), (-786672893/295147905179352825856)), (33759353/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5502435763/4398046511104), (-303492081/549755813888)), (1905/4398046511104), by norm_num⟩
  | 1 => ⟨((3299697963/2199023255552), (1726477693/4398046511104)), (4467/4398046511104), by norm_num⟩
  | 2 => ⟨((286107967/549755813888), (185721619/274877906944)), (1263/1099511627776), by norm_num⟩
  | 3 => ⟨((84494741/17592186044416), (5317793547/17592186044416)), (15191/17592186044416), by norm_num⟩
  | 4 => ⟨((-1538571031/35184372088832), (1127086143/17592186044416)), (34575/70368744177664), by norm_num⟩
  | 5 => ⟨((-3995220583/281474976710656), (103589283/17592186044416)), (63797/281474976710656), by norm_num⟩
  | 6 => ⟨((-2745197295/1125899906842624), (-93767607/281474976710656)), (199033/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2467525149/9007199254740992), (-105983727/562949953421312)), (540025/18014398509481984), by norm_num⟩
  | 8 => ⟨((-3072975627/144115188075855872), (-601704049/18014398509481984)), (1302223/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1071610397/1152921504606846976), (-2438634359/576460752303423488)), (1426137/576460752303423488), by norm_num⟩
  | 10 => ⟨((457673185/9223372036854775808), (-4025246177/9223372036854775808)), (2951337/4611686018427387904), by norm_num⟩
  | 11 => ⟨((2512657659/147573952589676412928), (-1376363327/36893488147419103232)), (25978059/147573952589676412928), by norm_num⟩
  | 12 => ⟨((2739452905/1180591620717411303424), (-786672893/295147905179352825856)), (40491509/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile028Gamma
