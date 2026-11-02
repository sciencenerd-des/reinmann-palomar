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
namespace Reinmann.XiRectangle.Tile024Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-311154521/134217728), (-4478680393/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-330576565380905/9007199254740992), (-822764687888769/9007199254740992)), (39071457/9007199254740992), by norm_num⟩
  | 1 => ⟨((1948978801/17179869184), (1212692537/4294967296)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((-753047027/4294967296), (-3748484115/8589934592)), (181/8589934592), by norm_num⟩
  | 3 => ⟨((387950055/2147483648), (1931120589/4294967296)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((-599585045/4294967296), (-5969175723/17179869184)), (293/17179869184), by norm_num⟩
  | 5 => ⟨((1482674263/17179869184), (1845097557/8589934592)), (183/17179869184), by norm_num⟩
  | 6 => ⟨((-1527669697/34359738368), (-3802183253/34359738368)), (95/17179869184), by norm_num⟩
  | 7 => ⟨((1349169111/68719476736), (839479275/17179869184)), (169/68719476736), by norm_num⟩
  | 8 => ⟨((-2085169499/274877906944), (-1297433039/68719476736)), (33/34359738368), by norm_num⟩
  | 9 => ⟨((179037429/68719476736), (3564818315/549755813888)), (183/549755813888), by norm_num⟩
  | 10 => ⟨((-442729835/549755813888), (-1101900475/549755813888)), (57/549755813888), by norm_num⟩
  | 11 => ⟨((1990540677/8796093022208), (2477106289/4398046511104)), (129/4398046511104), by norm_num⟩
  | 12 => ⟨((-2050948579/35184372088832), (-5104560467/35184372088832)), (67/8796093022208), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986543857/2535301200456458802993406410752), (-2543795652785/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444597171537553/158456325028528675187087900672), (-752309825017/158456325028528675187087900672)), (23125/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944657058679737/19807040628566084398385987584), (-211544012373/2475880078570760549798248448)), (6505/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889062272011527/2475880078570760549798248448), (-3595397054539/2475880078570760549798248448)), (6913/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885364156618521/77371252455336267181195264), (-1797219884803/77371252455336267181195264)), (13829/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549119728512973/9671406556917033397649408), (-1684385222547/4835703278458516698824704)), (1621/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258408978005093/604462909807314587353088), (-5755190647/1180591620717411303424)), (22701/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235896826215439/9444732965739290427392), (-2393206644049/37778931862957161709568)), (36901/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297076015074911/4722366482869645213696), (-897035865541/1180591620717411303424)), (27687/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810405149789555/295147905179352825856), (-616373803609/73786976294838206464)), (19043/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911338234602307/36893488147419103232), (-6159679953295/73786976294838206464)), (23817/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910878877071177/4611686018427387904), (-6924063600023/9223372036854775808)), (6703/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593004731729143/1152921504606846976), (-3458549219223/576460752303423488)), (26835/576460752303423488), by norm_num⟩
  | 5 => ⟨((298430140226047/36028797018963968), (-1511158143441/36028797018963968)), (47013/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490343684730931/36028797018963968), (-9051309848863/36028797018963968)), (70621/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487634592667991/9007199254740992), (-11286809757861/9007199254740992)), (88455/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224684207278755/4503599627370496), (-2811474949725/562949953421312)), (88725/2251799813685248), by norm_num⟩
  | 1 => ⟨((138197757917329/140737488355328), (-8383429655331/562949953421312)), (33441/281474976710656), by norm_num⟩
  | 0 => ⟨((2170681255705707/2251799813685248), (-66254923632931/2251799813685248)), (540489/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2170681255705707/2251799813685248), (-66254923632931/2251799813685248)), (2061801918990325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1045267738800981/1125899906842624), (-127736328917131/2251799813685248)), (268461/562949953421312), by norm_num⟩
  | 2 => ⟨((1933574195594917/2251799813685248), (-237176791433221/2251799813685248)), (2115711/2251799813685248), by norm_num⟩
  | 3 => ⟨((1635339126105239/2251799813685248), (-407317667336281/2251799813685248)), (2039561/1125899906842624), by norm_num⟩
  | 4 => ⟨((278491271737555/562949953421312), (-295808940963899/1125899906842624)), (3700261/1125899906842624), by norm_num⟩
  | 5 => ⟨((24727622636369/140737488355328), (-292673292393799/1125899906842624)), (5605385/1125899906842624), by norm_num⟩
  | 6 => ⟨((-330576565380905/9007199254740992), (-822764687888769/9007199254740992)), (39071457/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-311154521/134217728), (-4478680393/134217728)), (1/67108864), by norm_num⟩, -5, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-157814591/67108864), (-567885943/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-325505452248003/4503599627370496), (-558295136213823/9007199254740992)), (39169019/9007199254740992), by norm_num⟩
  | 1 => ⟨((3893358089/17179869184), (1669436617/8589934592)), (237/17179869184), by norm_num⟩
  | 2 => ⟨((-1525950221/4294967296), (-654313607/2147483648)), (187/8589934592), by norm_num⟩
  | 3 => ⟨((398717341/1073741824), (341932755/1073741824)), (197/8589934592), by norm_num⟩
  | 4 => ⟨((-2500351833/8589934592), (-2144256351/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((783983871/4294967296), (1344660677/8589934592)), (197/17179869184), by norm_num⟩
  | 6 => ⟨((-1638784595/17179869184), (-1405391925/17179869184)), (13/2147483648), by norm_num⟩
  | 7 => ⟨((1468114177/34359738368), (157378509/4294967296)), (47/17179869184), by norm_num⟩
  | 8 => ⟨((-2301631755/137438953472), (-3947675237/274877906944)), (297/274877906944), by norm_num⟩
  | 9 => ⟨((1603722901/274877906944), (2750647305/549755813888)), (209/549755813888), by norm_num⟩
  | 10 => ⟨((-125711597/68719476736), (-1724927743/1099511627776)), (33/274877906944), by norm_num⟩
  | 11 => ⟨((2293341005/4398046511104), (983363811/2199023255552)), (303/8796093022208), by norm_num⟩
  | 12 => ⟨((-149807447/1099511627776), (-2055554361/17592186044416)), (5/549755813888), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518636921/10141204801825835211973625643008), (-396110097213/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55572957403183/19807040628566084398385987584), (-3748491225275/633825300114114700748351602688)), (23143/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944626587627491/19807040628566084398385987584), (-2108087606117/19807040628566084398385987584)), (13021/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944498669625845/1237940039285380274899124224), (-4478609973813/2475880078570760549798248448)), (6919/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770663176182467/154742504910672534362390528), (-4477399502453/154742504910672534362390528)), (6921/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193632305703609/1208925819614629174706176), (-4196276207527/9671406556917033397649408)), (12981/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629177569387357/302231454903657293676544), (-3670456192463/604462909807314587353088)), (22725/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887086715049577/75557863725914323419136), (-2981040868295/37778931862957161709568)), (36943/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162126217410735/590295810358705651712), (-1117363409821/1180591620717411303424)), (27721/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620718594596143/590295810358705651712), (-3071037571963/295147905179352825856)), (19069/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822560975628275/73786976294838206464), (-7672460864377/73786976294838206464)), (47705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910813320135479/4611686018427387904), (-8624464325711/9223372036854775808)), (26857/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199109017693977/144115188075855872), (-8615652370393/1152921504606846976)), (26885/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193602888037801/144115188075855872), (-7528790251245/144115188075855872)), (47113/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490163873449815/36028797018963968), (-11273393925683/36028797018963968)), (70797/36028797018963968), by norm_num⟩
  | 3 => ⟨((743702037335377/4503599627370496), (-14057151686381/9007199254740992)), (88719/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112103003829081/2251799813685248), (-14005354258071/2251799813685248)), (2783/70368744177664), by norm_num⟩
  | 1 => ⟨((1105202130189909/1125899906842624), (-20878848166593/1125899906842624)), (67213/562949953421312), by norm_num⟩
  | 0 => ⟨((1084496650357347/1125899906842624), (-10310706513609/281474976710656)), (544471/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084496650357347/1125899906842624), (-10310706513609/281474976710656)), (2076992043502043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((521552585091167/562949953421312), (-158904735440425/2251799813685248)), (1088787/2251799813685248), by norm_num⟩
  | 2 => ⟨((60049505219693/70368744177664), (-147219437622293/1125899906842624)), (1085555/1125899906842624), by norm_num⟩
  | 3 => ⟨((400323270058429/562949953421312), (-251260825846775/1125899906842624)), (4273231/2251799813685248), by norm_num⟩
  | 4 => ⟨((513280866339631/1125899906842624), (-44668959837929/140737488355328)), (3992401/1125899906842624), by norm_num⟩
  | 5 => ⟨((241152920704837/2251799813685248), (-325822532035181/1125899906842624)), (24697857/4503599627370496), by norm_num⟩
  | 6 => ⟨((-325505452248003/4503599627370496), (-558295136213823/9007199254740992)), (39169019/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-157814591/67108864), (-567885943/16777216)), (1/67108864), by norm_num⟩, -5, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-319913373/134217728), (-4604753119/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1609935387301177/18014398509481984), (-205057562277135/9007199254740992)), (36020183/9007199254740992), by norm_num⟩
  | 1 => ⟨((1219859439/4294967296), (310747133/4294967296)), (55/4294967296), by norm_num⟩
  | 2 => ⟨((-3876778963/8589934592), (-246892779/2147483648)), (177/8589934592), by norm_num⟩
  | 3 => ⟨((513358843/1073741824), (1046184723/8589934592)), (189/8589934592), by norm_num⟩
  | 4 => ⟨((-6525928149/17179869184), (-1662415683/17179869184)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((2073975095/8589934592), (528324653/8589934592)), (193/17179869184), by norm_num⟩
  | 6 => ⟨((-2197068165/17179869184), (-1119362791/34359738368)), (103/17179869184), by norm_num⟩
  | 7 => ⟨((1994971685/34359738368), (508199315/34359738368)), (189/68719476736), by norm_num⟩
  | 8 => ⟨((-6340127405/274877906944), (-403771195/68719476736)), (303/274877906944), by norm_num⟩
  | 9 => ⟨((1119403677/137438953472), (1140628083/549755813888)), (27/68719476736), by norm_num⟩
  | 10 => ⟨((-5692040229/2199023255552), (-1449990979/2199023255552)), (277/2199023255552), by norm_num⟩
  | 11 => ⟨((1644510023/2199023255552), (1675690685/8796093022208)), (323/8796093022208), by norm_num⟩
  | 12 => ⟨((-3484227585/17592186044416), (-887572533/17592186044416)), (173/17592186044416), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98804433728147/633825300114114700748351602688), (-3767358323343/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889141170999637/316912650057057350374175801344), (-2228099814397/316912650057057350374175801344)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944597091383907/19807040628566084398385987584), (-5012159616611/39614081257132168796771975168)), (13031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888934445683929/2475880078570760549798248448), (-2662060951815/1237940039285380274899124224)), (27699/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442650010509393/38685626227668133590597632), (-5322662162113/154742504910672534362390528)), (27709/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774499500977685/4835703278458516698824704), (-4988445093699/9671406556917033397649408)), (25987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629151435186589/302231454903657293676544), (-1090834775405/151115727451828646838272)), (5687/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887001300899885/75557863725914323419136), (-7087519820943/75557863725914323419136)), (4623/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296945260904659/4722366482869645213696), (-2656548810691/2361183241434822606848)), (13877/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620629258844257/590295810358705651712), (-7301379390839/590295810358705651712)), (9547/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822448290540269/73786976294838206464), (-1140066471495/9223372036854775808)), (23887/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821498475921181/9223372036854775808), (-10252087327875/9223372036854775808)), (53799/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398185559746597/288230376151711744), (-5120727138529/576460752303423488)), (26933/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193487273042575/144115188075855872), (-8949318009139/144115188075855872)), (47209/144115188075855872), by norm_num⟩
  | 4 => ⟨((744993281772211/18014398509481984), (-6700043658525/18014398509481984)), (70965/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487175663719375/9007199254740992), (-16708345596625/9007199254740992)), (22243/2251799813685248), by norm_num⟩
  | 2 => ⟨((555932245605703/1125899906842624), (-2080723408195/281474976710656)), (22343/562949953421312), by norm_num⟩
  | 1 => ⟨((69051206998851/70368744177664), (-24812590238427/1125899906842624)), (135061/1125899906842624), by norm_num⟩
  | 0 => ⟨((270908010479185/281474976710656), (-24501327160483/562949953421312)), (274147/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((270908010479185/281474976710656), (-24501327160483/562949953421312)), (1045787815574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040818224618561/1125899906842624), (-23581512902901/281474976710656)), (551575/1125899906842624), by norm_num⟩
  | 2 => ⟨((477131744196723/562949953421312), (-21799511878677/140737488355328)), (69513/70368744177664), by norm_num⟩
  | 3 => ⟨((1563557829554653/2251799813685248), (-36952624516965/140737488355328)), (4459737/2251799813685248), by norm_num⟩
  | 4 => ⟨((116303966065465/281474976710656), (-102633573437483/281474976710656)), (4267627/1125899906842624), by norm_num⟩
  | 5 => ⟨((170130199763299/4503599627370496), (-1357044725665495/4503599627370496)), (103733/17592186044416), by norm_num⟩
  | 6 => ⟨((-1609935387301177/18014398509481984), (-205057562277135/9007199254740992)), (36020183/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-319913373/134217728), (-4604753119/134217728)), (1/67108864), by norm_num⟩, -5, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/67108864), (-2331950509/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1581878995307509/18014398509481984), (306279727343183/18014398509481984)), (34481765/9007199254740992), by norm_num⟩
  | 1 => ⟨((2427993801/8589934592), (-940205011/17179869184)), (107/8589934592), by norm_num⟩
  | 2 => ⟨((-3907705275/8589934592), (756600795/8589934592)), (87/4294967296), by norm_num⟩
  | 3 => ⟨((2096403007/4294967296), (-101475167/1073741824)), (47/2147483648), by norm_num⟩
  | 4 => ⟨((-6748060959/17179869184), (163317981/2147483648)), (305/17179869184), by norm_num⟩
  | 5 => ⟨((4344234057/17179869184), (-841120481/17179869184)), (99/8589934592), by norm_num⟩
  | 6 => ⟨((-145661979/1073741824), (902487461/34359738368)), (107/17179869184), by norm_num⟩
  | 7 => ⟨((4286791523/68719476736), (-1621091/134217728)), (199/68719476736), by norm_num⟩
  | 8 => ⟨((-53900975/2147483648), (1335831201/274877906944)), (161/137438953472), by norm_num⟩
  | 9 => ⟨((154222707/17179869184), (-238881931/137438953472)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((-6354223913/2199023255552), (307572509/549755813888)), (301/2199023255552), by norm_num⟩
  | 11 => ⟨((1859405249/2199023255552), (-180006857/1099511627776)), (89/2199023255552), by norm_num⟩
  | 12 => ⟨((-3990129737/17592186044416), (772559627/17592186044416)), (193/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (3843149096973/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778234737251365/633825300114114700748351602688), (568202315959/79228162514264337593543950336)), (11581/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889140615434253/39614081257132168796771975168), (5112720459059/39614081257132168796771975168)), (26065/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888877512571023/2475880078570760549798248448), (1357731172445/618970019642690137449562112)), (27703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770543088915655/154742504910672534362390528), (5429416449347/154742504910672534362390528)), (433/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1548945587174795/9671406556917033397649408), (5088475717421/9671406556917033397649408)), (12995/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629128055623015/302231454903657293676544), (556351798435/75557863725914323419136)), (22751/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886925277652791/75557863725914323419136), (7229570602109/75557863725914323419136)), (36989/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648444104417767/2361183241434822606848), (5419551241427/4722366482869645213696)), (13879/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810275378053475/295147905179352825856), (1861903976033/147573952589676412928)), (19097/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822350078145935/73786976294838206464), (2325780416765/18446744073709551616)), (23891/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821387871905771/9223372036854775808), (10457218180383/9223372036854775808)), (26905/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592631491716485/1152921504606846976), (5223115919349/576460752303423488)), (26939/576460752303423488), by norm_num⟩
  | 5 => ⟨((596695104411773/72057594037927936), (9128101176453/144115188075855872)), (47221/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489840648504969/36028797018963968), (6833734152501/18014398509481984)), (70987/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486992716676389/9007199254740992), (8520592091133/4503599627370496)), (22251/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111680723277755/2251799813685248), (8488273632983/1125899906842624)), (22353/562949953421312), by norm_num⟩
  | 1 => ⟨((552270819574695/562949953421312), (25303543961335/1125899906842624)), (135141/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083068799359219/1125899906842624), (12490969590741/281474976710656)), (274391/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083068799359219/1125899906842624), (12490969590741/281474976710656)), (1046718601707076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039649819571365/1125899906842624), (96126338444523/1125899906842624)), (138065/281474976710656), by norm_num⟩
  | 2 => ⟨((237949987356605/281474976710656), (177525070945535/1125899906842624)), (557105/562949953421312), by norm_num⟩
  | 3 => ⟨((1553260618638885/2251799813685248), (600296180933959/2251799813685248)), (4470399/2251799813685248), by norm_num⟩
  | 4 => ⟨((455693936933911/1125899906842624), (828152140076847/2251799813685248)), (2137681/562949953421312), by norm_num⟩
  | 5 => ⟨((64300515809389/2251799813685248), (1340736975989863/4503599627370496)), (26422113/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1581878995307509/18014398509481984), (306279727343183/18014398509481984)), (34481765/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-2331950509/67108864)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20498171/8388608), (-295045549/8388608)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1278198679372059/18014398509481984), (451117589292565/9007199254740992)), (71316357/18014398509481984), by norm_num⟩
  | 1 => ⟨((3971571629/17179869184), (-1401695877/8589934592)), (223/17179869184), by norm_num⟩
  | 2 => ⟨((-202183809/536870912), (1141715121/4294967296)), (183/8589934592), by norm_num⟩
  | 3 => ⟨((3513249963/8589934592), (-1239939361/4294967296)), (201/8589934592), by norm_num⟩
  | 4 => ⟨((-2861626885/8589934592), (1009960535/4294967296)), (83/4294967296), by norm_num⟩
  | 5 => ⟨((3729382659/17179869184), (-1316219569/8589934592)), (109/8589934592), by norm_num⟩
  | 6 => ⟨((-4050229577/34359738368), (1429456807/17179869184)), (239/34359738368), by norm_num⟩
  | 7 => ⟨((3770296847/68719476736), (-1330659507/34359738368)), (225/68719476736), by norm_num⟩
  | 8 => ⟨((-191937361/8589934592), (2167708567/137438953472)), (185/137438953472), by norm_num⟩
  | 9 => ⟨((4446936543/549755813888), (-784733753/137438953472)), (135/274877906944), by norm_num⟩
  | 10 => ⟨((-2897709711/1099511627776), (2045390659/1099511627776)), (177/1099511627776), by norm_num⟩
  | 11 => ⟨((1716548723/2199023255552), (-605825475/1099511627776)), (211/4398046511104), by norm_num⟩
  | 12 => ⟨((-3728454301/17592186044416), (657945961/4398046511104)), (231/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395198185306375/2535301200456458802993406410752), (3291623518563/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111137022976647/39614081257132168796771975168), (3893093318161/633825300114114700748351602688)), (11573/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889093124533885/39614081257132168796771975168), (1094696079835/9903520314283042199192993792)), (13023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888827283379865/2475880078570760549798248448), (1162824231867/618970019642690137449562112)), (27681/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885246559070357/77371252455336267181195264), (290624413109/9671406556917033397649408)), (27689/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548899013948529/9671406556917033397649408), (4357978570461/9671406556917033397649408)), (25967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258215633832513/604462909807314587353088), (3811844000985/604462909807314587353088)), (11365/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117928750965405/4722366482869645213696), (6191646214589/75557863725914323419136)), (4619/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296839711114479/4722366482869645213696), (4641460213151/4722366482869645213696)), (1733/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620484800399143/590295810358705651712), (6378313321785/590295810358705651712)), (9537/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455567181249369/18446744073709551616), (3983676290795/36893488147419103232)), (5965/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910648923984417/4611686018427387904), (8955659716479/9223372036854775808)), (53731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592543337068359/1152921504606846976), (8946151221255/1152921504606846976)), (26895/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193315171435281/144115188075855872), (7817194099543/144115188075855872)), (11783/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489732275741441/36028797018963968), (11704436809005/36028797018963968)), (70831/36028797018963968), by norm_num⟩
  | 3 => ⟨((92929033959737/562949953421312), (228019150669/140737488355328)), (22193/2251799813685248), by norm_num⟩
  | 2 => ⟨((555781716327459/1125899906842624), (7268672280739/1125899906842624)), (89121/2251799813685248), by norm_num⟩
  | 1 => ⟨((552196356752261/562949953421312), (21666662362785/1125899906842624)), (134557/1125899906842624), by norm_num⟩
  | 0 => ⟨((2165755627894087/2251799813685248), (85555993436373/2251799813685248)), (34079/140737488355328), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2165755627894087/2251799813685248), (85555993436373/2251799813685248)), (130001068652105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((519937161296505/562949953421312), (164573576353261/2251799813685248)), (1090293/2251799813685248), by norm_num⟩
  | 2 => ⟨((1908815312532123/2251799813685248), (303998313148413/2251799813685248)), (1086673/1125899906842624), by norm_num⟩
  | 3 => ⟨((1577032248327737/2251799813685248), (16105912024101/70368744177664)), (4271437/2251799813685248), by norm_num⟩
  | 4 => ⟨((986501858196257/2251799813685248), (721898420884393/2251799813685248)), (7938225/2251799813685248), by norm_num⟩
  | 5 => ⟨((200749899436875/2251799813685248), (1265039865983293/4503599627370496)), (24090359/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1278198679372059/18014398509481984), (451117589292565/9007199254740992)), (71316357/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20498171/8388608), (-295045549/8388608)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-165884901/67108864), (-1193852897/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-396648235826931/9007199254740992), (1297604686390171/18014398509481984)), (68669001/18014398509481984), by norm_num⟩
  | 1 => ⟨((623363437/4294967296), (-4078572619/17179869184)), (109/8589934592), by norm_num⟩
  | 2 => ⟨((-2054504197/8589934592), (3360577499/8589934592)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((1128551779/4294967296), (-3691971737/8589934592)), (101/4294967296), by norm_num⟩
  | 4 => ⟨((-1859761279/8589934592), (760508535/2147483648)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((1225893957/8589934592), (-2005209653/8589934592)), (223/17179869184), by norm_num⟩
  | 6 => ⟨((-2693564331/34359738368), (1101473983/8589934592)), (247/34359738368), by norm_num⟩
  | 7 => ⟨((79263827/2147483648), (-4148889783/68719476736)), (235/68719476736), by norm_num⟩
  | 8 => ⟨((-2089925145/137438953472), (3418515975/137438953472)), (195/137438953472), by norm_num⟩
  | 9 => ⟨((3061356595/549755813888), (-1251874553/137438953472)), (9/17179869184), by norm_num⟩
  | 10 => ⟨((-2017946385/1099511627776), (3300779443/1099511627776)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((302310095/549755813888), (-3955938391/4398046511104)), (29/549755813888), by norm_num⟩
  | 12 => ⟨((-2656972683/17592186044416), (4346042529/17592186044416)), (257/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (2760915253431/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778151168727335/633825300114114700748351602688), (408157184907/79228162514264337593543950336)), (23131/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889046919939093/39614081257132168796771975168), (459077251715/4951760157141521099596496896)), (6507/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888778380741019/2475880078570760549798248448), (1950585931361/1237940039285380274899124224)), (6915/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770444428775549/154742504910672534362390528), (3900064311807/154742504910672534362390528)), (27667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548853594111811/9671406556917033397649408), (3655133856677/9671406556917033397649408)), (25945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629088058869201/302231454903657293676544), (199816629255/37778931862957161709568)), (22709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943398112827081/37778931862957161709568), (2596514030089/37778931862957161709568)), (36915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296792239265951/4722366482869645213696), (121651346487/147573952589676412928)), (27699/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202552515993317/73786976294838206464), (5349527824083/590295810358705651712)), (4763/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227773598148449/9223372036854775808), (6682215289323/73786976294838206464)), (47659/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821209152187941/9223372036854775808), (7511041566367/9223372036854775808)), (6707/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592456183870835/1152921504606846976), (7502984707483/1152921504606846976)), (53705/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298310160901841/36028797018963968), (6556056495513/144115188075855872)), (47047/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489623935988023/36028797018963968), (9815996591795/36028797018963968)), (35341/18014398509481984), by norm_num⟩
  | 3 => ⟨((371683784042063/2251799813685248), (6119195579475/4503599627370496)), (88547/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222886009745281/4503599627370496), (24382167158313/4503599627370496)), (177681/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104234356815587/1125899906842624), (2271087948863/140737488355328)), (267991/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082649262935015/1125899906842624), (71735600610303/2251799813685248)), (270943/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1082649262935015/1125899906842624), (71735600610303/2251799813685248)), (1033565525535201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2079834842012575/2251799813685248), (34489964274329/562949953421312)), (1076667/2251799813685248), by norm_num⟩
  | 2 => ⟨((956275069769843/1125899906842624), (127424167923917/1125899906842624)), (2120817/2251799813685248), by norm_num⟩
  | 3 => ⟨((398892070704189/562949953421312), (432907239200403/2251799813685248)), (4082651/2251799813685248), by norm_num⟩
  | 4 => ⟨((1047353078655309/2251799813685248), (613494197905177/2251799813685248)), (3677751/1125899906842624), by norm_num⟩
  | 5 => ⟨((19999927839005/140737488355328), (285347317735843/1125899906842624)), (21700625/4503599627370496), by norm_num⟩
  | 6 => ⟨((-396648235826931/9007199254740992), (1297604686390171/18014398509481984)), (68669001/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-1193852897/33554432)), (1/67108864), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile024Terms3
