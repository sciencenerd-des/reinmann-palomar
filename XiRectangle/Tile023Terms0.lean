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
namespace Reinmann.XiRectangle.Tile023Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

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

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-279097919/536870912), (-7706591295/1073741824)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((838425841160985/2251799813685248), (-1043920869426101/2251799813685248)), (926601/281474976710656), by norm_num⟩
  | 1 => ⟨((-2216920883/8589934592), (1380139937/4294967296)), (21/8589934592), by norm_num⟩
  | 2 => ⟨((3073304919/34359738368), (-3826560425/34359738368)), (31/34359738368), by norm_num⟩
  | 3 => ⟨((-2840336853/137438953472), (442061595/17179869184)), (15/68719476736), by norm_num⟩
  | 4 => ⟨((984385741/274877906944), (-1225654993/274877906944)), (23/549755813888), by norm_num⟩
  | 5 => ⟨((-2183437443/4398046511104), (2718589769/4398046511104)), (27/4398046511104), by norm_num⟩
  | 6 => ⟨((2017924677/35184372088832), (-2512510445/35184372088832)), (27/35184372088832), by norm_num⟩
  | 7 => ⟨((-399633943/70368744177664), (1990330893/281474976710656)), (45/562949953421312), by norm_num⟩
  | 8 => ⟨((2216041127/4503599627370496), (-1379592247/2251799813685248)), (33/4503599627370496), by norm_num⟩
  | 9 => ⟨((-2730742505/72057594037927936), (3400037249/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 10 => ⟨((3028490349/1152921504606846976), (-3770761973/1152921504606846976)), (25/576460752303423488), by norm_num⟩
  | 11 => ⟨((-1526683307/9223372036854775808), (3801735317/18446744073709551616)), (53/18446744073709551616), by norm_num⟩
  | 12 => ⟨((1410954973/147573952589676412928), (-219596843/18446744073709551616)), (51/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197912323863903/1267650600228229401496703205376), (-291178363681/2535301200456458802993406410752)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890583959021887/316912650057057350374175801344), (-1381914632983/633825300114114700748351602688)), (4329/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473110142743211/9903520314283042199192993792), (-777290031241/19807040628566084398385987584)), (2435/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236547991216483/309485009821345068724781056), (-825826774231/1237940039285380274899124224)), (5175/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774049746592183/154742504910672534362390528), (-412888702131/38685626227668133590597632)), (647/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552233333748543/9671406556917033397649408), (-48382116311/302231454903657293676544)), (4853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630566571942999/302231454903657293676544), (-169324293229/75557863725914323419136)), (4247/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891600931366049/75557863725914323419136), (-2201019104439/75557863725914323419136)), (3451/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300395364031465/4722366482869645213696), (-825296104795/2361183241434822606848)), (2589/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625373766290239/590295810358705651712), (-2269284595915/590295810358705651712)), (7121/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57136870134053/2305843009213693952), (-2836186207695/73786976294838206464)), (8903/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828172731583351/9223372036854775808), (-797533155503/2305843009213693952)), (10019/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599418056970217/1152921504606846976), (-398676443503/144115188075855872)), (5011/576460752303423488), by norm_num⟩
  | 5 => ⟨((74958147371275/9007199254740992), (-43592560947/2251799813685248)), (4387/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498754645648841/36028797018963968), (-1045815863553/9007199254740992)), (13169/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498141736812417/9007199254740992), (-5226240149441/9007199254740992)), (16477/9007199254740992), by norm_num⟩
  | 2 => ⟨((561419684836393/1125899906842624), (-2610990725463/1125899906842624)), (16499/2251799813685248), by norm_num⟩
  | 1 => ⟨((280325779690049/281474976710656), (-7822325628755/1125899906842624)), (24807/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116682480235375/1125899906842624), (-7801033168431/562949953421312)), (24921/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116682480235375/1125899906842624), (-7801033168431/562949953421312)), (95066072704124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1107324309748713/1125899906842624), (-30948673195475/1125899906842624)), (50125/562949953421312), by norm_num⟩
  | 2 => ⟨((544102232863565/562949953421312), (-15219034114641/281474976710656)), (12669/70368744177664), by norm_num⟩
  | 3 => ⟨((524239787242185/562949953421312), (-117675973055539/1125899906842624)), (103439/281474976710656), by norm_num⟩
  | 4 => ⟨((964083731492911/1125899906842624), (-109584212065799/562949953421312)), (214275/281474976710656), by norm_num⟩
  | 5 => ⟨((782860570319037/1125899906842624), (-375338359792131/1125899906842624)), (1801521/1125899906842624), by norm_num⟩
  | 6 => ⟨((838425841160985/2251799813685248), (-1043920869426101/2251799813685248)), (926601/281474976710656), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/536870912), (-7706591295/1073741824)), (3/1073741824), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/67108864), (-3053664553/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((366607026628239/2251799813685248), (229324711805795/562949953421312)), (8475225/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1536403597/8589934592), (-3844283241/8589934592)), (19/4294967296), by norm_num⟩
  | 2 => ⟨((26373623/268435456), (2111688405/8589934592)), (11/4294967296), by norm_num⟩
  | 3 => ⟨((-1236240483/34359738368), (-48331809/536870912)), (17/17179869184), by norm_num⟩
  | 4 => ⟨((679074493/68719476736), (3398266835/137438953472)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((-2387326665/1099511627776), (-746675541/137438953472)), (73/1099511627776), by norm_num⟩
  | 6 => ⟨((218562201/549755813888), (4374970267/4398046511104)), (7/549755813888), by norm_num⟩
  | 7 => ⟨((-2195338239/35184372088832), (-343314007/2199023255552)), (73/35184372088832), by norm_num⟩
  | 8 => ⟨((2411825567/281474976710656), (377168987/17592186044416)), (83/281474976710656), by norm_num⟩
  | 9 => ⟨((-2355254405/2251799813685248), (-5893155329/2251799813685248)), (21/562949953421312), by norm_num⟩
  | 10 => ⟨((1035004573/9007199254740992), (5179434291/18014398509481984)), (19/4503599627370496), by norm_num⟩
  | 11 => ⟨((-1653918171/144115188075855872), (-4138320117/144115188075855872)), (63/144115188075855872), by norm_num⟩
  | 12 => ⟨((605671609/576460752303423488), (3030939557/1152921504606846976)), (95/2305843009213693952), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (387717043241/2535301200456458802993406410752)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890348628022257/316912650057057350374175801344), (28736877351/9903520314283042199192993792)), (5775/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236488882732795/4951760157141521099596496896), (2068900097329/39614081257132168796771975168)), (6497/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945910653409239/1237940039285380274899124224), (2198021235889/2475880078570760549798248448)), (863/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443371775445199/38685626227668133590597632), (2197812982527/154742504910672534362390528)), (6905/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551705830992349/9671406556917033397649408), (2060228410507/9671406556917033397649408)), (6475/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260671555752549/604462909807314587353088), (1802478608239/604462909807314587353088)), (2833/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890850807158795/75557863725914323419136), (2928612913379/75557863725914323419136)), (9209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299832732872349/4722366482869645213696), (4289251433/9223372036854775808)), (6909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203075010848125/73786976294838206464), (3019043251461/590295810358705651712)), (4751/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28553322696583/1152921504606846976), (1886459747897/36893488147419103232)), (11881/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456771128557653/2305843009213693952), (4243318260871/9223372036854775808)), (13371/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799164840834587/576460752303423488), (4241798210943/1152921504606846976)), (6689/576460752303423488), by norm_num⟩
  | 5 => ⟨((299594463103393/36028797018963968), (463732950689/18014398509481984)), (5857/72057594037927936), by norm_num⟩
  | 4 => ⟨((748662767232229/18014398509481984), (2780688159415/18014398509481984)), (8793/18014398509481984), by norm_num⟩
  | 3 => ⟨((93522170835989/562949953421312), (6945738274111/9007199254740992)), (22009/9007199254740992), by norm_num⟩
  | 2 => ⟨((560525725381627/1125899906842624), (3468383828999/1125899906842624)), (11025/1125899906842624), by norm_num⟩
  | 1 => ⟨((279654743356423/281474976710656), (10382733972059/1125899906842624)), (33177/1125899906842624), by norm_num⟩
  | 0 => ⟨((1111305251741021/1125899906842624), (20675852264041/1125899906842624)), (33381/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1111305251741021/1125899906842624), (20675852264041/1125899906842624)), (127338411571311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1096520093995261/1125899906842624), (40815676536799/1125899906842624)), (67123/562949953421312), by norm_num⟩
  | 2 => ⟨((533213649715689/562949953421312), (79501222445463/1125899906842624)), (67805/281474976710656), by norm_num⟩
  | 3 => ⟨((1004482488833051/1125899906842624), (37650893049527/281474976710656)), (552091/1125899906842624), by norm_num⟩
  | 4 => ⟨((27375425104931/35184372088832), (268724866410081/1125899906842624)), (566403/562949953421312), by norm_num⟩
  | 5 => ⟨((1234899790320275/2251799813685248), (209083096201589/562949953421312)), (2303521/1125899906842624), by norm_num⟩
  | 6 => ⟨((366607026628239/2251799813685248), (229324711805795/562949953421312)), (8475225/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-3053664553/268435456)), (1/268435456), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-279097919/268435456), (-7706591295/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5368107215641/70368744177664), (-388689184418057/1125899906842624)), (24988961/4503599627370496), by norm_num⟩
  | 1 => ⟨((908420015/8589934592), (4111004827/8589934592)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((-157417193/2147483648), (-5699062811/17179869184)), (97/17179869184), by norm_num⟩
  | 3 => ⟨((72742189/2147483648), (2633526213/17179869184)), (91/34359738368), by norm_num⟩
  | 4 => ⟨((-806736691/68719476736), (-3650842539/68719476736)), (65/68719476736), by norm_num⟩
  | 5 => ⟨((894699621/274877906944), (1012228485/68719476736)), (37/137438953472), by norm_num⟩
  | 6 => ⟨((-413439013/549755813888), (-3741991043/1099511627776)), (35/549755813888), by norm_num⟩
  | 7 => ⟨((655026483/4398046511104), (2964286333/4398046511104)), (113/8796093022208), by norm_num⟩
  | 8 => ⟨((-7094215/274877906944), (-1027343357/8796093022208)), (5/2199023255552), by norm_num⟩
  | 9 => ⟨((559483463/140737488355328), (5063823299/281474976710656)), (101/281474976710656), by norm_num⟩
  | 10 => ⟨((-77560877/140737488355328), (-1403989937/562949953421312)), (57/1125899906842624), by norm_num⟩
  | 11 => ⟨((1251167493/18014398509481984), (176940303/562949953421312)), (117/18014398509481984), by norm_num⟩
  | 12 => ⟨((-578162147/72057594037927936), (-1308220503/36028797018963968)), (55/72057594037927936), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414717067/10141204801825835211973625643008), (-291178363681/1267650600228229401496703205376)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((890180875827779/316912650057057350374175801344), (-1380732038481/316912650057057350374175801344)), (4335/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945766758589135/19807040628566084398385987584), (-776587884555/9903520314283042199192993792)), (9755/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891420036370629/2475880078570760549798248448), (-3300147458249/2475880078570760549798248448)), (10367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443271421505873/38685626227668133590597632), (-824938127147/38685626227668133590597632)), (10369/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551329349396497/9671406556917033397649408), (-3093098344197/9671406556917033397649408)), (2431/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260341980109175/604462909807314587353088), (-2706041420143/604462909807314587353088)), (4255/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945157478843725/37778931862957161709568), (-2198265251485/37778931862957161709568)), (13833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299430593011579/4722366482869645213696), (-3296709426549/4722366482869645213696)), (5189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101502920878127/36893488147419103232), (-4531856735853/590295810358705651712)), (3569/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826720346555117/73786976294838206464), (-5663142843381/73786976294838206464)), (8927/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826304825042823/9223372036854775808), (-6368728363861/9223372036854775808)), (10049/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399387234410573/288230376151711744), (-1591461056613/288230376151711744)), (10057/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197693516477829/144115188075855872), (-5566869088233/144115188075855872)), (17617/144115188075855872), by norm_num⟩
  | 4 => ⟨((748148332594411/18014398509481984), (-4171907264615/18014398509481984)), (6615/9007199254740992), by norm_num⟩
  | 3 => ⟨((1495064517392735/9007199254740992), (-5209206253737/4503599627370496)), (33137/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119755060708681/2251799813685248), (-2600344903413/562949953421312)), (33229/2251799813685248), by norm_num⟩
  | 1 => ⟨((558329511571615/562949953421312), (-15559489396315/1125899906842624)), (50073/1125899906842624), by norm_num⟩
  | 0 => ⟨((138415538718589/140737488355328), (-15474336597737/562949953421312)), (101069/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((138415538718589/140737488355328), (-15474336597737/562949953421312)), (385547642234420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((136025558215891/140737488355328), (-30438068229281/562949953421312)), (204361/1125899906842624), by norm_num⟩
  | 2 => ⟨((1048479574484367/1125899906842624), (-117675973055535/1125899906842624)), (208569/562949953421312), by norm_num⟩
  | 3 => ⟨((482041865746453/562949953421312), (-109584212065795/562949953421312)), (432053/562949953421312), by norm_num⟩
  | 4 => ⟨((97857571289879/140737488355328), (-93834589948029/281474976710656)), (1816247/1125899906842624), by norm_num⟩
  | 5 => ⟨((838425841160991/2251799813685248), (-1043920869426053/2251799813685248)), (3736701/1125899906842624), by norm_num⟩
  | 6 => ⟨((-5368107215641/70368744177664), (-388689184418057/1125899906842624)), (24988961/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/268435456), (-7706591295/536870912)), (3/536870912), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/134217728), (-4473537711/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-193871296702999/1125899906842624), (1101243201638481/4503599627370496)), (7494909/2251799813685248), by norm_num⟩
  | 1 => ⟨((595138197/2147483648), (-845137863/2147483648)), (3/536870912), by norm_num⟩
  | 2 => ⟨((-1915675955/8589934592), (680098459/2147483648)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((2055441007/17179869184), (-91214687/536870912)), (45/17179869184), by norm_num⟩
  | 4 => ⟨((-827026171/17179869184), (2348870007/34359738368)), (75/68719476736), by norm_num⟩
  | 5 => ⟨((2129675639/137438953472), (-3024288353/137438953472)), (25/68719476736), by norm_num⟩
  | 6 => ⟨((-1142526905/274877906944), (1622468111/274877906944)), (7/68719476736), by norm_num⟩
  | 7 => ⟨((1050757781/1099511627776), (-1492149537/1099511627776)), (53/2199023255552), by norm_num⟩
  | 8 => ⟨((-3382258819/17592186044416), (600380509/2199023255552)), (87/17592186044416), by norm_num⟩
  | 9 => ⟨((302418643/8796093022208), (-3435644989/70368744177664)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-3115033789/562949953421312), (4423565839/562949953421312)), (85/562949953421312), by norm_num⟩
  | 11 => ⟨((227884249/281474976710656), (-2588892571/2251799813685248)), (51/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1956082933/18014398509481984), (1388887285/9007199254740992)), (7/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (355666597235/1267650600228229401496703205376)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222512668887637/79228162514264337593543950336), (3372124588117/633825300114114700748351602688)), (723/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891240479642875/39614081257132168796771975168), (1896609910193/19807040628566084398385987584)), (1627/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891108571971055/2475880078570760549798248448), (4029798100099/2475880078570760549798248448)), (6917/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772774095676601/154742504910672534362390528), (4029237847823/154742504910672534362390528)), (3459/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551037099703939/9671406556917033397649408), (3776815205287/9671406556917033397649408)), (811/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260086127972041/604462909807314587353088), (3304118017421/604462909807314587353088)), (5679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889898947542489/75557863725914323419136), (5368075593361/75557863725914323419136)), (9231/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299118366466619/4722366482869645213696), (2012540005959/2361183241434822606848)), (6927/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811808533561295/295147905179352825856), (5532897866805/590295810358705651712)), (1191/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1826182730354189/73786976294838206464), (6913741540639/73786976294838206464)), (5959/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825699275547665/9223372036854775808), (7774685533035/9223372036854775808)), (13417/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596942475523667/1152921504606846976), (3885296622553/576460752303423488)), (6715/576460752303423488), by norm_num⟩
  | 5 => ⟨((598580918716665/72057594037927936), (6794665045559/144115188075855872)), (5883/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495497102264937/36028797018963968), (10182788941697/36028797018963968)), (17677/36028797018963968), by norm_num⟩
  | 3 => ⟨((747030748705337/4503599627370496), (1589046237347/1125899906842624)), (11073/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118746713814273/2251799813685248), (12688193194287/2251799813685248)), (22221/2251799813685248), by norm_num⟩
  | 1 => ⟨((557566632234063/562949953421312), (1185740023087/70368744177664)), (33519/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104220312128417/1125899906842624), (18850919914479/562949953421312)), (67791/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104220312128417/1125899906842624), (18850919914479/562949953421312)), (258602146628951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1081695683238673/1125899906842624), (73951755552577/1125899906842624)), (17189/140737488355328), by norm_num⟩
  | 2 => ⟨((517184823406623/562949953421312), (71048318116901/562949953421312)), (282291/1125899906842624), by norm_num⟩
  | 3 => ⟨((466173372002209/562949953421312), (261089723058397/1125899906842624)), (147485/281474976710656), by norm_num⟩
  | 4 => ⟨((711522048008221/1125899906842624), (432411712101753/1125899906842624)), (1250655/1125899906842624), by norm_num⟩
  | 5 => ⟨((141790462055555/562949953421312), (546532538296739/1125899906842624)), (5082749/2251799813685248), by norm_num⟩
  | 6 => ⟨((-193871296702999/1125899906842624), (1101243201638481/4503599627370496)), (7494909/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-4473537711/268435456)), (1/268435456), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-90182207/67108864), (-4980312377/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((70219397674083/281474976710656), (171586447142281/2251799813685248)), (2925495/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3839607871/8589934592), (-1172796789/8589934592)), (41/8589934592), by norm_num⟩
  | 2 => ⟨((3439826881/8589934592), (262671219/2147483648)), (19/4294967296), by norm_num⟩
  | 3 => ⟨((-4108894925/17179869184), (-1255049717/17179869184)), (47/17179869184), by norm_num⟩
  | 4 => ⟨((3681075695/34359738368), (1124373607/34359738368)), (11/8589934592), by norm_num⟩
  | 5 => ⟨((-5276481787/137438953472), (-805842823/68719476736)), (65/137438953472), by norm_num⟩
  | 6 => ⟨((1575697701/137438953472), (1925168679/549755813888)), (5/34359738368), by norm_num⟩
  | 7 => ⟨((-6453191489/2199023255552), (-246388515/274877906944)), (21/549755813888), by norm_num⟩
  | 8 => ⟨((5781283479/8796093022208), (441468955/2199023255552)), (77/8796093022208), by norm_num⟩
  | 9 => ⟨((-4603853075/35184372088832), (-703116605/17592186044416)), (63/35184372088832), by norm_num⟩
  | 10 => ⟨((3299598937/140737488355328), (251963167/35184372088832)), (23/70368744177664), by norm_num⟩
  | 11 => ⟨((-2149850051/562949953421312), (-656665295/562949953421312)), (61/1125899906842624), by norm_num⟩
  | 12 => ⟨((5136018915/9007199254740992), (1568781681/9007199254740992)), (75/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646016907/5070602400912917605986812821504), (386154717027/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779896234244981/633825300114114700748351602688), (228772603197/316912650057057350374175801344)), (2883/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472752525353475/9903520314283042199192993792), (514676974925/39614081257132168796771975168)), (12973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472716066874613/618970019642690137449562112), (546769305685/2475880078570760549798248448)), (13785/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772530322456707/154742504910672534362390528), (136671242861/38685626227668133590597632)), (13785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550809126564039/9671406556917033397649408), (512427573725/9671406556917033397649408)), (3231/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78742950968809/37778931862957161709568), (224142280199/302231454903657293676544)), (11309/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889576771843075/75557863725914323419136), (364147258287/37778931862957161709568)), (9189/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162359707392723/590295810358705651712), (546074023427/4722366482869645213696)), (1723/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202910949484509/73786976294838206464), (750613209387/590295810358705651712)), (9477/295147905179352825856), by norm_num⟩
  | 8 => ⟨((14263852669525/576460752303423488), (468954397253/36893488147419103232)), (11847/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825241580041007/9223372036854775808), (1054655763293/9223372036854775808)), (26659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399122160204959/288230376151711744), (527020785475/576460752303423488)), (26663/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598384535082673/72057594037927936), (921595883397/144115188075855872)), (23333/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494916614301685/36028797018963968), (1381014029857/36028797018963968)), (547/562949953421312), by norm_num⟩
  | 3 => ⟨((1493351017788351/9007199254740992), (3366905399/17592186044416)), (43773/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236117740221455/4503599627370496), (3440485871979/4503599627370496)), (87587/4503599627370496), by norm_num⟩
  | 1 => ⟨((2228315760757253/2251799813685248), (5142702931159/2251799813685248)), (131483/2251799813685248), by norm_num⟩
  | 0 => ⟨((2204987642775991/2251799813685248), (1276690688899/281474976710656)), (263379/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2204987642775991/2251799813685248), (1276690688899/281474976710656)), (1004711159712981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2159102314132723/2251799813685248), (10001198776413/1125899906842624)), (518197/2251799813685248), by norm_num⟩
  | 2 => ⟨((2070043117801309/2251799813685248), (38357959337273/2251799813685248)), (1002937/2251799813685248), by norm_num⟩
  | 3 => ⟨((1902303726325291/2251799813685248), (70523702201641/2251799813685248)), (1878137/2251799813685248), by norm_num⟩
  | 4 => ⟨((200605414203351/281474976710656), (59577898833235/1125899906842624)), (3290915/2251799813685248), by norm_num⟩
  | 5 => ⟨((142182041538993/281474976710656), (169843148580731/2251799813685248)), (629889/281474976710656), by norm_num⟩
  | 6 => ⟨((70219397674083/281474976710656), (171586447142281/2251799813685248)), (2925495/1125899906842624), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90182207/67108864), (-4980312377/268435456)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-391763459/268435456), (-5408784251/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((280202222432089/4503599627370496), (-1008282644533905/4503599627370496)), (18975723/4503599627370496), by norm_num⟩
  | 1 => ⟨((-259994673/2147483648), (1871135169/4294967296)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((505926273/4294967296), (-910265229/2147483648)), (9/1073741824), by norm_num⟩
  | 3 => ⟨((-656324713/8589934592), (4723451593/17179869184)), (95/17179869184), by norm_num⟩
  | 4 => ⟨((159643615/4294967296), (-4595706197/34359738368)), (47/17179869184), by norm_num⟩
  | 5 => ⟨((-497043409/34359738368), (894283133/17179869184)), (75/68719476736), by norm_num⟩
  | 6 => ⟨((1289602419/274877906944), (-4640518999/274877906944)), (99/274877906944), by norm_num⟩
  | 7 => ⟨((-1433971677/1099511627776), (5160018867/1099511627776)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((348797505/1099511627776), (-5020466541/4398046511104)), (111/4398046511104), by norm_num⟩
  | 9 => ⟨((-1206628631/17592186044416), (2170972621/8796093022208)), (97/17592186044416), by norm_num⟩
  | 10 => ⟨((117399545/8796093022208), (-3379614125/70368744177664)), (77/70368744177664), by norm_num⟩
  | 11 => ⟨((-1329157621/562949953421312), (4782854855/562949953421312)), (55/281474976710656), by norm_num⟩
  | 12 => ⟨((862140435/2251799813685248), (-775583817/562949953421312)), (145/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693180315/10141204801825835211973625643008), (-846525351455/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444928943306537/158456325028528675187087900672), (-2005671746011/633825300114114700748351602688)), (11551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236350873639229/4951760157141521099596496896), (-2256086681077/39614081257132168796771975168)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890648341050653/2475880078570760549798248448), (-2396734866289/2475880078570760549798248448)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886157130753425/77371252455336267181195264), (-299541630371/19342813113834066795298816)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775303213293959/4835703278458516698824704), (-1123067680417/4835703278458516698824704)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259709710268117/604462909807314587353088), (-1964941652879/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236161007293811/9444732965739290427392), (-1596115063389/37778931862957161709568)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298660890143163/4722366482869645213696), (-1196736355691/2361183241434822606848)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405747289693803/147573952589676412928), (-3289887982201/590295810358705651712)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1825399526301503/73786976294838206464), (-4110655035127/73786976294838206464)), (23769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824820481239519/9223372036854775808), (-2311071757071/4611686018427387904)), (209/72057594037927936), by norm_num⟩
  | 6 => ⟨((798033283278445/576460752303423488), (-1154803901761/288230376151711744)), (26767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196398659697029/144115188075855872), (-4038521607449/144115188075855872)), (11719/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494358812382193/36028797018963968), (-189100091549/1125899906842624)), (35191/36028797018963968), by norm_num⟩
  | 3 => ⟨((746324975101741/4503599627370496), (-7552499951721/9007199254740992)), (2753/562949953421312), by norm_num⟩
  | 2 => ⟨((1117352101099871/2251799813685248), (-15070530287795/4503599627370496)), (44137/2251799813685248), by norm_num⟩
  | 1 => ⟨((2226167095734591/2251799813685248), (-22519766626687/2251799813685248)), (66429/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100288886502273/1125899906842624), (-44696288887161/2251799813685248)), (133755/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100288886502273/1125899906842624), (-44696288887161/2251799813685248)), (510234837058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2149633705173565/2251799813685248), (-21839787725159/562949953421312)), (266735/1125899906842624), by norm_num⟩
  | 2 => ⟨((2048713840872973/2251799813685248), (-166791181072191/2251799813685248)), (1059925/2251799813685248), by norm_num⟩
  | 3 => ⟨((1851589594404249/2251799813685248), (-37937142449501/281474976710656)), (2085683/2251799813685248), by norm_num⟩
  | 4 => ⟨((1481603067949037/2251799813685248), (-499113768632695/2251799813685248)), (1996105/1125899906842624), by norm_num⟩
  | 5 => ⟨((216053075088015/562949953421312), (-328398859600035/1125899906842624)), (438951/140737488355328), by norm_num⟩
  | 6 => ⟨((280202222432089/4503599627370496), (-1008282644533905/4503599627370496)), (18975723/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-391763459/268435456), (-5408784251/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-418646879/268435456), (-5779943471/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-848695171292059/4503599627370496), (-419619876576285/4503599627370496)), (10495355/2251799813685248), by norm_num⟩
  | 1 => ⟨((3366111747/8589934592), (1664304739/8589934592)), (85/8589934592), by norm_num⟩
  | 2 => ⟨((-3499816301/8589934592), (-865206103/4294967296)), (91/8589934592), by norm_num⟩
  | 3 => ⟨((4851775603/17179869184), (599715171/4294967296)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((-2522245935/17179869184), (-9742755/134217728)), (137/34359738368), by norm_num⟩
  | 5 => ⟨((4195890381/68719476736), (2074571723/68719476736)), (117/68719476736), by norm_num⟩
  | 6 => ⟨((-727092397/34359738368), (-1437983541/137438953472)), (83/137438953472), by norm_num⟩
  | 7 => ⟨((215992305/34359738368), (53396477/17179869184)), (101/549755813888), by norm_num⟩
  | 8 => ⟨((-1796573487/1099511627776), (-1776557639/2199023255552)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((1660386463/4398046511104), (410471973/2199023255552)), (101/8796093022208), by norm_num⟩
  | 10 => ⟨((-5524282539/70368744177664), (-341420989/8796093022208)), (171/70368744177664), by norm_num⟩
  | 11 => ⟨((2088622291/140737488355328), (516338173/70368744177664)), (33/70368744177664), by norm_num⟩
  | 12 => ⟨((-2895445305/1125899906842624), (-1431593395/1125899906842624)), (47/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238520483/10141204801825835211973625643008), (-3494140362959/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779554238826037/633825300114114700748351602688), (-517331041311/79228162514264337593543950336)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945312440488791/19807040628566084398385987584), (-1163828625195/9903520314283042199192993792)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890454363798081/2475880078570760549798248448), (-2472740929949/1237940039285380274899124224)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443029934065629/38685626227668133590597632), (-2472296624883/77371252455336267181195264)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550423477224179/9671406556917033397649408), (-4634612029039/9671406556917033397649408)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314887261989563/151115727451828646838272), (-4054341389001/604462909807314587353088)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889025892268191/75557863725914323419136), (-6586534514887/75557863725914323419136)), (18483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20288489260679/73786976294838206464), (-1234587984527/1180591620717411303424)), (6935/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811357971312575/295147905179352825856), (-6787716901165/590295810358705651712)), (19083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912527843851125/36893488147419103232), (-8480870654449/73786976294838206464)), (23871/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824430478740031/9223372036854775808), (-9535788294185/9223372036854775808)), (105/36028797018963968), by norm_num⟩
  | 6 => ⟨((398918147393023/288230376151711744), (-4764649716105/576460752303423488)), (841/36028797018963968), by norm_num⟩
  | 5 => ⟨((598024733123937/72057594037927936), (-520677326129/9007199254740992)), (23583/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493826114293881/36028797018963968), (-12481656743667/36028797018963968)), (8861/9007199254740992), by norm_num⟩
  | 3 => ⟨((745984266024055/4503599627370496), (-3894130924597/2251799813685248)), (44427/9007199254740992), by norm_num⟩
  | 2 => ⟨((279161862790587/562949953421312), (-15538205354603/2251799813685248)), (44613/2251799813685248), by norm_num⟩
  | 1 => ⟨((555984398018651/562949953421312), (-11605760855755/562949953421312)), (33691/562949953421312), by norm_num⟩
  | 0 => ⟨((1097830087590935/1125899906842624), (-11509990396683/281474976710656)), (136619/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1097830087590935/1125899906842624), (-11509990396683/281474976710656)), (521160130027389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((133572178113385/140737488355328), (-89784277899421/1125899906842624)), (8675/35184372088832), by norm_num⟩
  | 2 => ⟨((503506790245079/562949953421312), (-170426255285791/1125899906842624)), (571209/1125899906842624), by norm_num⟩
  | 3 => ⟨((874883492586127/1125899906842624), (-304861120427933/1125899906842624)), (1194715/1125899906842624), by norm_num⟩
  | 4 => ⟨((74660369314819/140737488355328), (-947572551246303/2251799813685248)), (1251851/562949953421312), by norm_num⟩
  | 5 => ⟨((58741230897021/562949953421312), (-502681392537129/1125899906842624)), (4763547/1125899906842624), by norm_num⟩
  | 6 => ⟨((-848695171292059/4503599627370496), (-419619876576285/4503599627370496)), (10495355/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-418646879/268435456), (-5779943471/268435456)), (1/134217728), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile023Terms0
