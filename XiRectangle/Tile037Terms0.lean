/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile037Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-7268175/16777216), (-40031745/4194304)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1449692669167103/2251799813685248), (43529337046651/562949953421312)), (59432411/2251799813685248), by norm_num⟩
  | 1 => ⟨((1916600011/4294967296), (-115097951/2147483648)), (81/4294967296), by norm_num⟩
  | 2 => ⟨((-664242947/4294967296), (19944955/1073741824)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((1227781669/34359738368), (-147464419/34359738368)), (7/4294967296), by norm_num⟩
  | 4 => ⟨((-1702066805/274877906944), (204429093/274877906944)), (5/17179869184), by norm_num⟩
  | 5 => ⟨((1887652491/2199023255552), (-226719119/2199023255552)), (91/2199023255552), by norm_num⟩
  | 6 => ⟨((-218070167/2199023255552), (209532957/17592186044416)), (87/17592186044416), by norm_num⟩
  | 7 => ⟨((172748253/17592186044416), (-165985347/140737488355328)), (71/140737488355328), by norm_num⟩
  | 8 => ⟨((-239479929/281474976710656), (230104551/2251799813685248)), (101/2251799813685248), by norm_num⟩
  | 9 => ⟨((590203867/9007199254740992), (-141774507/18014398509481984)), (1/281474976710656), by norm_num⟩
  | 10 => ⟨((-327278517/72057594037927936), (2456765/4503599627370496)), (73/288230376151711744), by norm_num⟩
  | 11 => ⟨((1319867237/4611686018427387904), (-39631121/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-1219816339/73786976294838206464), (36626933/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453608229/10141204801825835211973625643008), (3936569070009/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781291236737939/633825300114114700748351602688), (4671344933527/633825300114114700748351602688)), (11583/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892578648663569/39614081257132168796771975168), (5255022700081/39614081257132168796771975168)), (6517/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946264922229209/1237940039285380274899124224), (5583210443497/2475880078570760549798248448)), (13853/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887097384708005/77371252455336267181195264), (2791463783425/77371252455336267181195264)), (27715/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552368345124603/9671406556917033397649408), (327105858759/604462909807314587353088)), (12997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261250331459749/604462909807314587353088), (2289590417327/302231454903657293676544)), (22755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891789585135213/75557863725914323419136), (1860150854725/18889465931478580854784)), (36995/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300535300625161/4722366482869645213696), (1394989274175/1180591620717411303424)), (6941/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406390913713457/147573952589676412928), (1917908635759/147573952589676412928)), (19101/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828613419602963/73786976294838206464), (1198541394297/9223372036854775808)), (2987/4611686018427387904), by norm_num⟩
  | 7 => ⟨((457107575126487/2305843009213693952), (10785202235477/9223372036854775808)), (53823/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799834562089377/576460752303423488), (10783108677715/1152921504606846976)), (53893/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199542730650737/144115188075855872), (589553565909/9007199254740992)), (47235/144115188075855872), by norm_num⟩
  | 4 => ⟨((374764647717889/9007199254740992), (3536135013855/9007199254740992)), (35505/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498496112971331/9007199254740992), (2209040834917/1125899906842624)), (89039/9007199254740992), by norm_num⟩
  | 2 => ⟨((280788862662379/562949953421312), (17659716763645/2251799813685248)), (89455/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121681635546273/1125899906842624), (26457745180069/1125899906842624)), (16903/140737488355328), by norm_num⟩
  | 0 => ⟨((1117057900532437/1125899906842624), (26393171653821/562949953421312)), (4291/17592186044416), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117057900532437/1125899906842624), (26393171653821/562949953421312)), (16368866033905739/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1105810514358779/1125899906842624), (104743594832291/1125899906842624)), (285343/562949953421312), by norm_num⟩
  | 2 => ⟨((134541896846589/140737488355328), (51437329274721/281474976710656)), (1227191/1125899906842624), by norm_num⟩
  | 3 => ⟨((495676667252075/562949953421312), (393383507420341/1125899906842624)), (1397427/562949953421312), by norm_num⟩
  | 4 => ⟨((367719565873411/562949953421312), (692747284993965/1125899906842624)), (3437373/562949953421312), by norm_num⟩
  | 5 => ⟨((54153939677457/1125899906842624), (452503334177061/562949953421312)), (34882033/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1449692669167103/2251799813685248), (43529337046651/562949953421312)), (59432411/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/16777216), (-40031745/4194304)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-46079139/67108864), (-1015181035/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-947563694550571/2251799813685248), (-155402287465403/562949953421312)), (75210033/2251799813685248), by norm_num⟩
  | 1 => ⟨((496389923/1073741824), (5088057/16777216)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-1090680139/4294967296), (-715494649/4294967296)), (23/1073741824), by norm_num⟩
  | 3 => ⟨((798823069/8589934592), (524034143/8589934592)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((-109699605/4294967296), (-575710349/34359738368)), (79/34359738368), by norm_num⟩
  | 5 => ⟨((771310939/137438953472), (505985971/137438953472)), (9/17179869184), by norm_num⟩
  | 6 => ⟨((-564914451/549755813888), (-741176541/1099511627776)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((354641119/2199023255552), (465294661/4398046511104)), (35/2199023255552), by norm_num⟩
  | 8 => ⟨((-779226183/35184372088832), (-511178433/35184372088832)), (79/35184372088832), by norm_num⟩
  | 9 => ⟨((380474427/140737488355328), (499188363/281474976710656)), (79/281474976710656), by norm_num⟩
  | 10 => ⟨((-334395105/1125899906842624), (-54841447/281474976710656)), (71/2251799813685248), by norm_num⟩
  | 11 => ⟨((534357195/18014398509481984), (701084947/36028797018963968)), (29/9007199254740992), by norm_num⟩
  | 12 => ⟨((-782735175/288230376151711744), (-513480359/288230376151711744)), (87/288230376151711744), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197885168922433/1267650600228229401496703205376), (-833998942421/2535301200456458802993406410752)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890451437897365/316912650057057350374175801344), (-3957021141131/633825300114114700748351602688)), (17361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236517746444441/4951760157141521099596496896), (-2225676401265/19807040628566084398385987584)), (39071/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473016536252071/618970019642690137449562112), (-4729228316347/2475880078570760549798248448)), (41523/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773731373758937/154742504910672534362390528), (-2364426174471/77371252455336267181195264)), (649/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1551934234490919/9671406556917033397649408), (-554112432639/1208925819614629174706176)), (38953/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630435403733297/302231454903657293676544), (-1939193621541/302231454903657293676544)), (34097/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472793365988103/18889465931478580854784), (-6301629312671/75557863725914323419136)), (55431/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300073739415499/4722366482869645213696), (-2362782706153/2361183241434822606848)), (41595/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624929868980815/590295810358705651712), (-1624146209605/147573952589676412928)), (57227/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827822478558887/73786976294838206464), (-8119128464705/73786976294838206464)), (35793/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913771133772409/4611686018427387904), (-9131814057985/9223372036854775808)), (20151/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199847913890747/144115188075855872), (-9129054360709/1152921504606846976)), (40347/576460752303423488), by norm_num⟩
  | 5 => ⟨((37461566937117/4503599627370496), (-7984813969693/144115188075855872)), (70707/144115188075855872), by norm_num⟩
  | 4 => ⟨((374476176070277/9007199254740992), (-5985496967665/18014398509481984)), (106261/36028797018963968), by norm_num⟩
  | 3 => ⟨((748531250197401/4503599627370496), (-7476411531085/4503599627370496)), (66589/4503599627370496), by norm_num⟩
  | 2 => ⟨((1121734960367303/2251799813685248), (-3734099993851/562949953421312)), (133707/2251799813685248), by norm_num⟩
  | 1 => ⟨((279895929671279/281474976710656), (-11181694248281/562949953421312)), (100941/562949953421312), by norm_num⟩
  | 0 => ⟨((556496707087453/562949953421312), (-44561012070081/1125899906842624)), (204533/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((556496707087453/562949953421312), (-44561012070081/1125899906842624)), (780231477977561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1098471230598367/1125899906842624), (-88100394469437/1125899906842624)), (420567/562949953421312), by norm_num⟩
  | 2 => ⟨((266204250853135/281474976710656), (-171908263142917/1125899906842624)), (886461/562949953421312), by norm_num⟩
  | 3 => ⟨((245200038011461/281474976710656), (-162581807236335/562949953421312)), (486859/140737488355328), by norm_num⟩
  | 4 => ⟨((760491724772745/1125899906842624), (-141629162848465/281474976710656)), (4517775/562949953421312), by norm_num⟩
  | 5 => ⟨((457245880520873/2251799813685248), (-382654996871953/562949953421312)), (5324741/281474976710656), by norm_num⟩
  | 6 => ⟨((-947563694550571/2251799813685248), (-155402287465403/562949953421312)), (75210033/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/67108864), (-1015181035/67108864)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-7268175/8388608), (-40031745/2097152)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((459919210293307/1125899906842624), (-224191015299815/2251799813685248)), (17840901/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1216093841/2147483648), (148198481/1073741824)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((842932017/2147483648), (-410893437/4294967296)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((-1558069203/8589934592), (189873085/4294967296)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((1079971275/17179869184), (-263219987/17179869184)), (3/1073741824), by norm_num⟩
  | 5 => ⟨((-1197726471/68719476736), (291920307/68719476736)), (55/68719476736), by norm_num⟩
  | 6 => ⟨((553467151/137438953472), (-134895825/137438953472)), (53/274877906944), by norm_num⟩
  | 7 => ⟨((-876878161/1099511627776), (213720367/1099511627776)), (11/274877906944), by norm_num⟩
  | 8 => ⟨((607805625/4398046511104), (-74069835/2199023255552)), (63/8796093022208), by norm_num⟩
  | 9 => ⟨((-748975565/35184372088832), (182546835/35184372088832)), (5/4398046511104), by norm_num⟩
  | 10 => ⟨((415320241/140737488355328), (-404901837/562949953421312)), (91/562949953421312), by norm_num⟩
  | 11 => ⟨((-418731715/1125899906842624), (408227733/4503599627370496)), (47/2251799813685248), by norm_num⟩
  | 12 => ⟨((386990277/9007199254740992), (-47160317/4503599627370496)), (89/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582847140111075/10141204801825835211973625643008), (-311412243867/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890316687847911/316912650057057350374175801344), (-92318762755/158456325028528675187087900672)), (46119/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945919653025429/19807040628566084398385987584), (-207701073743/19807040628566084398385987584)), (51885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891745200949181/2475880078570760549798248448), (-220662875029/1237940039285380274899124224)), (55129/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773411147389417/154742504910672534362390528), (-110320461301/38685626227668133590597632)), (27565/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551634784656103/9671406556917033397649408), (-413655087001/9671406556917033397649408)), (25843/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315152387767361/151115727451828646838272), (-361901565033/604462909807314587353088)), (45227/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472687587767163/18889465931478580854784), (-588002614919/75557863725914323419136)), (73497/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324939413634999/1180591620717411303424), (-440925475873/4722366482869645213696)), (27563/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624497282470347/590295810358705651712), (-303074133851/295147905179352825856)), (75801/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913642394733013/36893488147419103232), (-378749494729/36893488147419103232)), (47379/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456735387713457/2305843009213693952), (-425965107659/4611686018427387904)), (26653/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1598187820820953/1152921504606846976), (-53225634105/72057594037927936)), (106623/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198254963476449/144115188075855872), (-744798957383/144115188075855872)), (93307/144115188075855872), by norm_num⟩
  | 4 => ⟨((748571838535589/18014398509481984), (-279119747839/9007199254740992)), (69993/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496131738814233/9007199254740992), (-1394340600205/9007199254740992)), (87513/4503599627370496), by norm_num⟩
  | 2 => ⟨((2241669870592611/4503599627370496), (-2784910337975/4503599627370496)), (350183/4503599627370496), by norm_num⟩
  | 1 => ⟨((559155178567097/562949953421312), (-4167950780345/2251799813685248)), (525603/2251799813685248), by norm_num⟩
  | 0 => ⟨((2221504804233367/2251799813685248), (-1037289642493/281474976710656)), (1052529/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2221504804233367/2251799813685248), (-1037289642493/281474976710656)), (4015079506880950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1095793396724737/1125899906842624), (-4093337090047/562949953421312)), (130281/140737488355328), by norm_num⟩
  | 2 => ⟨((1066432406090639/1125899906842624), (-7967762900737/562949953421312)), (1021957/562949953421312), by norm_num⟩
  | 3 => ⟨((2019760600151877/2251799813685248), (-60375388680659/2251799813685248)), (245611/70368744177664), by norm_num⟩
  | 4 => ⟨((1810013336708285/2251799813685248), (-108307879354941/2251799813685248)), (7260387/1125899906842624), by norm_num⟩
  | 5 => ⟨((724846334583583/1125899906842624), (-174117348186651/2251799813685248)), (24740663/2251799813685248), by norm_num⟩
  | 6 => ⟨((459919210293307/1125899906842624), (-224191015299815/2251799813685248)), (17840901/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/8388608), (-40031745/2097152)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-67504719/67108864), (-1487213335/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-1623279290770957/4503599627370496), (69685579495069/1125899906842624)), (137157235/4503599627370496), by norm_num⟩
  | 1 => ⟨((1245769135/2147483648), (-213917949/2147483648)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((-501247019/1073741824), (172143829/2147483648)), (11/268435456), by norm_num⟩
  | 3 => ⟨((67227163/268435456), (-184703203/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((-865583559/8589934592), (148634169/8589934592)), (157/17179869184), by norm_num⟩
  | 5 => ⟨((1114482397/34359738368), (-191373973/34359738368)), (103/34359738368), by norm_num⟩
  | 6 => ⟨((-597896741/68719476736), (6416761/4294967296)), (7/8589934592), by norm_num⟩
  | 7 => ⟨((1099745923/549755813888), (-188843491/549755813888)), (105/549755813888), by norm_num⟩
  | 8 => ⟨((-1769972783/4398046511104), (151965937/2199023255552)), (171/4398046511104), by norm_num⟩
  | 9 => ⟨((633035845/8796093022208), (-108702107/8796093022208)), (31/4398046511104), by norm_num⟩
  | 10 => ⟨((-815065511/70368744177664), (69979717/35184372088832)), (81/70368744177664), by norm_num⟩
  | 11 => ⟨((954034425/562949953421312), (-5119455/17592186044416)), (97/562949953421312), by norm_num⟩
  | 12 => ⟨((-1023639449/4503599627370496), (87887413/2251799813685248)), (105/4503599627370496), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582665471740547/10141204801825835211973625643008), (3870756885175/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445101704217359/158456325028528675187087900672), (4588919134513/633825300114114700748351602688)), (23163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891583783104851/39614081257132168796771975168), (5162037344505/39614081257132168796771975168)), (52131/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891472908293451/2475880078570760549798248448), (5484097709317/2475880078570760549798248448)), (27703/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110821122218257/9671406556917033397649408), (2741729797749/77371252455336267181195264)), (55425/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551377712110363/9671406556917033397649408), (5140065179077/9671406556917033397649408)), (51981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260383657789529/604462909807314587353088), (4496878619897/604462909807314587353088)), (45503/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945190742478055/37778931862957161709568), (7306155267911/75557863725914323419136)), (18495/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299479439836413/4722366482869645213696), (2739251277913/2361183241434822606848)), (55519/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624112195288101/590295810358705651712), (14709238399/1152921504606846976)), (76391/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826799619910691/73786976294838206464), (9411194616041/73786976294838206464)), (95569/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826390499411645/9223372036854775808), (2645963567233/2305843009213693952)), (107625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597630230542305/1152921504606846976), (330599248825/36028797018963968)), (107763/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598879861870189/72057594037927936), (4625755387849/72057594037927936)), (5903/9007199254740992), by norm_num⟩
  | 4 => ⟨((748193070431035/18014398509481984), (13866717069497/36028797018963968)), (141983/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495159179243727/9007199254740992), (8657453452427/4503599627370496)), (22253/1125899906842624), by norm_num⟩
  | 2 => ⟨((279956001578211/562949953421312), (8643557964553/1125899906842624)), (89421/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116698353783653/1125899906842624), (1616312405577/70368744177664)), (33789/140737488355328), by norm_num⟩
  | 0 => ⟨((1107147839671633/1125899906842624), (51442115024405/1125899906842624)), (274423/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1107147839671633/1125899906842624), (51442115024405/1125899906842624)), (1046840669872093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1086357712846269/1125899906842624), (3161583579237/35184372088832)), (282391/281474976710656), by norm_num⟩
  | 2 => ⟨((129889163299989/140737488355328), (195235014991353/1125899906842624)), (2382787/1125899906842624), by norm_num⟩
  | 3 => ⟨((925161949235583/1125899906842624), (180185912370857/562949953421312)), (2612301/562949953421312), by norm_num⟩
  | 4 => ⟨((644867963691197/1125899906842624), (148060363892645/281474976710656)), (1491341/140737488355328), by norm_num⟩
  | 5 => ⟨((115649265983947/2251799813685248), (1356843673744771/2251799813685248)), (52436691/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1623279290770957/4503599627370496), (69685579495069/1125899906842624)), (137157235/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/67108864), (-1487213335/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-75151839/67108864), (-1655688955/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1316199663340487/4503599627370496), (326918470032069/2251799813685248)), (66356897/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1124531369/2147483648), (-279311783/1073741824)), (59/2147483648), by norm_num⟩
  | 2 => ⟨((1007444865/2147483648), (125114883/536870912)), (55/2147483648), by norm_num⟩
  | 3 => ⟨((-1203399251/4294967296), (-298901035/2147483648)), (17/1073741824), by norm_num⟩
  | 4 => ⟨((539050501/4294967296), (66944845/1073741824)), (63/8589934592), by norm_num⟩
  | 5 => ⟨((-24146221/536870912), (-5997453/268435456)), (47/17179869184), by norm_num⟩
  | 6 => ⟨((922970029/68719476736), (229247855/34359738368)), (29/34359738368), by norm_num⟩
  | 7 => ⟨((-944994451/274877906944), (-469436589/274877906944)), (61/274877906944), by norm_num⟩
  | 8 => ⟨((423300689/549755813888), (420558727/1099511627776)), (7/137438953472), by norm_num⟩
  | 9 => ⟨((-1348360921/8796093022208), (-334906703/4398046511104)), (91/8796093022208), by norm_num⟩
  | 10 => ⟨((966375379/35184372088832), (480057805/35184372088832)), (67/35184372088832), by norm_num⟩
  | 11 => ⟨((-1259281627/281474976710656), (-156390567/70368744177664)), (45/140737488355328), by norm_num⟩
  | 12 => ⟨((752109927/1125899906842624), (373619039/1125899906842624)), (55/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (300286650163/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890120910952795/316912650057057350374175801344), (355933608191/316912650057057350374175801344)), (5767/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891398835465777/39614081257132168796771975168), (400385276435/19807040628566084398385987584)), (51905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472819308443157/618970019642690137449562112), (850721471847/2475880078570760549798248448)), (55151/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772943217133977/154742504910672534362390528), (425306047265/77371252455336267181195264)), (27577/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775598069634065/4835703278458516698824704), (199333161005/2417851639229258349412352)), (25855/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630112887789509/302231454903657293676544), (697549890063/604462909807314587353088)), (22625/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890126789436593/75557863725914323419136), (1133300791051/75557863725914323419136)), (1149/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1299290047658137/4722366482869645213696), (424892540221/2361183241434822606848)), (55157/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811927213777033/295147905179352825856), (584072493215/295147905179352825856)), (37925/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826481377622973/73786976294838206464), (1459717131575/73786976294838206464)), (11853/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826037928105731/9223372036854775808), (410385968199/2305843009213693952)), (53347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798642233750139/576460752303423488), (820373428151/576460752303423488)), (106715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299366208092317/36028797018963968), (1434757348811/144115188075855872)), (11675/18014398509481984), by norm_num⟩
  | 4 => ⟨((93497442897721/2251799813685248), (2150344954379/36028797018963968)), (35037/9007199254740992), by norm_num⟩
  | 3 => ⟨((747326030262051/4503599627370496), (2684799592761/9007199254740992)), (175269/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119356846500065/2251799813685248), (5360215456419/4503599627370496)), (43849/562949953421312), by norm_num⟩
  | 1 => ⟨((2232194390809281/2251799813685248), (8016902569623/2251799813685248)), (263411/1125899906842624), by norm_num⟩
  | 0 => ⟨((1106341950874705/1125899906842624), (7970177292527/1125899906842624)), (528097/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1106341950874705/1125899906842624), (7970177292527/1125899906842624)), (2014530186179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((135883414358237/140737488355328), (3915863853013/281474976710656)), (261331/281474976710656), by norm_num⟩
  | 2 => ⟨((524678080188991/562949953421312), (60492874412081/2251799813685248)), (4095253/2251799813685248), by norm_num⟩
  | 3 => ⟨((1954407310406413/2251799813685248), (14095074090845/281474976710656)), (490857/140737488355328), by norm_num⟩
  | 4 => ⟨((845322253017575/1125899906842624), (195736872710963/2251799813685248)), (14419525/2251799813685248), by norm_num⟩
  | 5 => ⟨((626158219152055/1125899906842624), (293917306917005/2251799813685248)), (24159097/2251799813685248), by norm_num⟩
  | 6 => ⟨((1316199663340487/4503599627370496), (326918470032069/2251799813685248)), (66356897/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-1655688955/67108864)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-81617387/67108864), (-899066531/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-15116559920485/562949953421312), (-1329178724238289/4503599627370496)), (108632423/4503599627370496), by norm_num⟩
  | 1 => ⟨((112211103/2147483648), (616660683/1073741824)), (51/1073741824), by norm_num⟩
  | 2 => ⟨((-54588181/1073741824), (-599983141/1073741824)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((70815797/2147483648), (778342189/2147483648)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((-68900589/4294967296), (-1514583965/8589934592)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((26814871/4294967296), (294724431/4294967296)), (103/17179869184), by norm_num⟩
  | 6 => ⟨((-139144879/68719476736), (-1529352697/68719476736)), (135/68719476736), by norm_num⟩
  | 7 => ⟨((154721961/274877906944), (1700561677/274877906944)), (19/34359738368), by norm_num⟩
  | 8 => ⟨((-150537517/1099511627776), (-1654570113/1099511627776)), (75/549755813888), by norm_num⟩
  | 9 => ⟨((65096107/2199023255552), (715476617/2199023255552)), (33/1099511627776), by norm_num⟩
  | 10 => ⟨((-25334235/4398046511104), (-139225321/2199023255552)), (105/17592186044416), by norm_num⟩
  | 11 => ⟨((143412785/140737488355328), (98516351/8796093022208)), (151/140737488355328), by norm_num⟩
  | 12 => ⟨((-46511399/281474976710656), (-1022421159/562949953421312)), (99/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769420077/5070602400912917605986812821504), (-2164327523129/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222511229586155/79228162514264337593543950336), (-2564997836447/633825300114114700748351602688)), (46227/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945613839269467/19807040628566084398385987584), (-2885304708245/39614081257132168796771975168)), (52013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891095161587845/2475880078570760549798248448), (-1532627565933/1237940039285380274899124224)), (55273/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772760899859157/154742504910672534362390528), (-3064826386355/154742504910672534362390528)), (13821/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551024956517711/9671406556917033397649408), (-2872819227539/9671406556917033397649408)), (51839/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260075730482851/604462909807314587353088), (-2513261350897/604462909807314587353088)), (45371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944941239272885/37778931862957161709568), (-4083195760495/75557863725914323419136)), (18437/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299106388077445/4722366482869645213696), (-3061649705085/4722366482869645213696)), (27665/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623601203170877/590295810358705651712), (-4208554427731/590295810358705651712)), (19027/147573952589676412928), by norm_num⟩
  | 8 => ⟨((913081904630151/36893488147419103232), (-5258872414491/73786976294838206464)), (23795/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912839618958363/4611686018427387904), (-5913728528275/9223372036854775808)), (107139/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596923997047647/1152921504606846976), (-5910600478483/1152921504606846976)), (6701/72057594037927936), by norm_num⟩
  | 5 => ⟨((74821713788979/9007199254740992), (-1292064305005/36028797018963968)), (93901/144115188075855872), by norm_num⟩
  | 4 => ⟨((373869743820961/9007199254740992), (-3872675789709/18014398509481984)), (4407/1125899906842624), by norm_num⟩
  | 3 => ⟨((747022474132135/4503599627370496), (-9669384374769/9007199254740992)), (22073/1125899906842624), by norm_num⟩
  | 2 => ⟨((1118739304386327/2251799813685248), (-4825468213063/1125899906842624)), (88521/1125899906842624), by norm_num⟩
  | 1 => ⟨((278786228341835/281474976710656), (-1803789852577/140737488355328)), (266705/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104334144766545/1125899906842624), (-28676499489763/1125899906842624)), (537993/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1104334144766545/1125899906842624), (-28676499489763/1125899906842624)), (2052280430320357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082451072486519/1125899906842624), (-28127222807695/562949953421312)), (541391/562949953421312), by norm_num⟩
  | 2 => ⟨((1037868246168223/1125899906842624), (-108167137448791/1125899906842624)), (547549/281474976710656), by norm_num⟩
  | 3 => ⟨((473163893302181/562949953421312), (-99709784639591/562949953421312)), (1114683/281474976710656), by norm_num⟩
  | 4 => ⟨((1520149544177259/2251799813685248), (-670454907952815/2251799813685248)), (18149325/2251799813685248), by norm_num⟩
  | 5 => ⟨((826603165055811/2251799813685248), (-905224093653237/2251799813685248)), (551753/35184372088832), by norm_num⟩
  | 6 => ⟨((-15116559920485/562949953421312), (-1329178724238289/4503599627370496)), (108632423/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81617387/67108864), (-899066531/33554432)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-21804525/16777216), (-120095235/4194304)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-287425077088213/1125899906842624), (215457828434617/2251799813685248)), (160333245/4503599627370496), by norm_num⟩
  | 1 => ⟨((284997771/536870912), (-106819143/536870912)), (161/2147483648), by norm_num⟩
  | 2 => ⟨((-1185272409/2147483648), (444248327/2147483648)), (85/1073741824), by norm_num⟩
  | 3 => ⟨((821568229/2147483648), (-307929475/2147483648)), (15/268435456), by norm_num⟩
  | 4 => ⟨((-53387597/268435456), (320160671/4294967296)), (127/4294967296), by norm_num⟩
  | 5 => ⟨((710504877/8589934592), (-532604319/17179869184)), (107/8589934592), by norm_num⟩
  | 6 => ⟨((-984968905/34359738368), (184586591/17179869184)), (151/34359738368), by norm_num⟩
  | 7 => ⟨((146298947/17179869184), (-219335443/68719476736)), (91/68719476736), by norm_num⟩
  | 8 => ⟨((-76055027/34359738368), (890811/1073741824)), (3/8589934592), by norm_num⟩
  | 9 => ⟨((1124636321/2199023255552), (-421521499/2199023255552)), (45/549755813888), by norm_num⟩
  | 10 => ⟨((-467723097/4398046511104), (175305863/4398046511104)), (19/1099511627776), by norm_num⟩
  | 11 => ⟨((1414695037/70368744177664), (-530237519/70368744177664)), (233/70368744177664), by norm_num⟩
  | 12 => ⟨((-245147969/70368744177664), (367532641/281474976710656)), (41/70368744177664), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (1812578413071/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((55623583359369/19807040628566084398385987584), (4295671702577/633825300114114700748351602688)), (69467/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945537629060145/19807040628566084398385987584), (4832046281009/39614081257132168796771975168)), (78171/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945466383596851/1237940039285380274899124224), (5133365159611/2475880078570760549798248448)), (10385/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443149500498891/38685626227668133590597632), (2566297735873/77371252455336267181195264)), (41553/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550871705061863/9671406556917033397649408), (4810990378161/9671406556917033397649408)), (19485/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629970550503001/302231454903657293676544), (2104399305309/302231454903657293676544)), (34113/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944831352045003/37778931862957161709568), (1709440962327/18889465931478580854784)), (110919/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298940681417673/4722366482869645213696), (1281745133095/1180591620717411303424)), (20809/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623371934328473/590295810358705651712), (7047416534913/590295810358705651712)), (114525/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825875091712595/73786976294838206464), (8805997475687/73786976294838206464)), (143269/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228168937845981/1152921504606846976), (618890341955/576460752303423488)), (40333/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596592606360265/1152921504606846976), (9896616793117/1152921504606846976)), (80763/576460752303423488), by norm_num⟩
  | 5 => ⟨((598426673633549/72057594037927936), (8653205285655/144115188075855872)), (70777/72057594037927936), by norm_num⟩
  | 4 => ⟨((373757416794343/9007199254740992), (12967133776383/36028797018963968)), (6649/1125899906842624), by norm_num⟩
  | 3 => ⟨((1493469000115699/9007199254740992), (16186725526503/9007199254740992)), (266725/9007199254740992), by norm_num⟩
  | 2 => ⟨((69883872120565/140737488355328), (8076707161085/1125899906842624)), (267875/2251799813685248), by norm_num⟩
  | 1 => ⟨((278548904283851/281474976710656), (12073380757285/562949953421312)), (404693/1125899906842624), by norm_num⟩
  | 0 => ⟨((551111940629195/562949953421312), (47959598307629/1125899906842624)), (205235/281474976710656), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((551111940629195/562949953421312), (47959598307629/1125899906842624)), (782909394384288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1077002808133259/1125899906842624), (93902156433195/1125899906842624)), (838647/562949953421312), by norm_num⟩
  | 2 => ⟨((1022397663192117/1125899906842624), (179648094033381/1125899906842624)), (3488681/1125899906842624), by norm_num⟩
  | 3 => ⟨((899745650438599/1125899906842624), (326266643101019/1125899906842624)), (7449249/1125899906842624), by norm_num⟩
  | 4 => ⟨((78058927442145/140737488355328), (260730986146513/562949953421312)), (16223239/1125899906842624), by norm_num⟩
  | 5 => ⟨((209684652345429/2251799813685248), (578449462680327/1125899906842624)), (33023809/1125899906842624), by norm_num⟩
  | 6 => ⟨((-287425077088213/1125899906842624), (215457828434617/2251799813685248)), (160333245/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-120095235/4194304)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile037Terms0
