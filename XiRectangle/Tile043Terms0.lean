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
namespace Reinmann.XiRectangle.Tile043Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-10175445/16777216), (-650756047/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-73911430673991/140737488355328), (330146656093111/2251799813685248)), (26011263/1125899906842624), by norm_num⟩
  | 1 => ⟨((1563461297/4294967296), (-54559761/536870912)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-541854395/4294967296), (75635889/2147483648)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((500779795/17179869184), (-279609617/34359738368)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-347114103/68719476736), (387621235/274877906944)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((384961859/549755813888), (-214942853/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((-355780303/4398046511104), (397298753/17592186044416)), (19/4398046511104), by norm_num⟩
  | 7 => ⟨((563675689/70368744177664), (-314727441/140737488355328)), (31/70368744177664), by norm_num⟩
  | 8 => ⟨((-781420429/1125899906842624), (436304877/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 9 => ⟨((962914431/18014398509481984), (-268820885/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1067906277/288230376151711744), (149065951/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((538339073/2305843009213693952), (-150290391/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-995061895/73786976294838206464), (277795629/73786976294838206464)), (1/1152921504606846976), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (1868824278705/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445256140368179/158456325028528675187087900672), (554253765847/79228162514264337593543950336)), (2895/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((946139364265705/19807040628566084398385987584), (4987981758121/39614081257132168796771975168)), (26061/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946105640850463/1237940039285380274899124224), (5299398901607/2475880078570760549798248448)), (13849/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886938160947367/77371252455336267181195264), (662378182497/19342813113834066795298816)), (6927/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((388017480761363/2417851639229258349412352), (1241859838169/2417851639229258349412352)), (12993/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630494667325121/302231454903657293676544), (4346112154153/604462909807314587353088)), (22747/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891365695105567/75557863725914323419136), (3530843396043/37778931862957161709568)), (36981/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300217584245415/4722366482869645213696), (5295612258751/4722366482869645213696)), (27753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625127121837817/590295810358705651712), (3640202475225/295147905179352825856)), (38185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828068244103479/73786976294838206464), (9098911497267/73786976294838206464)), (47769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228477206662783/1152921504606846976), (5117039879187/4611686018427387904)), (26897/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599057321650695/1152921504606846976), (10231330702657/1152921504606846976)), (13465/288230376151711744), by norm_num⟩
  | 5 => ⟨((299752088642025/36028797018963968), (8949315549693/144115188075855872)), (47203/144115188075855872), by norm_num⟩
  | 4 => ⟨((46820591599131/1125899906842624), (419305012297/1125899906842624)), (35477/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497499875942275/9007199254740992), (1047580842811/562949953421312)), (22239/2251799813685248), by norm_num⟩
  | 2 => ⟨((561082114832643/1125899906842624), (16744864342429/2251799813685248)), (44675/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120207377729677/1125899906842624), (12537991999407/562949953421312)), (67507/562949953421312), by norm_num⟩
  | 0 => ⟨((1114159878946169/1125899906842624), (12496321107103/281474976710656)), (273991/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114159878946169/1125899906842624), (12496321107103/281474976710656)), (1045192722800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100323127895167/1125899906842624), (49464075899985/562949953421312)), (283299/562949953421312), by norm_num⟩
  | 2 => ⟨((266658740991065/281474976710656), (48340413194761/281474976710656)), (75439/70368744177664), by norm_num⟩
  | 3 => ⟨((977281737833375/1125899906842624), (183183512398029/562949953421312)), (1350783/562949953421312), by norm_num⟩
  | 4 => ⟨((91133189688531/140737488355328), (636013557691113/1125899906842624)), (3224049/562949953421312), by norm_num⟩
  | 5 => ⟨((225638677968943/2251799813685248), (1647377536003821/2251799813685248)), (31271569/2251799813685248), by norm_num⟩
  | 6 => ⟨((-73911430673991/140737488355328), (330146656093111/2251799813685248)), (26011263/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-650756047/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-64510795/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1624425368806711/4503599627370496), (-285984268167973/2251799813685248)), (74311585/2251799813685248), by norm_num⟩
  | 1 => ⟨((1662051/4194304), (149815479/1073741824)), (5/134217728), by norm_num⟩
  | 2 => ⟨((-934886223/4294967296), (-329178253/4294967296)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((684718329/8589934592), (482185699/17179869184)), (67/8589934592), by norm_num⟩
  | 4 => ⟨((-1504479941/68719476736), (-264867567/34359738368)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((1322272121/274877906944), (232789411/137438953472)), (135/274877906944), by norm_num⟩
  | 6 => ⟨((-484221467/549755813888), (-21312109/68719476736)), (101/1099511627776), by norm_num⟩
  | 7 => ⟨((607967605/4398046511104), (428137049/8796093022208)), (129/8796093022208), by norm_num⟩
  | 8 => ⟨((-333960341/17592186044416), (-470356623/70368744177664)), (9/4398046511104), by norm_num⟩
  | 9 => ⟨((326127053/140737488355328), (459324059/562949953421312)), (143/562949953421312), by norm_num⟩
  | 10 => ⟨((-573259501/2251799813685248), (-403695245/4503599627370496)), (1/35184372088832), by norm_num⟩
  | 11 => ⟨((229014521/9007199254740992), (322548769/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1341856891/576460752303423488), (-236237361/288230376151711744)), (155/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-456409665353/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780476952518715/633825300114114700748351602688), (-2164518253319/316912650057057350374175801344)), (46313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472915687823985/9903520314283042199192993792), (-1217429976687/9903520314283042199192993792)), (13029/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236444611870525/309485009821345068724781056), (-1293391621365/618970019642690137449562112)), (55389/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27706594304241/2417851639229258349412352), (-5172991482231/154742504910672534362390528)), (55407/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387864159046649/2417851639229258349412352), (-4849068411537/9671406556917033397649408)), (51963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260452815401627/604462909807314587353088), (-4242323574763/604462909807314587353088)), (45487/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945247025839555/37778931862957161709568), (-1723157315493/18889465931478580854784)), (36975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299564027174783/4722366482869645213696), (-2584234165585/2361183241434822606848)), (27747/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812114383204619/295147905179352825856), (-888126544529/73786976294838206464)), (76355/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913472864378877/36893488147419103232), (-2219704195167/18446744073709551616)), (95519/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28539928349137/144115188075855872), (-2496324977521/2305843009213693952)), (107563/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199724477840017/144115188075855872), (-9981085623347/1152921504606846976)), (26923/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197905377619295/144115188075855872), (-8728704625653/144115188075855872)), (94377/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496606140182699/36028797018963968), (-13083555817525/36028797018963968)), (141859/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495436829143341/9007199254740992), (-16337794180805/9007199254740992)), (88919/4503599627370496), by norm_num⟩
  | 2 => ⟨((140013202382799/281474976710656), (-16312771200835/2251799813685248)), (89305/1125899906842624), by norm_num⟩
  | 1 => ⟨((34910332297435/35184372088832), (-6101608817373/281474976710656)), (269847/1125899906842624), by norm_num⟩
  | 0 => ⟨((277012890507317/281474976710656), (-48561005877561/1125899906842624)), (547443/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277012890507317/281474976710656), (-48561005877561/1125899906842624)), (2088329319480514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088391681512899/1125899906842624), (-47791191818497/562949953421312)), (562377/562949953421312), by norm_num⟩
  | 2 => ⟨((1044018614071215/1125899906842624), (-92398152462251/562949953421312)), (2365539/1125899906842624), by norm_num⟩
  | 3 => ⟨((468880575349853/562949953421312), (-342713914407895/1125899906842624)), (1290883/281474976710656), by norm_num⟩
  | 4 => ⟨((676741461654067/1125899906842624), (-71361537731451/140737488355328)), (11744871/1125899906842624), by norm_num⟩
  | 5 => ⟨((234587435003163/2251799813685248), (-1372578462629235/2251799813685248)), (13014743/562949953421312), by norm_num⟩
  | 6 => ⟨((-1624425368806711/4503599627370496), (-285984268167973/2251799813685248)), (74311585/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-257855983/16777216)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-10175445/8388608), (-650756047/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((286327734643257/1125899906842624), (-693535516918359/4503599627370496)), (64289973/4503599627370496), by norm_num⟩
  | 1 => ⟨((-378546261/1073741824), (114613101/536870912)), (11/536870912), by norm_num⟩
  | 2 => ⟨((524776547/2147483648), (-635549983/4294967296)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-15156141/134217728), (587372905/8589934592)), (15/2147483648), by norm_num⟩
  | 4 => ⟨((336173965/8589934592), (-407135873/17179869184)), (43/17179869184), by norm_num⟩
  | 5 => ⟨((-745657715/68719476736), (112882033/17179869184)), (49/68719476736), by norm_num⟩
  | 6 => ⟨((689134057/274877906944), (-208650301/137438953472)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((-272955045/549755813888), (661144539/2199023255552)), (19/549755813888), by norm_num⟩
  | 8 => ⟨((756792079/8796093022208), (-458270473/8796093022208)), (55/8796093022208), by norm_num⟩
  | 9 => ⟨((-932565859/70368744177664), (564709131/70368744177664)), (35/35184372088832), by norm_num⟩
  | 10 => ⟨((1034248633/562949953421312), (-626282467/562949953421312)), (5/35184372088832), by norm_num⟩
  | 11 => ⟨((-1042744035/4503599627370496), (315713401/2251799813685248)), (83/4503599627370496), by norm_num⟩
  | 12 => ⟨((963700117/36028797018963968), (-583562277/36028797018963968)), (79/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (-354626634533/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780097890213313/633825300114114700748351602688), (-840557925797/633825300114114700748351602688)), (23071/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891236922900747/39614081257132168796771975168), (-945525431017/39614081257132168796771975168)), (6489/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891105214266773/2475880078570760549798248448), (-1004496402757/2475880078570760549798248448)), (6895/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886385605898603/77371252455336267181195264), (-502178257195/77371252455336267181195264)), (13791/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775517449659683/4835703278458516698824704), (-470717813299/4835703278458516698824704)), (51719/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315021176419523/151115727451828646838272), (-823607596595/604462909807314587353088)), (22629/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889897579073829/75557863725914323419136), (-334520956183/18889465931478580854784)), (73551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162389770572945/590295810358705651712), (-1003319225303/4722366482869645213696)), (55169/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202952266057385/73786976294838206464), (-1379168129839/590295810358705651712)), (75867/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826186063951537/73786976294838206464), (-861683328311/36893488147419103232)), (741/576460752303423488), by norm_num⟩
  | 7 => ⟨((228213222874267/1152921504606846976), (-484492936531/2305843009213693952)), (106725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596952425845849/1152921504606846976), (-968476279647/576460752303423488)), (53375/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197174412305697/144115188075855872), (-211710947441/18014398509481984)), (93435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495523689023015/36028797018963968), (-1269120618455/18014398509481984)), (140209/36028797018963968), by norm_num⟩
  | 3 => ⟨((747054110569611/4503599627370496), (-3168797608217/9007199254740992)), (175361/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118813617990123/2251799813685248), (-6325598563991/4503599627370496)), (351021/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115283879609063/1125899906842624), (-9458459217983/2251799813685248)), (263641/1125899906842624), by norm_num⟩
  | 0 => ⟨((552360712911485/562949953421312), (-9398740725523/1125899906842624)), (528787/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((552360712911485/562949953421312), (-9398740725523/1125899906842624)), (2017162327293014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2167725718651621/2251799813685248), (-9221947876661/562949953421312)), (2093019/2251799813685248), by norm_num⟩
  | 2 => ⟨((1043093185635657/1125899906842624), (-35510534225663/1125899906842624)), (4098321/2251799813685248), by norm_num⟩
  | 3 => ⟨((1930513341858655/2251799813685248), (-131595343578791/2251799813685248)), (7852323/2251799813685248), by norm_num⟩
  | 4 => ⟨((823688768001907/1125899906842624), (-225638677968947/2251799813685248)), (14381691/2251799813685248), by norm_num⟩
  | 5 => ⟨((1182582890783845/2251799813685248), (-330146656093115/2251799813685248)), (5981247/562949953421312), by norm_num⟩
  | 6 => ⟨((286327734643257/1125899906842624), (-693535516918359/4503599627370496)), (64289973/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-650756047/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-47253303/33554432), (-377752187/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-953303488240529/4503599627370496), (551709640136229/4503599627370496)), (98130337/4503599627370496), by norm_num⟩
  | 1 => ⟨((731603039/2147483648), (-13231373/67108864)), (77/2147483648), by norm_num⟩
  | 2 => ⟨((-294367417/1073741824), (681442347/4294967296)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((157922027/1073741824), (-91394929/1073741824)), (69/4294967296), by norm_num⟩
  | 4 => ⟨((-508331395/8589934592), (588377855/17179869184)), (113/17179869184), by norm_num⟩
  | 5 => ⟨((1309004511/68719476736), (-757566101/68719476736)), (37/17179869184), by norm_num⟩
  | 6 => ⟨((-702253829/137438953472), (406418535/137438953472)), (81/137438953472), by norm_num⟩
  | 7 => ⟨((161461991/137438953472), (-747549027/1099511627776)), (151/1099511627776), by norm_num⟩
  | 8 => ⟨((-1039452199/4398046511104), (601566873/4398046511104)), (123/4398046511104), by norm_num⟩
  | 9 => ⟨((743526123/17592186044416), (-430304237/17592186044416)), (45/8796093022208), by norm_num⟩
  | 10 => ⟨((-957327305/140737488355328), (277019181/70368744177664)), (59/70368744177664), by norm_num⟩
  | 11 => ⟨((560275949/562949953421312), (-648502069/1125899906842624)), (35/281474976710656), by norm_num⟩
  | 12 => ⟨((-1202305805/9007199254740992), (347907939/4503599627370496)), (19/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (3408877777757/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779788182943413/633825300114114700748351602688), (504833278539/79228162514264337593543950336)), (46299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890888055346305/39614081257132168796771975168), (4542910576307/39614081257132168796771975168)), (52099/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945366988176857/1237940039285380274899124224), (4826146324199/2475880078570760549798248448)), (27685/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886199668637727/77371252455336267181195264), (4825363036067/154742504910672534362390528)), (55387/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48458924714599/302231454903657293676544), (4522945577775/9671406556917033397649408)), (51943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259778385041409/604462909807314587353088), (3956745083927/604462909807314587353088)), (45467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472349635440543/18889465931478580854784), (6428150145821/75557863725914323419136)), (73917/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649371389672299/2361183241434822606848), (4819747011701/4722366482869645213696)), (13867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((50721880495241/18446744073709551616), (1656233233721/147573952589676412928)), (76315/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912767964371699/36893488147419103232), (4138918584115/36893488147419103232)), (11933/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824970679952275/9223372036854775808), (145437330171/144115188075855872)), (53747/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596212702527603/1152921504606846976), (9302266569795/1152921504606846976)), (107615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196521964686023/144115188075855872), (8133044746521/144115188075855872)), (23575/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494534658387877/36028797018963968), (1523336073329/4503599627370496)), (35431/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492853849718111/9007199254740992), (7605409961335/4503599627370496)), (177635/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117532212774323/2251799813685248), (15177002108161/2251799813685248)), (44589/562949953421312), by norm_num⟩
  | 1 => ⟨((556647252561235/562949953421312), (5670234058647/281474976710656)), (269339/1125899906842624), by norm_num⟩
  | 0 => ⟨((137559439328931/140737488355328), (45023476026723/1125899906842624)), (545921/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137559439328931/140737488355328), (45023476026723/1125899906842624)), (2082523350242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268456200582761/281474976710656), (88013566125875/1125899906842624)), (1110849/1125899906842624), by norm_num⟩
  | 2 => ⟨((254319525056859/281474976710656), (41971382035463/281474976710656)), (2292615/1125899906842624), by norm_num⟩
  | 3 => ⟨((894101843800563/1125899906842624), (75844340196617/281474976710656)), (4826583/1125899906842624), by norm_num⟩
  | 4 => ⟨((1256559805628761/2251799813685248), (481837250359493/1125899906842624)), (20533737/2251799813685248), by norm_num⟩
  | 5 => ⟨((288779667639095/2251799813685248), (1075508254289341/2251799813685248)), (40491795/2251799813685248), by norm_num⟩
  | 6 => ⟨((-953303488240529/4503599627370496), (551709640136229/4503599627370496)), (98130337/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-377752187/16777216)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-105212575/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1873924256728087/9007199254740992), (31108811747159/2251799813685248)), (30604307/4503599627370496), by norm_num⟩
  | 1 => ⟨((-800519355/2147483648), (-53157337/2147483648)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((1434338135/4294967296), (47622581/2147483648)), (25/2147483648), by norm_num⟩
  | 3 => ⟨((-1713325957/8589934592), (-113770947/8589934592)), (31/4294967296), by norm_num⟩
  | 4 => ⟨((383733501/4294967296), (50962543/8589934592)), (57/17179869184), by norm_num⟩
  | 5 => ⟨((-1100093015/34359738368), (-73050095/34359738368)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((1314068051/137438953472), (5453675/8589934592)), (13/34359738368), by norm_num⟩
  | 7 => ⟨((-1345425071/549755813888), (-44670509/274877906944)), (55/549755813888), by norm_num⟩
  | 8 => ⟨((75333691/137438953472), (10004851/274877906944)), (51/2199023255552), by norm_num⟩
  | 9 => ⟨((-959856741/8796093022208), (-127475815/17592186044416)), (83/17592186044416), by norm_num⟩
  | 10 => ⟨((343966481/17592186044416), (91362399/70368744177664)), (61/70368744177664), by norm_num⟩
  | 11 => ⟨((-1792887853/562949953421312), (-119054141/562949953421312)), (81/562949953421312), by norm_num⟩
  | 12 => ⟨((1070807929/2251799813685248), (35552731/1125899906842624)), (25/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (86371253997/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222443840223663/79228162514264337593543950336), (102301387659/633825300114114700748351602688)), (23053/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890621456198039/39614081257132168796771975168), (28768284591/9903520314283042199192993792)), (25935/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890451401137083/2475880078570760549798248448), (122245655039/2475880078570760549798248448)), (6889/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772117533902123/154742504910672534362390528), (30555915541/38685626227668133590597632)), (6889/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550422219943649/9671406556917033397649408), (114561321449/9671406556917033397649408)), (12917/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629774377417467/302231454903657293676544), (100217800739/604462909807314587353088)), (22605/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944513464068945/37778931862957161709568), (81405073985/37778931862957161709568)), (36733/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324616352958033/1180591620717411303424), (122069318407/4722366482869645213696)), (55101/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622720975872455/590295810358705651712), (167783112461/590295810358705651712)), (18941/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456266299151841/18446744073709551616), (104817816961/36893488147419103232)), (23677/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824445595185941/9223372036854775808), (235711931509/9223372036854775808)), (26637/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595693222296537/1152921504606846976), (3680497539/18014398509481984)), (13319/144115188075855872), by norm_num⟩
  | 5 => ⟨((598036857775997/72057594037927936), (205927908791/144115188075855872)), (93237/144115188075855872), by norm_num⟩
  | 4 => ⟨((186734356781267/4503599627370496), (308532322941/36028797018963968)), (69931/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492051040525641/9007199254740992), (192518516033/4503599627370496)), (21855/1125899906842624), by norm_num⟩
  | 2 => ⟨((558381110561201/1125899906842624), (384096120051/2251799813685248)), (174859/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224442413738941/2251799813685248), (1147595297787/2251799813685248)), (524677/2251799813685248), by norm_num⟩
  | 0 => ⟨((137331693784411/140737488355328), (2276487171815/2251799813685248)), (1049769/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137331693784411/140737488355328), (2276487171815/2251799813685248)), (4004550942427825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((268016348655483/281474976710656), (4442794067697/2251799813685248)), (1025427/1125899906842624), by norm_num⟩
  | 2 => ⟨((255200144514655/281474976710656), (4230363415489/1125899906842624)), (244605/140737488355328), by norm_num⟩
  | 3 => ⟨((1850992113699209/2251799813685248), (3835471868933/562949953421312)), (3563055/1125899906842624), by norm_num⟩
  | 4 => ⟨((1521421402845989/2251799813685248), (25222235612823/2251799813685248)), (11812509/2251799813685248), by norm_num⟩
  | 5 => ⟨((2055322067090291/4503599627370496), (68165294011943/4503599627370496)), (16226791/2251799813685248), by norm_num⟩
  | 6 => ⟨((1873924256728087/9007199254740992), (31108811747159/2251799813685248)), (30604307/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-841089989/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-57132171/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-814622925104941/9007199254740992), (-1424613472275159/9007199254740992)), (145944953/9007199254740992), by norm_num⟩
  | 1 => ⟨((755874165/4294967296), (165234197/536870912)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((-735431605/4294967296), (-321530901/1073741824)), (17/536870912), by norm_num⟩
  | 3 => ⟨((477027941/4294967296), (834226991/4294967296)), (45/2147483648), by norm_num⟩
  | 4 => ⟨((-116031689/2147483648), (-101458173/1073741824)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((180629793/8589934592), (1263542327/34359738368)), (35/8589934592), by norm_num⟩
  | 6 => ⟨((-468652463/68719476736), (-409789973/34359738368)), (23/17179869184), by norm_num⟩
  | 7 => ⟨((521117477/274877906944), (227832705/68719476736)), (13/34359738368), by norm_num⟩
  | 8 => ⟨((-253511947/549755813888), (-443341973/549755813888)), (103/1099511627776), by norm_num⟩
  | 9 => ⟨((438499085/4398046511104), (191711921/1099511627776)), (45/2199023255552), by norm_num⟩
  | 10 => ⟨((-42663991/2199023255552), (-1193773353/35184372088832)), (71/17592186044416), by norm_num⟩
  | 11 => ⟨((60378395/17592186044416), (422359215/70368744177664)), (51/70368744177664), by norm_num⟩
  | 12 => ⟨((-313309151/562949953421312), (-1095830777/1125899906842624)), (67/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-2722767988223/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779337088533031/633825300114114700748351602688), (-1612116169643/316912650057057350374175801344)), (46259/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945190416597171/19807040628566084398385987584), (-3626706704965/39614081257132168796771975168)), (13013/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890195371990309/2475880078570760549798248448), (-3852705279687/2475880078570760549798248448)), (55317/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885930545958621/77371252455336267181195264), (-3851950924895/154742504910672534362390528)), (27665/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775090683592615/4835703278458516698824704), (-902600648779/2417851639229258349412352)), (25943/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314834392636735/151115727451828646838272), (-1579150495875/302231454903657293676544)), (22707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944341466383523/37778931862957161709568), (-5130736964343/75557863725914323419136)), (2307/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649103348797049/2361183241434822606848), (-3846738595341/4722366482869645213696)), (1731/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1622364078603701/590295810358705651712), (-2643565290713/295147905179352825856)), (76201/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912308664567811/36893488147419103232), (-6605711570161/73786976294838206464)), (95307/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823939346774955/9223372036854775808), (-7427024578555/9223372036854775808)), (53649/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595183981631911/1152921504606846976), (-3710762708763/576460752303423488)), (26849/288230376151711744), by norm_num⟩
  | 5 => ⟨((298906192510675/36028797018963968), (-6487650951919/144115188075855872)), (735/1125899906842624), by norm_num⟩
  | 4 => ⟨((746597366003599/18014398509481984), (-4859557888461/18014398509481984)), (141339/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491189191432725/9007199254740992), (-12127279183095/9007199254740992)), (177057/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115882898823393/2251799813685248), (-12094887122795/2251799813685248)), (177633/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110858789162243/1125899906842624), (-18061460096763/1125899906842624)), (267893/1125899906842624), by norm_num⟩
  | 0 => ⟨((547878233021547/562949953421312), (-8950024202737/281474976710656)), (135393/281474976710656), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((547878233021547/562949953421312), (-8950024202737/281474976710656)), (516483307958507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532640858505385/562949953421312), (-69683259279367/1125899906842624)), (1088587/1125899906842624), by norm_num⟩
  | 2 => ⟨((1003614418214499/1125899906842624), (-32965764381401/281474976710656)), (137169/70368744177664), by norm_num⟩
  | 3 => ⟨((1758333984206265/2251799813685248), (-470164940802477/2251799813685248)), (8853495/2251799813685248), by norm_num⟩
  | 4 => ⟨((318709872765819/562949953421312), (-734263311126535/2251799813685248)), (17523765/2251799813685248), by norm_num⟩
  | 5 => ⟨((60289169096393/281474976710656), (-831395277834257/2251799813685248)), (31270139/2251799813685248), by norm_num⟩
  | 6 => ⟨((-814622925104941/9007199254740992), (-1424613472275159/9007199254740992)), (145944953/9007199254740992), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-1826903191/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-30526335/16777216), (-1952268141/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-499803171645973/4503599627370496), (1064289823396191/9007199254740992)), (99152103/4503599627370496), by norm_num⟩
  | 1 => ⟨((991164663/4294967296), (-1055301891/4294967296)), (199/4294967296), by norm_num⟩
  | 2 => ⟨((-128816811/536870912), (34288103/134217728)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((714312075/4294967296), (-380267231/2147483648)), (37/1073741824), by norm_num⟩
  | 4 => ⟨((-742685101/8589934592), (790743477/8589934592)), (39/2147483648), by norm_num⟩
  | 5 => ⟨((617748101/17179869184), (-328860967/8589934592)), (33/4294967296), by norm_num⟩
  | 6 => ⟨((-856380709/68719476736), (56987263/4294967296)), (185/68719476736), by norm_num⟩
  | 7 => ⟨((1017596355/274877906944), (-541721975/137438953472)), (223/274877906944), by norm_num⟩
  | 8 => ⟨((-529008033/549755813888), (563239589/549755813888)), (59/274877906944), by norm_num⟩
  | 9 => ⟨((977814471/4398046511104), (-520543911/2199023255552)), (221/4398046511104), by norm_num⟩
  | 10 => ⟨((-203330803/4398046511104), (432976253/8796093022208)), (187/17592186044416), by norm_num⟩
  | 11 => ⟨((76875367/8796093022208), (-163699783/17592186044416)), (143/70368744177664), by norm_num⟩
  | 12 => ⟨((-426287551/281474976710656), (113468043/70368744177664)), (201/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (3028395288345/10141204801825835211973625643008)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444788890053455/158456325028528675187087900672), (3585457296293/633825300114114700748351602688)), (69415/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945088285885317/19807040628566084398385987584), (4032979900609/39614081257132168796771975168)), (78109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889978286203865/2475880078570760549798248448), (4284244071399/2475880078570760549798248448)), (41505/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885821970467257/77371252455336267181195264), (2141673712925/77371252455336267181195264)), (10379/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549977718937623/9671406556917033397649408), (125458926511/302231454903657293676544)), (77867/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259159309207421/604462909807314587353088), (877974379141/151115727451828646838272)), (68157/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944196564325783/37778931862957161709568), (713130994847/9444732965739290427392)), (110799/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297989231415087/4722366482869645213696), (2138611972219/2361183241434822606848)), (41569/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622064879144435/590295810358705651712), (2939322591447/295147905179352825856)), (114377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824243055162521/73786976294838206464), (3672250414795/36893488147419103232)), (143065/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823517911798825/9223372036854775808), (8257332230491/9223372036854775808)), (161077/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594762077038065/1152921504606846976), (8250795576199/1152921504606846976)), (20155/144115188075855872), by norm_num⟩
  | 5 => ⟨((298813769256709/36028797018963968), (901511953369/18014398509481984)), (141267/144115188075855872), by norm_num⟩
  | 4 => ⟨((746319572022039/18014398509481984), (5401725265847/18014398509481984)), (106133/18014398509481984), by norm_num⟩
  | 3 => ⟨((745246440969035/4503599627370496), (13478618820033/9007199254740992)), (265973/9007199254740992), by norm_num⟩
  | 2 => ⟨((557591936466147/1125899906842624), (13440113870167/2251799813685248)), (266935/2251799813685248), by norm_num⟩
  | 1 => ⟨((277450882649857/281474976710656), (10032018376923/562949953421312)), (100703/281474976710656), by norm_num⟩
  | 0 => ⟨((273404874027737/281474976710656), (39744309936409/1125899906842624)), (815289/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((273404874027737/281474976710656), (39744309936409/1125899906842624)), (3110080723289107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66303850859797/70368744177664), (38604810198291/562949953421312)), (410347/281474976710656), by norm_num⟩
  | 2 => ⟨((497142788296399/562949953421312), (72749559702125/562949953421312)), (3318265/1125899906842624), by norm_num⟩
  | 3 => ⟨((1718507672295751/2251799813685248), (256981415401823/1125899906842624)), (13436747/2251799813685248), by norm_num⟩
  | 4 => ⟨((298551275733823/562949953421312), (784482761427537/2251799813685248)), (13321407/1125899906842624), by norm_num⟩
  | 5 => ⟨((180014364503593/1125899906842624), (104009391861563/281474976710656)), (46822825/2251799813685248), by norm_num⟩
  | 6 => ⟨((-499803171645973/4503599627370496), (1064289823396191/9007199254740992)), (99152103/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-1952268141/67108864)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile043Terms0
