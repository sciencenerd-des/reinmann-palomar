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
namespace Reinmann.XiRectangle.Tile029Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-259295435/134217728), (-5027090237/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((316531574578887/2251799813685248), (4933032058469/140737488355328)), (12559405/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3732347621/8589934592), (-232669243/2147483648)), (19/2147483648), by norm_num⟩
  | 2 => ⟨((2884211237/4294967296), (1438381015/8589934592)), (15/1073741824), by norm_num⟩
  | 3 => ⟨((-5943479585/8589934592), (-1482032261/8589934592)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((2296443465/4294967296), (1145256159/8589934592)), (99/8589934592), by norm_num⟩
  | 5 => ⟨((-2839361697/8589934592), (-1416014163/17179869184)), (31/4294967296), by norm_num⟩
  | 6 => ⟨((1462764591/8589934592), (1458986631/34359738368)), (65/17179869184), by norm_num⟩
  | 7 => ⟨((-1291847843/17179869184), (-1288511319/68719476736)), (117/68719476736), by norm_num⟩
  | 8 => ⟨((1996578263/68719476736), (995710797/137438953472)), (23/34359738368), by norm_num⟩
  | 9 => ⟨((-2742892521/274877906944), (-1367904153/549755813888)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((3391358891/1099511627776), (422824981/549755813888)), (5/68719476736), by norm_num⟩
  | 11 => ⟨((-952984937/1099511627776), (-237630903/1099511627776)), (91/4398046511104), by norm_num⟩
  | 12 => ⟨((1963811265/8796093022208), (979369613/17592186044416)), (3/549755813888), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790729624827833/5070602400912917605986812821504), (79580083725/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778989045275643/633825300114114700748351602688), (376804297021/633825300114114700748351602688)), (5765/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944994831633951/19807040628566084398385987584), (52979143283/4951760157141521099596496896)), (25943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236222529471357/309485009821345068724781056), (225116993957/1237940039285380274899124224)), (13783/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771446497448733/154742504910672534362390528), (450134200995/154742504910672534362390528)), (13783/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387448315050937/2417851639229258349412352), (421894820985/9671406556917033397649408)), (6461/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258998551958593/604462909807314587353088), (184526005483/302231454903657293676544)), (22615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888133105060955/75557863725914323419136), (599510922163/75557863725914323419136)), (18375/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324448817240981/1180591620717411303424), (449459494849/4722366482869645213696)), (6891/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621799893987311/590295810358705651712), (617724687641/590295810358705651712)), (18951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911957195408423/36893488147419103232), (96466615855/9223372036854775808)), (47381/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911575844878953/4611686018427387904), (867618406379/9223372036854775808)), (13327/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594400255064057/1152921504606846976), (866892579773/1152921504606846976)), (26657/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194943423783593/144115188075855872), (189428817023/36028797018963968)), (729/2251799813685248), by norm_num⟩
  | 4 => ⟨((746090761722369/18014398509481984), (70933966301/2251799813685248)), (69997/36028797018963968), by norm_num⟩
  | 3 => ⟨((744969029446715/4503599627370496), (176979047637/1125899906842624)), (87519/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114654752100367/2251799813685248), (2823142206659/4503599627370496)), (87553/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218147498442655/2251799813685248), (4213470762235/2251799813685248)), (262833/2251799813685248), by norm_num⟩
  | 0 => ⟨((546206702598015/562949953421312), (4171176646081/1125899906842624)), (131593/562949953421312), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((546206702598015/562949953421312), (4171176646081/1125899906842624)), (501987459422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2119814811041061/2251799813685248), (4047117559853/562949953421312)), (1025335/2251799813685248), by norm_num⟩
  | 2 => ⟨((498862369917625/562949953421312), (15239613562913/1125899906842624)), (1945217/2251799813685248), by norm_num⟩
  | 3 => ⟨((1767870135896335/2251799813685248), (27009398233075/1125899906842624)), (1750099/1125899906842624), by norm_num⟩
  | 4 => ⟨((693322463223839/1125899906842624), (42409727751633/1125899906842624)), (2831945/1125899906842624), by norm_num⟩
  | 5 => ⟨((850692766012891/2251799813685248), (104462632000287/2251799813685248)), (1850567/562949953421312), by norm_num⟩
  | 6 => ⟨((316531574578887/2251799813685248), (4933032058469/140737488355328)), (12559405/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-259295435/134217728), (-5027090237/134217728)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-263024319/134217728), (-5099383977/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1214589733998065/9007199254740992), (-368090525276789/9007199254740992)), (25485033/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1815957587/4294967296), (275169781/2147483648)), (39/4294967296), by norm_num⟩
  | 2 => ⟨((2846962255/4294967296), (-1725586513/8589934592)), (125/8589934592), by norm_num⟩
  | 3 => ⟨((-2975544561/4294967296), (1803522177/8589934592)), (133/8589934592), by norm_num⟩
  | 4 => ⟨((1166225345/2147483648), (-1413733339/8589934592)), (53/4294967296), by norm_num⟩
  | 5 => ⟨((-2925354259/8589934592), (1773101083/17179869184)), (135/17179869184), by norm_num⟩
  | 6 => ⟨((6114954239/34359738368), (-926591365/17179869184)), (143/34359738368), by norm_num⟩
  | 7 => ⟨((-2674861/33554432), (1660183923/68719476736)), (65/34359738368), by norm_num⟩
  | 8 => ⟨((4294149731/137438953472), (-20333973/2147483648)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((-5984125175/549755813888), (1813534001/549755813888)), (145/549755813888), by norm_num⟩
  | 10 => ⟨((3752637975/1099511627776), (-568632537/549755813888)), (93/1099511627776), by norm_num⟩
  | 11 => ⟨((-133708803/137438953472), (162085821/549755813888)), (27/1099511627776), by norm_num⟩
  | 12 => ⟨((1117981809/4398046511104), (-677625539/8796093022208)), (115/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581423060041861/10141204801825835211973625643008), (-383305816811/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889473086730319/316912650057057350374175801344), (-453708551539/633825300114114700748351602688)), (11531/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889941438745901/39614081257132168796771975168), (-127583651557/9903520314283042199192993792)), (25945/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889729004863343/2475880078570760549798248448), (-542122144329/2475880078570760549798248448)), (1723/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771395275142553/154742504910672534362390528), (-542000265219/154742504910672534362390528)), (1723/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387436312107217/2417851639229258349412352), (-63499473825/1208925819614629174706176)), (25847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258956550790763/604462909807314587353088), (-444366902067/604462909807314587353088)), (22617/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888064870287519/75557863725914323419136), (-360926827665/37778931862957161709568)), (18377/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297744107863407/4722366482869645213696), (-541178093043/4722366482869645213696)), (27567/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621729571808031/590295810358705651712), (-743775309123/590295810358705651712)), (37907/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911913262289947/36893488147419103232), (-232300646191/18446744073709551616)), (11847/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911526445194415/4611686018427387904), (-261160784773/2305843009213693952)), (53317/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199287689793233/144115188075855872), (-260939165543/288230376151711744)), (13331/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194857099591391/144115188075855872), (-28509087539/4503599627370496)), (23333/72057594037927936), by norm_num⟩
  | 4 => ⟨((746026088956927/18014398509481984), (-341611540941/9007199254740992)), (70015/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489776623046675/9007199254740992), (-1704580796373/9007199254740992)), (43773/4503599627370496), by norm_num⟩
  | 2 => ⟨((557246842418493/1125899906842624), (-106211045729/140737488355328)), (87587/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217666135954395/2251799813685248), (-317011799117/140737488355328)), (262969/2251799813685248), by norm_num⟩
  | 0 => ⟨((136491963809981/140737488355328), (-5020542031983/1125899906842624)), (8231/35184372088832), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((136491963809981/140737488355328), (-5020542031983/1125899906842624)), (31398773327577103/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((529486849911203/562949953421312), (-9738182048635/1125899906842624)), (1026485/2251799813685248), by norm_num⟩
  | 2 => ⟨((995941520121895/1125899906842624), (-36637284045991/2251799813685248)), (974347/1125899906842624), by norm_num⟩
  | 3 => ⟨((440342846122885/562949953421312), (-32408380304629/1125899906842624)), (3510939/2251799813685248), by norm_num⟩
  | 4 => ⟨((1375889598542631/2251799813685248), (-101400121519455/2251799813685248)), (5694677/2251799813685248), by norm_num⟩
  | 5 => ⟨((1672253626890845/4503599627370496), (-123914543061667/2251799813685248)), (14943937/4503599627370496), by norm_num⟩
  | 6 => ⟨((1214589733998065/9007199254740992), (-368090525276789/9007199254740992)), (25485033/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-263024319/134217728), (-5099383977/134217728)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-133297239/67108864), (-5168600439/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((852134649667699/9007199254740992), (-895061654432993/9007199254740992)), (35602467/9007199254740992), by norm_num⟩
  | 1 => ⟨((-80708557/268435456), (2712778205/8589934592)), (55/4294967296), by norm_num⟩
  | 2 => ⟨((4103938219/8589934592), (-4310677583/8589934592)), (177/8589934592), by norm_num⟩
  | 3 => ⟨((-33964939/67108864), (2283260901/4294967296)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((3454156943/8589934592), (-1814081513/4294967296)), (153/8589934592), by norm_num⟩
  | 5 => ⟨((-2195499341/8589934592), (288262435/1073741824)), (99/8589934592), by norm_num⟩
  | 6 => ⟨((1162902515/8589934592), (-610742357/4294967296)), (107/17179869184), by norm_num⟩
  | 7 => ⟨((-1055933369/17179869184), (1109126907/17179869184)), (99/34359738368), by norm_num⟩
  | 8 => ⟨((104869159/4294967296), (-3524865015/137438953472)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((-74062185/8589934592), (2489380169/274877906944)), (57/137438953472), by norm_num⟩
  | 10 => ⟨((3012782217/1099511627776), (-395569209/137438953472)), (147/1099511627776), by norm_num⟩
  | 11 => ⟨((-870434915/1099511627776), (3657135243/4398046511104)), (43/1099511627776), by norm_num⟩
  | 12 => ⟨((1844192677/8796093022208), (-3874190889/17592186044416)), (23/2199023255552), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395347102722001/2535301200456458802993406410752), (-1055066329797/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444726109180775/158456325028528675187087900672), (-1248798178753/633825300114114700748351602688)), (11541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236236806478125/4951760157141521099596496896), (-702326691117/19807040628566084398385987584)), (25969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889679037871291/2475880078570760549798248448), (-1492141815219/2475880078570760549798248448)), (13797/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221418157422793/19342813113834066795298816), (-745900861699/77371252455336267181195264)), (27597/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774849153436363/4835703278458516698824704), (-349550717961/2417851639229258349412352)), (12937/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258915425187837/604462909807314587353088), (-611533192859/302231454903657293676544)), (22643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887997944252019/75557863725914323419136), (-124175375705/4722366482869645213696)), (575/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297693828606515/4722366482869645213696), (-744756249463/2361183241434822606848)), (27605/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621660300300751/590295810358705651712), (-1023559067461/295147905179352825856)), (37963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823739729177827/73786976294838206464), (-2557456154261/73786976294838206464)), (47465/73786976294838206464), by norm_num⟩
  | 7 => ⟨((14241835646361/72057594037927936), (-1437578705191/4611686018427387904)), (13353/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594203237827431/1152921504606846976), (-2872683433735/1152921504606846976)), (53431/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597385354043175/72057594037927936), (-2510817497327/144115188075855872)), (23387/72057594037927936), by norm_num⟩
  | 4 => ⟨((745960900425249/18014398509481984), (-3760672016187/36028797018963968)), (70203/36028797018963968), by norm_num⟩
  | 3 => ⟨((744806137357469/4503599627370496), (-586391920601/1125899906842624)), (21957/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114327281289881/2251799813685248), (-4676608828735/2251799813685248)), (21985/562949953421312), by norm_num⟩
  | 1 => ⟨((1108578360507555/1125899906842624), (-13957406518381/2251799813685248)), (132191/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091406101322869/1125899906842624), (-27626406111087/2251799813685248)), (33189/140737488355328), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1091406101322869/1125899906842624), (-27626406111087/2251799813685248)), (126605988085699037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1057799602067649/1125899906842624), (-53560050949499/2251799813685248)), (1042541/2251799813685248), by norm_num⟩
  | 2 => ⟨((496590692287157/562949953421312), (-100640918853939/2251799813685248)), (2008561/2251799813685248), by norm_num⟩
  | 3 => ⟨((436929210158259/562949953421312), (-177555192117371/2251799813685248)), (3723133/2251799813685248), by norm_num⟩
  | 4 => ⟨((1342476489434079/2251799813685248), (-275616151595205/2251799813685248)), (6366503/2251799813685248), by norm_num⟩
  | 5 => ⟨((1533243631313661/4503599627370496), (-82158325392903/562949953421312)), (2287413/562949953421312), by norm_num⟩
  | 6 => ⟨((852134649667699/9007199254740992), (-895061654432993/9007199254740992)), (35602467/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-133297239/67108864), (-5168600439/134217728)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-270018875/134217728), (-2617495469/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((158449938093979/4503599627370496), (-1162267421628239/9007199254740992)), (2759715/562949953421312), by norm_num⟩
  | 1 => ⟨((-972806311/8589934592), (3567881113/8589934592)), (137/8589934592), by norm_num⟩
  | 2 => ⟨((782835679/4294967296), (-2871141565/4294967296)), (223/8589934592), by norm_num⟩
  | 3 => ⟨((-1679900561/8589934592), (1540308029/2147483648)), (121/4294967296), by norm_num⟩
  | 4 => ⟨((675923913/4294967296), (-2479030139/4294967296)), (197/8589934592), by norm_num⟩
  | 5 => ⟨((-870286057/8589934592), (6383752147/17179869184)), (1/67108864), by norm_num⟩
  | 6 => ⟨((933780917/17179869184), (-1712375455/8589934592)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((-107347315/4294967296), (6299341663/68719476736)), (129/34359738368), by norm_num⟩
  | 8 => ⟨((1382150709/137438953472), (-158412489/4294967296)), (105/68719476736), by norm_num⟩
  | 9 => ⟨((-494330167/137438953472), (226626725/17179869184)), (19/34359738368), by norm_num⟩
  | 10 => ⟨((1272949939/1099511627776), (-4668693033/1099511627776)), (197/1099511627776), by norm_num⟩
  | 11 => ⟨((-1489988285/4398046511104), (1366176649/1099511627776)), (233/4398046511104), by norm_num⟩
  | 12 => ⟨((1598695757/17592186044416), (-366462749/1099511627776)), (63/4398046511104), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581355176385417/10141204801825835211973625643008), (-1699400269687/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778863769953907/633825300114114700748351602688), (-251420047593/79228162514264337593543950336)), (5775/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889848634184443/39614081257132168796771975168), (-1131190004087/19807040628566084398385987584)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889630268419777/2475880078570760549798248448), (-2403285252577/2475880078570760549798248448)), (27619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885648195390413/77371252455336267181195264), (-2402730218419/154742504910672534362390528)), (27623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193706548410129/1208925819614629174706176), (-1125985006113/4835703278458516698824704)), (25901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157359392543139/75557863725914323419136), (-984942184459/302231454903657293676544)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471983071074447/18889465931478580854784), (-99998667603/2361183241434822606848)), (36843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324411102839179/1180591620717411303424), (-1199500875787/2361183241434822606848)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405398017982467/147573952589676412928), (-3297057917847/590295810358705651712)), (297/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1823654024776425/73786976294838206464), (-4118969385335/73786976294838206464)), (47537/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822857970121141/9223372036854775808), (-2315303577455/4611686018427387904)), (209/36028797018963968), by norm_num⟩
  | 6 => ⟨((398526381894501/288230376151711744), (-4626568380603/1152921504606846976)), (53535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37333887690113/4503599627370496), (-2021853903523/72057594037927936)), (46877/144115188075855872), by norm_num⟩
  | 4 => ⟨((372947685321579/9007199254740992), (-6056492888477/36028797018963968)), (70383/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489445648904873/9007199254740992), (-3777384333699/4503599627370496)), (88099/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114156473649025/2251799813685248), (-15062086878341/4503599627370496)), (176557/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216623529907353/2251799813685248), (-11237412621751/1125899906842624)), (265739/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181663589978359/2251799813685248), (-5559794085719/281474976710656)), (267551/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2181663589978359/2251799813685248), (-5559794085719/281474976710656)), (1020626072410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2112833328728857/2251799813685248), (-86185993983109/2251799813685248)), (1058011/2251799813685248), by norm_num⟩
  | 2 => ⟨((494786062058395/562949953421312), (-40433576610685/562949953421312)), (2066425/2251799813685248), by norm_num⟩
  | 3 => ⟨((431971566232153/562949953421312), (-284301935183425/2251799813685248)), (3929271/2251799813685248), by norm_num⟩
  | 4 => ⟨((1289974062759173/2251799813685248), (-218155009122285/1125899906842624)), (1755581/562949953421312), by norm_num⟩
  | 5 => ⟨((163609864608597/562949953421312), (-499892222600697/2251799813685248)), (10766967/2251799813685248), by norm_num⟩
  | 6 => ⟨((158449938093979/4503599627370496), (-1162267421628239/9007199254740992)), (2759715/562949953421312), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/134217728), (-2617495469/67108864)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-273308947/134217728), (-5298777207/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-243966996782715/9007199254740992), (-574964414938701/4503599627370496)), (24940437/4503599627370496), by norm_num⟩
  | 1 => ⟨((758045223/8589934592), (893254075/2147483648)), (39/2147483648), by norm_num⟩
  | 2 => ⟨((-617446129/4294967296), (-5820616019/8589934592)), (1/33554432), by norm_num⟩
  | 3 => ⟨((670566365/4294967296), (1580344075/2147483648)), (35/1073741824), by norm_num⟩
  | 4 => ⟨((-68274061/536870912), (-643614195/1073741824)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((1423638283/17179869184), (3355131489/8589934592)), (151/8589934592), by norm_num⟩
  | 6 => ⟨((-386529247/8589934592), (-3643780763/17179869184)), (83/8589934592), by norm_num⟩
  | 7 => ⟨((1439256687/68719476736), (1695969927/17179869184)), (311/68719476736), by norm_num⟩
  | 8 => ⟨((-1172309307/137438953472), (-1381408437/34359738368)), (255/137438953472), by norm_num⟩
  | 9 => ⟨((6631071/2147483648), (2000338687/137438953472)), (187/274877906944), by norm_num⟩
  | 10 => ⟨((-1106159077/1099511627776), (-5213837241/1099511627776)), (123/549755813888), by norm_num⟩
  | 11 => ⟨((655267829/2199023255552), (6177158205/4398046511104)), (293/4398046511104), by norm_num⟩
  | 12 => ⟨((-1423283897/17592186044416), (-1677148147/4398046511104)), (321/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245535579/10141204801825835211973625643008), (-2318459602493/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222353014198261/79228162514264337593543950336), (-685987468291/158456325028528675187087900672)), (23119/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889803923021061/39614081257132168796771975168), (-3086387801215/39614081257132168796771975168)), (6503/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889582635107979/2475880078570760549798248448), (-3278605220107/2475880078570760549798248448)), (27643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442812153481147/38685626227668133590597632), (-1638919175155/77371252455336267181195264)), (27649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549607444062625/9671406556917033397649408), (-384019855513/1208925819614629174706176)), (25927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258835662726151/604462909807314587353088), (-335915574095/75557863725914323419136)), (5673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471966961959689/18889465931478580854784), (-2182687962319/37778931862957161709568)), (36885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324398958647437/1180591620717411303424), (-818174168931/1180591620717411303424)), (13837/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621524874012169/590295810358705651712), (-4497788969219/590295810358705651712)), (38067/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823569420869361/73786976294838206464), (-5618984259233/73786976294838206464)), (47609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822761958048621/9223372036854775808), (-3158444136987/4611686018427387904)), (6699/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797004238284169/576460752303423488), (-3155652813023/576460752303423488)), (26817/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194598320267867/144115188075855872), (-5516116925517/144115188075855872)), (367/1125899906842624), by norm_num⟩
  | 4 => ⟨((1491659286743661/36028797018963968), (-2065409210791/9007199254740992)), (70557/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489277275244797/9007199254740992), (-1288141449791/1125899906842624)), (11045/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113982046104617/2251799813685248), (-20544631758365/4503599627370496)), (177209/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216070182638249/2251799813685248), (-30653260499979/2251799813685248)), (267045/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180437860959951/2251799813685248), (-60654118854981/2251799813685248)), (269515/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2180437860959951/2251799813685248), (-60654118854981/2251799813685248)), (1028118137839889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527425918869621/562949953421312), (-58731924734519/1125899906842624)), (1072935/2251799813685248), by norm_num⟩
  | 2 => ⟨((1970446846753111/2251799813685248), (-220102971369479/2251799813685248)), (2122397/2251799813685248), by norm_num⟩
  | 3 => ⟨((1702733713081985/2251799813685248), (-192602025837365/1125899906842624)), (2064667/1125899906842624), by norm_num⟩
  | 4 => ⟨((1221653860845311/2251799813685248), (-582556159047643/2251799813685248)), (7657691/2251799813685248), by norm_num⟩
  | 5 => ⟨((512064380797167/2251799813685248), (-158025144272271/562949953421312)), (3067787/562949953421312), by norm_num⟩
  | 6 => ⟨((-243966996782715/9007199254740992), (-574964414938701/4503599627370496)), (24940437/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-273308947/134217728), (-5298777207/134217728)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-276474835/134217728), (-670019483/16777216)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-709690831909853/9007199254740992), (-902507218142253/9007199254740992)), (25993275/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115334133/4294967296), (177295003/536870912)), (165/8589934592), by norm_num⟩
  | 2 => ⟨((-3675959353/8589934592), (-584335407/1073741824)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((2019227059/4294967296), (2567832235/4294967296)), (19/536870912), by norm_num⟩
  | 4 => ⟨((-3327521491/8589934592), (-4231578073/8589934592)), (63/2147483648), by norm_num⟩
  | 5 => ⟨((34271775/134217728), (2789318203/8589934592)), (21/1073741824), by norm_num⟩
  | 6 => ⟨((-2409689163/17179869184), (-3064379255/17179869184)), (93/8589934592), by norm_num⟩
  | 7 => ⟨((1134563197/17179869184), (2885626891/34359738368)), (177/34359738368), by norm_num⟩
  | 8 => ⟨((-3739335211/137438953472), (-297204859/8589934592)), (147/68719476736), by norm_num⟩
  | 9 => ⟨((2738719743/274877906944), (3482804377/274877906944)), (217/274877906944), by norm_num⟩
  | 10 => ⟨((-1805274699/549755813888), (-4591502025/1099511627776)), (9/34359738368), by norm_num⟩
  | 11 => ⟨((2163596693/2199023255552), (2751425753/2199023255552)), (87/1099511627776), by norm_num⟩
  | 12 => ⟨((-2376953915/8796093022208), (-47230471/137438953472)), (193/8796093022208), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790646259958961/5070602400912917605986812821504), (-2914152547803/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778785412999397/633825300114114700748351602688), (-1724415910097/316912650057057350374175801344)), (23135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889760260503433/39614081257132168796771975168), (-3879224495049/39614081257132168796771975168)), (26033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944768040540345/1237940039285380274899124224), (-4120808561379/2475880078570760549798248448)), (13833/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442800469279117/38685626227668133590597632), (-257489550949/9671406556917033397649408)), (27673/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193695429278679/1208925819614629174706176), (-1930653366839/4835703278458516698824704)), (25951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258796960191663/604462909807314587353088), (-1688803542967/302231454903657293676544)), (22715/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471951148227229/18889465931478580854784), (-2743334458999/37778931862957161709568)), (18463/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297548075803107/4722366482869645213696), (-2056651196833/2361183241434822606848)), (27707/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405364672543849/147573952589676412928), (-1413257583033/147573952589676412928)), (38117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911742959412741/36893488147419103232), (-1765537198211/18446744073709551616)), (11919/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911333479024031/4611686018427387904), (-1984807161171/2305843009213693952)), (53677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796956076886825/576460752303423488), (-1983030382589/288230376151711744)), (53729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194512553054475/144115188075855872), (-6932616089005/144115188075855872)), (1471/4503599627370496), by norm_num⟩
  | 4 => ⟨((372881918703829/9007199254740992), (-2595739192867/9007199254740992)), (17681/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489107597328493/9007199254740992), (-12950782652813/9007199254740992)), (88611/9007199254740992), by norm_num⟩
  | 2 => ⟨((556902330737047/1125899906842624), (-1613621482225/281474976710656)), (88919/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107749879542415/1125899906842624), (-9629569013723/562949953421312)), (134153/1125899906842624), by norm_num⟩
  | 0 => ⟨((544786378360075/562949953421312), (-38102241375497/1125899906842624)), (135705/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((544786378360075/562949953421312), (-38102241375497/1125899906842624)), (517673494579124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((526564130693479/562949953421312), (-36872872908515/562949953421312)), (543677/1125899906842624), by norm_num⟩
  | 2 => ⟨((122528731594885/140737488355328), (-275916992638419/2251799813685248)), (2176591/2251799813685248), by norm_num⟩
  | 3 => ⟨((836502438457947/1125899906842624), (-240218576646077/1125899906842624)), (4323367/2251799813685248), by norm_num⟩
  | 4 => ⟨((285119201573025/562949953421312), (-713894455114927/2251799813685248)), (8269049/2251799813685248), by norm_num⟩
  | 5 => ⟨((351293240117907/2251799813685248), (-1446274332648853/4503599627370496)), (3404807/562949953421312), by norm_num⟩
  | 6 => ⟨((-709690831909853/9007199254740992), (-902507218142253/9007199254740992)), (25993275/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-276474835/134217728), (-670019483/16777216)), (1/67108864), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile029Terms3
