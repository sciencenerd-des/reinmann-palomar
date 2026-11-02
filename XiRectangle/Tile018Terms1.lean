/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile018Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5217/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5217/640))
  have he : value ((3/4), (5217/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-19231589523/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((256029885926629/2251799813685248), (174820469664111/1125899906842624)), (3335579/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4291955245/17179869184), (-1465300875/4294967296)), (29/17179869184), by norm_num⟩
  | 2 => ⟨((9430389549/34359738368), (12878380383/34359738368)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-13813789127/68719476736), (-4716115649/17179869184)), (99/68719476736), by norm_num⟩
  | 4 => ⟨((1896999811/17179869184), (10362365213/68719476736)), (7/8589934592), by norm_num⟩
  | 5 => ⟨((-13338030745/274877906944), (-4553688705/68719476736)), (101/274877906944), by norm_num⟩
  | 6 => ⟨((9768882989/549755813888), (13340635653/549755813888)), (19/137438953472), by norm_num⟩
  | 7 => ⟨((-12265388455/2199023255552), (-8374963581/1099511627776)), (49/1099511627776), by norm_num⟩
  | 8 => ⟨((6737453241/4398046511104), (9200837907/4398046511104)), (55/4398046511104), by norm_num⟩
  | 9 => ⟨((-13158842533/35184372088832), (-4492512707/8796093022208)), (55/17592186044416), by norm_num⟩
  | 10 => ⟨((11565172889/140737488355328), (7896847467/70368744177664)), (99/140737488355328), by norm_num⟩
  | 11 => ⟨((-9240466223/562949953421312), (-6309508123/281474976710656)), (81/562949953421312), by norm_num⟩
  | 12 => ⟨((13535586327/4503599627370496), (9242270879/2251799813685248)), (121/4503599627370496), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (1222816856211/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889712993334641/316912650057057350374175801344), (1448159269803/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236310135571887/4951760157141521099596496896), (1628941667341/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890302198392455/2475880078570760549798248448), (1730459460685/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771968266075281/154742504910672534362390528), (1730132096333/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387570553062141/2417851639229258349412352), (1621651093959/9671406556917033397649408)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259426179042063/604462909807314587353088), (88662315557/37778931862957161709568)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944413806544503/37778931862957161709568), (9002220829/295147905179352825856)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649157906217271/2361183241434822606848), (431964093237/1180591620717411303424)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6337949582365/2305843009213693952), (593719142679/147573952589676412928)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912403784016363/36893488147419103232), (2967207413447/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824155385328779/9223372036854775808), (208512526481/576460752303423488)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595402541109081/1152921504606846976), (1666908510701/576460752303423488)), (6683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195818840376197/144115188075855872), (91075331817/4503599627370496)), (5851/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493491485983529/36028797018963968), (2183131251203/18014398509481984)), (4391/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491569989285557/9007199254740992), (681058894859/1125899906842624)), (2747/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232556841883989/4503599627370496), (10868917457455/4503599627370496)), (2751/562949953421312), by norm_num⟩
  | 1 => ⟨((2222977355196285/2251799813685248), (16233474975433/2251799813685248)), (8273/562949953421312), by norm_num⟩
  | 0 => ⟨((1097161434875591/1125899906842624), (16094154475039/1125899906842624)), (16627/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1097161434875591/1125899906842624), (16094154475039/1125899906842624)), (63426973583030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2137852903363323/2251799813685248), (62733411770009/2251799813685248)), (131523/2251799813685248), by norm_num⟩
  | 2 => ⟨((2027924297583665/2251799813685248), (14889734610879/281474976710656)), (32133/281474976710656), by norm_num⟩
  | 3 => ⟨((910002714990227/1125899906842624), (214550188118593/2251799813685248)), (490211/2251799813685248), by norm_num⟩
  | 4 => ⟨((1450567657961971/2251799813685248), (346818136324571/2251799813685248)), (221459/562949953421312), by norm_num⟩
  | 5 => ⟨((440506233854527/1125899906842624), (223413808230019/1125899906842624)), (1414149/2251799813685248), by norm_num⟩
  | 6 => ⟨((256029885926629/2251799813685248), (174820469664111/1125899906842624)), (3335579/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-19231589523/1073741824)), (1/536870912), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-927143219/536870912), (-20153775725/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1596623008130653/9007199254740992), (127825672159011/9007199254740992)), (1656791/4503599627370496), by norm_num⟩
  | 1 => ⟨((-28048403455/68719476736), (-561388945/17179869184)), (61/68719476736), by norm_num⟩
  | 2 => ⟨((16145958919/34359738368), (161580727/4294967296)), (37/34359738368), by norm_num⟩
  | 3 => ⟨((-24784962879/68719476736), (-992142329/34359738368)), (59/68719476736), by norm_num⟩
  | 4 => ⟨((28534743027/137438953472), (2284492137/137438953472)), (35/68719476736), by norm_num⟩
  | 5 => ⟨((-13140734785/137438953472), (-263011877/34359738368)), (67/274877906944), by norm_num⟩
  | 6 => ⟨((20171773351/549755813888), (807476303/274877906944)), (53/549755813888), by norm_num⟩
  | 7 => ⟨((-26541271209/2199023255552), (-2124894741/2199023255552)), (9/274877906944), by norm_num⟩
  | 8 => ⟨((30556767717/8796093022208), (2446375477/8796093022208)), (85/8796093022208), by norm_num⟩
  | 9 => ⟨((-31270914593/35184372088832), (-2503550091/35184372088832)), (89/35184372088832), by norm_num⟩
  | 10 => ⟨((14400788357/70368744177664), (18014491/1099511627776)), (21/35184372088832), by norm_num⟩
  | 11 => ⟨((-24115665889/562949953421312), (-1930700727/562949953421312)), (9/70368744177664), by norm_num⟩
  | 12 => ⟨((9254728797/1125899906842624), (1481867571/2251799813685248)), (57/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239623/5070602400912917605986812821504), (104065156427/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779305206007867/633825300114114700748351602688), (61613184521/316912650057057350374175801344)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945172645439679/19807040628566084398385987584), (138608614709/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890158024607905/2475880078570760549798248448), (73622855477/1237940039285380274899124224)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771824212619445/154742504910672534362390528), (147216534813/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550147289925829/9671406556917033397649408), (68992254959/4835703278458516698824704)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259308249737473/604462909807314587353088), (120705463915/604462909807314587353088)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888636217322091/75557863725914323419136), (196088306673/75557863725914323419136)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649086237453375/2361183241434822606848), (147015436387/4722366482869645213696)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622318343837169/590295810358705651712), (202063722037/590295810358705651712)), (37/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1824562140803663/73786976294838206464), (126227981065/36893488147419103232)), (5921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823879979300139/9223372036854775808), (283842987139/9223372036854775808)), (6661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199391001062103/144115188075855872), (141815340153/576460752303423488)), (6661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597789802719275/72057594037927936), (247938214389/144115188075855872)), (5829/144115188075855872), by norm_num⟩
  | 4 => ⟨((23330228000619/562949953421312), (185715297537/18014398509481984)), (8743/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491127290777659/9007199254740992), (463455175319/9007199254740992)), (10929/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231681668149787/4503599627370496), (924415949347/4503599627370496)), (5465/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110845017949005/1125899906842624), (43137646983/70368744177664)), (32799/2251799813685248), by norm_num⟩
  | 0 => ⟨((547962324327831/562949953421312), (2736032962607/2251799813685248)), (65627/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((547962324327831/562949953421312), (2736032962607/2251799813685248)), (250347146041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1066745770883009/1125899906842624), (2663190524337/1125899906842624)), (7995/140737488355328), by norm_num⟩
  | 2 => ⟨((1010693259851273/1125899906842624), (2523268020209/562949953421312)), (60751/562949953421312), by norm_num⟩
  | 3 => ⟨((907252404742907/1125899906842624), (18120615982465/2251799813685248)), (438457/2251799813685248), by norm_num⟩
  | 4 => ⟨((730992898861597/1125899906842624), (14601628728807/1125899906842624)), (713677/2251799813685248), by norm_num⟩
  | 5 => ⟨((474409321271227/1125899906842624), (75841106995053/4503599627370496)), (1890449/4503599627370496), by norm_num⟩
  | 6 => ⟨((1596623008130653/9007199254740992), (127825672159011/9007199254740992)), (1656791/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-927143219/536870912), (-20153775725/1073741824)), (1/536870912), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1931040333/1073741824), (-20987994619/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1143398480973535/9007199254740992), (-119661842511227/1125899906842624)), (4999367/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10458945513/34359738368), (8756609085/34359738368)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((6269864001/17179869184), (-10498715765/34359738368)), (15/8589934592), by norm_num⟩
  | 3 => ⟨((-10022984833/34359738368), (1048950871/4294967296)), (25/17179869184), by norm_num⟩
  | 4 => ⟨((12017033975/68719476736), (-2515274335/17179869184)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-11526235585/137438953472), (2412545775/34359738368)), (31/68719476736), by norm_num⟩
  | 6 => ⟨((9212901941/274877906944), (-3856688073/137438953472)), (51/274877906944), by norm_num⟩
  | 7 => ⟨((-12623756579/1099511627776), (5284533771/549755813888)), (9/137438953472), by norm_num⟩
  | 8 => ⟨((15135223113/4398046511104), (-12671758549/4398046511104)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((-4032519995/4398046511104), (13504688855/17592186044416)), (97/17592186044416), by norm_num⟩
  | 10 => ⟨((7735648507/35184372088832), (-12953131827/70368744177664)), (3/2199023255552), by norm_num⟩
  | 11 => ⟨((-13490381809/281474976710656), (352957427/8796093022208)), (43/140737488355328), by norm_num⟩
  | 12 => ⟨((10782840923/1125899906842624), (-1128473261/140737488355328)), (71/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-453984429865/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779194343629567/633825300114114700748351602688), (-537511871131/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59069392343929/1237940039285380274899124224), (-604605180637/19807040628566084398385987584)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890025471554911/2475880078570760549798248448), (-642275142751/1237940039285380274899124224)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771691635758003/154742504910672534362390528), (-321071293697/38685626227668133590597632)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775011486921833/4835703278458516698824704), (-601867872429/4835703278458516698824704)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259199447915685/604462909807314587353088), (-131623406635/75557863725914323419136)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472114841767629/18889465931478580854784), (-1710576605341/75557863725914323419136)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((324509948972661/1180591620717411303424), (-1282470909107/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405533960782759/147573952589676412928), (-881323909621/295147905179352825856)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824333914504005/73786976294838206464), (-275273228693/9223372036854775808)), (1483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911811543459023/4611686018427387904), (-2475914571097/9223372036854775808)), (6675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594870944288099/1152921504606846976), (-2473985366103/1152921504606846976)), (6677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149419310190457/18014398509481984), (-2162568768661/144115188075855872)), (5845/144115188075855872), by norm_num⟩
  | 4 => ⟨((746398261066061/18014398509481984), (-3239521117571/36028797018963968)), (8771/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490704034541291/9007199254740992), (-4041831163235/9007199254740992)), (2743/2251799813685248), by norm_num⟩
  | 2 => ⟨((2230833161926395/4503599627370496), (-251906089933/140737488355328)), (21967/4503599627370496), by norm_num⟩
  | 1 => ⟨((555103084214507/562949953421312), (-6017487403763/1125899906842624)), (16505/1125899906842624), by norm_num⟩
  | 0 => ⟨((273659300908703/281474976710656), (-11922392040729/1125899906842624)), (66261/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((273659300908703/281474976710656), (-11922392040729/1125899906842624)), (252765664107512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128232637498449/2251799813685248), (-23182689339943/1125899906842624)), (130247/2251799813685248), by norm_num⟩
  | 2 => ⟨((1005245755741563/1125899906842624), (-21910542748251/562949953421312)), (62891/562949953421312), by norm_num⟩
  | 3 => ⟨((447907818347175/562949953421312), (-78250224446469/1125899906842624)), (468795/2251799813685248), by norm_num⟩
  | 4 => ⟨((1414624075337977/2251799813685248), (-249037322795649/2251799813685248)), (811151/2251799813685248), by norm_num⟩
  | 5 => ⟨((53821993705755/140737488355328), (-156450049575181/1125899906842624)), (1198581/2251799813685248), by norm_num⟩
  | 6 => ⟨((1143398480973535/9007199254740992), (-119661842511227/1125899906842624)), (4999367/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-20987994619/1073741824)), (1/536870912), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2001111149/1073741824), (-679674275/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((228748347028709/9007199254740992), (-689084531764069/4503599627370496)), (3316727/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4336687383/68719476736), (26127788319/68719476736)), (1/536870912), by norm_num⟩
  | 2 => ⟨((2694065829/34359738368), (-16231278735/34359738368)), (81/34359738368), by norm_num⟩
  | 3 => ⟨((-1115750349/17179869184), (26888808309/68719476736)), (137/68719476736), by norm_num⟩
  | 4 => ⟨((1386267731/34359738368), (-16704044643/68719476736)), (87/68719476736), by norm_num⟩
  | 5 => ⟨((-2755796723/137438953472), (16603196645/137438953472)), (89/137438953472), by norm_num⟩
  | 6 => ⟨((1141316267/137438953472), (-27504929167/549755813888)), (75/274877906944), by norm_num⟩
  | 7 => ⟨((-810304109/274877906944), (19527766111/1099511627776)), (27/274877906944), by norm_num⟩
  | 8 => ⟨((2013530069/2199023255552), (-6065584483/1099511627776)), (137/4398046511104), by norm_num⟩
  | 9 => ⟨((-2223748559/8796093022208), (26795397719/17592186044416)), (77/8796093022208), by norm_num⟩
  | 10 => ⟨((4420646065/70368744177664), (-13316812395/35184372088832)), (39/17592186044416), by norm_num⟩
  | 11 => ⟨((-1997253237/140737488355328), (24066207763/281474976710656)), (143/281474976710656), by norm_num⟩
  | 12 => ⟨((3308658567/1125899906842624), (-19934093235/1125899906842624)), (121/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-1831883528667/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889545902307531/316912650057057350374175801344), (-2168693634293/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((14766446161473/309485009821345068724781056), (-2439378333747/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944951346355119/1237940039285380274899124224), (-2591346409387/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771568725268717/154742504910672534362390528), (-323848979805/19342813113834066795298816)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387476901369101/2417851639229258349412352), (-2428278253295/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259098360910753/604462909807314587353088), (-1037184829/295147905179352825856)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888294838993131/75557863725914323419136), (-3450647170875/75557863725914323419136)), (4607/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297916171062247/4722366482869645213696), (-2587019756463/4722366482869645213696)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621965487637797/590295810358705651712), (-3555583640673/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912060206900751/36893488147419103232), (-4442127832713/73786976294838206464)), (5945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455845533698681/2305843009213693952), (-156067560475/288230376151711744)), (6691/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797314519532587/576460752303423488), (-4990124692143/1152921504606846976)), (6695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149392718067469/18014398509481984), (-1090455196051/36028797018963968)), (5863/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492475282628141/36028797018963968), (-816707933867/4503599627370496)), (2201/9007199254740992), by norm_num⟩
  | 3 => ⟨((186287345454737/1125899906842624), (-8151230949639/9007199254740992)), (2755/2251799813685248), by norm_num⟩
  | 2 => ⟨((2230011507536599/4503599627370496), (-16254997043893/4503599627370496)), (2761/562949953421312), by norm_num⟩
  | 1 => ⟨((2219152255250269/2251799813685248), (-758253568887/70368744177664)), (33253/2251799813685248), by norm_num⟩
  | 0 => ⟨((136665308025595/140737488355328), (-48056385112483/2251799813685248)), (4187/140737488355328), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((136665308025595/140737488355328), (-48056385112483/2251799813685248)), (15972137988042787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2122349685679923/2251799813685248), (-46665893719891/1125899906842624)), (16621/281474976710656), by norm_num⟩
  | 2 => ⟨((62389778978641/70368744177664), (-343618692071/4398046511104)), (261671/2251799813685248), by norm_num⟩
  | 3 => ⟨((878175712110825/1125899906842624), (-77992060146205/562949953421312)), (504891/2251799813685248), by norm_num⟩
  | 4 => ⟨((1326692596773351/2251799813685248), (-486655927701093/2251799813685248)), (927505/2251799813685248), by norm_num⟩
  | 5 => ⟨((676471880452659/2251799813685248), (-286723008205717/1125899906842624)), (1493819/2251799813685248), by norm_num⟩
  | 6 => ⟨((228748347028709/9007199254740992), (-689084531764069/4503599627370496)), (3316727/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-679674275/33554432)), (1/536870912), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2065570051/1073741824), (-22450164493/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-308418039146629/4503599627370496), (-72628751441399/562949953421312)), (7311345/9007199254740992), by norm_num⟩
  | 1 => ⟨((6035435877/34359738368), (11370182455/34359738368)), (73/34359738368), by norm_num⟩
  | 2 => ⟨((-7740293687/34359738368), (-14581971091/34359738368)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((827227555/4294967296), (12467339127/34359738368)), (21/8589934592), by norm_num⟩
  | 4 => ⟨((-8487187143/68719476736), (-15989046741/68719476736)), (55/34359738368), by norm_num⟩
  | 5 => ⟨((8707682083/137438953472), (8202219033/68719476736)), (115/137438953472), by norm_num⟩
  | 6 => ⟨((-1861230297/68719476736), (-14025517625/274877906944)), (25/68719476736), by norm_num⟩
  | 7 => ⟨((1363988987/137438953472), (5139248917/274877906944)), (149/1099511627776), by norm_num⟩
  | 8 => ⟨((-6997125351/2199023255552), (-13181913207/2199023255552)), (49/1099511627776), by norm_num⟩
  | 9 => ⟨((3988282705/4398046511104), (1878385545/1099511627776)), (113/8796093022208), by norm_num⟩
  | 10 => ⟨((-8183794529/35184372088832), (-15417484149/35184372088832)), (59/17592186044416), by norm_num⟩
  | 11 => ⟨((7633097643/140737488355328), (7190012011/70368744177664)), (7/8796093022208), by norm_num⟩
  | 12 => ⟨((-203942801/17592186044416), (-384208681/17592186044416)), (49/281474976710656), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418445/10141204801825835211973625643008), (-2681802634691/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778996357180935/633825300114114700748351602688), (-793641106413/158456325028528675187087900672)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944998792239375/19807040628566084398385987584), (-3570772769747/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236223532275619/309485009821345068724781056), (-3793200429197/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110715879819955/9671406556917033397649408), (-948090428245/38685626227668133590597632)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24215623374771/151115727451828646838272), (-1777224066585/4835703278458516698824704)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259003888419275/604462909807314587353088), (-3109251327261/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888140896505417/75557863725914323419136), (-1262715891719/18889465931478580854784)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324450085735511/1180591620717411303424), (-3786686955205/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621805621337175/590295810358705651712), (-1301080406195/147573952589676412928)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823919678114863/73786976294838206464), (-3250921951481/36893488147419103232)), (5957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823155067636915/9223372036854775808), (-1827421011249/2305843009213693952)), (6707/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594400425298879/1152921504606846976), (-7303574233495/1152921504606846976)), (839/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194939971377439/144115188075855872), (-3191879104153/72057594037927936)), (735/18014398509481984), by norm_num⟩
  | 4 => ⟨((746084580091729/18014398509481984), (-4780954776401/18014398509481984)), (8833/36028797018963968), by norm_num⟩
  | 3 => ⟨((744955036134979/4503599627370496), (-5964193758113/4503599627370496)), (11065/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114608047680199/2251799813685248), (-2973109176309/562949953421312)), (11101/2251799813685248), by norm_num⟩
  | 1 => ⟨((554478590470605/562949953421312), (-17748947247175/1125899906842624)), (4185/281474976710656), by norm_num⟩
  | 0 => ⟨((1091995913170083/1125899906842624), (-35140079144081/1125899906842624)), (16917/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1091995913170083/1125899906842624), (-35140079144081/1125899906842624)), (64533235790061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((529008059232577/562949953421312), (-68163826252405/1125899906842624)), (67743/1125899906842624), by norm_num⟩
  | 2 => ⟨((1980196983671161/2251799813685248), (-256216121639251/2251799813685248)), (4235/35184372088832), by norm_num⟩
  | 3 => ⟨((1712200778115627/2251799813685248), (-56328096768917/281474976710656)), (538377/2251799813685248), by norm_num⟩
  | 4 => ⟨((1211727970185457/2251799813685248), (-685283020498503/2251799813685248)), (517105/1125899906842624), by norm_num⟩
  | 5 => ⟨((443499395229015/2251799813685248), (-368761289695745/1125899906842624)), (1742525/2251799813685248), by norm_num⟩
  | 6 => ⟨((-308418039146629/4503599627370496), (-72628751441399/562949953421312)), (7311345/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2065570051/1073741824), (-22450164493/1073741824)), (1/536870912), by norm_num⟩, -3, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2125249673/1073741824), (-2887350923/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1104603915758527/9007199254740992), (-573255775059001/9007199254740992)), (434997/562949953421312), by norm_num⟩
  | 1 => ⟨((2780068455/8589934592), (11542166557/68719476736)), (143/68719476736), by norm_num⟩
  | 2 => ⟨((-7336760033/17179869184), (-7615109813/34359738368)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((6454043447/17179869184), (6698903789/34359738368)), (43/17179869184), by norm_num⟩
  | 4 => ⟨((-17032590665/68719476736), (-2209848893/17179869184)), (29/17179869184), by norm_num⟩
  | 5 => ⟨((17979993295/137438953472), (9331068669/137438953472)), (125/137438953472), by norm_num⟩
  | 6 => ⟨((-3954186091/68719476736), (-2052102097/68719476736)), (7/17179869184), by norm_num⟩
  | 7 => ⟨((11926084327/549755813888), (6189274377/549755813888)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((-983550633/137438953472), (-8166924955/2199023255552)), (29/549755813888), by norm_num⟩
  | 9 => ⟨((18457930717/8796093022208), (2394775907/2199023255552)), (69/4398046511104), by norm_num⟩
  | 10 => ⟨((-19484614939/35184372088832), (-631995091/2199023255552)), (37/8796093022208), by norm_num⟩
  | 11 => ⟨((18698551225/140737488355328), (2425994585/35184372088832)), (9/8796093022208), by norm_num⟩
  | 12 => ⟨((-16448849555/562949953421312), (-4268225861/281474976710656)), (129/562949953421312), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-867176204795/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222363378651467/79228162514264337593543950336), (-4105677630671/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889896902114007/39614081257132168796771975168), (-288629042005/2475880078570760549798248448)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889681036971549/2475880078570760549798248448), (-4905700498321/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771346579096277/154742504910672534362390528), (-1226145793625/38685626227668133590597632)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549698822694833/9671406556917033397649408), (-2298429857447/4835703278458516698824704)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629457577807675/302231454903657293676544), (-4021065402523/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887996155524597/75557863725914323419136), (-3266003143069/37778931862957161709568)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297691306269283/4722366482869645213696), (-2448529096565/2361183241434822606848)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621654915261665/590295810358705651712), (-6730292570135/590295810358705651712)), (1193/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823730126070699/73786976294838206464), (-65688462397/576460752303423488)), (373/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822940216071929/9223372036854775808), (-9452619470785/9223372036854775808)), (105/144115188075855872), by norm_num⟩
  | 6 => ⟨((1594183570554401/1152921504606846976), (-2361118342529/288230376151711744)), (841/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194747975002521/144115188075855872), (-257961052563/4503599627370496)), (737/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491876681420065/36028797018963968), (-12363819126325/36028797018963968)), (8861/36028797018963968), by norm_num⟩
  | 3 => ⟨((372384163776937/2251799813685248), (-15422750704241/9007199254740992)), (5553/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114222959656933/2251799813685248), (-15374759522805/2251799813685248)), (697/140737488355328), by norm_num⟩
  | 1 => ⟨((554175285783017/562949953421312), (-11471157327669/562949953421312)), (16843/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090667980801513/1125899906842624), (-45406255840171/1125899906842624)), (8537/281474976710656), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090667980801513/1125899906842624), (-45406255840171/1125899906842624)), (32566071630382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1054707358140151/1125899906842624), (-87970785097291/1125899906842624)), (34457/562949953421312), by norm_num⟩
  | 2 => ⟨((981142946696017/1125899906842624), (-164816488179083/1125899906842624)), (139883/1125899906842624), by norm_num⟩
  | 3 => ⟨((1661740979620521/2251799813685248), (-574504123833161/2251799813685248)), (284751/1125899906842624), by norm_num⟩
  | 4 => ⟨((1079726572616507/2251799813685248), (-423961774813429/1125899906842624)), (1131137/2251799813685248), by norm_num⟩
  | 5 => ⟨((396869315724027/4503599627370496), (-101643758751927/281474976710656)), (1936617/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1104603915758527/9007199254740992), (-573255775059001/9007199254740992)), (434997/562949953421312), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-2887350923/134217728)), (1/536870912), by norm_num⟩, -3, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-272601259/134217728), (-5925669867/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1177602110627399/9007199254740992), (24696625323195/2251799813685248)), (762667/1125899906842624), by norm_num⟩
  | 1 => ⟨((6082545533/17179869184), (-2041006505/68719476736)), (129/68719476736), by norm_num⟩
  | 2 => ⟨((-8235919327/17179869184), (1381787019/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((29737710653/68719476736), (-1247316205/34359738368)), (163/68719476736), by norm_num⟩
  | 4 => ⟨((-78643763/268435456), (844448725/34359738368)), (7/4294967296), by norm_num⟩
  | 5 => ⟨((2726032105/17179869184), (-114340477/8589934592)), (123/137438953472), by norm_num⟩
  | 6 => ⟨((-1230371965/17179869184), (1651412009/274877906944)), (113/274877906944), by norm_num⟩
  | 7 => ⟨((1903948027/68719476736), (-2555489499/1099511627776)), (177/1099511627776), by norm_num⟩
  | 8 => ⟨((-20623947349/2199023255552), (1730098463/2199023255552)), (61/1099511627776), by norm_num⟩
  | 9 => ⟨((12411263281/4398046511104), (-1041154109/4398046511104)), (149/8796093022208), by norm_num⟩
  | 10 => ⟨((-26888259219/35184372088832), (2255598075/35184372088832)), (41/8796093022208), by norm_num⟩
  | 11 => ⟨((6619523253/35184372088832), (-2221190117/140737488355328)), (41/35184372088832), by norm_num⟩
  | 12 => ⟨((-23901335035/562949953421312), (250628931/70368744177664)), (75/281474976710656), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (3983257157981/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778824377246597/633825300114114700748351602688), (2357158405069/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944901886591463/19807040628566084398385987584), (2651315167213/19807040628566084398385987584)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944790947950835/1237940039285380274899124224), (5632873588727/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771247222665783/154742504910672534362390528), (5631555995767/154742504910672534362390528)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12106292557689/75557863725914323419136), (659772989303/1208925819614629174706176)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258833223745305/604462909807314587353088), (4617011217777/604462909807314587353088)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235982823529871/9444732965739290427392), (7500019042219/75557863725914323419136)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324397689174559/1180591620717411303424), (2811359191767/2361183241434822606848)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621516052409581/590295810358705651712), (1931876860361/147573952589676412928)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823555637997683/73786976294838206464), (2413447418239/18446744073709551616)), (747/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822742668495291/9223372036854775808), (5426411097067/4611686018427387904)), (6729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593984465476205/1152921504606846976), (10843210357697/1152921504606846976)), (6739/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298643002538061/36028797018963968), (9476998714801/144115188075855872)), (2953/72057594037927936), by norm_num⟩
  | 4 => ⟨((372902312257075/9007199254740992), (14193884836165/36028797018963968)), (8879/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489196289709673/9007199254740992), (17704549779853/9007199254740992)), (5567/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113873529927063/2251799813685248), (2205984307043/281474976710656)), (11187/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107803933979561/1125899906842624), (26330243888043/1125899906842624)), (1057/70368744177664), by norm_num⟩
  | 0 => ⟨((1089485738519633/1125899906842624), (26047474815509/562949953421312)), (34353/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1089485738519633/1125899906842624), (26047474815509/562949953421312)), (131046299460982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((262959718591163/281474976710656), (100820160525737/1125899906842624)), (2177/35184372088832), by norm_num⟩
  | 2 => ⟨((486810730773729/562949953421312), (188376539541677/1125899906842624)), (142641/1125899906842624), by norm_num⟩
  | 3 => ⟨((810421090001611/1125899906842624), (81449265887299/281474976710656)), (294429/1125899906842624), by norm_num⟩
  | 4 => ⟨((978130672461433/2251799813685248), (234508245143473/562949953421312)), (594255/1125899906842624), by norm_num⟩
  | 5 => ⟨((34121034782293/2251799813685248), (407460212272667/1125899906842624)), (31605/35184372088832), by norm_num⟩
  | 6 => ⟨((-1177602110627399/9007199254740992), (24696625323195/2251799813685248)), (762667/1125899906842624), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-5925669867/268435456)), (1/536870912), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile018Terms1
