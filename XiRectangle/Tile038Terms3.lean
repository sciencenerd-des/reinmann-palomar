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
namespace Reinmann.XiRectangle.Tile038Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-58341473/33554432), (-1445288443/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((243092285308487/2251799813685248), (156142071845029/1125899906842624)), (192164045/9007199254740992), by norm_num⟩
  | 1 => ⟨((-358299529/1073741824), (-460283063/1073741824)), (9/134217728), by norm_num⟩
  | 2 => ⟨((69219941/134217728), (177844311/268435456)), (113/1073741824), by norm_num⟩
  | 3 => ⟨((-570564737/1073741824), (-366482877/536870912)), (59/536870912), by norm_num⟩
  | 4 => ⟨((110227489/268435456), (1132814131/2147483648)), (185/2147483648), by norm_num⟩
  | 5 => ⟨((-545148557/2147483648), (-350157657/1073741824)), (29/536870912), by norm_num⟩
  | 6 => ⟨((140423111/1073741824), (360784061/2147483648)), (121/4294967296), by norm_num⟩
  | 7 => ⟨((-496061483/8589934592), (-637256485/8589934592)), (27/2147483648), by norm_num⟩
  | 8 => ⟨((47917097/2147483648), (61555839/2147483648)), (169/34359738368), by norm_num⟩
  | 9 => ⟨((-526626777/68719476736), (-676521641/68719476736)), (59/34359738368), by norm_num⟩
  | 10 => ⟨((325565145/137438953472), (836462845/274877906944)), (37/68719476736), by norm_num⟩
  | 11 => ⟨((-365940249/549755813888), (-940197151/1099511627776)), (21/137438953472), by norm_num⟩
  | 12 => ⟨((377045615/2199023255552), (968729769/4398046511104)), (175/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581710901395785/10141204801825835211973625643008), (1184523428861/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779286003720545/633825300114114700748351602688), (1402599024167/633825300114114700748351602688)), (92339/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472580907874825/9903520314283042199192993792), (394420451009/9903520314283042199192993792)), (51945/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945067469266031/1237940039285380274899124224), (1675989515367/2475880078570760549798248448)), (110393/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885900522246217/77371252455336267181195264), (1675655027331/154742504910672534362390528)), (27601/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550125482675063/9671406556917033397649408), (1570571280553/9671406556917033397649408)), (25879/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314822270328753/151115727451828646838272), (686947329813/302231454903657293676544)), (45295/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888604905478213/75557863725914323419136), (2231913006987/75557863725914323419136)), (73615/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298148848375021/4722366482869645213696), (418338093147/1180591620717411303424)), (110443/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405571406441275/147573952589676412928), (2299913525463/590295810358705651712)), (151891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824520896200325/73786976294838206464), (2873473599969/73786976294838206464)), (189913/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823833102584027/9223372036854775808), (3230708721801/9223372036854775808)), (26715/1152921504606846976), by norm_num⟩
  | 6 => ⟨((24923133390889/18014398509481984), (403534251729/144115188075855872)), (53451/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195537400031175/144115188075855872), (352750371099/18014398509481984)), (93587/72057594037927936), by norm_num⟩
  | 4 => ⟨((746534975658183/18014398509481984), (4227536495001/36028797018963968)), (35119/4503599627370496), by norm_num⟩
  | 3 => ⟨((745522082396809/4503599627370496), (5274864343669/9007199254740992)), (87881/2251799813685248), by norm_num⟩
  | 2 => ⟨((2231508468846231/4503599627370496), (10521110407963/4503599627370496)), (704051/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221412965995907/2251799813685248), (15710296549327/2251799813685248)), (1058593/2251799813685248), by norm_num⟩
  | 0 => ⟨((1095613327943451/1125899906842624), (7784043616997/562949953421312)), (2127285/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1095613327943451/1125899906842624), (7784043616997/562949953421312)), (8114948281295012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2131852381785391/2251799813685248), (1893663433189/70368744177664)), (4198953/2251799813685248), by norm_num⟩
  | 2 => ⟨((1008331763298529/1125899906842624), (114738750776947/2251799813685248)), (8176565/2251799813685248), by norm_num⟩
  | 3 => ⟨((1800234094496491/2251799813685248), (102757559696433/1125899906842624)), (7739387/1125899906842624), by norm_num⟩
  | 4 => ⟨((88779159876055/140737488355328), (328604099367129/2251799813685248)), (27574867/2251799813685248), by norm_num⟩
  | 5 => ⟨((424048482621995/1125899906842624), (414576048138449/2251799813685248)), (21418597/1125899906842624), by norm_num⟩
  | 6 => ⟨((243092285308487/2251799813685248), (156142071845029/1125899906842624)), (192164045/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-58341473/33554432), (-1445288443/33554432)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-7397559/4194304), (-1466072893/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1479463508976265/9007199254740992), (220681087506985/4503599627370496)), (123183493/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1105987853/2147483648), (-329944741/2147483648)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((866954629/1073741824), (258634957/1073741824)), (75/1073741824), by norm_num⟩
  | 3 => ⟨((-113263801/134217728), (-270316137/1073741824)), (5/67108864), by norm_num⟩
  | 4 => ⟨((1420551971/2147483648), (211893671/1073741824)), (127/2147483648), by norm_num⟩
  | 5 => ⟨((-445413249/1073741824), (-33219569/268435456)), (81/2147483648), by norm_num⟩
  | 6 => ⟨((232765111/1073741824), (277759377/4294967296)), (43/2147483648), by norm_num⟩
  | 7 => ⟨((-417047805/4294967296), (-248832263/8589934592)), (79/8589934592), by norm_num⟩
  | 8 => ⟨((326912745/8589934592), (390106061/34359738368)), (63/17179869184), by norm_num⟩
  | 9 => ⟨((-911140463/68719476736), (-271816733/68719476736)), (89/68719476736), by norm_num⟩
  | 10 => ⟨((285687565/68719476736), (170455959/137438953472)), (57/137438953472), by norm_num⟩
  | 11 => ⟨((-1302940665/1099511627776), (-388700853/1099511627776)), (33/274877906944), by norm_num⟩
  | 12 => ⟨((1361787639/4398046511104), (406256425/4398046511104)), (35/1099511627776), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581678330739479/10141204801825835211973625643008), (377653364099/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779248382440707/633825300114114700748351602688), (13973826433/19807040628566084398385987584)), (92245/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890281368491367/39614081257132168796771975168), (502979774589/39614081257132168796771975168)), (51889/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945045055934307/1237940039285380274899124224), (534319866381/2475880078570760549798248448)), (110267/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885878152639671/77371252455336267181195264), (133552934331/38685626227668133590597632)), (110271/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((3027507094789/18889465931478580854784), (250354323665/4835703278458516698824704)), (103383/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259252555256289/604462909807314587353088), (438005244557/604462909807314587353088)), (2827/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((472136431137945/18889465931478580854784), (711543304827/75557863725914323419136)), (147011/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649052307373729/2361183241434822606848), (266734618307/2361183241434822606848)), (110265/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622225051426907/590295810358705651712), (183303611149/147573952589676412928)), (151625/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824445548260615/73786976294838206464), (458029831325/36893488147419103232)), (189547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911874422141705/4611686018427387904), (514968610299/4611686018427387904)), (213261/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594996912988933/1152921504606846976), (514575215635/576460752303423488)), (213289/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597732470669319/72057594037927936), (899622293809/144115188075855872)), (186659/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492962684883643/36028797018963968), (336916695683/9007199254740992)), (280049/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490912562694985/9007199254740992), (420374085513/2251799813685248)), (43771/1125899906842624), by norm_num⟩
  | 2 => ⟨((2231252680060331/4503599627370496), (838437327079/1125899906842624)), (350331/2251799813685248), by norm_num⟩
  | 1 => ⟨((555261931413043/562949953421312), (312973657359/140737488355328)), (262953/562949953421312), by norm_num⟩
  | 0 => ⟨((2190569374461477/2251799813685248), (4961676126143/1125899906842624)), (2106927/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2190569374461477/2251799813685248), (4961676126143/1125899906842624)), (8037288674361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1065480084474185/1125899906842624), (19307037334083/2251799813685248)), (2058921/1125899906842624), by norm_num⟩
  | 2 => ⟨((126027479562081/140737488355328), (36541905092351/2251799813685248)), (3932171/1125899906842624), by norm_num⟩
  | 3 => ⟨((1805086588643659/2251799813685248), (65445024648423/2251799813685248)), (896247/140737488355328), by norm_num⟩
  | 4 => ⟨((1445090510032707/2251799813685248), (104924012843741/2251799813685248)), (23823907/2251799813685248), by norm_num⟩
  | 5 => ⟨((922496538586939/2251799813685248), (134669782201371/2251799813685248)), (16399061/1125899906842624), by norm_num⟩
  | 6 => ⟨((1479463508976265/9007199254740992), (220681087506985/4503599627370496)), (123183493/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7397559/4194304), (-1466072893/33554432)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-29991879/16777216), (-742986313/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1438644132646709/9007199254740992), (-224988112407869/4503599627370496)), (118781/8796093022208), by norm_num⟩
  | 1 => ⟨((-1090070843/2147483648), (340950171/2147483648)), (47/1073741824), by norm_num⟩
  | 2 => ⟨((433037977/536870912), (-270889499/1073741824)), (19/268435456), by norm_num⟩
  | 3 => ⟨((-229369667/268435456), (286967137/1073741824)), (83/1073741824), by norm_num⟩
  | 4 => ⟨((1457898297/2147483648), (-56999813/268435456)), (67/1073741824), by norm_num⟩
  | 5 => ⟨((-926655853/2147483648), (144918779/1073741824)), (87/2147483648), by norm_num⟩
  | 6 => ⟨((981654061/4294967296), (-307039787/4294967296)), (47/2147483648), by norm_num⟩
  | 7 => ⟨((-891356985/8589934592), (278796849/8589934592)), (87/8589934592), by norm_num⟩
  | 8 => ⟨((44262195/1073741824), (-443015697/34359738368)), (35/8589934592), by norm_num⟩
  | 9 => ⟨((-500151603/34359738368), (312872829/68719476736)), (101/68719476736), by norm_num⟩
  | 10 => ⟨((635803487/137438953472), (-397730677/274877906944)), (65/137438953472), by norm_num⟩
  | 11 => ⟨((-734770075/549755813888), (459639819/1099511627776)), (153/1099511627776), by norm_num⟩
  | 12 => ⟨((778379617/2199023255552), (-486920029/4398046511104)), (41/1099511627776), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581647146492273/10141204801825835211973625643008), (-394871232629/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779211449326471/633825300114114700748351602688), (-467530890213/633825300114114700748351602688)), (46123/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472559956163117/9903520314283042199192993792), (-65736207317/4951760157141521099596496896)), (103781/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945022989399625/1237940039285380274899124224), (-558655875713/2475880078570760549798248448)), (55135/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771712180374753/154742504910672534362390528), (-558541289027/154742504910672534362390528)), (55137/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550042274106943/9671406556917033397649408), (-130877685769/2417851639229258349412352)), (51693/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259216375305119/604462909807314587353088), (-228975110949/302231454903657293676544)), (90467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888486948383853/75557863725914323419136), (-743941042579/75557863725914323419136)), (18377/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((5070549011085/18446744073709551616), (-557756301193/4722366482869645213696)), (110269/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622164481143313/590295810358705651712), (-383295452775/295147905179352825856)), (151631/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824369870028463/73786976294838206464), (-957752877243/73786976294838206464)), (94777/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911831876925967/4611686018427387904), (-538402246749/4611686018427387904)), (213271/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594911881993063/1152921504606846976), (-537985377633/576460752303423488)), (53325/288230376151711744), by norm_num⟩
  | 5 => ⟨((37355956438397/4503599627370496), (-235134329711/36028797018963968)), (186669/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492851315407745/36028797018963968), (-704466975415/18014398509481984)), (70017/9007199254740992), by norm_num⟩
  | 3 => ⟨((372693396038723/2251799813685248), (-54934257405/281474976710656)), (175099/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230975421692093/4503599627370496), (-3505998225473/4503599627370496)), (700735/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220633580678109/2251799813685248), (-5234579331709/2251799813685248)), (525979/1125899906842624), by norm_num⟩
  | 0 => ⟨((547437007417859/562949953421312), (-10371891268183/2251799813685248)), (263421/281474976710656), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((547437007417859/562949953421312), (-10371891268183/2251799813685248)), (1004871369481944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532339600991689/562949953421312), (-10086077958813/1125899906842624)), (4118007/2251799813685248), by norm_num⟩
  | 2 => ⟨((2013394027797537/2251799813685248), (-19075296777393/1125899906842624)), (7861963/2251799813685248), by norm_num⟩
  | 3 => ⟨((1799582724340979/2251799813685248), (-17055729544277/562949953421312)), (3581395/562949953421312), by norm_num⟩
  | 4 => ⟨((22439297747575/35184372088832), (-54522069062047/1125899906842624)), (23765345/2251799813685248), by norm_num⟩
  | 5 => ⟨((910620836320713/2251799813685248), (-278177354061227/4503599627370496)), (32615015/2251799813685248), by norm_num⟩
  | 6 => ⟨((1438644132646709/9007199254740992), (-224988112407869/4503599627370496)), (118781/8796093022208), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29991879/16777216), (-742986313/16777216)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-60754247/33554432), (-1505059895/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((473847434462199/4503599627370496), (-1127856721119653/9007199254740992)), (10961799/562949953421312), by norm_num⟩
  | 1 => ⟨((-727298761/2147483648), (865562137/2147483648)), (17/268435456), by norm_num⟩
  | 2 => ⟨((146317775/268435456), (-174133565/268435456)), (111/1073741824), by norm_num⟩
  | 3 => ⟨((-627971665/1073741824), (373676215/536870912)), (121/1073741824), by norm_num⟩
  | 4 => ⟨((505340703/1073741824), (-601408667/1073741824)), (99/1073741824), by norm_num⟩
  | 5 => ⟨((-650651589/2147483648), (96792991/268435456)), (129/2147483648), by norm_num⟩
  | 6 => ⟨((43632639/268435456), (-830838983/4294967296)), (141/4294967296), by norm_num⟩
  | 7 => ⟨((-321024107/4294967296), (764105005/8589934592)), (131/8589934592), by norm_num⟩
  | 8 => ⟨((516668369/17179869184), (-307444891/8589934592)), (107/17179869184), by norm_num⟩
  | 9 => ⟨((-739151699/68719476736), (219917095/17179869184)), (155/68719476736), by norm_num⟩
  | 10 => ⟨((475847507/137438953472), (-1132617313/274877906944)), (201/274877906944), by norm_num⟩
  | 11 => ⟨((-278489825/274877906944), (165716113/137438953472)), (119/549755813888), by norm_num⟩
  | 12 => ⟨((298808055/1099511627776), (-88903265/274877906944)), (129/2199023255552), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581617235452561/10141204801825835211973625643008), (-70990955273/633825300114114700748351602688)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444793796183609/158456325028528675187087900672), (-1344811354031/633825300114114700748351602688)), (92333/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890198984650919/39614081257132168796771975168), (-1512671553517/39614081257132168796771975168)), (103883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890002531502911/2475880078570760549798248448), (-200864576685/309485009821345068724781056)), (110385/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771668671481311/154742504910672534362390528), (-401645670561/38685626227668133590597632)), (27599/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550001419111393/9671406556917033397649408), (-752908276693/4835703278458516698824704)), (103509/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259180561819927/604462909807314587353088), (-658617437527/302231454903657293676544)), (90581/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888428629005913/75557863725914323419136), (-1069920998301/37778931862957161709568)), (147217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324504175060241/1180591620717411303424), (-100268757703/295147905179352825856)), (110433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811052009134617/295147905179352825856), (-551242085651/147573952589676412928)), (37969/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912147015517833/36893488147419103232), (-688698662133/18446744073709551616)), (47473/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823578077429993/9223372036854775808), (-387149804569/1152921504606846976)), (213693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797412879684681/576460752303423488), (-773692059453/288230376151711744)), (213773/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597657373887509/72057594037927936), (-2705190611647/144115188075855872)), (23393/18014398509481984), by norm_num⟩
  | 4 => ⟨((373184132163763/9007199254740992), (-2026164331181/18014398509481984)), (140449/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490628357525571/9007199254740992), (-2527936988755/4503599627370496)), (351443/9007199254740992), by norm_num⟩
  | 2 => ⟨((557669940416671/1125899906842624), (-1260398839725/562949953421312)), (703849/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110088576640653/1125899906842624), (-15053579268969/2251799813685248)), (264547/562949953421312), by norm_num⟩
  | 0 => ⟨((2188783900902153/2251799813685248), (-14911723254959/1125899906842624)), (531519/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2188783900902153/2251799813685248), (-14911723254959/1125899906842624)), (2027584078075218023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2127136478907373/2251799813685248), (-28988846696587/1125899906842624)), (4189475/2251799813685248), by norm_num⟩
  | 2 => ⟨((2007881943807305/2251799813685248), (-109535906193805/2251799813685248)), (4065407/1125899906842624), by norm_num⟩
  | 3 => ⟨((223132167494017/281474976710656), (-195341670168425/2251799813685248)), (15291175/2251799813685248), by norm_num⟩
  | 4 => ⟨((699056665623489/1125899906842624), (-19356520949013/140737488355328)), (13448189/1125899906842624), by norm_num⟩
  | 5 => ⟨((825474849265819/2251799813685248), (-48072852339545/281474976710656)), (20398843/1125899906842624), by norm_num⟩
  | 6 => ⟨((473847434462199/4503599627370496), (-1127856721119653/9007199254740992)), (10961799/562949953421312), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60754247/33554432), (-1505059895/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-61494513/33554432), (-1523398447/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((54648159707537/2251799813685248), (-712167402950341/4503599627370496)), (54946447/2251799813685248), by norm_num⟩
  | 1 => ⟨((-169800739/2147483648), (553205049/1073741824)), (43/536870912), by norm_num⟩
  | 2 => ⟨((8644175/67108864), (-1802395455/2147483648)), (141/1073741824), by norm_num⟩
  | 3 => ⟨((-150205635/1073741824), (244682433/268435456)), (155/1073741824), by norm_num⟩
  | 4 => ⟨((122346115/1073741824), (-199299747/268435456)), (127/1073741824), by norm_num⟩
  | 5 => ⟨((-79723091/1073741824), (1038940505/2147483648)), (167/2147483648), by norm_num⟩
  | 6 => ⟨((173163685/4294967296), (-1128322821/4294967296)), (183/4294967296), by norm_num⟩
  | 7 => ⟨((-161195429/8589934592), (1050338479/8589934592)), (43/2147483648), by norm_num⟩
  | 8 => ⟨((262595135/34359738368), (-1711052081/34359738368)), (283/34359738368), by norm_num⟩
  | 9 => ⟨((-190124511/68719476736), (619419207/34359738368)), (207/68719476736), by norm_num⟩
  | 10 => ⟨((61944401/68719476736), (-1614502059/274877906944)), (17/17179869184), by norm_num⟩
  | 11 => ⟨((-18347349/68719476736), (956400649/549755813888)), (163/549755813888), by norm_num⟩
  | 12 => ⟨((159406491/2199023255552), (-1038681881/2199023255552)), (179/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581588497695471/10141204801825835211973625643008), (-1847773503993/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444784892116379/158456325028528675187087900672), (-2187617019869/633825300114114700748351602688)), (361/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((945079415775847/19807040628566084398385987584), (-1230334990721/19807040628566084398385987584)), (103981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889959759251783/2475880078570760549798248448), (-653493182637/618970019642690137449562112)), (3453/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442906444009711/38685626227668133590597632), (-326677824019/19342813113834066795298816)), (55257/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387490268454999/2417851639229258349412352), (-612374822385/2417851639229258349412352)), (51813/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157393141120273/75557863725914323419136), (-2142727635583/604462909807314587353088)), (22673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944185402840421/37778931862957161709568), (-1740418633367/37778931862957161709568)), (73705/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297973118615555/4722366482869645213696), (-652417503907/1180591620717411303424)), (110589/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622043745913771/590295810358705651712), (-1793370108357/295147905179352825856)), (152111/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824218169760955/73786976294838206464), (-4481092218607/73786976294838206464)), (190215/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823492018329015/9223372036854775808), (-5038022472059/9223372036854775808)), (107049/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797369403885291/576460752303423488), (-2517008569157/576460752303423488)), (214229/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195237663072435/144115188075855872), (-4400262443371/144115188075855872)), (187599/144115188075855872), by norm_num⟩
  | 4 => ⟨((373154725625733/9007199254740992), (-6591397174735/36028797018963968)), (8803/1125899906842624), by norm_num⟩
  | 3 => ⟨((1490477837664927/9007199254740992), (-8223521981599/9007199254740992)), (352641/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230368305345085/4503599627370496), (-2049993490661/562949953421312)), (706845/4503599627370496), by norm_num⟩
  | 1 => ⟨((2219684084062351/2251799813685248), (-12241226245541/1125899906842624)), (266047/562949953421312), by norm_num⟩
  | 0 => ⟨((2187695160710361/2251799813685248), (-24248324666481/1125899906842624)), (268013/281474976710656), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2187695160710361/2251799813685248), (-24248324666481/1125899906842624)), (1022388459325694949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2124370986322347/2251799813685248), (-94232075526069/2251799813685248)), (2129243/1125899906842624), by norm_num⟩
  | 2 => ⟨((2000209954764567/2251799813685248), (-44449752152013/562949953421312)), (8391413/2251799813685248), by norm_num⟩
  | 3 => ⟨((881345524489877/1125899906842624), (-315867640456965/2251799813685248)), (8116429/1125899906842624), by norm_num⟩
  | 4 => ⟨((1335512752771659/2251799813685248), (-61814671436605/281474976710656)), (29967983/2251799813685248), by norm_num⟩
  | 5 => ⟨((683474113797343/2251799813685248), (-293291726947501/1125899906842624)), (48709759/2251799813685248), by norm_num⟩
  | 6 => ⟨((54648159707537/2251799813685248), (-712167402950341/4503599627370496)), (54946447/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61494513/33554432), (-1523398447/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-31103419/16777216), (-1541044811/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-128726280690895/2251799813685248), (-1313417759160633/9007199254740992)), (246496779/9007199254740992), by norm_num⟩
  | 1 => ⟨((404606649/2147483648), (1032068889/2147483648)), (195/2147483648), by norm_num⟩
  | 2 => ⟨((-333379377/1073741824), (-850382673/1073741824)), (81/536870912), by norm_num⟩
  | 3 => ⟨((45781835/134217728), (934240855/1073741824)), (45/268435456), by norm_num⟩
  | 4 => ⟨((-301778919/1073741824), (-769776363/1073741824)), (299/2147483648), by norm_num⟩
  | 5 => ⟨((397845635/2147483648), (507411463/1073741824)), (199/2147483648), by norm_num⟩
  | 6 => ⟨((-54634763/536870912), (-1114896937/4294967296)), (221/4294967296), by norm_num⟩
  | 7 => ⟨((205791161/4294967296), (131232801/1073741824)), (105/4294967296), by norm_num⟩
  | 8 => ⟨((-42390881/2147483648), (-865043807/17179869184)), (175/17179869184), by norm_num⟩
  | 9 => ⟨((62094857/8589934592), (633565171/34359738368)), (129/34359738368), by norm_num⟩
  | 10 => ⟨((-163723615/68719476736), (-835250979/137438953472)), (171/137438953472), by norm_num⟩
  | 11 => ⟨((98110241/137438953472), (250259179/137438953472)), (207/549755813888), by norm_num⟩
  | 12 => ⟨((-215570233/1099511627776), (-549875619/1099511627776)), (115/1099511627776), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197695105578977/1267650600228229401496703205376), (-2532820395467/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((13899254533103/4951760157141521099596496896), (-1499276546719/316912650057057350374175801344)), (92495/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945059673758045/19807040628566084398385987584), (-3372814808263/39614081257132168796771975168)), (26019/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236239706169883/309485009821345068724781056), (-3582937041963/2475880078570760549798248448)), (110603/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771583488403053/154742504910672534362390528), (-3582173631133/154742504910672534362390528)), (27657/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774960620210499/4835703278458516698824704), (-3357476801763/9671406556917033397649408)), (25935/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259110086123107/604462909807314587353088), (-2936981388909/604462909807314587353088)), (90799/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472078376920215/18889465931478580854784), (-4771074833485/75557863725914323419136)), (36899/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297929836168827/4722366482869645213696), (-1788488271139/2361183241434822606848)), (110741/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101373983188147/36893488147419103232), (-4916182830233/590295810358705651712)), (76169/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824142399696151/73786976294838206464), (-6141989814021/73786976294838206464)), (190527/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823405745200231/9223372036854775808), (-1726321790855/2305843009213693952)), (26811/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797325623504827/576460752303423488), (-6899725743771/1152921504606846976)), (53667/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195159601739765/144115188075855872), (-1507751820495/36028797018963968)), (188039/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492498926459903/36028797018963968), (-9034015069959/36028797018963968)), (282465/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490322836912369/9007199254740992), (-11270672776451/9007199254740992)), (353795/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115021638569541/2251799813685248), (-5618973528993/1125899906842624)), (354867/2251799813685248), by norm_num⟩
  | 1 => ⟨((34674362552437/35184372088832), (-16775258138401/1125899906842624)), (534987/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093248705803509/1125899906842624), (-16612388948173/562949953421312)), (67547/70368744177664), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1093248705803509/1125899906842624), (-16612388948173/562949953421312)), (257671356469607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((132570493124849/140737488355328), (-129045025104053/2251799813685248)), (4325211/2251799813685248), by norm_num⟩
  | 2 => ⟨((1990643608716479/2251799813685248), (-243113086829579/2251799813685248)), (8644173/2251799813685248), by norm_num⟩
  | 3 => ⟨((54172749674119/70368744177664), (-429835289577195/2251799813685248)), (4287455/562949953421312), by norm_num⟩
  | 4 => ⟨((1252491849995857/2251799813685248), (-330904861462043/1125899906842624)), (32952567/2251799813685248), by norm_num⟩
  | 5 => ⟨((251075543677801/1125899906842624), (-736221114481625/2251799813685248)), (28013659/1125899906842624), by norm_num⟩
  | 6 => ⟨((-128726280690895/2251799813685248), (-1313417759160633/9007199254740992)), (246496779/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-31103419/16777216), (-1541044811/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile038Terms3
