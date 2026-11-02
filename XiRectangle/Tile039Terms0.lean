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
namespace Reinmann.XiRectangle.Tile039Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-24711795/67108864), (-1306636157/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-370918264441163/562949953421312), (475948526488055/2251799813685248)), (33135615/1125899906842624), by norm_num⟩
  | 1 => ⟨((61297643/134217728), (-157309713/1073741824)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((-679812615/4294967296), (1703731/33554432)), (65/8589934592), by norm_num⟩
  | 3 => ⟨((628280263/17179869184), (-403092937/34359738368)), (31/17179869184), by norm_num⟩
  | 4 => ⟨((-435490693/68719476736), (279402733/137438953472)), (45/137438953472), by norm_num⟩
  | 5 => ⟨((965949267/1099511627776), (-309867547/1099511627776)), (13/274877906944), by norm_num⟩
  | 6 => ⟨((-892726681/8796093022208), (143189211/4398046511104)), (25/4398046511104), by norm_num⟩
  | 7 => ⟨((1414379387/140737488355328), (-226859881/70368744177664)), (41/70368744177664), by norm_num⟩
  | 8 => ⟨((-245093271/281474976710656), (157247287/562949953421312)), (59/1125899906842624), by norm_num⟩
  | 9 => ⟨((604038079/9007199254740992), (-96884901/4503599627370496)), (75/18014398509481984), by norm_num⟩
  | 10 => ⟨((-1339799333/288230376151711744), (214897587/144115188075855872)), (85/288230376151711744), by norm_num⟩
  | 11 => ⟨((1350804553/4611686018427387904), (-216662773/2305843009213693952)), (11/576460752303423488), by norm_num⟩
  | 12 => ⟨((-624204245/36893488147419103232), (400477841/73786976294838206464)), (83/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791748050316401/5070602400912917605986812821504), (3687918434113/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781393110127713/633825300114114700748351602688), (2188375380233/316912650057057350374175801344)), (11579/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946346668605733/19807040628566084398385987584), (4923652071247/39614081257132168796771975168)), (6515/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892651801128573/2475880078570760549798248448), (653897520521/309485009821345068724781056)), (1731/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((887158419336913/77371252455336267181195264), (653869342023/19342813113834066795298816)), (27705/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552482904643319/9671406556917033397649408), (4903780300461/9671406556917033397649408)), (203/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((315337672647235/151115727451828646838272), (2145283860005/302231454903657293676544)), (22745/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891952892793629/75557863725914323419136), (6971721873595/75557863725914323419136)), (18489/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325164494337459/1180591620717411303424), (2614198238433/2361183241434822606848)), (13875/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625732653662573/590295810358705651712), (3594201144835/295147905179352825856)), (38181/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828825145308033/73786976294838206464), (2246134156409/18446744073709551616)), (11941/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828669147619723/9223372036854775808), (5053135990839/4611686018427387904)), (53787/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799954395120719/576460752303423488), (5052301305317/576460752303423488)), (13463/288230376151711744), by norm_num⟩
  | 5 => ⟨((599876679424733/72057594037927936), (8839642757773/144115188075855872)), (47195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499376371643431/36028797018963968), (13255678884191/36028797018963968)), (17735/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498896551045447/9007199254740992), (16562937994681/9007199254740992)), (44467/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123560696414479/2251799813685248), (2069109289547/281474976710656)), (22331/562949953421312), by norm_num⟩
  | 1 => ⟨((70143842913457/70368744177664), (3100487243589/140737488355328)), (8435/70368744177664), by norm_num⟩
  | 0 => ⟨((1118345310329501/1125899906842624), (49504618532217/1125899906842624)), (273829/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1118345310329501/1125899906842624), (49504618532217/1125899906842624)), (1044574741843795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108664738573821/1125899906842624), (1536639093057/17592186044416)), (568065/1125899906842624), by norm_num⟩
  | 2 => ⟨((1083103191860151/1125899906842624), (96839447586851/562949953421312)), (608989/562949953421312), by norm_num⟩
  | 3 => ⟨((1008616310277991/1125899906842624), (372633887406309/1125899906842624)), (86325/35184372088832), by norm_num⟩
  | 4 => ⟨((780221085352695/1125899906842624), (166908538812425/281474976710656)), (6777807/1125899906842624), by norm_num⟩
  | 5 => ⟨((144781588294191/1125899906842624), (1850616531937457/2251799813685248)), (34863787/2251799813685248), by norm_num⟩
  | 6 => ⟨((-370918264441163/562949953421312), (475948526488055/2251799813685248)), (33135615/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24711795/67108864), (-1306636157/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-9791817/16777216), (-64717791/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1207957030214395/2251799813685248), (-344790684115031/2251799813685248)), (26634855/562949953421312), by norm_num⟩
  | 1 => ⟨((1265598715/2147483648), (180621759/1073741824)), (57/1073741824), by norm_num⟩
  | 2 => ⟨((-1390402301/4294967296), (-49608321/536870912)), (1/33554432), by norm_num⟩
  | 3 => ⟨((254585509/2147483648), (145334163/4294967296)), (3/268435456), by norm_num⟩
  | 4 => ⟨((-1118763075/34359738368), (-319331795/34359738368)), (107/34359738368), by norm_num⟩
  | 5 => ⟨((491634745/68719476736), (280657467/137438953472)), (3/4294967296), by norm_num⟩
  | 6 => ⟨((-360077315/274877906944), (-51388957/137438953472)), (143/1099511627776), by norm_num⟩
  | 7 => ⟨((226048779/1099511627776), (258087039/4398046511104)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((-496679933/17592186044416), (-283537593/35184372088832)), (103/35184372088832), by norm_num⟩
  | 9 => ⟨((30314371/8796093022208), (8652719/8796093022208)), (51/140737488355328), by norm_num⟩
  | 10 => ⟨((-852575757/2251799813685248), (-30419147/281474976710656)), (91/2251799813685248), by norm_num⟩
  | 11 => ⟨((1362400297/36028797018963968), (97218469/9007199254740992)), (37/9007199254740992), by norm_num⟩
  | 12 => ⟨((-997833139/288230376151711744), (-284814413/288230376151711744)), (55/144115188075855872), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583215513741263/10141204801825835211973625643008), (-233131106641/633825300114114700748351602688)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781059939447407/633825300114114700748351602688), (-4425239022425/633825300114114700748351602688)), (23159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473079632121925/9903520314283042199192993792), (-1244525653893/9903520314283042199192993792)), (52121/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946126784815367/1237940039285380274899124224), (-2644457661289/1237940039285380274899124224)), (55395/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886959305176779/77371252455336267181195264), (-5288556518695/154742504910672534362390528)), (55413/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776054784515399/4835703278458516698824704), (-2478820135821/4835703278458516698824704)), (51969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315256006358721/151115727451828646838272), (-4337553508331/604462909807314587353088)), (45493/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891422068640677/75557863725914323419136), (-7047808146181/75557863725914323419136)), (73961/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650129932632065/2361183241434822606848), (-5285228780825/4722366482869645213696)), (55503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625185259617261/590295810358705651712), (-1816542277747/147573952589676412928)), (4773/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1828140918341987/73786976294838206464), (-9081178852505/73786976294838206464)), (5971/4611686018427387904), by norm_num⟩
  | 7 => ⟨((913949707251311/4611686018427387904), (-5107107990043/4611686018427387904)), (107585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399784771518105/288230376151711744), (-10211573709873/1152921504606846976)), (53859/576460752303423488), by norm_num⟩
  | 5 => ⟨((599539950940435/72057594037927936), (-8932148282381/144115188075855872)), (94403/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498366258578461/36028797018963968), (-3348062403445/9007199254740992)), (141903/36028797018963968), by norm_num⟩
  | 3 => ⟨((93602127840777/562949953421312), (-4182456259295/2251799813685248)), (177903/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122298412530647/2251799813685248), (-4178506389861/562949953421312)), (44673/562949953421312), by norm_num⟩
  | 1 => ⟨((1120408678343219/1125899906842624), (-25031298650443/1125899906842624)), (135005/562949953421312), by norm_num⟩
  | 0 => ⟨((278640635768083/281474976710656), (-12475549211731/281474976710656)), (547931/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((278640635768083/281474976710656), (-12475549211731/281474976710656)), (2090190891746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((137640946770125/140737488355328), (-98799403187761/1125899906842624)), (1133399/1125899906842624), by norm_num⟩
  | 2 => ⟨((1068230492957617/1125899906842624), (-96625593891181/562949953421312)), (2415839/1125899906842624), by norm_num⟩
  | 3 => ⟨((490172509029021/562949953421312), (-366705442170807/1125899906842624)), (2706757/562949953421312), by norm_num⟩
  | 4 => ⟨((734171366468615/1125899906842624), (-319298235253493/562949953421312)), (6476843/562949953421312), by norm_num⟩
  | 5 => ⟨((233061824414473/2251799813685248), (-1665651593093815/2251799813685248)), (31587895/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1207957030214395/2251799813685248), (-344790684115031/2251799813685248)), (26634855/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9791817/16777216), (-64717791/4194304)), (1/33554432), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-24711795/33554432), (-1306636157/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((876969049588283/2251799813685248), (-313594486215673/1125899906842624)), (6766491/281474976710656), by norm_num⟩
  | 1 => ⟨((-1159417389/2147483648), (207297453/536870912)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((401823447/1073741824), (-143687645/536870912)), (53/2147483648), by norm_num⟩
  | 3 => ⟨((-371363719/2147483648), (531182325/4294967296)), (51/4294967296), by norm_num⟩
  | 4 => ⟨((1029638859/17179869184), (-368187531/8589934592)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-1141906035/68719476736), (816666077/68719476736)), (83/68719476736), by norm_num⟩
  | 6 => ⟨((1055345265/274877906944), (-377379859/137438953472)), (79/274877906944), by norm_num⟩
  | 7 => ⟨((-418005483/549755813888), (149474163/274877906944)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((144869661/1099511627776), (-828860757/8796093022208)), (91/8796093022208), by norm_num⟩
  | 9 => ⟨((-714069313/35184372088832), (63835833/4398046511104)), (29/17592186044416), by norm_num⟩
  | 10 => ⟨((395964105/140737488355328), (-283184817/140737488355328)), (33/140737488355328), by norm_num⟩
  | 11 => ⟨((-199608293/562949953421312), (35688865/140737488355328)), (17/562949953421312), by norm_num⟩
  | 12 => ⟨((92238617/2251799813685248), (-263868119/9007199254740992)), (1/281474976710656), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583016434160221/10141204801825835211973625643008), (-202178378915/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780833729766783/633825300114114700748351602688), (-959184033561/633825300114114700748351602688)), (11537/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892064662902573/39614081257132168796771975168), (-539505145643/19807040628566084398385987584)), (51919/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891984592088273/2475880078570760549798248448), (-1146362217683/2475880078570760549798248448)), (55167/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773650481708709/154742504910672534362390528), (-1146265231581/154742504910672534362390528)), (55171/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551859100220363/9671406556917033397649408), (-1074520615751/9671406556917033397649408)), (3233/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260805766840427/604462909807314587353088), (-940102509911/604462909807314587353088)), (22633/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891069088570679/75557863725914323419136), (-763736710345/37778931862957161709568)), (18391/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299996608707617/4722366482869645213696), (-1145436073559/4722366482869645213696)), (13795/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812412841845861/295147905179352825856), (-1574700028989/590295810358705651712)), (18971/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1827695049939995/73786976294838206464), (-983981623805/36893488147419103232)), (94871/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827402762579075/9223372036854775808), (-2213392557301/9223372036854775808)), (106753/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598648618620507/1152921504606846976), (-553171276651/288230376151711744)), (53391/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198657696172277/144115188075855872), (-30239122179/2251799813685248)), (46733/72057594037927936), by norm_num⟩
  | 4 => ⟨((748873423038025/18014398509481984), (-2901365014471/36028797018963968)), (17533/4503599627370496), by norm_num⟩
  | 3 => ⟨((187110509264797/1125899906842624), (-1811961914341/4503599627370496)), (175443/9007199254740992), by norm_num⟩
  | 2 => ⟨((2243169669804401/4503599627370496), (-7239505583231/4503599627370496)), (175613/2251799813685248), by norm_num⟩
  | 1 => ⟨((2238858257180289/2251799813685248), (-10838421538039/2251799813685248)), (263845/1125899906842624), by norm_num⟩
  | 0 => ⟨((1112965700884375/1125899906842624), (-21593605773781/2251799813685248)), (1058789/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1112965700884375/1125899906842624), (-21593605773781/2251799813685248)), (4038959511763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1100076545761359/1125899906842624), (-21345540965567/1125899906842624)), (2113559/2251799813685248), by norm_num⟩
  | 2 => ⟨((1074440780271085/1125899906842624), (-83423859723583/2251799813685248)), (4210307/2251799813685248), by norm_num⟩
  | 3 => ⟨((127973532350805/140737488355328), (-159221963497615/2251799813685248)), (2086929/562949953421312), by norm_num⟩
  | 4 => ⟨((925308265968739/1125899906842624), (-144781588294199/1125899906842624)), (16361781/2251799813685248), by norm_num⟩
  | 5 => ⟨((1483673057764683/2251799813685248), (-237974263244043/1125899906842624)), (3887685/281474976710656), by norm_num⟩
  | 6 => ⟨((876969049588283/2251799813685248), (-313594486215673/1125899906842624)), (6766491/281474976710656), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24711795/33554432), (-1306636157/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-57379011/67108864), (-758478801/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-391561441398029/1125899906842624), (551172924150921/2251799813685248)), (85137845/2251799813685248), by norm_num⟩
  | 1 => ⟨((600999669/1073741824), (-422992039/1073741824)), (33/536870912), by norm_num⟩
  | 2 => ⟨((-967271653/2147483648), (21274357/67108864)), (27/536870912), by norm_num⟩
  | 3 => ⟨((1037842447/4294967296), (-730448143/4294967296)), (59/2147483648), by norm_num⟩
  | 4 => ⟨((-835171491/8589934592), (587805467/8589934592)), (97/8589934592), by norm_num⟩
  | 5 => ⟨((1075325329/34359738368), (-756829123/34359738368)), (127/34359738368), by norm_num⟩
  | 6 => ⟨((-1153779569/137438953472), (812046323/137438953472)), (139/137438953472), by norm_num⟩
  | 7 => ⟨((530553309/274877906944), (-373410897/274877906944)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((-426946305/1099511627776), (600981655/2199023255552)), (107/2199023255552), by norm_num⟩
  | 9 => ⟨((1221588569/17592186044416), (-429885627/8796093022208)), (155/17592186044416), by norm_num⟩
  | 10 => ⟨((-786428383/70368744177664), (553499381/70368744177664)), (101/70368744177664), by norm_num⟩
  | 11 => ⟨((460257329/281474976710656), (-80983899/70368744177664)), (15/70368744177664), by norm_num⟩
  | 12 => ⟨((-987674127/4503599627370496), (695138973/4503599627370496)), (131/4503599627370496), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197857752006023/1267650600228229401496703205376), (3293407986345/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445160739241031/158456325028528675187087900672), (3905422160385/633825300114114700748351602688)), (46293/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945924799974767/19807040628566084398385987584), (4393243002421/39614081257132168796771975168)), (52091/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891755540781883/2475880078570760549798248448), (4667410910811/2475880078570760549798248448)), (55361/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886710407625543/77371252455336267181195264), (4666949750417/154742504910672534362390528)), (55377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775821567247623/4835703278458516698824704), (4374775287137/9671406556917033397649408)), (51933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260616143608951/604462909807314587353088), (3827438136365/604462909807314587353088)), (45459/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472689931612855/18889465931478580854784), (1554666870755/18889465931478580854784)), (36951/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299763516219279/4722366482869645213696), (2331597885599/2361183241434822606848)), (27727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624503442103197/590295810358705651712), (3205292889049/295147905179352825856)), (76295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913644820108949/36893488147419103232), (4005634333335/36893488147419103232)), (95437/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826943093261993/9223372036854775808), (9009975826789/9223372036854775808)), (26865/2305843009213693952), by norm_num⟩
  | 6 => ⟨((12485816198957/9007199254740992), (2251649187585/288230376151711744)), (53789/576460752303423488), by norm_num⟩
  | 5 => ⟨((149780817313193/18014398509481984), (7876967541837/144115188075855872)), (94263/144115188075855872), by norm_num⟩
  | 4 => ⟨((748560029957643/18014398509481984), (11807834214859/36028797018963968)), (70829/18014398509481984), by norm_num⟩
  | 3 => ⟨((187010378842879/1125899906842624), (14746445186591/9007199254740992)), (1387/70368744177664), by norm_num⟩
  | 2 => ⟨((560378751504195/1125899906842624), (460199643775/70368744177664)), (178231/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118122593311281/1125899906842624), (22039318680081/1125899906842624)), (269087/1125899906842624), by norm_num⟩
  | 0 => ⟨((1110091584769699/1125899906842624), (43876847840823/1125899906842624)), (545155/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1110091584769699/1125899906842624), (43876847840823/1125899906842624)), (2079601292136764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((546397659917399/562949953421312), (86521580219167/1125899906842624)), (1117493/1125899906842624), by norm_num⟩
  | 2 => ⟨((1054015210408125/1125899906842624), (83977605250333/562949953421312)), (2341023/1125899906842624), by norm_num⟩
  | 3 => ⟨((480832756294341/562949953421312), (157231868889163/562949953421312)), (5081555/1125899906842624), by norm_num⟩
  | 4 => ⟨((733558205934181/1125899906842624), (134296543477473/281474976710656)), (11519179/1125899906842624), by norm_num⟩
  | 5 => ⟨((443269698375249/2251799813685248), (1399972852261965/2251799813685248)), (26002191/1125899906842624), by norm_num⟩
  | 6 => ⟨((-391561441398029/1125899906842624), (551172924150921/2251799813685248)), (85137845/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57379011/67108864), (-758478801/33554432)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-63879063/67108864), (-844401367/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((434389395385101/1125899906842624), (-56282716643743/4503599627370496)), (6787587/562949953421312), by norm_num⟩
  | 1 => ⟨((-371132523/536870912), (24043343/1073741824)), (3/134217728), by norm_num⟩
  | 2 => ⟨((1329960425/2147483648), (-43079887/2147483648)), (45/2147483648), by norm_num⟩
  | 3 => ⟨((-397161531/1073741824), (51459197/4294967296)), (55/4294967296), by norm_num⟩
  | 4 => ⟨((355808967/2147483648), (-11525313/2147483648)), (51/8589934592), by norm_num⟩
  | 5 => ⟨((-2040077075/34359738368), (16520471/8589934592)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((1218442473/68719476736), (-19733807/34359738368)), (47/68719476736), by norm_num⟩
  | 7 => ⟨((-623758811/137438953472), (10102353/68719476736)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((279406439/274877906944), (-36201973/1099511627776)), (47/1099511627776), by norm_num⟩
  | 9 => ⟨((-1780014695/8796093022208), (14414495/2199023255552)), (77/8796093022208), by norm_num⟩
  | 10 => ⟨((637871637/17592186044416), (-41323693/35184372088832)), (57/35184372088832), by norm_num⟩
  | 11 => ⟨((-1662418249/281474976710656), (53848813/281474976710656)), (19/70368744177664), by norm_num⟩
  | 12 => ⟨((1985769093/2251799813685248), (-64322747/2251799813685248)), (93/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582735847268683/10141204801825835211973625643008), (-21089631219/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780501484436941/633825300114114700748351602688), (-25004728803/316912650057057350374175801344)), (46103/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945845472376187/19807040628566084398385987584), (-28127924035/19807040628566084398385987584)), (25933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891587586978839/2475880078570760549798248448), (-14941508031/618970019642690137449562112)), (13777/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773253555812989/154742504910672534362390528), (-3734968803/9671406556917033397649408)), (13777/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387871766585657/2417851639229258349412352), (-56017593575/9671406556917033397649408)), (3229/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260480321329961/604462909807314587353088), (-49008457045/604462909807314587353088)), (22603/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472635099332173/18889465931478580854784), (-39812868807/37778931862957161709568)), (18365/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1299600228238577/4722366482869645213696), (-59707926177/4722366482869645213696)), (6887/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624280884668277/590295810358705651712), (-82079915341/590295810358705651712)), (75757/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827014387224835/73786976294838206464), (-12821522171/9223372036854775808)), (94697/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913318739460447/4611686018427387904), (-115355601795/9223372036854775808)), (13317/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399470978011291/288230376151711744), (-57653999453/576460752303423488)), (106537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197989226741729/144115188075855872), (-100840972307/144115188075855872)), (93221/144115188075855872), by norm_num⟩
  | 4 => ⟨((374186359647053/9007199254740992), (-151154471241/36028797018963968)), (139835/36028797018963968), by norm_num⟩
  | 3 => ⟨((93477161355563/562949953421312), (-94378005191/4503599627370496)), (10925/562949953421312), by norm_num⟩
  | 2 => ⟨((560169369214989/1125899906842624), (-11779730629/140737488355328)), (174809/2251799813685248), by norm_num⟩
  | 1 => ⟨((2235136916512135/2251799813685248), (-564027550197/2251799813685248)), (131119/562949953421312), by norm_num⟩
  | 0 => ⟨((1109278164730623/1125899906842624), (-561234746151/1125899906842624)), (524573/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1109278164730623/1125899906842624), (-561234746151/1125899906842624)), (2001087193015670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2185803061684941/2251799813685248), (-1105898393649/1125899906842624)), (1034181/1125899906842624), by norm_num⟩
  | 2 => ⟨((2121738399386001/2251799813685248), (-4293944923629/2251799813685248)), (4019547/2251799813685248), by norm_num⟩
  | 3 => ⟨((999590498699479/1125899906842624), (-8091863027915/2251799813685248)), (474381/140737488355328), by norm_num⟩
  | 4 => ⟨((55464788069529/70368744177664), (-3592037511649/562949953421312)), (13531749/2251799813685248), by norm_num⟩
  | 5 => ⟨((1398867020901463/2251799813685248), (-22650010501071/2251799813685248)), (21504191/2251799813685248), by norm_num⟩
  | 6 => ⟨((434389395385101/1125899906842624), (-56282716643743/4503599627370496)), (6787587/562949953421312), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-63879063/67108864), (-844401367/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-69374779/67108864), (-458523931/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-469647585173463/2251799813685248), (-324365429875665/1125899906842624)), (142360159/4503599627370496), by norm_num⟩
  | 1 => ⟨((871555331/2147483648), (150486465/268435456)), (67/1073741824), by norm_num⟩
  | 2 => ⟨((-423992091/1073741824), (-585666279/1073741824)), (33/536870912), by norm_num⟩
  | 3 => ⟨((550033675/2147483648), (94971163/268435456)), (87/2147483648), by norm_num⟩
  | 4 => ⟨((-535158055/4294967296), (-92402675/536870912)), (43/2147483648), by norm_num⟩
  | 5 => ⟨((833095593/17179869184), (287691685/4294967296)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((-270188195/17179869184), (-93303695/4294967296)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((600870801/137438953472), (829991347/137438953472)), (51/68719476736), by norm_num⟩
  | 8 => ⟨((-584620295/549755813888), (-807544293/549755813888)), (25/137438953472), by norm_num⟩
  | 9 => ⟨((505608251/2199023255552), (349201919/1099511627776)), (11/274877906944), by norm_num⟩
  | 10 => ⟨((-393547291/8796093022208), (-1087224893/17592186044416)), (139/17592186044416), by norm_num⟩
  | 11 => ⟨((556951031/70368744177664), (769324347/70368744177664)), (25/17592186044416), by norm_num⟩
  | 12 => ⟨((-45157361/35184372088832), (-998024037/562949953421312)), (33/140737488355328), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197828646634871/1267650600228229401496703205376), (-1431189059527/5070602400912917605986812821504)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890184437304051/316912650057057350374175801344), (-1696647334709/316912650057057350374175801344)), (11567/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891541406103889/39614081257132168796771975168), (-3817090864513/39614081257132168796771975168)), (26031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236428533001525/309485009821345068724781056), (-2027614797705/1237940039285380274899124224)), (1729/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1773093740075847/154742504910672534362390528), (-2027373196369/77371252455336267181195264)), (55341/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775668357845007/4835703278458516698824704), (-3800811300279/9671406556917033397649408)), (51897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260348241300609/604462909807314587353088), (-3325196399753/604462909807314587353088)), (45425/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890324786670669/75557863725914323419136), (-5402481263965/75557863725914323419136)), (73843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299437662616255/4722366482869645213696), (-4051018327557/4722366482869645213696)), (27703/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624055964050505/590295810358705651712), (-5568780763517/590295810358705651712)), (1191/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1826731148451373/73786976294838206464), (-1739730371763/18446744073709551616)), (95339/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456578991614745/2305843009213693952), (-1956490318641/2305843009213693952)), (107337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798779408385225/576460752303423488), (-1955607192549/288230376151711744)), (6715/72057594037927936), by norm_num⟩
  | 5 => ⟨((149712592770665/18014398509481984), (-3420325035049/72057594037927936)), (94125/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496304670432477/36028797018963968), (-5126511158709/18014398509481984)), (17677/4503599627370496), by norm_num⟩
  | 3 => ⟨((1495069574272667/9007199254740992), (-12802354743143/9007199254740992)), (44293/2251799813685248), by norm_num⟩
  | 2 => ⟨((1119752710239539/2251799813685248), (-12781458537613/2251799813685248)), (177777/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116637039161875/1125899906842624), (-4779976866879/281474976710656)), (134089/562949953421312), by norm_num⟩
  | 0 => ⟨((1107206869441963/1125899906842624), (-38030457327173/1125899906842624)), (542419/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1107206869441963/1125899906842624), (-38030457327173/1125899906842624)), (2069164280418014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1087539601534145/1125899906842624), (-18699523529915/281474976710656)), (1103471/1125899906842624), by norm_num⟩
  | 2 => ⟨((261379280446475/281474976710656), (-72249663562481/562949953421312)), (2278367/1125899906842624), by norm_num⟩
  | 3 => ⟨((476163995525483/562949953421312), (-134182905316473/562949953421312)), (4816227/1125899906842624), by norm_num⟩
  | 4 => ⟨((741547618174901/1125899906842624), (-453987555649671/1125899906842624)), (10443449/1125899906842624), by norm_num⟩
  | 5 => ⟨((610690465905083/2251799813685248), (-598016552851737/1125899906842624)), (22178723/1125899906842624), by norm_num⟩
  | 6 => ⟨((-469647585173463/2251799813685248), (-324365429875665/1125899906842624)), (142360159/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69374779/67108864), (-458523931/16777216)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-74135385/67108864), (-489988559/16777216)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-445255243371561/2251799813685248), (1197207235500129/4503599627370496)), (99659507/2251799813685248), by norm_num⟩
  | 1 => ⟨((441495061/1073741824), (-1187096815/2147483648)), (25/268435456), by norm_num⟩
  | 2 => ⟨((-459031585/1073741824), (2410643/4194304)), (53/536870912), by norm_num⟩
  | 3 => ⟨((318176449/1073741824), (-213879091/536870912)), (149/2147483648), by norm_num⟩
  | 4 => ⟨((-330814663/2147483648), (889498133/4294967296)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((275163901/4294967296), (-184965937/2147483648)), (67/4294967296), by norm_num⟩
  | 6 => ⟨((-762916329/34359738368), (512834471/17179869184)), (47/8589934592), by norm_num⟩
  | 7 => ⟨((453268545/68719476736), (-1218753489/137438953472)), (113/68719476736), by norm_num⟩
  | 8 => ⟨((-471272721/274877906944), (633581659/274877906944)), (119/274877906944), by norm_num⟩
  | 9 => ⟨((435548477/1099511627776), (-1171107575/2199023255552)), (223/2199023255552), by norm_num⟩
  | 10 => ⟨((-724558077/8796093022208), (974099897/8796093022208)), (47/2199023255552), by norm_num⟩
  | 11 => ⟨((273941121/17592186044416), (-184143981/8796093022208)), (9/2199023255552), by norm_num⟩
  | 12 => ⟨((-759526063/281474976710656), (510555525/140737488355328)), (101/140737488355328), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582536767687641/10141204801825835211973625643008), (719801227187/2535301200456458802993406410752)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1780259263750573/633825300114114700748351602688), (3412843588459/633825300114114700748351602688)), (34701/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945709051315915/19807040628566084398385987584), (1919528704909/19807040628566084398385987584)), (78093/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29551519736971/38685626227668133590597632), (4078537056353/2475880078570760549798248448)), (82993/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772962749473315/154742504910672534362390528), (2039008933761/77371252455336267181195264)), (41507/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551213922894987/9671406556917033397649408), (3822590082555/9671406556917033397649408)), (9731/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((39382525266009/18889465931478580854784), (1672107310051/302231454903657293676544)), (68139/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945075114433699/37778931862957161709568), (5433314244311/75557863725914323419136)), (6923/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649653381104161/2361183241434822606848), (4074080412359/4722366482869645213696)), (83113/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623876005199071/590295810358705651712), (5600389367767/590295810358705651712)), (114339/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826506243788065/73786976294838206464), (3499139838495/36893488147419103232)), (143013/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826063009217469/9223372036854775808), (3935014793957/4611686018427387904)), (161013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597305935370853/1152921504606846976), (7866235211325/1152921504606846976)), (161167/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197479556552569/144115188075855872), (6878686362209/144115188075855872)), (141195/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495973063960233/36028797018963968), (2577372181067/9007199254740992)), (106069/18014398509481984), by norm_num⟩
  | 3 => ⟨((747327684356447/4503599627370496), (12871910175265/9007199254740992)), (66445/2251799813685248), by norm_num⟩
  | 2 => ⟨((1119338961713875/2251799813685248), (12849475565255/2251799813685248)), (66673/562949953421312), by norm_num⟩
  | 1 => ⟨((1116017570253729/1125899906842624), (19218097373815/1125899906842624)), (25145/70368744177664), by norm_num⟩
  | 0 => ⟨((1105972614605583/1125899906842624), (38211556977833/1125899906842624)), (813793/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1105972614605583/1125899906842624), (38211556977833/1125899906842624)), (3104373936179732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1085101165517379/1125899906842624), (75070501955075/1125899906842624)), (1654019/1125899906842624), by norm_num⟩
  | 2 => ⟨((520387714761211/562949953421312), (144700410173873/1125899906842624)), (1704367/562949953421312), by norm_num⟩
  | 3 => ⟨((471744992399923/562949953421312), (267520461873231/1125899906842624)), (7178209/1125899906842624), by norm_num⟩
  | 4 => ⟨((363534160062405/562949953421312), (28022348497905/70368744177664)), (15441669/1125899906842624), by norm_num⟩
  | 5 => ⟨((145485324322159/562949953421312), (1158137015882163/2251799813685248)), (64483665/2251799813685248), by norm_num⟩
  | 6 => ⟨((-445255243371561/2251799813685248), (1197207235500129/4503599627370496)), (99659507/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74135385/67108864), (-489988559/16777216)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile039Terms0
