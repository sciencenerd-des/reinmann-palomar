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
namespace Reinmann.XiRectangle.Tile028Terms3
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
  | 0 => ⟨((-45376701/16777216), (-1211071739/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-42848200915715/18014398509481984), (602136845423929/9007199254740992)), (24725903/9007199254740992), by norm_num⟩
  | 1 => ⟨((252619949/34359738368), (-7100031097/34359738368)), (147/17179869184), by norm_num⟩
  | 2 => ⟨((-195214747/17179869184), (5486624385/17179869184)), (229/17179869184), by norm_num⟩
  | 3 => ⟨((12571189/1073741824), (-5653129633/17179869184)), (119/8589934592), by norm_num⟩
  | 4 => ⟨((-38858079/4294967296), (4368515923/17179869184)), (93/8589934592), by norm_num⟩
  | 5 => ⟨((192179155/34359738368), (-5401307271/34359738368)), (29/4294967296), by norm_num⟩
  | 6 => ⟨((-198011309/68719476736), (86956615/1073741824)), (241/68719476736), by norm_num⟩
  | 7 => ⟨((174874675/137438953472), (-2457477381/68719476736)), (215/137438953472), by norm_num⟩
  | 8 => ⟨((-135136261/274877906944), (7596166913/549755813888)), (167/274877906944), by norm_num⟩
  | 9 => ⟨((92824871/549755813888), (-2608897157/549755813888)), (231/1099511627776), by norm_num⟩
  | 10 => ⟨((-114770247/2199023255552), (6451369495/4398046511104)), (9/137438953472), by norm_num⟩
  | 11 => ⟨((258007059/17592186044416), (-3625719453/8796093022208)), (163/8796093022208), by norm_num⟩
  | 12 => ⟨((-66459231/17592186044416), (1867875459/17592186044416)), (169/35184372088832), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (1046232565199/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444448762699401/158456325028528675187087900672), (2473748804797/633825300114114700748351602688)), (2889/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888646513894803/39614081257132168796771975168), (695578800783/9903520314283042199192993792)), (26005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472088310254699/618970019642690137449562112), (2955394254243/2475880078570760549798248448)), (13817/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770019616988493/154742504910672534362390528), (2954477044675/154742504910672534362390528)), (3455/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774227840648783/4835703278458516698824704), (2768848050257/9671406556917033397649408)), (25917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157228536505339/75557863725914323419136), (2421768265405/604462909807314587353088)), (5671/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886231660964243/75557863725914323419136), (1966774223649/37778931862957161709568)), (18435/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324092346460067/1180591620717411303424), (1474282662467/2361183241434822606848)), (27661/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809919815006413/295147905179352825856), (4051685398419/590295810358705651712)), (38049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113841534345911/4611686018427387904), (5060721650411/73786976294838206464)), (47583/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820396291401599/9223372036854775808), (177749199187/288230376151711744)), (53561/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591645699776133/1152921504606846976), (2840654652449/576460752303423488)), (26799/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192534138703715/144115188075855872), (4963656758729/144115188075855872)), (46941/144115188075855872), by norm_num⟩
  | 4 => ⟨((93035593953821/2251799813685248), (1857632661203/9007199254740992)), (70495/36028797018963968), by norm_num⟩
  | 3 => ⟨((742713192382613/4503599627370496), (1157755654287/1125899906842624)), (88267/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110148130658279/2251799813685248), (18445945058135/4503599627370496)), (176979/4503599627370496), by norm_num⟩
  | 1 => ⟨((275581634814393/281474976710656), (27474283253117/2251799813685248)), (133293/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157940823813303/2251799813685248), (54174391346307/2251799813685248)), (268833/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2157940823813303/2251799813685248), (54174391346307/2251799813685248)), (1025516514304732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033345350265845/1125899906842624), (51916307116177/1125899906842624)), (528191/1125899906842624), by norm_num⟩
  | 2 => ⟨((1892010654763007/2251799813685248), (190594116707655/2251799813685248)), (2036507/2251799813685248), by norm_num⟩
  | 3 => ⟨((786788012610711/1125899906842624), (320282555629017/2251799813685248)), (1883489/1125899906842624), by norm_num⟩
  | 4 => ⟨((131759080963045/281474976710656), (223816054949241/1125899906842624)), (792047/281474976710656), by norm_num⟩
  | 5 => ⟨((101107415864811/562949953421312), (838150461529675/4503599627370496)), (16902687/4503599627370496), by norm_num⟩
  | 6 => ⟨((-42848200915715/18014398509481984), (602136845423929/9007199254740992)), (24725903/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-1211071739/33554432)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-184117023/67108864), (-4913951833/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((269402671544991/9007199254740992), (256554234745135/4503599627370496)), (19560381/9007199254740992), by norm_num⟩
  | 1 => ⟨((-402789363/4294967296), (-1534317625/8589934592)), (119/17179869184), by norm_num⟩
  | 2 => ⟨((631471859/4294967296), (4810844039/17179869184)), (189/17179869184), by norm_num⟩
  | 3 => ⟨((-1319984241/8589934592), (-5028124553/17179869184)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((517350369/4294967296), (3941413863/17179869184)), (159/17179869184), by norm_num⟩
  | 5 => ⟨((-2595438543/34359738368), (-1235828037/8589934592)), (201/34359738368), by norm_num⟩
  | 6 => ⟨((1356330423/34359738368), (5166575549/68719476736)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((-151884507/8589934592), (-4628505071/137438953472)), (3/2147483648), by norm_num⟩
  | 8 => ⟨((1904931973/274877906944), (113380085/8589934592)), (153/274877906944), by norm_num⟩
  | 9 => ⟨((-2654623637/1099511627776), (-1264009247/274877906944)), (215/1099511627776), by norm_num⟩
  | 10 => ⟨((416177853/549755813888), (1585317473/1099511627776)), (17/274877906944), by norm_num⟩
  | 11 => ⟨((-1898070183/8796093022208), (-3615093649/8796093022208)), (157/8796093022208), by norm_num⟩
  | 12 => ⟨((1983796027/35184372088832), (3778368409/35184372088832)), (83/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395100494305569/2535301200456458802993406410752), (1416352654285/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222217116708997/79228162514264337593543950336), (1674329236221/633825300114114700748351602688)), (5773/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888581245138283/39614081257132168796771975168), (470793737251/9903520314283042199192993792)), (25981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888284043168709/2475880078570760549798248448), (2000313618311/2475880078570760549798248448)), (3451/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1769950587934499/154742504910672534362390528), (249960524357/19342813113834066795298816)), (6903/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774195572884001/4835703278458516698824704), (234254429507/1208925819614629174706176)), (25889/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257772002508311/604462909807314587353088), (409778202265/151115727451828646838272)), (22657/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886140525868773/75557863725914323419136), (665576519943/18889465931478580854784)), (36825/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648150663831935/2361183241434822606848), (1995634489231/4722366482869645213696)), (27625/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404936631441709/147573952589676412928), (1371109561405/295147905179352825856)), (37993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821348881772873/73786976294838206464), (3425108534397/73786976294838206464)), (23753/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910133571588479/4611686018427387904), (3849585596981/9223372036854775808)), (6683/1152921504606846976), by norm_num⟩
  | 6 => ⟨((397879442862395/288230376151711744), (480626722405/144115188075855872)), (26745/576460752303423488), by norm_num⟩
  | 5 => ⟨((596211785109653/72057594037927936), (52488292419/2251799813685248)), (2927/9007199254740992), by norm_num⟩
  | 4 => ⟨((93025398699713/2251799813685248), (5028620746449/36028797018963968)), (35153/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485227234770871/9007199254740992), (6267868102909/9007199254740992)), (87983/9007199254740992), by norm_num⟩
  | 2 => ⟨((554978036641733/1125899906842624), (12482168344997/4503599627370496)), (44067/1125899906842624), by norm_num⟩
  | 1 => ⟨((2204112090528331/2251799813685248), (9294938043129/1125899906842624)), (265161/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156997919602175/2251799813685248), (36649493938233/2251799813685248)), (266693/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156997919602175/2251799813685248), (36649493938233/2251799813685248)), (1017353062156295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2065590738348081/2251799813685248), (70213063966699/2251799813685248)), (129903/281474976710656), by norm_num⟩
  | 2 => ⟨((1892590628215353/2251799813685248), (128813808189547/2251799813685248)), (1971383/2251799813685248), by norm_num⟩
  | 3 => ⟨((1583314052679215/2251799813685248), (108265310567409/1125899906842624)), (1769679/1125899906842624), by norm_num⟩
  | 4 => ⟨((546229257274977/1125899906842624), (304499514738869/2251799813685248)), (5657959/2251799813685248), by norm_num⟩
  | 5 => ⟨((244414633318365/1125899906842624), (295455293611019/2251799813685248)), (3510051/1125899906842624), by norm_num⟩
  | 6 => ⟨((269402671544991/9007199254740992), (256554234745135/4503599627370496)), (19560381/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-184117023/67108864), (-4913951833/134217728)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-373232269/134217728), (-1245162833/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((115959946975415/2251799813685248), (310813602583425/9007199254740992)), (3545603/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2811637525/17179869184), (-942022667/8589934592)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((4467767703/17179869184), (2993798745/17179869184)), (71/8589934592), by norm_num⟩
  | 3 => ⟨((-1183233855/4294967296), (-3171484523/17179869184)), (153/17179869184), by norm_num⟩
  | 4 => ⟨((3760380885/17179869184), (1259893567/8589934592)), (123/17179869184), by norm_num⟩
  | 5 => ⟨((-2390138575/17179869184), (-3203207661/34359738368)), (79/17179869184), by norm_num⟩
  | 6 => ⟨((2531996351/34359738368), (3393322125/68719476736)), (85/34359738368), by norm_num⟩
  | 7 => ⟨((-2299091629/68719476736), (-3081188679/137438953472)), (39/34359738368), by norm_num⟩
  | 8 => ⟨((3653318479/274877906944), (2448045871/274877906944)), (63/137438953472), by norm_num⟩
  | 9 => ⟨((-2580098397/549755813888), (-1728893679/549755813888)), (91/549755813888), by norm_num⟩
  | 10 => ⟨((3279876637/2199023255552), (2197806871/2199023255552)), (59/1099511627776), by norm_num⟩
  | 11 => ⟨((-236900557/549755813888), (-1269954281/4398046511104)), (139/8796093022208), by norm_num⟩
  | 12 => ⟨((501921815/4398046511104), (1345327689/17592186044416)), (149/35184372088832), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790176734201497/5070602400912917605986812821504), (769019803551/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888840325857715/316912650057057350374175801344), (454517141131/316912650057057350374175801344)), (23073/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236064750130463/4951760157141521099596496896), (511209639839/19807040628566084398385987584)), (25959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888216943310703/2475880078570760549798248448), (1086012528575/2475880078570760549798248448)), (27583/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884941798536949/77371252455336267181195264), (271416566061/38685626227668133590597632)), (27585/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548328457558739/9671406556917033397649408), (508722185407/4835703278458516698824704)), (25863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628858632974775/302231454903657293676544), (889896245823/604462909807314587353088)), (2829/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943025897773951/37778931862957161709568), (1445392557523/75557863725914323419136)), (9195/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296234969228597/4722366482869645213696), (1083442049225/4722366482869645213696)), (27589/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809827795074661/295147905179352825856), (744377328649/295147905179352825856)), (9485/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455308918103821/18446744073709551616), (929738643005/36893488147419103232)), (5929/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820140414268505/9223372036854775808), (261237263007/1152921504606846976)), (13343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795695915203293/576460752303423488), (32615370811/18014398509481984)), (26693/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192314255879585/144115188075855872), (911818061025/72057594037927936)), (46729/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488244170154613/36028797018963968), (2729814944221/36028797018963968)), (70125/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485027545050867/9007199254740992), (850605644441/2251799813685248)), (43855/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219521931081375/4503599627370496), (6775396899107/4503599627370496)), (175587/4503599627370496), by norm_num⟩
  | 1 => ⟨((275443687523091/281474976710656), (5044894470011/1125899906842624)), (263801/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155962614491073/2251799813685248), (4972057522453/562949953421312)), (132325/562949953421312), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155962614491073/2251799813685248), (4972057522453/562949953421312)), (504779817821311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2064028616194181/2251799813685248), (2380222715705/140737488355328)), (63931/140737488355328), by norm_num⟩
  | 2 => ⟨((945635518925973/1125899906842624), (69815766297133/2251799813685248)), (238725/281474976710656), by norm_num⟩
  | 3 => ⟨((793150411436443/1125899906842624), (58637777648233/1125899906842624)), (3326481/2251799813685248), by norm_num⟩
  | 4 => ⟨((555688105480701/1125899906842624), (165231659350037/2251799813685248)), (314577/140737488355328), by norm_num⟩
  | 5 => ⟨((134098907649189/562949953421312), (163100231542143/2251799813685248)), (11413917/4503599627370496), by norm_num⟩
  | 6 => ⟨((115959946975415/2251799813685248), (310813602583425/9007199254740992)), (3545603/2251799813685248), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-373232269/134217728), (-1245162833/33554432)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-378026425/134217728), (-5044627631/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1070554113342931/18014398509481984), (61128477033717/9007199254740992)), (1170429/1125899906842624), by norm_num⟩
  | 1 => ⟨((-6572686681/34359738368), (-187649705/8589934592)), (117/34359738368), by norm_num⟩
  | 2 => ⟨((2644582783/8589934592), (604021099/17179869184)), (3/536870912), by norm_num⟩
  | 3 => ⟨((-5675055725/17179869184), (-324044819/8589934592)), (105/17179869184), by norm_num⟩
  | 4 => ⟨((570853115/2147483648), (521530017/17179869184)), (43/8589934592), by norm_num⟩
  | 5 => ⟨((-5880016933/34359738368), (-671496145/34359738368)), (113/34359738368), by norm_num⟩
  | 6 => ⟨((6309014785/68719476736), (720487569/68719476736)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-725283399/17179869184), (-165654287/34359738368)), (115/137438953472), by norm_num⟩
  | 8 => ⟨((4669194399/274877906944), (133305145/68719476736)), (95/274877906944), by norm_num⟩
  | 9 => ⟨((-6679803099/1099511627776), (-381415741/549755813888)), (69/549755813888), by norm_num⟩
  | 10 => ⟨((2150145671/1099511627776), (491091963/2199023255552)), (45/1099511627776), by norm_num⟩
  | 11 => ⟨((-2516746153/4398046511104), (-287411645/4398046511104)), (107/8796093022208), by norm_num⟩
  | 12 => ⟨((1350182225/8796093022208), (616761597/35184372088832)), (117/35184372088832), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940097431/10141204801825835211973625643008), (148116189101/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222203260074843/79228162514264337593543950336), (5471037067/19807040628566084398385987584)), (23055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236057080824543/4951760157141521099596496896), (24613721241/4951760157141521099596496896)), (12969/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944075902114637/1237940039285380274899124224), (209156565637/2475880078570760549798248448)), (27559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442454628551801/38685626227668133590597632), (209089030441/154742504910672534362390528)), (27559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774133751029027/4835703278458516698824704), (48987310185/2417851639229258349412352)), (25837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257663989526747/604462909807314587353088), (85691947537/302231454903657293676544)), (1413/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((942982666543789/37778931862957161709568), (69591120855/18889465931478580854784)), (18369/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648085110022753/2361183241434822606848), (208655883451/4722366482869645213696)), (13777/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619566718538619/590295810358705651712), (71677768569/147573952589676412928)), (37/576460752303423488), by norm_num⟩
  | 8 => ⟨((1821124820352683/73786976294838206464), (11190716753/2305843009213693952)), (23681/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820016031668235/9223372036854775808), (100618268329/2305843009213693952)), (13321/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198908481810403/144115188075855872), (100495687099/288230376151711744)), (53287/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192206233379663/144115188075855872), (175592047901/72057594037927936)), (23315/72057594037927936), by norm_num⟩
  | 4 => ⟨((744041523290187/18014398509481984), (525676538629/36028797018963968)), (69951/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484827727353127/9007199254740992), (327587942429/4503599627370496)), (43725/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219127031926987/4503599627370496), (1304610442183/4503599627370496)), (21867/562949953421312), by norm_num⟩
  | 1 => ⟨((1101484454086893/1125899906842624), (1942625278823/2251799813685248)), (131249/1125899906842624), by norm_num⟩
  | 0 => ⟨((1077423978463011/1125899906842624), (1914232524451/1125899906842624)), (262695/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077423978463011/1125899906842624), (1914232524451/1125899906842624)), (1002101902488326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1031031939896203/1125899906842624), (3663629439283/1125899906842624)), (503663/1125899906842624), by norm_num⟩
  | 2 => ⟨((1888291192574093/2251799813685248), (13419732766255/2251799813685248)), (1851455/2251799813685248), by norm_num⟩
  | 3 => ⟨((1583383885661759/2251799813685248), (11253381866013/1125899906842624)), (3127217/2251799813685248), by norm_num⟩
  | 4 => ⟨((556576557055797/1125899906842624), (31651878461935/2251799813685248)), (4460405/2251799813685248), by norm_num⟩
  | 5 => ⟨((274915204833397/1125899906842624), (62587068110149/4503599627370496)), (9070601/4503599627370496), by norm_num⟩
  | 6 => ⟨((1070554113342931/18014398509481984), (61128477033717/9007199254740992)), (1170429/1125899906842624), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/134217728), (-5044627631/134217728)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-191316263/67108864), (-5106094399/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((980073194860157/18014398509481984), (-351388282058373/18014398509481984)), (11040927/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6090494315/34359738368), (2183641329/34359738368)), (35/8589934592), by norm_num⟩
  | 2 => ⟨((4960854611/17179869184), (-444657141/4294967296)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((-5387647745/17179869184), (120727991/1073741824)), (1/134217728), by norm_num⟩
  | 4 => ⟨((4388369117/17179869184), (-786686899/8589934592)), (53/8589934592), by norm_num⟩
  | 5 => ⟨((-5719092091/34359738368), (1025240745/17179869184)), (35/8589934592), by norm_num⟩
  | 6 => ⟨((6211118047/68719476736), (-2226888881/68719476736)), (77/34359738368), by norm_num⟩
  | 7 => ⟨((-1445458729/34359738368), (518244211/34359738368)), (145/137438953472), by norm_num⟩
  | 8 => ⟨((4709444081/274877906944), (-844244835/137438953472)), (15/34359738368), by norm_num⟩
  | 9 => ⟨((-1704869273/274877906944), (152812843/68719476736)), (11/68719476736), by norm_num⟩
  | 10 => ⟨((4443702941/2199023255552), (-1593212783/2199023255552)), (29/549755813888), by norm_num⟩
  | 11 => ⟨((-5264732061/8796093022208), (1887578565/8796093022208)), (139/8796093022208), by norm_num⟩
  | 12 => ⟨((2858834217/17592186044416), (-2049971063/35184372088832)), (153/35184372088832), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395065559226429/2535301200456458802993406410752), (-448431892239/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777573108659321/633825300114114700748351602688), (-265007993539/316912650057057350374175801344)), (2883/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236049632541215/4951760157141521099596496896), (-596122306529/39614081257132168796771975168)), (6487/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944044251112389/1237940039285380274899124224), (-633195893913/2475880078570760549798248448)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769755221660047/154742504910672534362390528), (-632988946995/154742504910672534362390528)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387052043836085/2417851639229258349412352), (-593207351973/9671406556917033397649408)), (12925/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257612088702433/604462909807314587353088), (-32427297149/37778931862957161709568)), (5655/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235735126636769/9444732965739290427392), (-842698056273/75557863725914323419136)), (36759/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296106996542737/4722366482869645213696), (-631663558917/4722366482869645213696)), (27571/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619479813025987/590295810358705651712), (-867952847129/590295810358705651712)), (37913/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821016228673819/73786976294838206464), (-542032492509/36893488147419103232)), (11849/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909946960665629/4611686018427387904), (-1218369717099/9223372036854775808)), (53327/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99446613330551/72057594037927936), (-1216867292079/1152921504606846976)), (53335/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596049762570447/72057594037927936), (-265767785763/36028797018963968)), (23339/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487923139886633/36028797018963968), (-397809364039/9007199254740992)), (70035/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484628116513353/9007199254740992), (-1983164577975/9007199254740992)), (10947/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109364314139863/2251799813685248), (-1974369066425/2251799813685248)), (43813/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101186674660119/1125899906842624), (-5879323991161/2251799813685248)), (263129/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153665034600545/2251799813685248), (-2896169089985/562949953421312)), (263643/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153665034600545/2251799813685248), (-2896169089985/562949953421312)), (1005718235496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2059747428855109/2251799813685248), (-11079809253885/1125899906842624)), (1014039/2251799813685248), by norm_num⟩
  | 2 => ⟨((941928406824127/1125899906842624), (-40539320563395/2251799813685248)), (937533/1125899906842624), by norm_num⟩
  | 3 => ⟨((1575305689368461/2251799813685248), (-67830430396063/2251799813685248)), (3204877/2251799813685248), by norm_num⟩
  | 4 => ⟨((1100003220808133/2251799813685248), (-47452558733609/1125899906842624)), (584649/281474976710656), by norm_num⟩
  | 5 => ⟨((66668898427813/281474976710656), (-185444432938755/4503599627370496)), (2481933/1125899906842624), by norm_num⟩
  | 6 => ⟨((980073194860157/18014398509481984), (-351388282058373/18014398509481984)), (11040927/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-191316263/67108864), (-5106094399/134217728)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-387064769/134217728), (-5165241105/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((712628624506571/18014398509481984), (-711966399854025/18014398509481984)), (3625587/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2239902203/17179869184), (279727591/2147483648)), (47/17179869184), by norm_num⟩
  | 2 => ⟨((57674627/268435456), (-3687746027/17179869184)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-2027585727/8589934592), (4051403103/17179869184)), (45/8589934592), by norm_num⟩
  | 4 => ⟨((1670647947/8589934592), (-1669095463/8589934592)), (19/4294967296), by norm_num⟩
  | 5 => ⟨((-2202473237/17179869184), (137526659/1073741824)), (13/4294967296), by norm_num⟩
  | 6 => ⟨((604916041/8589934592), (-2417415641/34359738368)), (59/34359738368), by norm_num⟩
  | 7 => ⟨((-1139259765/34359738368), (2276402169/68719476736)), (57/68719476736), by norm_num⟩
  | 8 => ⟨((3754814333/274877906944), (-3751325095/274877906944)), (3/8589934592), by norm_num⟩
  | 9 => ⟨((-2750056779/549755813888), (171718827/34359738368)), (9/68719476736), by norm_num⟩
  | 10 => ⟨((1812747703/1099511627776), (-905531585/549755813888)), (97/2199023255552), by norm_num⟩
  | 11 => ⟨((-2172552985/4398046511104), (2170534095/4398046511104)), (15/1099511627776), by norm_num⟩
  | 12 => ⟨((2386793407/17592186044416), (-1192287715/8796093022208)), (67/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580219221042939/10141204801825835211973625643008), (-511231638745/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777521635225203/633825300114114700748351602688), (-1208416083145/633825300114114700748351602688)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888339132561083/39614081257132168796771975168), (-169891485019/4951760157141521099596496896)), (12985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888026925387433/2475880078570760549798248448), (-721826536949/1237940039285380274899124224)), (13797/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442423403181297/38685626227668133590597632), (-1443175721487/154742504910672534362390528)), (6899/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774075191451977/4835703278458516698824704), (-676235134941/4835703278458516698824704)), (12937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257561486297829/604462909807314587353088), (-1182904762441/604462909807314587353088)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885798720495423/75557863725914323419136), (-960635326501/37778931862957161709568)), (18399/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648022610729313/2361183241434822606848), (-720061311345/2361183241434822606848)), (6901/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809697391027923/295147905179352825856), (-1978820235259/590295810358705651712)), (18981/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227613725615887/9223372036854775808), (-2471504443463/73786976294838206464)), (23731/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819774009447637/9223372036854775808), (-694416649657/2305843009213693952)), (26705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795512835348995/576460752303423488), (-346775109091/144115188075855872)), (13357/576460752303423488), by norm_num⟩
  | 5 => ⟨((297998535465527/36028797018963968), (-2423532520087/144115188075855872)), (23385/144115188075855872), by norm_num⟩
  | 4 => ⟨((743882275261273/18014398509481984), (-906881629033/9007199254740992)), (35099/36028797018963968), by norm_num⟩
  | 3 => ⟨((742214492654607/4503599627370496), (-2260419312201/4503599627370496)), (43909/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109163852703535/2251799813685248), (-9001096148351/4503599627370496)), (10991/562949953421312), by norm_num⟩
  | 1 => ⟨((2201765394049861/2251799813685248), (-6700318113471/1125899906842624)), (132169/2251799813685248), by norm_num⟩
  | 0 => ⟨((269052914763225/281474976710656), (-26399898149221/2251799813685248)), (265457/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((269052914763225/281474976710656), (-26399898149221/2251799813685248)), (1012638100630950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1028561499461687/1125899906842624), (-50469634135909/2251799813685248)), (513709/2251799813685248), by norm_num⟩
  | 2 => ⟨((29346024559907/35184372088832), (-92212677607707/2251799813685248)), (480811/1125899906842624), by norm_num⟩
  | 3 => ⟨((781358891163877/1125899906842624), (-153822583218389/2251799813685248)), (420717/562949953421312), by norm_num⟩
  | 4 => ⟨((536998330268411/1125899906842624), (-53375367707657/562949953421312)), (641423/562949953421312), by norm_num⟩
  | 5 => ⟨((246000097802713/1125899906842624), (-203659193235767/2251799813685248)), (5867883/4503599627370496), by norm_num⟩
  | 6 => ⟨((712628624506571/18014398509481984), (-711966399854025/18014398509481984)), (3625587/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-387064769/134217728), (-5165241105/134217728)), (1/134217728), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile028Terms3
