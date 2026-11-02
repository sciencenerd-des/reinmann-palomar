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
namespace Reinmann.XiRectangle.Tile025Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-368633113/268435456), (-6627101795/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1029643767722887/4503599627370496), (15339609218893/140737488355328)), (9579309/2251799813685248), by norm_num⟩
  | 1 => ⟨((-539388321/1073741824), (-514290869/2147483648)), (83/8589934592), by norm_num⟩
  | 2 => ⟨((4740629103/8589934592), (2260025075/8589934592)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((-3472075593/8589934592), (-103453805/536870912)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((1907232457/8589934592), (227311243/2147483648)), (5/1073741824), by norm_num⟩
  | 5 => ⟨((-419061803/4294967296), (-49945385/1073741824)), (73/34359738368), by norm_num⟩
  | 6 => ⟨((4910788763/137438953472), (1170573093/68719476736)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((-3082887361/274877906944), (-1469721125/274877906944)), (71/274877906944), by norm_num⟩
  | 8 => ⟨((846724485/274877906944), (1614653689/1099511627776)), (5/68719476736), by norm_num⟩
  | 9 => ⟨((-3307455731/4398046511104), (-788390393/2199023255552)), (5/274877906944), by norm_num⟩
  | 10 => ⟨((5813778417/35184372088832), (2771633197/35184372088832)), (143/35184372088832), by norm_num⟩
  | 11 => ⟨((-4645155209/140737488355328), (-1107254651/70368744177664)), (117/140737488355328), by norm_num⟩
  | 12 => ⟨((1701074865/281474976710656), (1621924755/562949953421312)), (11/70368744177664), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582186935648693/10141204801825835211973625643008), (289741996799/5070602400912917605986812821504)), (7279/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((13905083186365/4951760157141521099596496896), (171645743561/158456325028528675187087900672)), (17301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945479407354303/19807040628566084398385987584), (772311721491/39614081257132168796771975168)), (2433/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118175610786581/154742504910672534362390528), (410233110197/1237940039285380274899124224)), (10341/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886237912205079/77371252455336267181195264), (820336892013/154742504910672534362390528)), (20683/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550758031319575/9671406556917033397649408), (384464226363/4835703278458516698824704)), (303/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1259842503840045/604462909807314587353088), (42042190247/37778931862957161709568)), (16969/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889504109173515/75557863725914323419136), (1092839477681/75557863725914323419136)), (3447/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649411578352361/2361183241434822606848), (204851097425/1180591620717411303424)), (5171/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623212646208653/590295810358705651712), (1126315180483/590295810358705651712)), (28443/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825679441416887/73786976294838206464), (1407345410901/73786976294838206464)), (17779/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456284037279843/2305843009213693952), (791254832715/4611686018427387904)), (40009/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399095796833251/288230376151711744), (790783897407/576460752303423488)), (2501/72057594037927936), by norm_num⟩
  | 5 => ⟨((1196676773067579/144115188075855872), (172851618329/18014398509481984)), (35023/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494778118283791/36028797018963968), (2072103497501/36028797018963968)), (6569/4503599627370496), by norm_num⟩
  | 3 => ⟨((1493177810115727/9007199254740992), (1293215305347/4503599627370496)), (8215/1125899906842624), by norm_num⟩
  | 2 => ⟨((2235771063918901/4503599627370496), (5161781332103/4503599627370496)), (32883/1125899906842624), by norm_num⟩
  | 1 => ⟨((556948775217109/562949953421312), (7715029573343/2251799813685248)), (197529/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203943782857417/2251799813685248), (15319832586549/2251799813685248)), (24749/140737488355328), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2203943782857417/2251799813685248), (15319832586549/2251799813685248)), (94409943163824037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2157000578473403/2251799813685248), (14994250189711/1125899906842624)), (390263/1125899906842624), by norm_num⟩
  | 2 => ⟨((2065792952423523/2251799813685248), (28726004981811/1125899906842624)), (379031/562949953421312), by norm_num⟩
  | 3 => ⟨((946842557433011/1125899906842624), (52706264812759/1125899906842624)), (1429569/1125899906842624), by norm_num⟩
  | 4 => ⟨((793794255407729/1125899906842624), (177296522594099/2251799813685248)), (5076559/2251799813685248), by norm_num⟩
  | 5 => ⟨((1105339474504989/2251799813685248), (249999063475603/2251799813685248)), (3978837/1125899906842624), by norm_num⟩
  | 6 => ⟨((1029643767722887/4503599627370496), (15339609218893/140737488355328)), (9579309/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/268435456), (-6627101795/268435456)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-386309675/268435456), (-6944882175/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((197352845564565/1125899906842624), (-359650307910335/2251799813685248)), (5481293/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3466962587/8589934592), (3159047843/8589934592)), (99/8589934592), by norm_num⟩
  | 2 => ⟨((3991488185/8589934592), (-3636988235/8589934592)), (117/8589934592), by norm_num⟩
  | 3 => ⟨((-1531790199/4294967296), (2791491631/8589934592)), (23/2147483648), by norm_num⟩
  | 4 => ⟨((1763538639/8589934592), (-803455877/4294967296)), (27/4294967296), by norm_num⟩
  | 5 => ⟨((-3248558225/34359738368), (370005105/4294967296)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((2493360581/68719476736), (-283989413/8589934592)), (5/4294967296), by norm_num⟩
  | 7 => ⟨((-1640335687/137438953472), (747325473/68719476736)), (107/274877906944), by norm_num⟩
  | 8 => ⟨((944253125/274877906944), (-3441560987/1099511627776)), (63/549755813888), by norm_num⟩
  | 9 => ⟨((-3865285635/4398046511104), (3521994233/4398046511104)), (33/1099511627776), by norm_num⟩
  | 10 => ⟨((3560059633/17592186044416), (-3243876567/17592186044416)), (31/4398046511104), by norm_num⟩
  | 11 => ⟨((-2980850997/70368744177664), (2716109755/70368744177664)), (53/35184372088832), by norm_num⟩
  | 12 => ⟨((1143943845/140737488355328), (-2084691277/281474976710656)), (83/281474976710656), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791050579124123/5070602400912917605986812821504), (-481289579063/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889874289944195/316912650057057350374175801344), (-570178579469/316912650057057350374175801344)), (17309/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472710994180131/9903520314283042199192993792), (-641368953335/19807040628566084398385987584)), (9737/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472671935502917/618970019642690137449562112), (-1362708862651/2475880078570760549798248448)), (20693/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772353776739055/154742504910672534362390528), (-170310465887/19342813113834066795298816)), (20695/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775321796737505/4835703278458516698824704), (-638544667849/4835703278458516698824704)), (19403/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314935588146989/151115727451828646838272), (-1117214064359/604462909807314587353088)), (4245/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236167666176425/9444732965739290427392), (-907512324383/37778931862957161709568)), (27595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649350521092145/2361183241434822606848), (-680438210671/2361183241434822606848)), (5175/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623044690541351/590295810358705651712), (-1870568188637/590295810358705651712)), (28467/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825469424633229/73786976294838206464), (-1168627638183/36893488147419103232)), (17795/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824899781130695/9223372036854775808), (-2628099728481/9223372036854775808)), (40049/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798073347855603/576460752303423488), (-2626460073943/1152921504606846976)), (40063/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196469704155589/144115188075855872), (-2296309213871/144115188075855872)), (35069/144115188075855872), by norm_num⟩
  | 4 => ⟨((46702101196553/1125899906842624), (-3440780268381/36028797018963968)), (52633/36028797018963968), by norm_num⟩
  | 3 => ⟨((746394363979341/4503599627370496), (-4294536198787/9007199254740992)), (65841/9007199254740992), by norm_num⟩
  | 2 => ⟨((2234991460821035/4503599627370496), (-8569783279147/4503599627370496)), (65917/2251799813685248), by norm_num⟩
  | 1 => ⟨((2226622126175565/2251799813685248), (-6403275507449/1125899906842624)), (198133/2251799813685248), by norm_num⟩
  | 0 => ⟨((2201583714209573/2251799813685248), (-12710599370531/1125899906842624)), (49725/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2201583714209573/2251799813685248), (-12710599370531/1125899906842624)), (189685822606944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2152200468209469/2251799813685248), (-12427147565221/562949953421312)), (786841/2251799813685248), by norm_num⟩
  | 2 => ⟨((2055909181304531/2251799813685248), (-47509929871795/1125899906842624)), (6011/8796093022208), by norm_num⟩
  | 3 => ⟨((1873050065282633/2251799813685248), (-43376902526119/562949953421312)), (2939769/2251799813685248), by norm_num⟩
  | 4 => ⟨((386159066533399/562949953421312), (-72161929861197/562949953421312)), (1335911/562949953421312), by norm_num⟩
  | 5 => ⟨((1022552570934847/2251799813685248), (-395999442651607/2251799813685248)), (8700967/2251799813685248), by norm_num⟩
  | 6 => ⟨((197352845564565/1125899906842624), (-359650307910335/2251799813685248)), (5481293/1125899906842624), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-386309675/268435456), (-6944882175/268435456)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-402300069/268435456), (-7232349497/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-119132047217913/2251799813685248), (-244398768914815/1125899906842624)), (15980151/2251799813685248), by norm_num⟩
  | 1 => ⟨((1089729969/8589934592), (4471150609/8589934592)), (149/8589934592), by norm_num⟩
  | 2 => ⟨((-1306529171/8589934592), (-5360675455/8589934592)), (181/8589934592), by norm_num⟩
  | 3 => ⟨((261076677/2147483648), (1071194861/2147483648)), (147/8589934592), by norm_num⟩
  | 4 => ⟨((-1252069059/17179869184), (-5137226187/17179869184)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((1200932191/34359738368), (1231853039/8589934592)), (173/34359738368), by norm_num⟩
  | 6 => ⟨((-119987901/8589934592), (-984618193/17179869184)), (35/17179869184), by norm_num⟩
  | 7 => ⟨((82205263/17179869184), (5396597281/274877906944)), (97/137438953472), by norm_num⟩
  | 8 => ⟨((-394239223/274877906944), (-6470237555/1099511627776)), (235/1099511627776), by norm_num⟩
  | 9 => ⟨((420153053/1099511627776), (6895534243/4398046511104)), (253/4398046511104), by norm_num⟩
  | 10 => ⟨((-1611972831/17592186044416), (-3306953793/8796093022208)), (245/17592186044416), by norm_num⟩
  | 11 => ⟨((175697365/8796093022208), (1441768885/17592186044416)), (27/8796093022208), by norm_num⟩
  | 12 => ⟨((-140434627/35184372088832), (-576201799/35184372088832)), (175/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197752945394709/1267650600228229401496703205376), (-2357544966213/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111228324134283/39614081257132168796771975168), (-2792683834481/633825300114114700748351602688)), (4335/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236342058819059/4951760157141521099596496896), (-3141345797991/39614081257132168796771975168)), (19511/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236321659669785/309485009821345068724781056), (-3337168727335/2475880078570760549798248448)), (10367/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886119521481597/77371252455336267181195264), (-3336593694461/154742504910672534362390528)), (10369/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550535744754873/9671406556917033397649408), (-97732677773/302231454903657293676544)), (19447/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157455962413383/75557863725914323419136), (-2735904159449/604462909807314587353088)), (4255/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889186982562951/75557863725914323419136), (-4444699148489/75557863725914323419136)), (13833/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162323101752175/590295810358705651712), (-1666261281565/2361183241434822606848)), (20757/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622884116877099/590295810358705651712), (-4580590927691/590295810358705651712)), (14277/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825267568726249/73786976294838206464), (-5723297834577/73786976294838206464)), (17855/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912335564547687/4611686018427387904), (-3217677427971/4611686018427387904)), (40199/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797958045559621/576460752303423488), (-3215581118211/576460752303423488)), (20115/576460752303423488), by norm_num⟩
  | 5 => ⟨((149533216513597/18014398509481984), (-5622552172909/144115188075855872)), (35237/144115188075855872), by norm_num⟩
  | 4 => ⟨((23346201611669/562949953421312), (-4212201738719/18014398509481984)), (26463/18014398509481984), by norm_num⟩
  | 3 => ⟨((746196584673035/4503599627370496), (-1314252719561/1125899906842624)), (66281/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117088752600313/2251799813685248), (-10489319450999/2251799813685248)), (16617/562949953421312), by norm_num⟩
  | 1 => ⟨((17385502957307/17592186044416), (-7836149524775/562949953421312)), (50085/562949953421312), by norm_num⟩
  | 0 => ⟨((549700662149277/562949953421312), (-15549166131125/562949953421312)), (101107/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((549700662149277/562949953421312), (-15549166131125/562949953421312)), (385692598583030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1072667435408833/1125899906842624), (-60732836844213/1125899906842624)), (203041/562949953421312), by norm_num⟩
  | 2 => ⟨((127334470691511/140737488355328), (-115722784853007/1125899906842624)), (102197/140737488355328), by norm_num⟩
  | 3 => ⟨((113721093913749/140737488355328), (-418808086698313/2251799813685248)), (1647495/1125899906842624), by norm_num⟩
  | 4 => ⟨((10877814308879/17592186044416), (-338412418154067/1125899906842624)), (3275303/1125899906842624), by norm_num⟩
  | 5 => ⟨((328753725425041/1125899906842624), (-418502559625569/1125899906842624)), (12038741/2251799813685248), by norm_num⟩
  | 6 => ⟨((-119132047217913/2251799813685248), (-244398768914815/1125899906842624)), (15980151/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-402300069/268435456), (-7232349497/268435456)), (3/268435456), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-104224539/67108864), (-936848325/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-893838060745627/4503599627370496), (-330413378608201/4503599627370496)), (10403887/2251799813685248), by norm_num⟩
  | 1 => ⟨((2118209973/4294967296), (391505433/2147483648)), (101/8589934592), by norm_num⟩
  | 2 => ⟨((-5263554047/8589934592), (-486427227/2147483648)), (1/67108864), by norm_num⟩
  | 3 => ⟨((1089953371/2147483648), (1611635001/8589934592)), (27/2147483648), by norm_num⟩
  | 4 => ⟨((-5416864759/17179869184), (-2002381265/17179869184)), (137/17179869184), by norm_num⟩
  | 5 => ⟨((673020163/4294967296), (124393263/2147483648)), (69/17179869184), by norm_num⟩
  | 6 => ⟨((-2229856371/34359738368), (-1648563447/68719476736)), (117/68719476736), by norm_num⟩
  | 7 => ⟨((791569275/34359738368), (585218039/68719476736)), (85/137438953472), by norm_num⟩
  | 8 => ⟨((-1966975755/274877906944), (-1454212197/549755813888)), (27/137438953472), by norm_num⟩
  | 9 => ⟨((2172333837/1099511627776), (200754531/274877906944)), (121/2199023255552), by norm_num⟩
  | 10 => ⟨((-2159218719/4398046511104), (-1596340061/8796093022208)), (61/4398046511104), by norm_num⟩
  | 11 => ⟨((3902150511/35184372088832), (1442456739/35184372088832)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((-1616079959/70368744177664), (-597395057/70368744177664)), (95/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581952724385157/10141204801825835211973625643008), (-453881121221/1267650600228229401496703205376)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779563558667823/633825300114114700748351602688), (-4300856469801/633825300114114700748351602688)), (11579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890635321691091/39614081257132168796771975168), (-75590207693/618970019642690137449562112)), (13029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945232700633121/1237940039285380274899124224), (-5139316545657/2475880078570760549798248448)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772130710990821/154742504910672534362390528), (-2569198325351/77371252455336267181195264)), (3463/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387608424850185/2417851639229258349412352), (-4816269457383/9671406556917033397649408)), (12991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259557925765069/604462909807314587353088), (-4213258356371/604462909807314587353088)), (2843/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889040193904937/75557863725914323419136), (-6844712134767/75557863725914323419136)), (18487/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298473929782909/4722366482869645213696), (-2565965229977/2361183241434822606848)), (6937/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811365181968719/295147905179352825856), (-7053798403583/590295810358705651712)), (19089/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456268362194359/18446744073709551616), (-8813338929495/73786976294838206464)), (23879/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824450095177811/9223372036854775808), (-9909631147653/9223372036854775808)), (13445/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797845875307817/576460752303423488), (-9902911963791/1152921504606846976)), (13461/576460752303423488), by norm_num⟩
  | 5 => ⟨((299016430156753/36028797018963968), (-8657488554179/144115188075855872)), (11797/72057594037927936), by norm_num⟩
  | 4 => ⟨((746924737378159/18014398509481984), (-3242778300437/9007199254740992)), (35463/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491995950104607/9007199254740992), (-8093715214359/4503599627370496)), (5557/1125899906842624), by norm_num⟩
  | 2 => ⟨((558336102133541/1125899906842624), (-252308368391/35184372088832)), (44649/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111999294229359/1125899906842624), (-12061177899363/562949953421312)), (33727/562949953421312), by norm_num⟩
  | 0 => ⟨((1097864743656995/1125899906842624), (-47847665947017/1125899906842624)), (68419/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1097864743656995/1125899906842624), (-47847665947017/1125899906842624)), (260997774364280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1068494267489639/1125899906842624), (-23328124103331/281474976710656)), (278493/1125899906842624), by norm_num⟩
  | 2 => ⟨((503140985617693/562949953421312), (-177109646953227/1125899906842624)), (287375/562949953421312), by norm_num⟩
  | 3 => ⟨((217878066386285/281474976710656), (-39573287904581/140737488355328)), (604099/562949953421312), by norm_num⟩
  | 4 => ⟨((292791009925331/562949953421312), (-980225132616155/2251799813685248)), (2549887/1125899906842624), by norm_num⟩
  | 5 => ⟨((91212348180473/1125899906842624), (-1019632757010227/2251799813685248)), (4872369/1125899906842624), by norm_num⟩
  | 6 => ⟨((-893838060745627/4503599627370496), (-330413378608201/4503599627370496)), (10403887/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-104224539/67108864), (-936848325/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-215163547/134217728), (-1934051333/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-387501200566659/2251799813685248), (470136042226511/4503599627370496)), (10144461/2251799813685248), by norm_num⟩
  | 1 => ⟨((3791507551/8589934592), (-1150012149/4294967296)), (51/4294967296), by norm_num⟩
  | 2 => ⟨((-1215628107/2147483648), (2949722923/8589934592)), (133/8589934592), by norm_num⟩
  | 3 => ⟨((4157366043/8589934592), (-2521963305/8589934592)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((-666464585/2147483648), (3234354079/17179869184)), (151/17179869184), by norm_num⟩
  | 5 => ⟨((1367558327/8589934592), (-1659190883/17179869184)), (5/1073741824), by norm_num⟩
  | 6 => ⟨((-292309821/4294967296), (2837160393/68719476736)), (139/68719476736), by norm_num⟩
  | 7 => ⟨((856868443/34359738368), (-129949513/8589934592)), (13/17179869184), by norm_num⟩
  | 8 => ⟨((-4395648325/549755813888), (2666511359/549755813888)), (17/68719476736), by norm_num⟩
  | 9 => ⟨((2505470077/1099511627776), (-759940733/549755813888)), (157/2199023255552), by norm_num⟩
  | 10 => ⟨((-5141123091/8796093022208), (389841899/1099511627776)), (41/2199023255552), by norm_num⟩
  | 11 => ⟨((4795171043/35184372088832), (-2908871937/35184372088832)), (155/35184372088832), by norm_num⟩
  | 12 => ⟨((-4099790295/140737488355328), (1243518201/70368744177664)), (67/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395471889758183/2535301200456458802993406410752), (13210903497/39614081257132168796771975168)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222435960640121/79228162514264337593543950336), (4005525507327/633825300114114700748351602688)), (11575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890550053179597/39614081257132168796771975168), (2252778749209/19807040628566084398385987584)), (13025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890374914913495/2475880078570760549798248448), (1196592350755/618970019642690137449562112)), (13843/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886020174987521/77371252455336267181195264), (1196371432309/38685626227668133590597632)), (13847/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775174559535403/4835703278458516698824704), (4485453998965/9671406556917033397649408)), (6493/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259484051044637/604462909807314587353088), (1961916705923/302231454903657293676544)), (11367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118057524804515/4722366482869645213696), (3187234524479/37778931862957161709568)), (18479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298384300107883/4722366482869645213696), (1194827911741/1180591620717411303424)), (13867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622607477330265/590295810358705651712), (6569050928555/590295810358705651712)), (9539/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824920371434881/73786976294838206464), (8207560029939/73786976294838206464)), (23865/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824278612563749/9223372036854775808), (9228344197431/9223372036854775808)), (3359/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595521178825989/1152921504606846976), (144092090089/18014398509481984)), (13451/576460752303423488), by norm_num⟩
  | 5 => ⟨((149489686715205/18014398509481984), (8061901160299/144115188075855872)), (11787/72057594037927936), by norm_num⟩
  | 4 => ⟨((373407294512617/9007199254740992), (3019585530155/9007199254740992)), (8857/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491724148479021/9007199254740992), (3768135178237/2251799813685248)), (11101/2251799813685248), by norm_num⟩
  | 2 => ⟨((279101435561507/562949953421312), (7517235125325/1125899906842624)), (44583/2251799813685248), by norm_num⟩
  | 1 => ⟨((555806450088489/562949953421312), (22456564702215/1125899906842624)), (33661/562949953421312), by norm_num⟩
  | 0 => ⟨((137143106360127/140737488355328), (22266392497899/562949953421312)), (68221/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((137143106360127/140737488355328), (22266392497899/562949953421312)), (260242464305686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((266840695067937/281474976710656), (43395434582233/562949953421312)), (276709/1125899906842624), by norm_num⟩
  | 2 => ⟨((1005178740011481/1125899906842624), (164556978556593/1125899906842624)), (567307/1125899906842624), by norm_num⟩
  | 3 => ⟨((873350547596091/1125899906842624), (146912860868309/562949953421312)), (589395/562949953421312), by norm_num⟩
  | 4 => ⟨((1201541309527605/2251799813685248), (113959000003879/281474976710656)), (2444011/1125899906842624), by norm_num⟩
  | 5 => ⟨((272029369190787/2251799813685248), (972920916077535/2251799813685248)), (2293595/562949953421312), by norm_num⟩
  | 6 => ⟨((-387501200566659/2251799813685248), (470136042226511/4503599627370496)), (10144461/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-215163547/134217728), (-1934051333/67108864)), (1/134217728), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-442760349/268435456), (-7959724165/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-331724377117023/9007199254740992), (1698765729198885/9007199254740992)), (54548789/9007199254740992), by norm_num⟩
  | 1 => ⟨((834884309/8589934592), (-4275455617/8589934592)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-1101653777/8589934592), (5641586241/8589934592)), (187/8589934592), by norm_num⟩
  | 3 => ⟨((484554579/4294967296), (-4962823173/8589934592)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((-1278767313/17179869184), (6548587435/17179869184)), (111/8589934592), by norm_num⟩
  | 5 => ⟨((337474025/8589934592), (-6912839067/34359738368)), (59/8589934592), by norm_num⟩
  | 6 => ⟨((-1187484399/68719476736), (3040563101/34359738368)), (105/34359738368), by norm_num⟩
  | 7 => ⟨((27980709/4294967296), (-1146317191/34359738368)), (5/4294967296), by norm_num⟩
  | 8 => ⟨((-1181483123/549755813888), (6050393569/549755813888)), (107/274877906944), by norm_num⟩
  | 9 => ⟨((1385778531/2199023255552), (-7096593553/2199023255552)), (253/2199023255552), by norm_num⟩
  | 10 => ⟨((-365714899/2199023255552), (1872831723/2199023255552)), (135/4398046511104), by norm_num⟩
  | 11 => ⟨((87740235/2199023255552), (-3594552935/17592186044416)), (131/17592186044416), by norm_num⟩
  | 12 => ⟨((-308735347/35184372088832), (6324154179/140737488355328)), (233/140737488355328), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225338149/10141204801825835211973625643008), (1148671171691/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444855212170903/158456325028528675187087900672), (2720693131697/633825300114114700748351602688)), (17339/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29538674081131/618970019642690137449562112), (1530164141833/19807040628566084398385987584)), (19509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890295675227201/2475880078570760549798248448), (3251050904625/2475880078570760549798248448)), (5183/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771961508687033/154742504910672534362390528), (812608650495/38685626227668133590597632)), (81/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((1550275628461375/9671406556917033397649408), (761656930165/2417851639229258349412352)), (4861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259420169634551/604462909807314587353088), (2665144652535/604462909807314587353088)), (17019/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472204345497543/18889465931478580854784), (541204115681/9444732965739290427392)), (27663/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324576932956679/1180591620717411303424), (1623075598417/2361183241434822606848)), (20755/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622503320978647/590295810358705651712), (278857120221/36893488147419103232)), (28549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824791861980855/73786976294838206464), (5574527252959/73786976294838206464)), (35705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824136355112387/9223372036854775808), (97933572459/144115188075855872)), (157/36028797018963968), by norm_num⟩
  | 6 => ⟨((1595381812162935/1152921504606846976), (6263257451489/1152921504606846976)), (40223/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195798794781679/144115188075855872), (5475300390823/144115188075855872)), (17615/72057594037927936), by norm_num⟩
  | 4 => ⟨((373364402577619/9007199254740992), (2050714397841/9007199254740992)), (52913/36028797018963968), by norm_num⟩
  | 3 => ⟨((745760500247375/4503599627370496), (10235924469947/9007199254740992)), (33131/4503599627370496), by norm_num⟩
  | 2 => ⟨((558109751438405/1125899906842624), (10209483643741/2251799813685248)), (66445/2251799813685248), by norm_num⟩
  | 1 => ⟨((555687803314389/562949953421312), (15248230025193/1125899906842624)), (100123/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096837291157415/1125899906842624), (15116559180253/562949953421312)), (202075/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1096837291157415/1125899906842624), (15116559180253/562949953421312)), (770854954246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((133464128840603/140737488355328), (58905434567043/1125899906842624)), (404571/1125899906842624), by norm_num⟩
  | 2 => ⟨((1009451425344971/1125899906842624), (55861182406627/562949953421312)), (809659/1125899906842624), by norm_num⟩
  | 3 => ⟨((446980360871553/562949953421312), (25041813157245/140737488355328)), (3225043/2251799813685248), by norm_num⟩
  | 4 => ⟨((674155716160477/1125899906842624), (318129840533839/1125899906842624)), (6269029/2251799813685248), by norm_num⟩
  | 5 => ⟨((156887540378463/562949953421312), (761947129309379/2251799813685248)), (11050125/2251799813685248), by norm_num⟩
  | 6 => ⟨((-331724377117023/9007199254740992), (1698765729198885/9007199254740992)), (54548789/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-442760349/268435456), (-7959724165/268435456)), (3/268435456), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-56791929/33554432), (-4083907611/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((455887568477563/4503599627370496), (173068560308015/1125899906842624)), (26208259/4503599627370496), by norm_num⟩
  | 1 => ⟨((-73585893/268435456), (-3575732037/8589934592)), (137/8589934592), by norm_num⟩
  | 2 => ⟨((3188388677/8589934592), (4841630931/8589934592)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-2878105533/8589934592), (-136576871/268435456)), (43/2147483648), by norm_num⟩
  | 4 => ⟨((1948513567/8589934592), (369857023/1073741824)), (59/4294967296), by norm_num⟩
  | 5 => ⟨((-2110669023/17179869184), (-1602546217/8589934592)), (65/8589934592), by norm_num⟩
  | 6 => ⟨((1905265891/34359738368), (2893183737/34359738368)), (119/34359738368), by norm_num⟩
  | 7 => ⟨((-2948317531/137438953472), (-1119269543/34359738368)), (93/68719476736), by norm_num⟩
  | 8 => ⟨((1996047971/274877906944), (3031038111/274877906944)), (1/2147483648), by norm_num⟩
  | 9 => ⟨((-300299895/137438953472), (-3648090385/1099511627776)), (39/274877906944), by norm_num⟩
  | 10 => ⟨((2602327011/4398046511104), (493960595/549755813888)), (171/4398046511104), by norm_num⟩
  | 11 => ⟨((-1281314943/8796093022208), (-1945701947/8796093022208)), (171/17592186044416), by norm_num⟩
  | 12 => ⟨((2313243459/70368744177664), (3512705699/70368744177664)), (157/70368744177664), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (643779159159/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889678522403709/316912650057057350374175801344), (1524719188835/633825300114114700748351602688)), (1443/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945201764750247/19807040628566084398385987584), (1715052420763/39614081257132168796771975168)), (3247/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890219801186679/2475880078570760549798248448), (1821928452539/2475880078570760549798248448)), (27603/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885942937283491/77371252455336267181195264), (1821574452405/154742504910672534362390528)), (13803/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193775622033215/1208925819614629174706176), (853675005193/4835703278458516698824704)), (6471/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259358603616207/604462909807314587353088), (1493555317535/604462909807314587353088)), (5663/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888717814389117/75557863725914323419136), (2426322707061/75557863725914323419136)), (36815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649116736681055/2361183241434822606848), (14211919049/36893488147419103232)), (27617/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405600473261333/147573952589676412928), (1250148251247/295147905179352825856)), (18991/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228083261534971/9223372036854775808), (3123869429757/73786976294838206464)), (47491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455999064637123/2305843009213693952), (3512290060111/9223372036854775808)), (53445/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797621728090349/576460752303423488), (877428224473/288230376151711744)), (13367/288230376151711744), by norm_num⟩
  | 5 => ⟨((597839844107697/72057594037927936), (3068101743135/144115188075855872)), (46811/144115188075855872), by norm_num⟩
  | 4 => ⟨((186660356526911/4503599627370496), (2298182094023/18014398509481984)), (70267/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491309362783967/9007199254740992), (2867669104315/4503599627370496)), (87925/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232036087524849/4503599627370496), (11440376163185/4503599627370496)), (176121/4503599627370496), by norm_num⟩
  | 1 => ⟨((555549368888131/562949953421312), (17084991247437/2251799813685248)), (264865/2251799813685248), by norm_num⟩
  | 0 => ⟨((1096384074765237/1125899906842624), (4233594291439/281474976710656)), (266235/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1096384074765237/1125899906842624), (4233594291439/281474976710656)), (1015605930808639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2134774608231341/2251799813685248), (32980873926297/1125899906842624)), (1053041/2251799813685248), by norm_num⟩
  | 2 => ⟨((2021898948609605/2251799813685248), (62533740155091/1125899906842624)), (514581/562949953421312), by norm_num⟩
  | 3 => ⟨((1808523767968801/2251799813685248), (14037316139715/140737488355328)), (3924997/2251799813685248), by norm_num⟩
  | 4 => ⟨((1430106868811645/2251799813685248), (360768408955417/2251799813685248)), (7087659/2251799813685248), by norm_num⟩
  | 5 => ⟨((850453845711929/2251799813685248), (114561111640963/562949953421312)), (5636875/1125899906842624), by norm_num⟩
  | 6 => ⟨((455887568477563/4503599627370496), (173068560308015/1125899906842624)), (26208259/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-4083907611/134217728)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile025Terms1
