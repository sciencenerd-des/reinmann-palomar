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
namespace Reinmann.XiRectangle.Tile026Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-516086359/268435456), (-6627101795/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((1188930209996007/9007199254740992), (17712654979895/281474976710656)), (11157387/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4982655865/17179869184), (-2375407767/17179869184)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1368501741/4294967296), (652413041/4294967296)), (27/4294967296), by norm_num⟩
  | 3 => ⟨((-2004603773/8589934592), (-29864541/268435456)), (81/17179869184), by norm_num⟩
  | 4 => ⟨((2202282339/17179869184), (2099811311/34359738368)), (91/34359738368), by norm_num⟩
  | 5 => ⟨((-3871127105/68719476736), (-230687851/8589934592)), (41/34359738368), by norm_num⟩
  | 6 => ⟨((1417622603/68719476736), (21119709/2147483648)), (123/274877906944), by norm_num⟩
  | 7 => ⟨((-1779905843/274877906944), (-1697087769/549755813888)), (79/549755813888), by norm_num⟩
  | 8 => ⟨((15276769/8589934592), (932220739/1099511627776)), (89/2199023255552), by norm_num⟩
  | 9 => ⟨((-3819120903/8796093022208), (-1820709617/8796093022208)), (89/8796093022208), by norm_num⟩
  | 10 => ⟨((3356586525/35184372088832), (50006349/1099511627776)), (5/2199023255552), by norm_num⟩
  | 11 => ⟨((-5363763207/281474976710656), (-639273769/70368744177664)), (131/281474976710656), by norm_num⟩
  | 12 => ⟨((3928464115/1125899906842624), (1872837383/1125899906842624)), (49/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403062135/10141204801825835211973625643008), (289741996799/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111187703494669/39614081257132168796771975168), (685961266979/633825300114114700748351602688)), (17301/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472501409377083/9903520314283042199192993792), (385788222823/19807040628566084398385987584)), (2433/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889797192095215/2475880078570760549798248448), (204909803287/618970019642690137449562112)), (10341/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771463435441205/154742504910672534362390528), (204864604605/38685626227668133590597632)), (20683/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549809120104323/9671406556917033397649408), (768050228341/9671406556917033397649408)), (19391/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629506204957889/302231454903657293676544), (671851973287/604462909807314587353088)), (16969/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944077793893125/37778931862957161709568), (1091399633213/75557863725914323419136)), (3447/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648906049567085/2361183241434822606848), (204558752995/1180591620717411303424)), (5171/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621822983722529/590295810358705651712), (1124561981329/590295810358705651712)), (28443/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455985793860719/18446744073709551616), (702468085423/36893488147419103232)), (17779/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911591982985481/4611686018427387904), (197437528395/1152921504606846976)), (40009/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398608099589611/288230376151711744), (1578185078255/1152921504606846976)), (40017/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597485699950481/72057594037927936), (1379433853601/144115188075855872)), (2189/9007199254740992), by norm_num⟩
  | 4 => ⟨((373055797440003/9007199254740992), (2066198228455/36028797018963968)), (6569/4503599627370496), by norm_num⟩
  | 3 => ⟨((1489989622035029/9007199254740992), (322198621465/1125899906842624)), (65721/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229411077227635/4503599627370496), (642466757219/562949953421312)), (131535/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109147997891113/1125899906842624), (7671105082599/2251799813685248)), (6173/70368744177664), by norm_num⟩
  | 0 => ⟨((2185108481395623/2251799813685248), (15188906531467/2251799813685248)), (396013/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185108481395623/2251799813685248), (15188906531467/2251799813685248)), (1510669716841887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120289887035593/2251799813685248), (29478116379019/2251799813685248)), (96739/281474976710656), by norm_num⟩
  | 2 => ⟨((249509315748417/281474976710656), (55513062633221/2251799813685248)), (1477691/2251799813685248), by norm_num⟩
  | 3 => ⟨((1768022090141773/2251799813685248), (3075545656531/70368744177664)), (1346307/1125899906842624), by norm_num⟩
  | 4 => ⟨((1383877952053781/2251799813685248), (9659175965713/140737488355328)), (4463631/2251799813685248), by norm_num⟩
  | 5 => ⟨((1679752752905013/4503599627370496), (379916419147947/4503599627370496)), (12198173/4503599627370496), by norm_num⟩
  | 6 => ⟨((1188930209996007/9007199254740992), (17712654979895/281474976710656)), (11157387/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/268435456), (-6627101795/268435456)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-6944882175/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((887837288464035/9007199254740992), (-808984925595861/9007199254740992)), (388807/140737488355328), by norm_num⟩
  | 1 => ⟨((-974808171/4294967296), (444115789/2147483648)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((2244578763/8589934592), (-4090457581/17179869184)), (131/17179869184), by norm_num⟩
  | 3 => ⟨((-3445555733/17179869184), (392442777/2147483648)), (103/17179869184), by norm_num⟩
  | 4 => ⟨((1983421317/17179869184), (-112954111/1073741824)), (121/34359738368), by norm_num⟩
  | 5 => ⟨((-1826798543/34359738368), (832276647/17179869184)), (57/34359738368), by norm_num⟩
  | 6 => ⟨((2804239395/137438953472), (-1277591867/68719476736)), (89/137438953472), by norm_num⟩
  | 7 => ⟨((-3689714187/549755813888), (1681007993/274877906944)), (119/549755813888), by norm_num⟩
  | 8 => ⟨((2123970221/1099511627776), (-1935331973/1099511627776)), (35/549755813888), by norm_num⟩
  | 9 => ⟨((-4347219705/8796093022208), (3961125823/8796093022208)), (73/4398046511104), by norm_num⟩
  | 10 => ⟨((4003937315/35184372088832), (-912082927/8796093022208)), (137/35184372088832), by norm_num⟩
  | 11 => ⟨((-3352511409/140737488355328), (3054761529/140737488355328)), (117/140737488355328), by norm_num⟩
  | 12 => ⟨((1286573799/281474976710656), (-293077015/70368744177664)), (23/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-481289579063/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889430334927407/316912650057057350374175801344), (-1139274922411/633825300114114700748351602688)), (17309/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944922615359977/19807040628566084398385987584), (-320364556563/9903520314283042199192993792)), (19475/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236203345180487/309485009821345068724781056), (-340317386721/618970019642690137449562112)), (20693/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771293006563597/154742504910672534362390528), (-680477429165/77371252455336267181195264)), (20695/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549649344928475/9671406556917033397649408), (-79722557595/604462909807314587353088)), (19403/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258872608547719/604462909807314587353088), (-557890829453/302231454903657293676544)), (4245/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471982103543857/18889465931478580854784), (-226564863067/9444732965739290427392)), (27595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648820861058137/2361183241434822606848), (-84927588047/295147905179352825856)), (5175/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621588720562251/590295810358705651712), (-1867517252023/590295810358705651712)), (28467/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823650354448039/73786976294838206464), (-2333062808269/73786976294838206464)), (35591/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822854553447221/9223372036854775808), (-2622862995453/9223372036854775808)), (20025/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99631437496161/72057594037927936), (-2620574041811/1152921504606846976)), (40063/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194683192472331/144115188075855872), (-572607447811/36028797018963968)), (35069/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491790911797469/36028797018963968), (-1715253066635/18014398509481984)), (52633/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489449334448999/9007199254740992), (-2139577331445/4503599627370496)), (32921/4503599627370496), by norm_num⟩
  | 2 => ⟨((557082672209365/1125899906842624), (-4265716541719/2251799813685248)), (131837/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216675905169517/2251799813685248), (-3182540199553/562949953421312)), (198141/2251799813685248), by norm_num⟩
  | 0 => ⟨((1090935208630427/1125899906842624), (-25193573674461/2251799813685248)), (49729/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090935208630427/1125899906842624), (-25193573674461/2251799813685248)), (189701081396007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2113830799982869/2251799813685248), (-48822380010261/2251799813685248)), (389929/1125899906842624), by norm_num⟩
  | 2 => ⟨((1983256681621959/2251799813685248), (-91662011842215/2251799813685248)), (1497969/2251799813685248), by norm_num⟩
  | 3 => ⟨((435752005676713/562949953421312), (-161461330915977/2251799813685248)), (2760605/2251799813685248), by norm_num⟩
  | 4 => ⟨((668799950051933/1125899906842624), (-249958627257273/2251799813685248)), (1167397/562949953421312), by norm_num⟩
  | 5 => ⟨((1533612505804111/4503599627370496), (-74239422353945/562949953421312)), (1646071/562949953421312), by norm_num⟩
  | 6 => ⟨((887837288464035/9007199254740992), (-808984925595861/9007199254740992)), (388807/140737488355328), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-6944882175/268435456)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-563220097/268435456), (-7232349497/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-65415465056705/2251799813685248), (-1073595862822887/9007199254740992)), (23621453/9007199254740992), by norm_num⟩
  | 1 => ⟨((1196742511/17179869184), (4910221947/17179869184)), (55/8589934592), by norm_num⟩
  | 2 => ⟨((-1434831605/17179869184), (-2943549499/8589934592)), (67/8589934592), by norm_num⟩
  | 3 => ⟨((1146858641/17179869184), (4705548953/17179869184)), (109/17179869184), by norm_num⟩
  | 4 => ⟨((-1375023457/34359738368), (-5641706795/34359738368)), (133/34359738368), by norm_num⟩
  | 5 => ⟨((1318864899/68719476736), (2705644411/34359738368)), (65/34359738368), by norm_num⟩
  | 6 => ⟨((-263541659/34359738368), (-4325234629/137438953472)), (53/68719476736), by norm_num⟩
  | 7 => ⟨((361111599/137438953472), (5926548383/549755813888)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((-216476949/274877906944), (-888202647/274877906944)), (45/549755813888), by norm_num⟩
  | 9 => ⟨((922824983/4398046511104), (1893170603/2199023255552)), (49/2199023255552), by norm_num⟩
  | 10 => ⟨((-442567533/8796093022208), (-113490621/549755813888)), (3/549755813888), by norm_num⟩
  | 11 => ⟨((1543608139/140737488355328), (197918999/4398046511104)), (85/70368744177664), by norm_num⟩
  | 12 => ⟨((-1233803553/562949953421312), (-5062283009/562949953421312)), (69/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681576647/10141204801825835211973625643008), (-2357544966213/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778728632150335/633825300114114700748351602688), (-697480877329/158456325028528675187087900672)), (1445/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472424129689941/9903520314283042199192993792), (-1569041227747/19807040628566084398385987584)), (813/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889468532120743/2475880078570760549798248448), (-1666749170845/1237940039285380274899124224)), (13823/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885567263371445/77371252455336267181195264), (-1666347492419/77371252455336267181195264)), (6913/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549500504128463/9671406556917033397649408), (-3123548188357/9671406556917033397649408)), (12965/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258742107088405/604462909807314587353088), (-2732251537347/604462909807314587353088)), (11347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887715851448795/75557863725914323419136), (-2219154814051/37778931862957161709568)), (4611/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81092616555695/295147905179352825856), (-831833371207/1180591620717411303424)), (13839/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621368210540201/590295810358705651712), (-4572811520987/590295810358705651712)), (4759/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455843414716541/18446744073709551616), (-5712607989973/73786976294838206464)), (23807/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911270909224997/4611686018427387904), (-6422002804617/9223372036854775808)), (26799/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593788452888495/1152921504606846976), (-802019408801/144115188075855872)), (26821/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298601482523431/36028797018963968), (-5607562809387/144115188075855872)), (5873/36028797018963968), by norm_num⟩
  | 4 => ⟨((372842740728769/9007199254740992), (-8398211663415/36028797018963968)), (35285/36028797018963968), by norm_num⟩
  | 3 => ⟨((744458664364831/4503599627370496), (-10474813096085/9007199254740992)), (44189/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227245577023835/4503599627370496), (-10440446793389/2251799813685248)), (44313/2251799813685248), by norm_num⟩
  | 1 => ⟨((2214995864994361/2251799813685248), (-31149934970487/2251799813685248)), (133565/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178303108593747/2251799813685248), (-30808401055075/1125899906842624)), (269643/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2178303108593747/2251799813685248), (-30808401055075/1125899906842624)), (1028606423384856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1052759613397325/1125899906842624), (-119211371066315/2251799813685248)), (536441/2251799813685248), by norm_num⟩
  | 2 => ⟨((1962430157669473/2251799813685248), (-222934412115341/2251799813685248)), (529993/1125899906842624), by norm_num⟩
  | 3 => ⟨((844087549106791/1125899906842624), (-388572031011467/2251799813685248)), (2057427/2251799813685248), by norm_num⟩
  | 4 => ⟨((1198573213542913/2251799813685248), (-582625171766291/2251799813685248)), (1897485/1125899906842624), by norm_num⟩
  | 5 => ⟨((974443332643635/4503599627370496), (-1240463597467061/4503599627370496)), (12007453/4503599627370496), by norm_num⟩
  | 6 => ⟨((-65415465056705/2251799813685248), (-1073595862822887/9007199254740992)), (23621453/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-563220097/268435456), (-7232349497/268435456)), (1/134217728), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-291828709/134217728), (-936848325/33554432)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-240122876368907/2251799813685248), (-5547691910489/140737488355328)), (2116831/562949953421312), by norm_num⟩
  | 1 => ⟨((1138082375/4294967296), (420699967/4294967296)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((-5656056923/17179869184), (-2090800291/17179869184)), (203/17179869184), by norm_num⟩
  | 3 => ⟨((2342462243/8589934592), (1731814515/17179869184)), (171/17179869184), by norm_num⟩
  | 4 => ⟨((-1455200001/8589934592), (-1075849351/17179869184)), (215/34359738368), by norm_num⟩
  | 5 => ⟨((5785657855/68719476736), (2138708165/68719476736)), (27/8589934592), by norm_num⟩
  | 6 => ⟨((-2396136613/68719476736), (-885748357/68719476736)), (181/137438953472), by norm_num⟩
  | 7 => ⟨((3402386173/274877906944), (628857709/137438953472)), (131/274877906944), by norm_num⟩
  | 8 => ⟨((-4227306013/1099511627776), (-1562652703/1099511627776)), (165/1099511627776), by norm_num⟩
  | 9 => ⟨((2334324627/2199023255552), (1725798263/4398046511104)), (185/4398046511104), by norm_num⟩
  | 10 => ⟨((-4640463031/17592186044416), (-214422379/2199023255552)), (93/8796093022208), by norm_num⟩
  | 11 => ⟨((262070851/4398046511104), (1550020641/70368744177664)), (85/35184372088832), by norm_num⟩
  | 12 => ⟨((-868295467/70368744177664), (-1283885533/281474976710656)), (143/281474976710656), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581143507299009/10141204801825835211973625643008), (-453881121221/1267650600228229401496703205376)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778605558928193/633825300114114700748351602688), (-1074112699273/158456325028528675187087900672)), (2171/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889557765954651/39614081257132168796771975168), (-4832565610983/39614081257132168796771975168)), (2443/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889320718034637/2475880078570760549798248448), (-1283364846119/618970019642690137449562112)), (20771/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885493137573161/77371252455336267181195264), (-5132175199071/154742504910672534362390528)), (10389/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549361053734055/9671406556917033397649408), (-4810050010765/9671406556917033397649408)), (9743/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258619623844235/604462909807314587353088), (-4207429755269/604462909807314587353088)), (8529/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887515946690999/75557863725914323419136), (-6834516342545/75557863725914323419136)), (27731/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324332794078899/1180591620717411303424), (-1280912592929/1180591620717411303424)), (10405/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621159780223413/590295810358705651712), (-3520692628905/295147905179352825856)), (3579/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823111273281257/73786976294838206464), (-8796282205251/73786976294838206464)), (17909/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822244098315391/9223372036854775808), (-9888327265623/9223372036854775808)), (40335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398371892160011/288230376151711744), (-4939484248887/576460752303423488)), (40383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597069552718611/72057594037927936), (-4316787165555/72057594037927936)), (17695/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490963645748217/36028797018963968), (-6464664542075/18014398509481984)), (53195/36028797018963968), by norm_num⟩
  | 3 => ⟨((23256185010879/140737488355328), (-16124885737881/9007199254740992)), (33343/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113082885422917/2251799813685248), (-8034892338667/1125899906842624)), (66975/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106642379982951/1125899906842624), (-11983571671439/562949953421312)), (101185/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087259689771741/1125899906842624), (-47385471420247/1125899906842624)), (51319/281474976710656), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087259689771741/1125899906842624), (-47385471420247/1125899906842624)), (195766450048351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1047951281397295/1125899906842624), (-22879615071887/281474976710656)), (206871/562949953421312), by norm_num⟩
  | 2 => ⟨((241990041251767/281474976710656), (-170364855964499/1125899906842624)), (418729/562949953421312), by norm_num⟩
  | 3 => ⟨((1612794692272079/2251799813685248), (-292932601004029/1125899906842624)), (3386801/2251799813685248), by norm_num⟩
  | 4 => ⟨((501347560021747/1125899906842624), (-839222281166401/2251799813685248)), (6613753/2251799813685248), by norm_num⟩
  | 5 => ⟨((267433601089183/4503599627370496), (-93423500708547/281474976710656)), (21639557/4503599627370496), by norm_num⟩
  | 6 => ⟨((-240122876368907/2251799813685248), (-5547691910489/140737488355328)), (2116831/562949953421312), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-291828709/134217728), (-936848325/33554432)), (3/268435456), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-150614483/67108864), (-1934051333/67108864)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-102036891125699/1125899906842624), (247592627247555/4503599627370496)), (16190391/4503599627370496), by norm_num⟩
  | 1 => ⟨((499190251/2147483648), (-1211285687/8589934592)), (161/17179869184), by norm_num⟩
  | 2 => ⟨((-2560795427/8589934592), (3106886445/17179869184)), (209/17179869184), by norm_num⟩
  | 3 => ⟨((4378873723/17179869184), (-332041933/2147483648)), (181/17179869184), by norm_num⟩
  | 4 => ⟨((-350987167/2147483648), (1703341485/17179869184)), (59/8589934592), by norm_num⟩
  | 5 => ⟨((2880845787/34359738368), (-1747593859/34359738368)), (123/34359738368), by norm_num⟩
  | 6 => ⟨((-4926149033/137438953472), (2988326497/137438953472)), (213/137438953472), by norm_num⟩
  | 7 => ⟨((902523057/68719476736), (-2189973179/274877906944)), (159/274877906944), by norm_num⟩
  | 8 => ⟨((-2314925935/549755813888), (2808585149/1099511627776)), (103/549755813888), by norm_num⟩
  | 9 => ⟨((1319481731/1099511627776), (-3201723855/4398046511104)), (237/4398046511104), by norm_num⟩
  | 10 => ⟨((-1353761527/4398046511104), (1642451909/8796093022208)), (123/8796093022208), by norm_num⟩
  | 11 => ⟨((5050661467/70368744177664), (-1531929443/35184372088832)), (29/8796093022208), by norm_num⟩
  | 12 => ⟨((-4318230295/281474976710656), (2619547627/281474976710656)), (25/35184372088832), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275801731/10141204801825835211973625643008), (13210903497/39614081257132168796771975168)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778498924652105/633825300114114700748351602688), (4001289845013/633825300114114700748351602688)), (8681/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889437900983571/39614081257132168796771975168), (4500551521083/39614081257132168796771975168)), (19537/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889193486930609/2475880078570760549798248448), (2390369567217/1237940039285380274899124224)), (5191/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221357398135229/19342813113834066795298816), (4779505335857/154742504910672534362390528)), (10385/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387310514145065/2417851639229258349412352), (4479475593383/9671406556917033397649408)), (9739/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258515651034503/604462909807314587353088), (1959115384153/302231454903657293676544)), (8525/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887347271388525/75557863725914323419136), (3182334322693/37778931862957161709568)), (13859/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648602457557039/2361183241434822606848), (1192838194239/1180591620717411303424)), (325/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1620986569317865/590295810358705651712), (3278559774115/295147905179352825856)), (28617/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822895356448931/73786976294838206464), (8191165631549/73786976294838206464)), (35797/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822002011552113/9223372036854775808), (2301967017105/2305843009213693952)), (10077/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398311626269727/288230376151711744), (4599440653341/576460752303423488)), (20177/576460752303423488), by norm_num⟩
  | 5 => ⟨((298482331003507/36028797018963968), (502432354427/9007199254740992)), (1105/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490651267226709/36028797018963968), (3009546539855/9007199254740992)), (26571/18014398509481984), by norm_num⟩
  | 3 => ⟨((744004685317315/4503599627370496), (15012436971363/9007199254740992)), (66607/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112702398542667/2251799813685248), (1869946027469/281474976710656)), (16719/562949953421312), by norm_num⟩
  | 1 => ⟨((276521633145359/281474976710656), (2788430344797/140737488355328)), (25247/281474976710656), by norm_num⟩
  | 0 => ⟨((1086207076879145/1125899906842624), (11022205996029/281474976710656)), (204683/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086207076879145/1125899906842624), (11022205996029/281474976710656)), (780803684714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046187127562023/1125899906842624), (2658406418489/35184372088832)), (205483/562949953421312), by norm_num⟩
  | 2 => ⟨((965690434460733/1125899906842624), (316184761556025/2251799813685248)), (1651685/2251799813685248), by norm_num⟩
  | 3 => ⟨((806079482583843/1125899906842624), (135596689324347/562949953421312)), (3297159/2251799813685248), by norm_num⟩
  | 4 => ⟨((511784644547701/1125899906842624), (776635354573697/2251799813685248)), (3154757/1125899906842624), by norm_num⟩
  | 5 => ⟨((98705846963799/1125899906842624), (88256079973909/281474976710656)), (20176601/4503599627370496), by norm_num⟩
  | 6 => ⟨((-102036891125699/1125899906842624), (247592627247555/4503599627370496)), (16190391/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-150614483/67108864), (-1934051333/67108864)), (3/268435456), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-7959724165/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-171492597751843/9007199254740992), (1756432556473623/18014398509481984)), (56990803/18014398509481984), by norm_num⟩
  | 1 => ⟨((431612775/8589934592), (-1105147889/4294967296)), (145/17179869184), by norm_num⟩
  | 2 => ⟨((-1139050857/17179869184), (5833097273/17179869184)), (193/17179869184), by norm_num⟩
  | 3 => ⟨((501003419/8589934592), (-160352897/536870912)), (43/4294967296), by norm_num⟩
  | 4 => ⟨((-1322176745/34359738368), (3385443905/17179869184)), (229/34359738368), by norm_num⟩
  | 5 => ⟨((348930023/17179869184), (-7147504441/68719476736)), (61/17179869184), by norm_num⟩
  | 6 => ⟨((-1227795113/137438953472), (3143778997/68719476736)), (217/137438953472), by norm_num⟩
  | 7 => ⟨((462888813/137438953472), (-4740921717/274877906944)), (83/137438953472), by norm_num⟩
  | 8 => ⟨((-1221590115/1099511627776), (6255782103/1099511627776)), (111/549755813888), by norm_num⟩
  | 9 => ⟨((716410299/2199023255552), (-1834374179/1099511627776)), (33/549755813888), by norm_num⟩
  | 10 => ⟨((-189064785/2199023255552), (1936407449/4398046511104)), (141/8796093022208), by norm_num⟩
  | 11 => ⟨((725749537/35184372088832), (-3716574743/35184372088832)), (137/35184372088832), by norm_num⟩
  | 12 => ⟨((-638431545/140737488355328), (6538835877/281474976710656)), (243/281474976710656), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (1148671171691/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55575112927701/19807040628566084398385987584), (2717732771279/633825300114114700748351602688)), (8669/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889330957392879/39614081257132168796771975168), (3056830021941/39614081257132168796771975168)), (19509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889080226227211/2475880078570760549798248448), (202944773979/154742504910672534362390528)), (5183/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885373168387701/77371252455336267181195264), (3246255441391/154742504910672534362390528)), (81/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((1549136699180421/9671406556917033397649408), (3042449986063/9671406556917033397649408)), (19445/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629211950438673/302231454903657293676544), (2661229541009/604462909807314587353088)), (17019/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887198997143439/75557863725914323419136), (4322784508565/75557863725914323419136)), (27663/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297094426041717/4722366482869645213696), (810147424011/1180591620717411303424)), (20755/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810417905032471/295147905179352825856), (4453376636539/590295810358705651712)), (14275/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911354324995257/36893488147419103232), (86922992907/1152921504606846976)), (35705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910897179629863/4611686018427387904), (6253441090635/9223372036854775808)), (157/36028797018963968), by norm_num⟩
  | 6 => ⟨((1593041837964467/1152921504606846976), (3123589034623/576460752303423488)), (40223/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193753591177911/144115188075855872), (1364810437731/36028797018963968)), (17615/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490394351183241/36028797018963968), (2043700398455/9007199254740992)), (26457/18014398509481984), by norm_num⟩
  | 3 => ⟨((371924969871513/2251799813685248), (5096966799131/4503599627370496)), (8283/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112410304985537/2251799813685248), (20314315505109/4503599627370496)), (132893/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211383191007441/2251799813685248), (15144065260093/1125899906842624)), (3129/35184372088832), by norm_num⟩
  | 0 => ⟨((135698534643503/140737488355328), (14961525806239/562949953421312)), (12631/70368744177664), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((135698534643503/140737488355328), (14961525806239/562949953421312)), (48183441430544831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2091849393194799/2251799813685248), (115406756318497/2251799813685248)), (400463/1125899906842624), by norm_num⟩
  | 2 => ⟨((1937345912319751/2251799813685248), (26802288519193/281474976710656)), (785083/1125899906842624), by norm_num⟩
  | 3 => ⟨((1646387014768989/2251799813685248), (184475738164285/1125899906842624)), (3000825/2251799813685248), by norm_num⟩
  | 4 => ⟨((142911516538275/281474976710656), (269756181706529/1125899906842624)), (2685709/1125899906842624), by norm_num⟩
  | 5 => ⟨((112803467624291/562949953421312), (547846426332719/2251799813685248)), (16056573/4503599627370496), by norm_num⟩
  | 6 => ⟨((-171492597751843/9007199254740992), (1756432556473623/18014398509481984)), (56990803/18014398509481984), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-7959724165/268435456)), (3/268435456), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-159017401/67108864), (-4083907611/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((28956425447721/562949953421312), (703534427053807/9007199254740992)), (26920751/9007199254740992), by norm_num⟩
  | 1 => ⟨((-299131217/2147483648), (-1816946551/8589934592)), (141/17179869184), by norm_num⟩
  | 2 => ⟨((1620124705/8589934592), (4920382473/17179869184)), (193/17179869184), by norm_num⟩
  | 3 => ⟨((-731229839/4294967296), (-2220773791/8589934592)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((1980207113/17179869184), (93968233/536870912)), (121/17179869184), by norm_num⟩
  | 5 => ⟨((-536250027/8589934592), (-3257224861/34359738368)), (133/34359738368), by norm_num⟩
  | 6 => ⟨((1936255991/68719476736), (2940242813/68719476736)), (61/34359738368), by norm_num⟩
  | 7 => ⟨((-1498136693/137438953472), (-4549900081/274877906944)), (191/274877906944), by norm_num⟩
  | 8 => ⟨((1014257343/274877906944), (3080339457/549755813888)), (33/137438953472), by norm_num⟩
  | 9 => ⟨((-2441475379/2199023255552), (-1853714197/1099511627776)), (161/2199023255552), by norm_num⟩
  | 10 => ⟨((2644655157/8796093022208), (4015960883/8796093022208)), (177/8796093022208), by norm_num⟩
  | 11 => ⟨((-1302156169/17592186044416), (-3954699519/35184372088832)), (11/2199023255552), by norm_num⟩
  | 12 => ⟨((2350869517/140737488355328), (3569841609/140737488355328)), (161/140737488355328), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790444585791105/5070602400912917605986812821504), (643779159159/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889156652682591/316912650057057350374175801344), (190377082897/79228162514264337593543950336)), (23089/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59038422913555/1237940039285380274899124224), (856520401045/19807040628566084398385987584)), (25977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888972688798125/2475880078570760549798248448), (909832988653/1237940039285380274899124224)), (27603/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885319526541457/77371252455336267181195264), (909585659889/77371252455336267181195264)), (13803/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774518195068013/4835703278458516698824704), (852473859045/4835703278458516698824704)), (6471/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629168199840341/302231454903657293676544), (1491304061015/604462909807314587353088)), (5663/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943528656028029/37778931862957161709568), (302798099049/9444732965739290427392)), (36815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296988603113997/4722366482869645213696), (1815927754507/4722366482869645213696)), (27617/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810345509593131/295147905179352825856), (2495502601033/590295810358705651712)), (18991/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822528733471199/73786976294838206464), (24353770031/576460752303423488)), (47491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821593425025475/9223372036854775808), (3504063595567/9223372036854775808)), (53445/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592842740158637/1152921504606846976), (875116975839/288230376151711744)), (53469/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596790720966595/72057594037927936), (3058868958077/144115188075855872)), (46811/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490140238389849/36028797018963968), (4580234249493/36028797018963968)), (17567/9007199254740992), by norm_num⟩
  | 3 => ⟨((743694703416583/4503599627370496), (713899760179/1125899906842624)), (87927/9007199254740992), by norm_num⟩
  | 2 => ⟨((556055266446905/1125899906842624), (711263573323/281474976710656)), (43/1099511627776), by norm_num⟩
  | 1 => ⟨((2210537015103675/2251799813685248), (8482622818721/1125899906842624)), (264879/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169694598909611/2251799813685248), (33512368081693/2251799813685248)), (532529/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169694598909611/2251799813685248), (33512368081693/2251799813685248)), (2031436928755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090084360572273/2251799813685248), (64580877555471/2251799813685248)), (1042075/2251799813685248), by norm_num⟩
  | 2 => ⟨((1938130520323865/2251799813685248), (59942931583167/1125899906842624)), (249281/281474976710656), by norm_num⟩
  | 3 => ⟨((1661771739602233/2251799813685248), (206372208529297/2251799813685248)), (1822629/1125899906842624), by norm_num⟩
  | 4 => ⟨((603716149535887/1125899906842624), (38074377425677/281474976710656)), (3024189/1125899906842624), by norm_num⟩
  | 5 => ⟨((303116338916701/1125899906842624), (653304725102709/4503599627370496)), (4061335/1125899906842624), by norm_num⟩
  | 6 => ⟨((28956425447721/562949953421312), (703534427053807/9007199254740992)), (26920751/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-159017401/67108864), (-4083907611/134217728)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile026Terms1
