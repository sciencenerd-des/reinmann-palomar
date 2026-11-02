/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile013Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-14033862625/1073741824)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((759081423166009/4503599627370496), (-209162466023405/2251799813685248)), (477091/4503599627370496), by norm_num⟩
  | 1 => ⟨((-198825879/536870912), (7012587143/34359738368)), (17/68719476736), by norm_num⟩
  | 2 => ⟨((55918733817/137438953472), (-30816457643/137438953472)), (5/17179869184), by norm_num⟩
  | 3 => ⟨((-81910677517/274877906944), (2821278255/17179869184)), (61/274877906944), by norm_num⟩
  | 4 => ⟨((44994038447/274877906944), (-12397963843/137438953472)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((-79089605687/1099511627776), (5448222173/137438953472)), (33/549755813888), by norm_num⟩
  | 6 => ⟨((28962937571/1099511627776), (-15961290215/1099511627776)), (51/2199023255552), by norm_num⟩
  | 7 => ⟨((-18182308075/2199023255552), (40080616167/8796093022208)), (67/8796093022208), by norm_num⟩
  | 8 => ⟨((39950614175/17592186044416), (-22016528729/17592186044416)), (19/8796093022208), by norm_num⟩
  | 9 => ⟨((-9753385705/17592186044416), (43000229361/140737488355328)), (19/35184372088832), by norm_num⟩
  | 10 => ⟨((34288606053/281474976710656), (-37792464313/562949953421312)), (69/562949953421312), by norm_num⟩
  | 11 => ⟨((-54792558503/2251799813685248), (15097914805/1125899906842624)), (29/1125899906842624), by norm_num⟩
  | 12 => ⟨((80261037465/18014398509481984), (-2764459123/1125899906842624)), (87/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-82012829643/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779426784953175/633825300114114700748351602688), (-388505077885/316912650057057350374175801344)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890482028683195/39614081257132168796771975168), (-437004690611/19807040628566084398385987584)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890303260284731/2475880078570760549798248448), (-116059855667/309485009821345068724781056)), (647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13843510891025/1208925819614629174706176), (-464151627873/77371252455336267181195264)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550283339904395/9671406556917033397649408), (-870097783895/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259427235879417/604462909807314587353088), (-761149093813/604462909807314587353088)), (531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944414730937321/37778931862957161709568), (-77282360035/4722366482869645213696)), (863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298317313935875/4722366482869645213696), (-115885325253/590295810358705651712)), (81/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405629336055801/147573952589676412928), (-1274241989457/590295810358705651712)), (445/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28512666586523/1152921504606846976), (-796028980643/36893488147419103232)), (139/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824159249496857/9223372036854775808), (-1790042063577/9223372036854775808)), (1251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595406884570703/1152921504606846976), (-1788764004067/1152921504606846976)), (313/288230376151711744), by norm_num⟩
  | 5 => ⟨((597911589591271/72057594037927936), (-1563731880719/144115188075855872)), (137/18014398509481984), by norm_num⟩
  | 4 => ⟨((746749534215705/18014398509481984), (-2342727558059/36028797018963968)), (411/9007199254740992), by norm_num⟩
  | 3 => ⟨((372895335514693/2251799813685248), (-2923393191093/9007199254740992)), (257/1125899906842624), by norm_num⟩
  | 2 => ⟨((2232585150797039/4503599627370496), (-1457941098023/1125899906842624)), (4113/4503599627370496), by norm_num⟩
  | 1 => ⟨((2223033754462195/2251799813685248), (-4355092589731/1125899906842624)), (3089/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097245489119767/1125899906842624), (-17271084836261/2251799813685248)), (12387/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1097245489119767/1125899906842624), (-17271084836261/2251799813685248)), (47252663619231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1069254099306979/1125899906842624), (-33663063321385/2251799813685248)), (12167/1125899906842624), by norm_num⟩
  | 2 => ⟨((2030413221424137/2251799813685248), (-31969421289465/1125899906842624)), (11737/562949953421312), by norm_num⟩
  | 3 => ⟨((1828976825166077/2251799813685248), (-57652669898019/1125899906842624)), (21833/562949953421312), by norm_num⟩
  | 4 => ⟨((1479643476902261/2251799813685248), (-187308652414989/2251799813685248)), (37703/562949953421312), by norm_num⟩
  | 5 => ⟨((956683748873873/2251799813685248), (-246158671857791/2251799813685248)), (111643/1125899906842624), by norm_num⟩
  | 6 => ⟨((759081423166009/4503599627370496), (-209162466023405/2251799813685248)), (477091/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-14033862625/1073741824)), (3/8589934592), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-7417145753/4294967296), (-58827237253/4294967296)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((682796343239103/9007199254740992), (-1448907721361047/9007199254740992)), (636175/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2998727191/17179869184), (25453440249/68719476736)), (47/137438953472), by norm_num⟩
  | 2 => ⟨((431551533/2147483648), (-58608712083/137438953472)), (7/17179869184), by norm_num⟩
  | 3 => ⟨((-1324912169/8589934592), (89967697841/274877906944)), (89/274877906944), by norm_num⟩
  | 4 => ⟨((24405784079/274877906944), (-51789569975/274877906944)), (53/274877906944), by norm_num⟩
  | 5 => ⟨((-22478557841/549755813888), (47699956719/549755813888)), (51/549755813888), by norm_num⟩
  | 6 => ⟨((4313232683/274877906944), (-36611069759/1099511627776)), (81/2199023255552), by norm_num⟩
  | 7 => ⟨((-22700766351/4398046511104), (24085743847/2199023255552)), (55/4398046511104), by norm_num⟩
  | 8 => ⟨((6533805775/4398046511104), (-3466217171/1099511627776)), (33/8796093022208), by norm_num⟩
  | 9 => ⟨((-26746033383/70368744177664), (28377813287/35184372088832)), (69/70368744177664), by norm_num⟩
  | 10 => ⟨((12317003553/140737488355328), (-52273863877/281474976710656)), (65/281474976710656), by norm_num⟩
  | 11 => ⟨((-20626144561/1125899906842624), (87538196157/2251799813685248)), (111/2251799813685248), by norm_num⟩
  | 12 => ⟨((31662301995/9007199254740992), (-67188048513/9007199254740992)), (11/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-1472489013031/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779303588618007/633825300114114700748351602688), (-1743614104463/633825300114114700748351602688)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236292922301491/4951760157141521099596496896), (-980633112333/19807040628566084398385987584)), (305/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945077936783945/1237940039285380274899124224), (-1041739039511/1237940039285380274899124224)), (81/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771821927743647/154742504910672534362390528), (-520766245759/38685626227668133590597632)), (81/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550145005729515/9671406556917033397649408), (-488108651659/2417851639229258349412352)), (19/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259306109025141/604462909807314587353088), (-213492697225/75557863725914323419136)), (133/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888632472518397/75557863725914323419136), (-43352855213/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649084716802943/2361183241434822606848), (-1040108874499/2361183241434822606848)), (649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622313784250975/590295810358705651712), (-2859130986087/590295810358705651712)), (223/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912277937606905/36893488147419103232), (-893040471037/18446744073709551616)), (1115/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911936076535425/4611686018427387904), (-2008137297285/4611686018427387904)), (627/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398779802975033/288230376151711744), (-501658385891/144115188075855872)), (1255/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195570818721903/144115188075855872), (-3508227864965/144115188075855872)), (1099/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493119237490793/36028797018963968), (-1313896661155/9007199254740992)), (1649/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491104303303173/9007199254740992), (-6557676445925/9007199254740992)), (129/562949953421312), by norm_num⟩
  | 2 => ⟨((278953044300783/562949953421312), (-13079990883863/4503599627370496)), (2067/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110787936064749/1125899906842624), (-19531786041741/2251799813685248)), (3109/1125899906842624), by norm_num⟩
  | 0 => ⟨((273938639606193/281474976710656), (-38711997247503/2251799813685248)), (3127/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((273938639606193/281474976710656), (-38711997247503/2251799813685248)), (11928560497093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2132167149728205/2251799813685248), (-75351009786713/2251799813685248)), (12389/1125899906842624), by norm_num⟩
  | 2 => ⟨((2016368840653469/2251799813685248), (-142695586694399/2251799813685248)), (48583/2251799813685248), by norm_num⟩
  | 3 => ⟨((898255086111667/1125899906842624), (-255552854175313/2251799813685248)), (93165/2251799813685248), by norm_num⟩
  | 4 => ⟨((351068234219461/562949953421312), (-1592834551987/8796093022208)), (169803/2251799813685248), by norm_num⟩
  | 5 => ⟨((801896176018569/2251799813685248), (-127145907201753/562949953421312)), (273285/2251799813685248), by norm_num⟩
  | 6 => ⟨((682796343239103/9007199254740992), (-1448907721361047/9007199254740992)), (636175/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-58827237253/4294967296)), (3/8589934592), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1931040333/1073741824), (-15315563641/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-188231678495529/9007199254740992), (-1479304613967997/9007199254740992)), (965999/4503599627370496), by norm_num⟩
  | 1 => ⟨((3443602387/68719476736), (108252488429/274877906944)), (9/17179869184), by norm_num⟩
  | 2 => ⟨((-8257397885/137438953472), (-8111816571/17179869184)), (11/17179869184), by norm_num⟩
  | 3 => ⟨((3300062559/68719476736), (51870097625/137438953472)), (143/274877906944), by norm_num⟩
  | 4 => ⟨((-3956602205/137438953472), (-62189530947/274877906944)), (87/274877906944), by norm_num⟩
  | 5 => ⟨((7590014179/549755813888), (29824796455/274877906944)), (169/1099511627776), by norm_num⟩
  | 6 => ⟨((-12133372747/2199023255552), (-47677825621/1099511627776)), (137/2199023255552), by norm_num⟩
  | 7 => ⟨((8312730615/4398046511104), (65329390099/4398046511104)), (3/137438953472), by norm_num⟩
  | 8 => ⟨((-9966528723/17592186044416), (-39163258923/8796093022208)), (117/17592186044416), by norm_num⟩
  | 9 => ⟨((5310820469/35184372088832), (41737508195/35184372088832)), (127/70368744177664), by norm_num⟩
  | 10 => ⟨((-5093916519/140737488355328), (-80065738879/281474976710656)), (31/70368744177664), by norm_num⟩
  | 11 => ⟨((4441701215/562949953421312), (69814275189/1125899906842624)), (55/562949953421312), by norm_num⟩
  | 12 => ⟨((-14200979129/9007199254740992), (-111604880299/9007199254740992)), (89/4503599627370496), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-1105500160875/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889595648389795/316912650057057350374175801344), (-2617796650799/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890216952924663/39614081257132168796771975168), (-368068778405/4951760157141521099596496896)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890021420170437/2475880078570760549798248448), (-3128010009299/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771687332347709/154742504910672534362390528), (-3127363693483/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775009335883427/4835703278458516698824704), (-732804221367/2417851639229258349412352)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629597708067535/302231454903657293676544), (-1282064173797/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944226157143131/37778931862957161709568), (-4165421832553/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298034068157243/4722366482869645213696), (-3122940802337/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405531814043259/147573952589676412928), (-4292215146055/590295810358705651712)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824322114976315/73786976294838206464), (-2681263646153/36893488147419103232)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((227951043601379/1152921504606846976), (-3014537573605/4611686018427387904)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797427189723913/576460752303423488), (-3012183812103/576460752303423488)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((597668968039805/72057594037927936), (-5266029210517/144115188075855872)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492767611201417/36028797018963968), (-3944233824879/18014398509481984)), (2205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490660755225241/9007199254740992), (-4921047983501/4503599627370496)), (2761/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230725267909407/4503599627370496), (-19628804909111/4503599627370496)), (5535/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110098729809109/1125899906842624), (-29305015370145/2251799813685248)), (4169/1125899906842624), by norm_num⟩
  | 0 => ⟨((8549352794395/8796093022208), (-58058915421393/2251799813685248)), (2103/281474976710656), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((8549352794395/8796093022208), (-58058915421393/2251799813685248)), (8022309423351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((132858982946733/140737488355328), (-112860596072421/2251799813685248)), (8393/562949953421312), by norm_num⟩
  | 2 => ⟨((250135960797709/281474976710656), (-53271321607951/562949953421312)), (1043/35184372088832), by norm_num⟩
  | 3 => ⟨((439531365669613/562949953421312), (-189360679504611/1125899906842624)), (65637/1125899906842624), by norm_num⟩
  | 4 => ⟨((1308986374736655/2251799813685248), (-591384421019737/2251799813685248)), (124573/1125899906842624), by norm_num⟩
  | 5 => ⟨((302804402845549/1125899906842624), (-343775740916979/1125899906842624)), (420527/2251799813685248), by norm_num⟩
  | 6 => ⟨((-188231678495529/9007199254740992), (-1479304613967997/9007199254740992)), (965999/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-15315563641/1073741824)), (1/2147483648), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2001111149/1073741824), (-63485251201/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-419466872131073/4503599627370496), (-1117079203401709/9007199254740992)), (984387/9007199254740992), by norm_num⟩
  | 1 => ⟨((31809570921/137438953472), (10588979877/34359738368)), (39/137438953472), by norm_num⟩
  | 2 => ⟨((-19760953577/68719476736), (-26312626511/68719476736)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((8184020825/34359738368), (43589613727/137438953472)), (11/34359738368), by norm_num⟩
  | 4 => ⟨((-10168263885/68719476736), (-27079030253/137438953472)), (57/274877906944), by norm_num⟩
  | 5 => ⟨((5053437309/68719476736), (53831089877/549755813888)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((-8371546649/274877906944), (-44588411067/1099511627776)), (25/549755813888), by norm_num⟩
  | 7 => ⟨((23774299357/2199023255552), (63313165237/4398046511104)), (73/4398046511104), by norm_num⟩
  | 8 => ⟨((-29538457283/8796093022208), (-39331826329/8796093022208)), (47/8796093022208), by norm_num⟩
  | 9 => ⟨((32622359523/35184372088832), (21719092621/17592186044416)), (27/17592186044416), by norm_num⟩
  | 10 => ⟨((-8106351811/35184372088832), (-43175934145/140737488355328)), (7/17592186044416), by norm_num⟩
  | 11 => ⟨((14649838197/281474976710656), (78027756995/1125899906842624)), (13/140737488355328), by norm_num⟩
  | 12 => ⟨((-24268986903/2251799813685248), (-64630564075/4503599627370496)), (89/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-2885208323579/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444772019913525/158456325028528675187087900672), (-3415682726023/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890100705615689/39614081257132168796771975168), (-240125115861/2475880078570760549798248448)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889897740497341/2475880078570760549798248448), (-4081349437765/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221445433130725/19342813113834066795298816), (-4080474805809/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549902346944297/9671406556917033397649408), (-3824515975605/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259093432832927/604462909807314587353088), (-1672761241475/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944143109223975/37778931862957161709568), (-5307355963/73786976294838206464)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324477292558691/1180591620717411303424), (-4074525880361/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621954992283957/590295810358705651712), (-5599998033941/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912052996126425/36893488147419103232), (-6996286076247/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823364122196011/9223372036854775808), (-7865720376275/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594608794593415/1152921504606846976), (-7859346263145/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((597560762338825/72057594037927936), (-1717440208349/36028797018963968)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((746219976596417/18014398509481984), (-10290316289737/36028797018963968)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490245880010797/9007199254740992), (-3209461925411/2251799813685248)), (1385/9007199254740992), by norm_num⟩
  | 2 => ⟨((557469921191355/1125899906842624), (-50001243363/8796093022208)), (695/1125899906842624), by norm_num⟩
  | 1 => ⟨((554722441605495/562949953421312), (-9553400744011/562949953421312)), (2097/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092931615133475/1125899906842624), (-37839786125465/1125899906842624)), (265/70368744177664), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1092931615133475/1125899906842624), (-37839786125465/1125899906842624)), (1010895043826081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1059656954133677/1125899906842624), (-73463543810721/1125899906842624)), (4259/562949953421312), by norm_num⟩
  | 2 => ⟨((248129509866553/281474976710656), (-138282549987307/1125899906842624)), (8573/562949953421312), by norm_num⟩
  | 3 => ⟨((857953703667801/1125899906842624), (-243801290988071/1125899906842624)), (17221/562949953421312), by norm_num⟩
  | 4 => ⟨((600981920362151/1125899906842624), (-371560951894535/1125899906842624)), (134815/2251799813685248), by norm_num⟩
  | 5 => ⟨((396343806893295/2251799813685248), (-793325989438523/2251799813685248)), (232905/2251799813685248), by norm_num⟩
  | 6 => ⟨((-419466872131073/4503599627370496), (-1117079203401709/9007199254740992)), (984387/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-63485251201/4294967296)), (1/4294967296), by norm_num⟩, -2, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8262280205/4294967296), (-65530209873/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-592176016967439/4503599627370496), (-572870407328141/9007199254740992)), (28623/140737488355328), by norm_num⟩
  | 1 => ⟨((23176597507/68719476736), (5605253537/34359738368)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((-14861699721/34359738368), (-7188595729/34359738368)), (97/137438953472), by norm_num⟩
  | 3 => ⟨((25413004767/68719476736), (24584511995/137438953472)), (21/34359738368), by norm_num⟩
  | 4 => ⟨((-65183070249/274877906944), (-31529014123/274877906944)), (55/137438953472), by norm_num⟩
  | 5 => ⟨((66876509661/549755813888), (32348129807/549755813888)), (115/549755813888), by norm_num⟩
  | 6 => ⟨((-14294571707/274877906944), (-27657104921/1099511627776)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((41902688589/2199023255552), (40536613427/4398046511104)), (149/4398046511104), by norm_num⟩
  | 8 => ⟨((-26869568543/4398046511104), (-25993590141/8796093022208)), (97/8796093022208), by norm_num⟩
  | 9 => ⟨((61261406729/35184372088832), (14816053851/17592186044416)), (113/35184372088832), by norm_num⟩
  | 10 => ⟨((-62852962331/140737488355328), (-7600485561/35184372088832)), (59/70368744177664), by norm_num⟩
  | 11 => ⟨((58623514671/562949953421312), (28356160809/562949953421312)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((-50122115429/2251799813685248), (-757626213/70368744177664)), (49/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418141/10141204801825835211973625643008), (-1752709781637/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778992536804977/633825300114114700748351602688), (-4149514993609/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944996534656741/19807040628566084398385987584), (-583424262659/4951760157141521099596496896)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944891589975339/1237940039285380274899124224), (-2479065209469/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771448683067133/154742504910672534362390528), (-4957032645515/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549794503725167/9671406556917033397649408), (-4646051843095/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258998835078957/604462909807314587353088), (-1016032309443/151115727451828646838272)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472033014241557/18889465931478580854784), (-6602023818849/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648896582192021/2361183241434822606848), (-2474802618869/2361183241434822606848)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621794859741691/590295810358705651712), (-6802599732343/590295810358705651712)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911952445530121/36893488147419103232), (-1062323677771/9223372036854775808)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823136599021619/9223372036854775808), (-2388626707473/2305843009213693952)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594379669001387/1152921504606846976), (-9546501343727/1152921504606846976)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194919241184259/144115188075855872), (-8344185744677/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492132941041347/36028797018963968), (-781142554999/2251799813685248)), (277/4503599627370496), by norm_num⟩
  | 3 => ⟨((372463965212929/2251799813685248), (-15591373404845/9007199254740992)), (1389/4503599627370496), by norm_num⟩
  | 2 => ⟨((278635122113747/562949953421312), (-15544193708755/2251799813685248)), (1395/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108822676757719/1125899906842624), (-11599235495551/562949953421312)), (4213/1125899906842624), by norm_num⟩
  | 0 => ⟨((545797732903549/562949953421312), (-22963223658253/562949953421312)), (8541/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((545797732903549/562949953421312), (-22963223658253/562949953421312)), (32581333640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056462848232353/1125899906842624), (-44527138999341/562949953421312)), (17259/1125899906842624), by norm_num⟩
  | 2 => ⟨((984264301409387/1125899906842624), (-167124156614597/1125899906842624)), (2195/70368744177664), by norm_num⟩
  | 3 => ⟨((417819437405939/562949953421312), (-292200648137885/1125899906842624)), (71831/1125899906842624), by norm_num⟩
  | 4 => ⟨((544374421384807/1125899906842624), (-216870273587627/562949953421312)), (71955/562949953421312), by norm_num⟩
  | 5 => ⟨((192224278084571/2251799813685248), (-838857017270053/2251799813685248)), (1000165/4503599627370496), by norm_num⟩
  | 6 => ⟨((-592176016967439/4503599627370496), (-572870407328141/9007199254740992)), (28623/140737488355328), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8262280205/4294967296), (-65530209873/4294967296)), (1/2147483648), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2125249673/1073741824), (-33711772939/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-622219094172377/4503599627370496), (-6033028607795/4503599627370496)), (391817/2251799813685248), by norm_num⟩
  | 1 => ⟨((12528014077/34359738368), (971771751/274877906944)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-66124294751/137438953472), (-1282280681/274877906944)), (171/274877906944), by norm_num⟩
  | 3 => ⟨((116337203153/274877906944), (1128004077/274877906944)), (153/274877906944), by norm_num⟩
  | 4 => ⟨((-19188784293/68719476736), (-744216857/274877906944)), (103/274877906944), by norm_num⟩
  | 5 => ⟨((10128060367/68719476736), (785612381/549755813888)), (111/549755813888), by norm_num⟩
  | 6 => ⟨((-35638042595/549755813888), (-691092037/1099511627776)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((3358958483/137438953472), (130273679/549755813888)), (153/4398046511104), by norm_num⟩
  | 8 => ⟨((-17728968009/2199023255552), (-687599415/8796093022208)), (103/8796093022208), by norm_num⟩
  | 9 => ⟨((83178245281/35184372088832), (403247617/17592186044416)), (123/35184372088832), by norm_num⟩
  | 10 => ⟨((-43902431575/70368744177664), (-851354863/140737488355328)), (33/35184372088832), by norm_num⟩
  | 11 => ⟨((84262570063/562949953421312), (817008833/562949953421312)), (129/562949953421312), by norm_num⟩
  | 12 => ⟨((-74124584379/2251799813685248), (-359355525/1125899906842624)), (115/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-1019911370333/2535301200456458802993406410752)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778903571918927/633825300114114700748351602688), (-37725061629/4951760157141521099596496896)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944946408313317/19807040628566084398385987584), (-2715715371531/19807040628566084398385987584)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236209555253683/309485009821345068724781056), (-5769725774301/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885670849227613/77371252455336267181195264), (-5768410102493/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549693943724413/9671406556917033397649408), (-337905415297/604462909807314587353088)), (407/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258910583355415/604462909807314587353088), (-2364639035829/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943994078809455/37778931862957161709568), (-7682456278015/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648842405648893/2361183241434822606848), (-2879774686539/2361183241434822606848)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405411294656361/147573952589676412928), (-7915654868305/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823716747653171/73786976294838206464), (-9888980900091/73786976294838206464)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822923507232623/9223372036854775808), (-11117421416367/9223372036854775808)), (421/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398541198151465/288230376151711744), (-2776955065527/288230376151711744)), (843/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194729221415447/144115188075855872), (-9708543461977/144115188075855872)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((186480489679191/4503599627370496), (-14541221782209/36028797018963968)), (1111/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489487618653181/9007199254740992), (-2267343801779/1125899906842624)), (1393/4503599627370496), by norm_num⟩
  | 2 => ⟨((278540463907517/562949953421312), (-18082108819549/2251799813685248)), (2799/2251799813685248), by norm_num⟩
  | 1 => ⟨((554114468810489/562949953421312), (-13490821672659/562949953421312)), (529/140737488355328), by norm_num⟩
  | 0 => ⟨((1090305945865799/1125899906842624), (-53397723029701/1125899906842624)), (8599/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090305945865799/1125899906842624), (-53397723029701/1125899906842624)), (32802586082076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((263326191688575/281474976710656), (-12927404683389/140737488355328)), (17471/1125899906842624), by norm_num⟩
  | 2 => ⟨((487945414291003/562949953421312), (-96751030119261/562949953421312)), (8975/281474976710656), by norm_num⟩
  | 3 => ⟨((406306038589009/562949953421312), (-335441693796839/1125899906842624)), (37287/562949953421312), by norm_num⟩
  | 4 => ⟨((3801245832257/8796093022208), (-968412804412687/2251799813685248)), (152083/1125899906842624), by norm_num⟩
  | 5 => ⟨((2028843343347/1125899906842624), (-104625290097091/281474976710656)), (1049025/4503599627370496), by norm_num⟩
  | 6 => ⟨((-622219094172377/4503599627370496), (-6033028607795/4503599627370496)), (391817/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-33711772939/2147483648)), (1/2147483648), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8723240287/4294967296), (-8648274941/536870912)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1088128800152057/9007199254740992), (460956851258107/9007199254740992)), (1637267/9007199254740992), by norm_num⟩
  | 1 => ⟨((89926373781/274877906944), (-4761864829/34359738368)), (69/137438953472), by norm_num⟩
  | 2 => ⟨((-30440641825/68719476736), (805960563/4294967296)), (3/4294967296), by norm_num⟩
  | 3 => ⟨((3434782759/8589934592), (-11640435545/68719476736)), (11/17179869184), by norm_num⟩
  | 4 => ⟨((-37206256565/137438953472), (15761441909/137438953472)), (121/274877906944), by norm_num⟩
  | 5 => ⟨((40302564229/274877906944), (-34146220745/549755813888)), (133/549755813888), by norm_num⟩
  | 6 => ⟨((-72760911443/1099511627776), (7705806663/274877906944)), (61/549755813888), by norm_num⟩
  | 7 => ⟨((56297200247/2199023255552), (-23848812895/2199023255552)), (3/68719476736), by norm_num⟩
  | 8 => ⟨((-76227822225/8796093022208), (16145945639/4398046511104)), (33/2199023255552), by norm_num⟩
  | 9 => ⟨((91746119691/35184372088832), (-38865805631/35184372088832)), (161/35184372088832), by norm_num⟩
  | 10 => ⟨((-6211327447/8796093022208), (21050110551/70368744177664)), (89/70368744177664), by norm_num⟩
  | 11 => ⟨((48932615395/281474976710656), (-10364501111/140737488355328)), (89/281474976710656), by norm_num⟩
  | 12 => ⟨((-88341319307/2251799813685248), (4677931553/281474976710656)), (163/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (3570313362691/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889413357849097/316912650057057350374175801344), (4225584147757/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889806536179675/39614081257132168796771975168), (1188228384561/9903520314283042199192993792)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889585003420921/2475880078570760549798248448), (1262230409409/618970019642690137449562112)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771250523374633/154742504910672534362390528), (5047741559319/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549608746933855/9671406556917033397649408), (2365502017425/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258836315841649/604462909807314587353088), (4138375028815/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((14748968726133/590295810358705651712), (6722509479073/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324398787240919/1180591620717411303424), (5039826282645/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621522636769155/590295810358705651712), (54112665007/4611686018427387904)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911782342465459/36893488147419103232), (8653017602013/73786976294838206464)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822753967322741/9223372036854775808), (1215969962621/1152921504606846976)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593997163132679/1152921504606846976), (9719156325421/1152921504606846976)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194584690909741/144115188075855872), (4247293560803/72057594037927936)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491631402349233/36028797018963968), (3180635428899/9007199254740992)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489229443726881/9007199254740992), (15869357326003/9007199254740992)), (1389/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113914839613367/2251799813685248), (3954668626541/562949953421312)), (2791/2251799813685248), by norm_num⟩
  | 1 => ⟨((276971538814385/281474976710656), (23601469608819/1125899906842624)), (4215/1125899906842624), by norm_num⟩
  | 0 => ⟨((272432603695069/281474976710656), (11674441437905/281474976710656)), (2137/281474976710656), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((272432603695069/281474976710656), (11674441437905/281474976710656)), (8152009130382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((65799127012045/70368744177664), (90395203574589/1125899906842624)), (17257/1125899906842624), by norm_num⟩
  | 2 => ⟨((977162472493731/1125899906842624), (169050209742751/1125899906842624)), (35045/1125899906842624), by norm_num⟩
  | 3 => ⟨((205672928518473/281474976710656), (293435535297367/1125899906842624)), (71355/1125899906842624), by norm_num⟩
  | 4 => ⟨((524662307404521/1125899906842624), (53603118278285/140737488355328)), (4421/35184372088832), by norm_num⟩
  | 5 => ⟨((324645918343919/4503599627370496), (799318960388361/2251799813685248)), (117/549755813888), by norm_num⟩
  | 6 => ⟨((-1088128800152057/9007199254740992), (460956851258107/9007199254740992)), (1637267/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-8648274941/536870912)), (1/2147483648), by norm_num⟩, -3, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile013Terms1
