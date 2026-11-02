/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile031Gamma
public import XiRectangle.Tile031Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile031
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2504711085/4398046511104), (517836493/4398046511104)), (1813/8796093022208), by norm_num⟩
  | 1 => ⟨((3873274693/8796093022208), (4566544293/8796093022208)), (3993/8796093022208), by norm_num⟩
  | 2 => ⟨((86541401/4398046511104), (6812526037/17592186044416)), (8949/17592186044416), by norm_num⟩
  | 3 => ⟨((-1393278811/17592186044416), (4188106013/35184372088832)), (13483/35184372088832), by norm_num⟩
  | 4 => ⟨((-5035846735/140737488355328), (965604383/70368744177664)), (15349/70368744177664), by norm_num⟩
  | 5 => ⟨((-4369302219/562949953421312), (-992557767/562949953421312)), (56427/562949953421312), by norm_num⟩
  | 6 => ⟨((-4300702969/4503599627370496), (-4213092023/4503599627370496)), (174689/4503599627370496), by norm_num⟩
  | 7 => ⟨((-1957724363/36028797018963968), (-1622301677/9007199254740992)), (234673/18014398509481984), by norm_num⟩
  | 8 => ⟨((125675401/36028797018963968), (-6549669343/288230376151711744)), (280557/72057594037927936), by norm_num⟩
  | 9 => ⟨((3012791261/2305843009213693952), (-1248611223/576460752303423488)), (2464635/2305843009213693952), by norm_num⟩
  | 10 => ⟨((3702360139/18446744073709551616), (-2967575037/18446744073709551616)), (5355631/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1689617631/73786976294838206464), (-1208606919/147573952589676412928)), (7088071/73786976294838206464), by norm_num⟩
  | 12 => ⟨((2513425103/1180591620717411303424), (-71828869/1180591620717411303424)), (60977493/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile031Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((69437971/8388608), (2478704347/268435456)), (19/8388608), by norm_num⟩
  | 1 => ⟨((-3240872355/536870912), (287300281/536870912)), (5961/1073741824), by norm_num⟩
  | 2 => ⟨((735472805/268435456), (188345797/268435456)), (16497/2147483648), by norm_num⟩
  | 3 => ⟨((-22029663/33554432), (-122399239/268435456)), (15937/2147483648), by norm_num⟩
  | 4 => ⟨((26571597/268435456), (40129233/268435456)), (95239/17179869184), by norm_num⟩
  | 5 => ⟨((-1717859/268435456), (-8946971/268435456)), (468023/137438953472), by norm_num⟩
  | 6 => ⟨((-325237/268435456), (92077/16777216)), (1958323/1099511627776), by norm_num⟩
  | 7 => ⟨((1058877/2147483648), (-180337/268435456)), (3622603/4398046511104), by norm_num⟩
  | 8 => ⟨((-26267/268435456), (59431/1073741824)), (12678743/35184372088832), by norm_num⟩
  | 9 => ⟨((119499/8589934592), (-10333/8589934592)), (46543539/281474976710656), by norm_num⟩
  | 10 => ⟨((-26035/17179869184), (-2353/4294967296)), (210802069/2251799813685248), by norm_num⟩
  | 11 => ⟨((8471/68719476736), (2111/17179869184)), (1256107175/18014398509481984), by norm_num⟩
  | 12 => ⟨((-207/34359738368), (-143/8589934592)), (4511412891/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile031Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8037/640))
  have he : value ((5/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negativeHalfLogPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piArg : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-384107611/1073741824), (-7536799/1048576)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piPower : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((486634433062945/1125899906842624), (-1237786378544861/2251799813685248)), (5829893/2251799813685248), by norm_num⟩
  | 1 => ⟨((-531258563/2147483648), (2702581519/8589934592)), (15/8589934592), by norm_num⟩
  | 2 => ⟨((304073777/4294967296), (-3093725833/34359738368)), (5/8589934592), by norm_num⟩
  | 3 => ⟨((-3712878293/274877906944), (1180493473/68719476736)), (17/137438953472), by norm_num⟩
  | 4 => ⟨((531280343/274877906944), (-2702692317/1099511627776)), (21/1099511627776), by norm_num⟩
  | 5 => ⟨((-486537989/2199023255552), (1237541067/4398046511104)), (21/8796093022208), by norm_num⟩
  | 6 => ⟨((371303051/17592186044416), (-3777733985/140737488355328)), (35/140737488355328), by norm_num⟩
  | 7 => ⟨((-242880971/140737488355328), (1235567141/562949953421312)), (25/1125899906842624), by norm_num⟩
  | 8 => ⟨((2224264849/18014398509481984), (-176798829/1125899906842624)), (31/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1131636643/144115188075855872), (1439195757/144115188075855872)), (33/288230376151711744), by norm_num⟩
  | 10 => ⟨((259083657/576460752303423488), (-2635984631/4611686018427387904)), (1/144115188075855872), by norm_num⟩
  | 11 => ⟨((-3451122095/147573952589676412928), (1097269231/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 12 => ⟨((658433767/590295810358705651712), (-1674769175/1180591620717411303424)), (45/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893164321/5070602400912917605986812821504), (-1178168375155/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890709253985193/316912650057057350374175801344), (-1398251773775/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892722471510165/39614081257132168796771975168), (-1572981309457/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946341716911733/1237940039285380274899124224), (-1671231486629/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887174616773715/77371252455336267181195264), (-104447667675/9671406556917033397649408)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552514084558567/9671406556917033397649408), (-391660476639/2417851639229258349412352)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315344695657679/151115727451828646838272), (-1370738554607/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1892000060167359/75557863725914323419136), (-1113656526215/37778931862957161709568)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300694680735945/4722366482869645213696), (-52198900535/147573952589676412928)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812892639081511/295147905179352825856), (-2296556648569/590295810358705651712)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((457223540303065/18446744073709551616), (-2870403313025/73786976294838206464)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828751237818473/9223372036854775808), (-3228801485621/9223372036854775808)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599996437767013/1152921504606846976), (-3228298597945/1152921504606846976)), (3341/576460752303423488), by norm_num⟩
  | 5 => ⟨((599918149968611/72057594037927936), (-2824195406739/144115188075855872)), (2925/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499513276037889/36028797018963968), (-4235161082903/36028797018963968)), (2195/9007199254740992), by norm_num⟩
  | 3 => ⟨((93693095611015/562949953421312), (-1322992411171/2251799813685248)), (5493/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123786419180973/2251799813685248), (-5288995760573/2251799813685248)), (11001/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122721831163105/1125899906842624), (-7740287419/1099511627776)), (4135/281474976710656), by norm_num⟩
  | 0 => ⟨((1119512438333127/1125899906842624), (-7911161864455/562949953421312)), (33233/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1119512438333127/1125899906842624), (-7911161864455/562949953421312)), (126773838523482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1112938855433755/1125899906842624), (-15732560337021/562949953421312)), (4189/70368744177664), by norm_num⟩
  | 2 => ⟨((549623831831509/562949953421312), (-62205805642629/1125899906842624)), (34063/281474976710656), by norm_num⟩
  | 3 => ⟨((534894734644167/562949953421312), (-121466546188273/1125899906842624)), (140555/562949953421312), by norm_num⟩
  | 4 => ⟨((1003371063352627/1125899906842624), (-230826259409581/1125899906842624)), (594857/1125899906842624), by norm_num⟩
  | 5 => ⟨((846853901439781/1125899906842624), (-411412041063209/1125899906842624)), (1304151/1125899906842624), by norm_num⟩
  | 6 => ⟨((486634433062945/1125899906842624), (-1237786378544861/2251799813685248)), (5829893/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-384107611/1073741824), (-7536799/1048576)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piGamma : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1367230007/4398046511104), (-288247551/1099511627776)), (1797/8796093022208), by norm_num⟩
  | 1 => ⟨((5238326861/17592186044416), (582257467/4398046511104)), (9945/17592186044416), by norm_num⟩
  | 2 => ⟨((663569/35184372088832), (2176602709/17592186044416)), (6957/8796093022208), by norm_num⟩
  | 3 => ⟨((-3842147247/140737488355328), (751109945/70368744177664)), (104621/140737488355328), by norm_num⟩
  | 4 => ⟨((-843259191/281474976710656), (-1052996373/281474976710656)), (37087/70368744177664), by norm_num⟩
  | 5 => ⟨((1672772355/4503599627370496), (-1924282531/4503599627370496)), (2707971/9007199254740992), by norm_num⟩
  | 6 => ⟨((1319663317/36028797018963968), (2601675687/72057594037927936)), (5181573/36028797018963968), by norm_num⟩
  | 7 => ⟨((-157909591/36028797018963968), (2041083957/1152921504606846976)), (4279285/72057594037927936), by norm_num⟩
  | 8 => ⟨((12693197/1152921504606846976), (-2508890355/4611686018427387904)), (199590615/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1033245045/18446744073709551616), (1184385849/73786976294838206464)), (523461845/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-867817161/295147905179352825856), (1355470263/295147905179352825856)), (633000271/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-348290259/1180591620717411303424), (-3783619011/9444732965739290427392)), (2981573315/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1673052633/37778931862957161709568), (-455246831/37778931862957161709568)), (3969904547/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5491010391/1099511627776), (385100651/549755813888)), (2681/549755813888), by norm_num⟩
  | 1 => ⟨((-543161823/1099511627776), (384438351/68719476736)), (16931/1099511627776), by norm_num⟩
  | 2 => ⟨((-4342976865/2199023255552), (-63587807/549755813888)), (27861/1099511627776), by norm_num⟩
  | 3 => ⟨((74208377/8796093022208), (-2714310261/8796093022208)), (505217/17592186044416), by norm_num⟩
  | 4 => ⟨((4759794869/281474976710656), (-236212169/281474976710656)), (3527135/140737488355328), by norm_num⟩
  | 5 => ⟨((804058697/4503599627370496), (-3020318245/2251799813685248)), (40308087/2251799813685248), by norm_num⟩
  | 6 => ⟨((2146576857/9007199254740992), (103039537/18014398509481984)), (97863227/9007199254740992), by norm_num⟩
  | 7 => ⟨((268972113/288230376151711744), (1891388949/288230376151711744)), (1658148845/288230376151711744), by norm_num⟩
  | 8 => ⟨((1075130651/1152921504606846976), (5846323/72057594037927936)), (1567693255/576460752303423488), by norm_num⟩
  | 9 => ⟨((602367/576460752303423488), (328986851/4611686018427387904)), (5440602573/4611686018427387904), by norm_num⟩
  | 10 => ⟨((9380107/9223372036854775808), (894975/2305843009213693952)), (568098109/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-371039/36893488147419103232), (631345/2305843009213693952)), (8061112007/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-37945/18446744073709551616), (52479/18446744073709551616)), (2199253873/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5362315/1073741824), (376075/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-530431/1073741824), (6006849/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1060297/536870912), (-124195/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((9059/1073741824), (-331337/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((18157/1073741824), (-901/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((3/16777216), (-45/33554432)), (1/10000000), by norm_num⟩
  | 6 => ⟨((1/4194304), (3/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (7/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/1073741824), 0), (1/10000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨31,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨31,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(4539941/536870912)) (L:=(5544763969/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile031
