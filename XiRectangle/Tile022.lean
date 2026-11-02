/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile022Gamma
public import XiRectangle.Tile022Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile022
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-241927589/137438953472), (-2119069667/549755813888)), (589/1099511627776), by norm_num⟩
  | 1 => ⟨((1394720253/1099511627776), (-4771886343/1099511627776)), (1243/1099511627776), by norm_num⟩
  | 2 => ⟨((4230796493/2199023255552), (-705291263/549755813888)), (2765/2199023255552), by norm_num⟩
  | 3 => ⟨((6584549461/8796093022208), (143793495/2199023255552)), (8407/8796093022208), by norm_num⟩
  | 4 => ⟨((285839719/2199023255552), (1012822033/8796093022208)), (9747/17592186044416), by norm_num⟩
  | 5 => ⟨((1137924171/140737488355328), (4130966583/140737488355328)), (18331/70368744177664), by norm_num⟩
  | 6 => ⟨((-1033761329/1125899906842624), (4724217161/1125899906842624)), (116403/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2646794041/9007199254740992), (1982052499/4503599627370496)), (320989/9007199254740992), by norm_num⟩
  | 8 => ⟨((-217208955/4503599627370496), (2767938809/72057594037927936)), (392967/36028797018963968), by norm_num⟩
  | 9 => ⟨((-3641346955/576460752303423488), (1335355477/576460752303423488)), (436445/144115188075855872), by norm_num⟩
  | 10 => ⟨((-5986648545/9223372036854775808), (86353907/4611686018427387904)), (7285153/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-4052560927/73786976294838206464), (-931482139/73786976294838206464)), (7875601/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-1305052809/295147905179352825856), (-1173220365/590295810358705651712)), (22817725/295147905179352825856), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile022Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135803581/268435456), (7792050511/536870912)), (263/268435456), by norm_num⟩
  | 1 => ⟨((106250993/67108864), (-415169419/134217728)), (2369/1073741824), by norm_num⟩
  | 2 => ⟨((-83915787/134217728), (497351385/536870912)), (6377/2147483648), by norm_num⟩
  | 3 => ⟨((4105789/16777216), (-18929553/134217728)), (48455/17179869184), by norm_num⟩
  | 4 => ⟨((-15421533/268435456), (1187801/536870912)), (287287/137438953472), by norm_num⟩
  | 5 => ⟨((1203435/134217728), (1195735/268435456)), (352877/274877906944), by norm_num⟩
  | 6 => ⟨((-58673/67108864), (-1362389/1073741824)), (751027/1099511627776), by norm_num⟩
  | 7 => ⟨((673/33554432), (57167/268435456)), (11777623/35184372088832), by norm_num⟩
  | 8 => ⟨((94539/8589934592), (-213429/8589934592)), (11783341/70368744177664), by norm_num⟩
  | 9 => ⟨((-43937/17179869184), (32867/17179869184)), (110021323/1125899906842624), by norm_num⟩
  | 10 => ⟨((11931/34359738368), (-3125/68719476736)), (1297394855/18014398509481984), by norm_num⟩
  | 11 => ⟨((-4603/137438953472), (-927/68719476736)), (4574589595/72057594037927936), by norm_num⟩
  | 12 => ⟨((605/274877906944), (379/137438953472)), (4390040219/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile022Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-460929133/1073741824), (-6092906981/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((75161065473293/140737488355328), (838220839066583/2251799813685248)), (4541089/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1312852751/4294967296), (-1830170527/8589934592)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((3005723559/34359738368), (1047525449/17179869184)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-573456931/34359738368), (-3197689833/274877906944)), (27/274877906944), by norm_num⟩
  | 4 => ⟨((656453287/274877906944), (1830245559/1099511627776)), (9/549755813888), by norm_num⟩
  | 5 => ⟨((-601169357/2199023255552), (-3352218863/17592186044416)), (9/4398046511104), by norm_num⟩
  | 6 => ⟨((3670274823/140737488355328), (319782093/17592186044416)), (29/140737488355328), by norm_num⟩
  | 7 => ⟨((-4801683747/2251799813685248), (-3346871943/2251799813685248)), (5/281474976710656), by norm_num⟩
  | 8 => ⟨((687078861/4503599627370496), (239454021/2251799813685248)), (25/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1398257255/144115188075855872), (-1949227905/288230376151711744)), (7/72057594037927936), by norm_num⟩
  | 10 => ⟨((640250747/1152921504606846976), (892535775/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-2132113933/73786976294838206464), (-371531773/18446744073709551616)), (49/147573952589676412928), by norm_num⟩
  | 12 => ⟨((3254259385/2361183241434822606848), (1134142731/1180591620717411303424)), (5/295147905179352825856), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173537/10141204801825835211973625643008), (396465155511/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781308478438403/633825300114114700748351602688), (470469965789/316912650057057350374175801344)), (2885/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892598727803853/39614081257132168796771975168), (1058516010069/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892552003634709/2475880078570760549798248448), (1124623936593/2475880078570760549798248448)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774217856791397/154742504910672534362390528), (1124568447829/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388097743904261/2417851639229258349412352), (1054223964313/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630635559534251/302231454903657293676544), (230596753673/151115727451828646838272)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891825213294817/75557863725914323419136), (374692090761/18889465931478580854784)), (2299/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300563638683605/4722366482869645213696), (140497444563/590295810358705651712)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625605246609439/590295810358705651712), (772657366407/295147905179352825856)), (593/73786976294838206464), by norm_num⟩
  | 8 => ⟨((914334674316765/36893488147419103232), (1931407690041/73786976294838206464)), (2965/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914249317770223/4611686018427387904), (1086254772241/4611686018427387904)), (6673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599744225234389/1152921504606846976), (1086052217791/576460752303423488)), (6675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199616052302855/144115188075855872), (1900135667493/144115188075855872)), (2921/72057594037927936), by norm_num⟩
  | 4 => ⟨((374795945229965/9007199254740992), (2849292158697/36028797018963968)), (8767/36028797018963968), by norm_num⟩
  | 3 => ⟨((749339596859985/4503599627370496), (222501283735/562949953421312)), (10965/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123378380901165/2251799813685248), (1778814466973/1125899906842624)), (343/70368744177664), by norm_num⟩
  | 1 => ⟨((561057756491311/562949953421312), (5330465725673/1125899906842624)), (16489/1125899906842624), by norm_num⟩
  | 0 => ⟨((1118322727694375/1125899906842624), (10637028801519/1125899906842624)), (33081/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118322727694375/1125899906842624), (10637028801519/1125899906842624)), (126194004539107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((555348023965535/562949953421312), (10565442799651/562949953421312)), (66343/1125899906842624), by norm_num⟩
  | 2 => ⟨((547650456789611/562949953421312), (41691079254541/1125899906842624)), (133385/1125899906842624), by norm_num⟩
  | 3 => ⟨((1063989736492195/1125899906842624), (81116051112677/1125899906842624)), (269399/1125899906842624), by norm_num⟩
  | 4 => ⟨((124954973658455/140737488355328), (153311400638971/1125899906842624)), (273995/562949953421312), by norm_num⟩
  | 5 => ⟨((866662584116867/1125899906842624), (136118828410641/562949953421312)), (1122313/1125899906842624), by norm_num⟩
  | 6 => ⟨((75161065473293/140737488355328), (838220839066583/2251799813685248)), (4541089/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-460929133/1073741824), (-6092906981/1073741824)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1088022279/2199023255552), (-372979373/137438953472)), (547/1099511627776), by norm_num⟩
  | 1 => ⟨((4419579093/2199023255552), (-20088317/68719476736)), (2907/2199023255552), by norm_num⟩
  | 2 => ⟨((300898105/1099511627776), (1413685067/2199023255552)), (16031/8796093022208), by norm_num⟩
  | 3 => ⟨((-1107136269/8796093022208), (2755332151/35184372088832)), (1881/1099511627776), by norm_num⟩
  | 4 => ⟨((-3166391747/281474976710656), (-1335242369/70368744177664)), (344115/281474976710656), by norm_num⟩
  | 5 => ⟨((2988777429/1125899906842624), (-1521257213/2251799813685248)), (1592109/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1301533103/18014398509481984), (6375541697/18014398509481984)), (774877/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2884420347/72057594037927936), (-1976454891/72057594037927936)), (10439109/72057594037927936), by norm_num⟩
  | 8 => ⟨((711444427/144115188075855872), (-473315441/144115188075855872)), (7761975/144115188075855872), by norm_num⟩
  | 9 => ⟨((128877493/1152921504606846976), (3109491913/4611686018427387904)), (41466777/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-5485667943/73786976294838206464), (-767282085/36893488147419103232)), (404636373/73786976294838206464), by norm_num⟩
  | 11 => ⟨((1616502035/295147905179352825856), (-3806213189/590295810358705651712)), (231386117/147573952589676412928), by norm_num⟩
  | 12 => ⟨((446156953/1180591620717411303424), (3838687915/4722366482869645213696)), (2126247495/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5447759813/137438953472), (798267155/137438953472)), (365/34359738368), by norm_num⟩
  | 1 => ⟨((-80798799/34359738368), (3187866667/137438953472)), (1083/34359738368), by norm_num⟩
  | 2 => ⟨((-80909857/17179869184), (-250017211/1099511627776)), (54793/1099511627776), by norm_num⟩
  | 3 => ⟨((-454720573/17592186044416), (-5368568009/17592186044416)), (119999/2199023255552), by norm_num⟩
  | 4 => ⟨((-3629471067/140737488355328), (-418765141/70368744177664)), (3246231/70368744177664), by norm_num⟩
  | 5 => ⟨((158862861/1125899906842624), (-5384019711/1125899906842624)), (8999379/281474976710656), by norm_num⟩
  | 6 => ⟨((3452777401/36028797018963968), (-1532109425/36028797018963968)), (340392713/18014398509481984), by norm_num⟩
  | 7 => ⟨((418728151/144115188075855872), (-3509852787/144115188075855872)), (2833127213/288230376151711744), by norm_num⟩
  | 8 => ⟨((848803931/576460752303423488), (-78963733/576460752303423488)), (1344107495/288230376151711744), by norm_num⟩
  | 9 => ⟨((42905877/2305843009213693952), (-31690315/576460752303423488)), (615292581/288230376151711744), by norm_num⟩
  | 10 => ⟨((15934101/2305843009213693952), (-3349571/4611686018427387904)), (2404814531/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1560503/9223372036854775808), (254625/2305843009213693952)), (5712602029/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-220589/9223372036854775808), (-456663/9223372036854775808)), (4333299049/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42560623/1073741824), (3118231/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1262481/536870912), (3113151/134217728)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-2528433/536870912), (-122079/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-13877/536870912), (-327671/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-27691/1073741824), (-3195/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((19/134217728), (-5135/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((103/1073741824), (-23/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((3/1073741824), (-13/536870912)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/536870912), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨22,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨22,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(71831655/1073741824)) (L:=(22023738701/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile022
