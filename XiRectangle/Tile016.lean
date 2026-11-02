/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile016Gamma
public import XiRectangle.Tile016Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile016
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4926418431/274877906944), (10226888709/549755813888)), (635/549755813888), by norm_num⟩
  | 1 => ⟨((-13301071655/549755813888), (162109065/549755813888)), (1353/549755813888), by norm_num⟩
  | 2 => ⟨((-521872353/68719476736), (-15907003975/2199023255552)), (6137/2199023255552), by norm_num⟩
  | 3 => ⟨((-1913815829/8796093022208), (-12021923983/4398046511104)), (19191/8796093022208), by norm_num⟩
  | 4 => ⟨((8679239897/35184372088832), (-7139233161/17592186044416)), (5749/4398046511104), by norm_num⟩
  | 5 => ⟨((13684063651/281474976710656), (-2594762477/70368744177664)), (179515/281474976710656), by norm_num⟩
  | 6 => ⟨((2050236969/281474976710656), (-2374562057/562949953421312)), (148389/562949953421312), by norm_num⟩
  | 7 => ⟨((21950268603/18014398509481984), (-2123759869/9007199254740992)), (1709637/18014398509481984), by norm_num⟩
  | 8 => ⟨((17931756315/144115188075855872), (2581905/70368744177664)), (136893/4503599627370496), by norm_num⟩
  | 9 => ⟨((19867247541/2305843009213693952), (8340301329/2305843009213693952)), (20324111/2305843009213693952), by norm_num⟩
  | 10 => ⟨((11153086819/9223372036854775808), (5675875123/18446744073709551616)), (43529099/18446744073709551616), by norm_num⟩
  | 11 => ⟨((14476109449/147573952589676412928), (16886188315/147573952589676412928)), (89535611/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-918487455/590295810358705651712), (8688981957/1180591620717411303424)), (399112937/2361183241434822606848), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile016Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2993036083/1073741824), (8303330235/1073741824)), (111/536870912), by norm_num⟩
  | 1 => ⟨((1327065413/536870912), (151400123/536870912)), (889/2147483648), by norm_num⟩
  | 2 => ⟨((-383298263/1073741824), (-296912125/1073741824)), (9575/17179869184), by norm_num⟩
  | 3 => ⟨((18121825/536870912), (49545291/536870912)), (74807/137438953472), by norm_num⟩
  | 4 => ⟨((4953709/1073741824), (-37011021/2147483648)), (465331/1099511627776), by norm_num⟩
  | 5 => ⟨((-1185653/536870912), (970073/536870912)), (1246923/4398046511104), by norm_num⟩
  | 6 => ⟨((1754275/4294967296), (-14367/536870912)), (12397741/70368744177664), by norm_num⟩
  | 7 => ⟨((-195541/4294967296), (-30003/1073741824)), (31535795/281474976710656), by norm_num⟩
  | 8 => ⟨((21971/8589934592), (101251/17179869184)), (182031765/2251799813685248), by norm_num⟩
  | 9 => ⟨((4801/34359738368), (-24227/34359738368)), (1213508775/18014398509481984), by norm_num⟩
  | 10 => ⟨((-3695/68719476736), (14501/274877906944)), (8990319925/144115188075855872), by norm_num⟩
  | 11 => ⟨((4019/549755813888), (-741/549755813888)), (8747312437/144115188075855872), by norm_num⟩
  | 12 => ⟨((-175/274877906944), (-601/2199023255552)), (8674043189/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile016Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4653/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4653/640))
  have he : value ((3/4), (4653/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-9833154845/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1843716533/4294967296), (-8936263573/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-9833154845/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-767592444588121/2251799813685248), (624421245715757/1125899906842624)), (7827/8796093022208), by norm_num⟩
  | 1 => ⟨((6703842251/34359738368), (-10906885701/34359738368)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((-7674088575/137438953472), (1560679753/17179869184)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((11713011385/1099511627776), (-1191037837/68719476736)), (41/1099511627776), by norm_num⟩
  | 4 => ⟨((-6704117093/4398046511104), (5453666429/2199023255552)), (25/4398046511104), by norm_num⟩
  | 5 => ⟨((12279045111/70368744177664), (-4994379959/17592186044416)), (3/4398046511104), by norm_num⟩
  | 6 => ⟨((-1171349159/70368744177664), (7622954667/281474976710656)), (39/562949953421312), by norm_num⟩
  | 7 => ⟨((12259459557/9007199254740992), (-4986413729/2251799813685248)), (27/4503599627370496), by norm_num⟩
  | 8 => ⟨((-3508442435/36028797018963968), (5708096819/36028797018963968)), (33/72057594037927936), by norm_num⟩
  | 9 => ⟨((3569972363/576460752303423488), (-11616407147/1152921504606846976)), (9/288230376151711744), by norm_num⟩
  | 10 => ⟨((-6538646489/18446744073709551616), (5319059371/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 11 => ⟨((5443624763/295147905179352825856), (-1107070223/36893488147419103232)), (59/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-4154319969/4722366482869645213696), (13517827947/9444732965739290427392)), (47/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086617/5070602400912917605986812821504), (1382014498297/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((890651611116187/316912650057057350374175801344), (3279967001865/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((473148123167405/9903520314283042199192993792), (3689807626311/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892544989540757/2475880078570760549798248448), (3920247323753/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221776300601191/19342813113834066795298816), (3920052285447/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552383524189939/9671406556917033397649408), (3674841693241/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78829008371575/37778931862957161709568), (3215279049089/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945906495254319/37778931862957161709568), (5224439289129/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162569213597015/590295810358705651712), (979497179319/1180591620717411303424)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812795176842517/295147905179352825856), (1346670084449/147573952589676412928)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((914324437005677/36893488147419103232), (3366259223333/36893488147419103232)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914236523494377/4611686018427387904), (7572938063229/9223372036854775808)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599715444616425/1152921504606846976), (7571504743417/1152921504606846976)), (1679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599793639909931/72057594037927936), (3311725823363/72057594037927936)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((1499133447396473/36028797018963968), (9931941170239/36028797018963968)), (1105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498603730124009/9007199254740992), (12409248794439/9007199254740992)), (173/562949953421312), by norm_num⟩
  | 2 => ⟨((561642057857143/1125899906842624), (6200352019959/1125899906842624)), (2777/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121927175941033/1125899906842624), (9289797725263/562949953421312)), (1047/281474976710656), by norm_num⟩
  | 0 => ⟨((139719835760113/140737488355328), (37072757398167/1125899906842624)), (4233/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139719835760113/140737488355328), (37072757398167/1125899906842624)), (16147615672874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((554227815182975/562949953421312), (73609379212007/1125899906842624)), (2171/140737488355328), by norm_num⟩
  | 2 => ⟨((1086469175765713/1125899906842624), (72468902732307/562949953421312)), (18235/562949953421312), by norm_num⟩
  | 3 => ⟨((514880716922463/562949953421312), (279723725143609/1125899906842624)), (2493/35184372088832), by norm_num⟩
  | 4 => ⟨((872336201697035/1125899906842624), (127919321483961/281474976710656)), (185569/1125899906842624), by norm_num⟩
  | 5 => ⟨((55417537653095/140737488355328), (49555317639163/70368744177664)), (456223/1125899906842624), by norm_num⟩
  | 6 => ⟨((-767592444588121/2251799813685248), (624421245715757/1125899906842624)), (7827/8796093022208), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-1843716533/4294967296), (-8936263573/2147483648)), (1/2147483648), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-144573521/34359738368), (-17900990769/1099511627776)), (587/549755813888), by norm_num⟩
  | 1 => ⟨((11536277427/1099511627776), (-9236202555/2199023255552)), (1561/549755813888), by norm_num⟩
  | 2 => ⟨((5648645027/4398046511104), (14623026637/4398046511104)), (17435/4398046511104), by norm_num⟩
  | 3 => ⟨((-25758848997/35184372088832), (1844527029/17592186044416)), (33377/8796093022208), by norm_num⟩
  | 4 => ⟨((5707737643/140737488355328), (-4413002721/35184372088832)), (195467/70368744177664), by norm_num⟩
  | 5 => ⟨((8828744707/562949953421312), (9770146611/562949953421312)), (464799/281474976710656), by norm_num⟩
  | 6 => ⟨((-17079987149/4503599627370496), (2001572605/2251799813685248)), (3731047/4503599627370496), by norm_num⟩
  | 7 => ⟨((3073762579/18014398509481984), (-20770359241/36028797018963968)), (1623179/4503599627370496), by norm_num⟩
  | 8 => ⟨((1093092729/18014398509481984), (2332955073/36028797018963968)), (9998095/72057594037927936), by norm_num⟩
  | 9 => ⟨((-14171093145/1152921504606846976), (1631805985/576460752303423488)), (27687645/576460752303423488), by norm_num⟩
  | 10 => ⟨((578319509/1152921504606846976), (-15258072573/9223372036854775808)), (69908363/4611686018427387904), by norm_num⟩
  | 11 => ⟨((5858253511/36893488147419103232), (12256950065/73786976294838206464)), (326899407/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-8489559667/295147905179352825856), (1127726915/147573952589676412928)), (22772901/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4728926531/34359738368), (882671289/68719476736)), (2127/137438953472), by norm_num⟩
  | 1 => ⟨((-44258129/17179869184), (3533160359/68719476736)), (24373/549755813888), by norm_num⟩
  | 2 => ⟨((-22747371061/4398046511104), (237497709/1099511627776)), (150977/2199023255552), by norm_num⟩
  | 3 => ⟨((-2792802277/35184372088832), (20215235483/70368744177664)), (2610413/35184372088832), by norm_num⟩
  | 4 => ⟨((-11213802047/140737488355328), (-308241061/140737488355328)), (17503057/281474976710656), by norm_num⟩
  | 5 => ⟨((-204619155/281474976710656), (-15993634055/9007199254740992)), (387936259/9007199254740992), by norm_num⟩
  | 6 => ⟨((-17529768427/36028797018963968), (-1702475203/36028797018963968)), (466363657/18014398509481984), by norm_num⟩
  | 7 => ⟨((-467611975/144115188075855872), (-7846599573/288230376151711744)), (512526711/36028797018963968), by norm_num⟩
  | 8 => ⟨((-3767028353/2305843009213693952), (-6345977/18014398509481984)), (17768809801/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-29784221/4611686018427387904), (-723368841/4611686018427387904)), (5263265549/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-944109/288230376151711744), (-19947555/9223372036854775808)), (29760460369/9223372036854775808), by norm_num⟩
  | 11 => ⟨((3112159/9223372036854775808), (-4937421/9223372036854775808)), (25021669827/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-700287/9223372036854775808), (314959/9223372036854775808)), (5840500493/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73889477/536870912), (13791739/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2766133/1073741824), (55205631/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-5553557/1073741824), (231931/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-42615/536870912), (77115/268435456)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-85555/1073741824), (-147/67108864)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-781/1073741824), (-1907/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-261/536870912), (-51/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-3/1073741824), (-29/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-1/536870912), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨16,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨16,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(102716681/1073741824)) (L:=(37995808831/274877906944)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile016
