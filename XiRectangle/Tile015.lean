/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile015Gamma
public import XiRectangle.Tile015Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile015
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35350126865/2199023255552), (67362776513/2199023255552)), (889/2199023255552), by norm_num⟩
  | 1 => ⟨((-8327400071/274877906944), (9517552643/1099511627776)), (2055/2199023255552), by norm_num⟩
  | 2 => ⟨((-50398747305/4398046511104), (-14149721389/2199023255552)), (2369/2199023255552), by norm_num⟩
  | 3 => ⟨((-8957630997/8796093022208), (-105986599/34359738368)), (14847/17592186044416), by norm_num⟩
  | 4 => ⟨((5111182517/35184372088832), (-69934388687/140737488355328)), (71025/140737488355328), by norm_num⟩
  | 5 => ⟨((36436564093/1125899906842624), (-61430757075/1125899906842624)), (34547/140737488355328), by norm_num⟩
  | 6 => ⟨((52824680145/9007199254740992), (-73068580369/9007199254740992)), (227821/2251799813685248), by norm_num⟩
  | 7 => ⟨((5790501419/4503599627370496), (-24708846581/36028797018963968)), (1310003/36028797018963968), by norm_num⟩
  | 8 => ⟨((4559622015/36028797018963968), (773697851/576460752303423488)), (1678903/144115188075855872), by norm_num⟩
  | 9 => ⟨((81212520911/9223372036854775808), (-13701776809/4611686018427387904)), (15664301/4611686018427387904), by norm_num⟩
  | 10 => ⟨((66137266261/36893488147419103232), (-8982512357/36893488147419103232)), (34285419/36893488147419103232), by norm_num⟩
  | 11 => ⟨((2292921229/18446744073709551616), (9523450661/73786976294838206464)), (38099831/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-88874921791/18889465931478580854784), (3718402715/2361183241434822606848)), (1700208245/18889465931478580854784), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile015Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22347666639/8589934592), (14387883787/2147483648)), (403/4294967296), by norm_num⟩
  | 1 => ⟨((2377251819/1073741824), (584885079/1073741824)), (2469/17179869184), by norm_num⟩
  | 2 => ⟨((-519012413/2147483648), (-1301174589/4294967296)), (24471/137438953472), by norm_num⟩
  | 3 => ⟨((32888101/4294967296), (349206165/4294967296)), (193459/1099511627776), by norm_num⟩
  | 4 => ⟨((64371649/8589934592), (-106620915/8589934592)), (650443/4398046511104), by norm_num⟩
  | 5 => ⟨((-2277351/1073741824), (7302515/8589934592)), (4019799/35184372088832), by norm_num⟩
  | 6 => ⟨((1344301/4294967296), (1425805/17179869184)), (24851123/281474976710656), by norm_num⟩
  | 7 => ⟨((-899683/34359738368), (-139979/4294967296)), (164009365/2251799813685248), by norm_num⟩
  | 8 => ⟨((16481/68719476736), (5343/1073741824)), (1174449319/18014398509481984), by norm_num⟩
  | 9 => ⟨((82445/274877906944), (-63817/137438953472)), (8911676725/144115188075855872), by norm_num⟩
  | 10 => ⟨((-29333/549755813888), (11789/549755813888)), (69865253285/1152921504606846976), by norm_num⟩
  | 11 => ⟨((6045/1099511627776), (349/274877906944)), (69378189733/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-3117/8796093022208), (-3403/8796093022208)), (69230209445/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile015Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-3687433067/8589934592), (-33578687365/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-527469202240975/1125899906842624), (1017796979580107/2251799813685248)), (507941/2251799813685248), by norm_num⟩
  | 1 => ⟨((36853623027/137438953472), (-35556110237/137438953472)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((-42187443681/549755813888), (40702142013/549755813888)), (25/549755813888), by norm_num⟩
  | 3 => ⟨((64390970119/4398046511104), (-62123944507/4398046511104)), (41/4398046511104), by norm_num⟩
  | 4 => ⟨((-36855133937/17592186044416), (2222347997/1099511627776)), (25/17592186044416), by norm_num⟩
  | 5 => ⟨((8437834653/35184372088832), (-65126097125/281474976710656)), (3/17592186044416), by norm_num⟩
  | 6 => ⟨((-12878721999/562949953421312), (776581143/35184372088832)), (39/2251799813685248), by norm_num⟩
  | 7 => ⟨((67395007835/36028797018963968), (-65022218473/36028797018963968)), (27/18014398509481984), by norm_num⟩
  | 8 => ⟨((-38574539813/288230376151711744), (37216438365/288230376151711744)), (33/288230376151711744), by norm_num⟩
  | 9 => ⟨((19625523803/2305843009213693952), (-37869128215/4611686018427387904)), (9/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-35945477797/73786976294838206464), (34679938255/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | 11 => ⟨((7481429581/295147905179352825856), (-57744235287/2361183241434822606848)), (61/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-11418954707/9444732965739290427392), (22033850623/18889465931478580854784)), (3/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (773136361085/2535301200456458802993406410752)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781301779831671/633825300114114700748351602688), (917451211773/158456325028528675187087900672)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946295390816407/19807040628566084398385987584), (32252760983/309485009821345068724781056)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892543064750165/2475880078570760549798248448), (548272650889/309485009821345068724781056)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774208359855697/154742504910672534362390528), (4385962492365/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((97023842461839/604462909807314587353088), (4111607313661/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78828888569233/37778931862957161709568), (3597423720795/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891809636369339/75557863725914323419136), (5845376942981/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300550983844095/4722366482869645213696), (4383650348617/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625586266823313/590295810358705651712), (3013448638359/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828643255449019/73786976294838206464), (7532687582623/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828466025096419/9223372036854775808), (8472987501013/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599707546792503/1152921504606846976), (2117844330981/288230376151711744)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149947423032061/18014398509481984), (926330010153/18014398509481984)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499119635258779/36028797018963968), (11112320904717/36028797018963968)), (277/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498583022143819/9007199254740992), (1735501516231/1125899906842624)), (347/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123258248702455/2251799813685248), (1734298492015/281474976710656)), (87/281474976710656), by norm_num⟩
  | 1 => ⟨((560937748038225/562949953421312), (10393689611389/562949953421312)), (525/562949953421312), by norm_num⟩
  | 0 => ⟨((558801959580647/562949953421312), (5184637043073/140737488355328)), (2125/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558801959580647/562949953421312), (5184637043073/140737488355328)), (8106235984420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107841081629873/1125899906842624), (82342959881987/1125899906842624)), (547/140737488355328), by norm_num⟩
  | 2 => ⟨((1084049738069055/1125899906842624), (40511111683135/281474976710656)), (9253/1125899906842624), by norm_num⟩
  | 3 => ⟨((15944265795025/17592186044416), (78010593556479/281474976710656)), (10241/562949953421312), by norm_num⟩
  | 4 => ⟨((104795404174889/140737488355328), (282812297539787/562949953421312)), (48481/1125899906842624), by norm_num⟩
  | 5 => ⟨((42512851967267/140737488355328), (842346396050031/1125899906842624)), (7557/70368744177664), by norm_num⟩
  | 6 => ⟨((-527469202240975/1125899906842624), (1017796979580107/2251799813685248)), (507941/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-33578687365/8589934592)), (1/8589934592), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-27772827627/4398046511104), (-11884141707/549755813888)), (421/1099511627776), by norm_num⟩
  | 1 => ⟨((30554582239/2199023255552), (-11820819925/2199023255552)), (2395/2199023255552), by norm_num⟩
  | 2 => ⟨((23899018429/17592186044416), (78331012685/17592186044416)), (6847/4398046511104), by norm_num⟩
  | 3 => ⟨((-270712981/274877906944), (-33571249/4398046511104)), (105743/70368744177664), by norm_num⟩
  | 4 => ⟨((25819052189/281474976710656), (-11389543339/70368744177664)), (310223/281474976710656), by norm_num⟩
  | 5 => ⟨((4774161083/281474976710656), (2113425857/70368744177664)), (23033/35184372088832), by norm_num⟩
  | 6 => ⟨((-53281036559/9007199254740992), (-414771895/4503599627370496)), (369105/1125899906842624), by norm_num⟩
  | 7 => ⟨((36305082133/72057594037927936), (-57828169869/72057594037927936)), (10257161/72057594037927936), by norm_num⟩
  | 8 => ⟨((18606394919/288230376151711744), (75116599757/576460752303423488)), (7886825/144115188075855872), by norm_num⟩
  | 9 => ⟨((-49309278903/2305843009213693952), (-8329095623/4611686018427387904)), (87380661/4611686018427387904), by norm_num⟩
  | 10 => ⟨((32826269383/18446744073709551616), (-45861929195/18446744073709551616)), (110784475/18446744073709551616), by norm_num⟩
  | 11 => ⟨((6396914141/36893488147419103232), (28473427525/73786976294838206464)), (65853971/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-4194635631/73786976294838206464), (-6223228179/1180591620717411303424)), (622619587/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88654090165/549755813888), (1914645807/137438953472)), (425/68719476736), by norm_num⟩
  | 1 => ⟨((-5143447267/2199023255552), (61327829441/1099511627776)), (9351/549755813888), by norm_num⟩
  | 2 => ⟨((-82654382707/17592186044416), (5679325419/17592186044416)), (457079/17592186044416), by norm_num⟩
  | 3 => ⟨((-2876280655/35184372088832), (30279009613/70368744177664)), (3965045/140737488355328), by norm_num⟩
  | 4 => ⟨((-46216586613/562949953421312), (-519780195/1125899906842624)), (13551349/562949953421312), by norm_num⟩
  | 5 => ⟨((-60309219625/72057594037927936), (-6971031033/18014398509481984)), (626557821/36028797018963968), by norm_num⟩
  | 6 => ⟨((-80780865617/144115188075855872), (-637173929/18014398509481984)), (204964179/18014398509481984), by norm_num⟩
  | 7 => ⟨((-20407979903/4611686018427387904), (-94142606661/4611686018427387904)), (33750304101/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-40939763093/18446744073709551616), (-5724228477/18446744073709551616)), (93407877169/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-263403495/18446744073709551616), (-2543131889/18446744073709551616)), (36732723161/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-101464835/18446744073709551616), (-63803309/36893488147419103232)), (130009127283/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-562773/18446744073709551616), (-17469185/36893488147419103232)), (123543558555/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-95965/9223372036854775808), (-13665/576460752303423488)), (121287459993/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21644065/134217728), (7479085/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2511449/1073741824), (29945229/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-5044823/1073741824), (173319/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-87777/1073741824), (462021/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-88151/1073741824), (-31/67108864)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-899/1073741824), (-13/33554432)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-301/536870912), (-19/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-5/1073741824), (-11/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨15,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨15,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(53468127/536870912)) (L:=(177968554643/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile015
