/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile036Gamma
public import XiRectangle.Tile036Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile036
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((301869295/2199023255552), (804032731/2199023255552)), (1083/2199023255552), by norm_num⟩
  | 1 => ⟨((-71700031/549755813888), (492749641/1099511627776)), (2259/2199023255552), by norm_num⟩
  | 2 => ⟨((-949078763/4398046511104), (182689809/1099511627776)), (615/549755813888), by norm_num⟩
  | 3 => ⟨((-908038293/8796093022208), (70865109/17592186044416)), (1829/2199023255552), by norm_num⟩
  | 4 => ⟨((-853769443/35184372088832), (-133654135/8796093022208)), (16579/35184372088832), by norm_num⟩
  | 5 => ⟨((-92121271/35184372088832), (-394111795/70368744177664)), (30431/140737488355328), by norm_num⟩
  | 6 => ⟨((128522449/1125899906842624), (-607703745/562949953421312)), (47087/562949953421312), by norm_num⟩
  | 7 => ⟨((825430669/9007199254740992), (-295861331/2251799813685248)), (126363/4503599627370496), by norm_num⟩
  | 8 => ⟨((646170943/36028797018963968), (-711268551/72057594037927936)), (37583/4503599627370496), by norm_num⟩
  | 9 => ⟨((669200427/288230376151711744), (-30342509/144115188075855872)), (1297929/576460752303423488), by norm_num⟩
  | 10 => ⟨((268231055/1152921504606846976), (156110681/2305843009213693952)), (2654637/4611686018427387904), by norm_num⟩
  | 11 => ⟨((347699511/18446744073709551616), (505922059/36893488147419103232)), (5872847/36893488147419103232), by norm_num⟩
  | 12 => ⟨((711615725/590295810358705651712), (502164421/295147905179352825856)), (1191059/18446744073709551616), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile036Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((575605957/134217728), (713565081/134217728)), (85/16777216), by norm_num⟩
  | 1 => ⟨((-65908191/16777216), (707096855/134217728)), (1579/134217728), by norm_num⟩
  | 2 => ⟨((684477033/268435456), (-201911747/134217728)), (2049/134217728), by norm_num⟩
  | 3 => ⟨((-111964605/134217728), (25005583/134217728)), (15169/1073741824), by norm_num⟩
  | 4 => ⟨((3254587/16777216), (3040587/134217728)), (21921/2147483648), by norm_num⟩
  | 5 => ⟨((-8990017/268435456), (-2284679/134217728)), (103367/17179869184), by norm_num⟩
  | 6 => ⟨((1132477/268435456), (2519063/536870912)), (418359/137438953472), by norm_num⟩
  | 7 => ⟨((-351383/1073741824), (-477351/536870912)), (1488307/1099511627776), by norm_num⟩
  | 8 => ⟨((-2523/536870912), (138715/1073741824)), (2442955/4398046511104), by norm_num⟩
  | 9 => ⟨((29243/4294967296), (-126471/8589934592)), (16231597/70368744177664), by norm_num⟩
  | 10 => ⟨((-24087/17179869184), (21747/17179869184)), (31896243/281474976710656), by norm_num⟩
  | 11 => ⟨((1673/8589934592), (-4521/68719476736)), (169285013/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1439/68719476736), (-127/68719476736)), (1153084583/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile036Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-4201177/8388608), (-1032409239/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((220020634367101/2251799813685248), (-1346813688051545/2251799813685248)), (25392083/1125899906842624), by norm_num⟩
  | 1 => ⟨((-240196415/4294967296), (1470315819/4294967296)), (29/2147483648), by norm_num⟩
  | 2 => ⟨((274960015/17179869184), (-420778615/4294967296)), (69/17179869184), by norm_num⟩
  | 3 => ⟨((-209836631/68719476736), (1284474283/68719476736)), (55/68719476736), by norm_num⟩
  | 4 => ⟨((240206263/549755813888), (-367594025/137438953472)), (65/549755813888), by norm_num⟩
  | 5 => ⟨((-109988515/2199023255552), (1346546773/4398046511104)), (31/2199023255552), by norm_num⟩
  | 6 => ⟨((167876187/35184372088832), (-256905389/8796093022208)), (49/35184372088832), by norm_num⟩
  | 7 => ⟨((-109813079/281474976710656), (1344398979/562949953421312)), (33/281474976710656), by norm_num⟩
  | 8 => ⟨((251412627/9007199254740992), (-769486845/4503599627370496)), (39/4503599627370496), by norm_num⟩
  | 9 => ⟨((-63955455/36028797018963968), (1565963713/144115188075855872)), (41/72057594037927936), by norm_num⟩
  | 10 => ⟨((117138753/1152921504606846976), (-717042185/1152921504606846976)), (39/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-97521623/18446744073709551616), (596959723/18446744073709551616)), (67/36893488147419103232), by norm_num⟩
  | 12 => ⟨((297695777/1180591620717411303424), (-1822287029/1180591620717411303424)), (105/1180591620717411303424), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-1835201275805/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890597919533293/316912650057057350374175801344), (-2177506389501/633825300114114700748351602688)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1892471888506181/39614081257132168796771975168), (-153098770991/2475880078570760549798248448)), (6499/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946208545566119/1237940039285380274899124224), (-650636402797/618970019642690137449562112)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774082780344069/154742504910672534362390528), (-1301197703077/77371252455336267181195264)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776132083642321/4835703278458516698824704), (-2439586080549/9671406556917033397649408)), (25907/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157644998455817/75557863725914323419136), (-2134478185413/604462909807314587353088)), (22673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891644298306113/75557863725914323419136), (-1734113844039/37778931862957161709568)), (9213/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300427666885405/4722366482869645213696), (-1300454387899/2361183241434822606848)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625417821484529/590295810358705651712), (-446977967955/73786976294838206464)), (38027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828434371596451/73786976294838206464), (-4469140789437/73786976294838206464)), (47553/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828233330243017/9223372036854775808), (-5026904661721/9223372036854775808)), (53523/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599477725316389/1152921504606846976), (-5025805875319/1152921504606846976)), (53555/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599690760836489/72057594037927936), (-274771467901/9007199254740992)), (23449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498829300438469/36028797018963968), (-6592040622761/36028797018963968)), (17605/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498231399380327/9007199254740992), (-8235717300537/9007199254740992)), (88153/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122923554359555/2251799813685248), (-4114605631351/1125899906842624)), (88347/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121415722094407/1125899906842624), (-6163765737447/562949953421312)), (133003/1125899906842624), by norm_num⟩
  | 0 => ⟨((558426559142525/562949953421312), (-24589799716075/1125899906842624)), (66985/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558426559142525/562949953421312), (-24589799716075/1125899906842624)), (255527497411632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1107341977733401/1125899906842624), (-48784433365695/1125899906842624)), (271639/562949953421312), by norm_num⟩
  | 2 => ⟨((1086976139951641/1125899906842624), (-749692681903/8796093022208)), (1115727/1125899906842624), by norm_num⟩
  | 3 => ⟨((130152408842215/140737488355328), (-185286366450991/1125899906842624)), (1172249/562949953421312), by norm_num⟩
  | 4 => ⟨((932415506727383/1125899906842624), (-342701396778265/1125899906842624)), (2553993/562949953421312), by norm_num⟩
  | 5 => ⟨((667869697174613/1125899906842624), (-567617235939345/1125899906842624)), (11569909/1125899906842624), by norm_num⟩
  | 6 => ⟨((220020634367101/2251799813685248), (-1346813688051545/2251799813685248)), (25392083/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1032409239/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((510391623/2199023255552), (-203977197/4398046511104)), (779/2199023255552), by norm_num⟩
  | 1 => ⟨((269279303/2199023255552), (326203351/2199023255552)), (4095/4398046511104), by norm_num⟩
  | 2 => ⟨((-262238931/8796093022208), (1196190659/17592186044416)), (5551/4398046511104), by norm_num⟩
  | 3 => ⟨((-315337587/17592186044416), (13022011/35184372088832)), (40897/35184372088832), by norm_num⟩
  | 4 => ⟨((-166178495/140737488355328), (-386924699/140737488355328)), (114685/140737488355328), by norm_num⟩
  | 5 => ⟨((305820813/1125899906842624), (-262156079/1125899906842624)), (260161/562949953421312), by norm_num⟩
  | 6 => ⟨((825695443/36028797018963968), (740507673/36028797018963968)), (7940935/36028797018963968), by norm_num⟩
  | 7 => ⟨((-526903459/288230376151711744), (162032547/144115188075855872)), (6546653/72057594037927936), by norm_num⟩
  | 8 => ⟨((2552549/288230376151711744), (-2026516795/9223372036854775808)), (304752665/9223372036854775808), by norm_num⟩
  | 9 => ⟨((110840701/4611686018427387904), (277100957/36893488147419103232)), (397828401/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-324064131/295147905179352825856), (591224725/295147905179352825856)), (1897793247/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-296356863/2361183241434822606848), (-326617813/2361183241434822606848)), (2134814787/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((35961557/2361183241434822606848), (-25465705/4722366482869645213696)), (619603423/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((341385567/274877906944), (71127991/68719476736)), (331/68719476736), by norm_num⟩
  | 1 => ⟨((-255894513/274877906944), (1480028561/549755813888)), (579/34359738368), by norm_num⟩
  | 2 => ⟨((-676117167/549755813888), (-74749861/274877906944)), (33047/1099511627776), by norm_num⟩
  | 3 => ⟨((134059095/4398046511104), (-531998711/2199023255552)), (159299/4398046511104), by norm_num⟩
  | 4 => ⟨((1447956671/70368744177664), (-13929583/35184372088832)), (1163109/35184372088832), by norm_num⟩
  | 5 => ⟨((230578195/562949953421312), (-426033451/2251799813685248)), (1710167/70368744177664), by norm_num⟩
  | 6 => ⟨((1648121293/9007199254740992), (132268401/4503599627370496)), (33733721/2251799813685248), by norm_num⟩
  | 7 => ⟨((155321213/144115188075855872), (1646284779/144115188075855872)), (1148517641/144115188075855872), by norm_num⟩
  | 8 => ⟨((101745997/288230376151711744), (16858603/72057594037927936)), (1078787399/288230376151711744), by norm_num⟩
  | 9 => ⟨((-2831803/576460752303423488), (81486787/1152921504606846976)), (914398919/576460752303423488), by norm_num⟩
  | 10 => ⟨((-3461399/2305843009213693952), (494519/576460752303423488)), (360457389/576460752303423488), by norm_num⟩
  | 11 => ⟨((-103397/2305843009213693952), (121207/576460752303423488)), (280506087/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-280449/18446744073709551616), (-9001/4611686018427387904)), (1951551693/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1333537/1073741824), (1111375/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-249897/268435456), (2890681/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1320541/1073741824), (-36499/134217728)), (1/10000000), by norm_num⟩
  | 3 => ⟨((32729/1073741824), (-259765/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((11047/536870912), (-425/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((55/134217728), (-203/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((49/268435456), (1/33554432)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (3/268435456)), (1/10000000), by norm_num⟩
  | 8 => ⟨(0, 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨36,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨36,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(6103549/1073741824)) (L:=(1777598913/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile036
