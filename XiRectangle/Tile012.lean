/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile012Gamma
public import XiRectangle.Tile012Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile012
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1560846413/68719476736), (5358387151/68719476736)), (613/274877906944), by norm_num⟩
  | 1 => ⟨((-10205300107/274877906944), (7630748755/137438953472)), (1339/274877906944), by norm_num⟩
  | 2 => ⟨((-26125907731/1099511627776), (3389188693/1099511627776)), (399/68719476736), by norm_num⟩
  | 3 => ⟨((-254425497/68719476736), (-1499317697/549755813888)), (2619/549755813888), by norm_num⟩
  | 4 => ⟨((-10218472643/35184372088832), (-13999175713/35184372088832)), (26277/8796093022208), by norm_num⟩
  | 5 => ⟨((-10763624859/140737488355328), (-69122969/1099511627776)), (214495/140737488355328), by norm_num⟩
  | 6 => ⟨((-1313764277/281474976710656), (-21092762979/1125899906842624)), (742393/1125899906842624), by norm_num⟩
  | 7 => ⟨((2074241167/2251799813685248), (-5327319669/4503599627370496)), (2241645/9007199254740992), by norm_num⟩
  | 8 => ⟨((-16335692511/144115188075855872), (-6982103769/144115188075855872)), (6030829/72057594037927936), by norm_num⟩
  | 9 => ⟨((-87336479/144115188075855872), (-6438160865/144115188075855872)), (7350639/288230376151711744), by norm_num⟩
  | 10 => ⟨((24108998679/4611686018427387904), (258184409/2305843009213693952)), (16487231/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-17828214971/36893488147419103232), (15292470335/36893488147419103232)), (34710433/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-3504011585/147573952589676412928), (-583322131/4611686018427387904)), (17956677/36893488147419103232), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile012Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3483618043/2147483648), (1151694265/268435456)), (337/2147483648), by norm_num⟩
  | 1 => ⟨((3130921655/2147483648), (447370029/536870912)), (165/536870912), by norm_num⟩
  | 2 => ⟨((-781747/134217728), (-66254689/268435456)), (7111/17179869184), by norm_num⟩
  | 3 => ⟨((-28523729/1073741824), (20355511/536870912)), (113773/274877906944), by norm_num⟩
  | 4 => ⟨((7961171/1073741824), (-3840255/2147483648)), (363443/1099511627776), by norm_num⟩
  | 5 => ⟨((-136865/134217728), (-573743/1073741824)), (1009355/4398046511104), by norm_num⟩
  | 6 => ⟨((127087/2147483648), (624573/4294967296)), (10431661/70368744177664), by norm_num⟩
  | 7 => ⟨((51001/8589934592), (-160371/8589934592)), (112642763/1125899906842624), by norm_num⟩
  | 8 => ⟨((-32665/17179869184), (21339/17179869184)), (171546005/2251799813685248), by norm_num⟩
  | 9 => ⟨((16817/68719476736), (1575/68719476736)), (4735546011/72057594037927936), by norm_num⟩
  | 10 => ⟨((-2495/137438953472), (-2353/137438953472)), (8914298165/144115188075855872), by norm_num⟩
  | 11 => ⟨((207/549755813888), (649/274877906944)), (8725554485/144115188075855872), by norm_num⟩
  | 12 => ⟨((227/2199023255552), (-421/2199023255552)), (8668144949/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile012Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (705/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (705/128))
  have he : value ((3/4), (705/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-27079586585/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-1465793671867153/2251799813685248), (7978728086003/1125899906842624)), (450665/1125899906842624), by norm_num⟩
  | 1 => ⟨((800103103/2147483648), (-278731949/68719476736)), (9/34359738368), by norm_num⟩
  | 2 => ⟨((-29308861881/274877906944), (39884099/34359738368)), (23/274877906944), by norm_num⟩
  | 3 => ⟨((11183576705/549755813888), (-243501441/1099511627776)), (5/274877906944), by norm_num⟩
  | 4 => ⟨((-12802174485/4398046511104), (278743377/8796093022208)), (25/8796093022208), by norm_num⟩
  | 5 => ⟨((23448050779/70368744177664), (-255268699/70368744177664)), (25/70368744177664), by norm_num⟩
  | 6 => ⟨((-2236807041/70368744177664), (194809139/562949953421312)), (21/562949953421312), by norm_num⟩
  | 7 => ⟨((5852662557/2251799813685248), (-254861535/9007199254740992)), (15/4503599627370496), by norm_num⟩
  | 8 => ⟨((-26798870963/144115188075855872), (9117113/4503599627370496)), (37/144115188075855872), by norm_num⟩
  | 9 => ⟨((3408607611/288230376151711744), (-296864191/2305843009213693952)), (5/288230376151711744), by norm_num⟩
  | 10 => ⟨((-24972384009/36893488147419103232), (271863449/36893488147419103232)), (39/36893488147419103232), by norm_num⟩
  | 11 => ⟨((324848117/9223372036854775808), (-113167351/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-7933084755/4722366482869645213696), (172728065/9444732965739290427392)), (27/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (4078094787429/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1781296481716541/633825300114114700748351602688), (1209829595649/158456325028528675187087900672)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892584496784207/39614081257132168796771975168), (2721991756409/19807040628566084398385987584)), (409/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946267997392171/1237940039285380274899124224), (2891987140941/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887100424260215/77371252455336267181195264), (5783683466819/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388093492155305/2417851639229258349412352), (2710946963337/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315313794091427/151115727451828646838272), (2371923744361/302231454903657293676544)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472949329069663/18889465931478580854784), (3854085346647/37778931862957161709568)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300540974904365/4722366482869645213696), (5780618435041/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625571255401325/590295810358705651712), (3973760392661/295147905179352825856)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828622617979629/73786976294838206464), (4966577017785/36893488147419103232)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828440233123905/9223372036854775808), (11173079513229/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799839268764359/576460752303423488), (11170924706855/1152921504606846976)), (211/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199550383399783/144115188075855872), (9772126255855/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((749534451372719/18014398509481984), (14653301911909/36028797018963968)), (1111/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498506961520325/9007199254740992), (4577006357851/2251799813685248)), (697/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123163240072165/2251799813685248), (2286878105795/281474976710656)), (175/281474976710656), by norm_num⟩
  | 1 => ⟨((560842840915699/562949953421312), (13704847287183/562949953421312)), (529/281474976710656), by norm_num⟩
  | 0 => ⟨((279258875615039/281474976710656), (54685975253699/1125899906842624)), (4299/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279258875615039/281474976710656), (54685975253699/1125899906842624)), (16399387839889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((552792370930073/562949953421312), (54255423127571/562949953421312)), (8949/1125899906842624), by norm_num⟩
  | 2 => ⟨((537589092210559/562949953421312), (213105863526439/1125899906842624)), (19301/1125899906842624), by norm_num⟩
  | 3 => ⟨((986405640888803/1125899906842624), (6359545541175/17592186044416)), (44171/1125899906842624), by norm_num⟩
  | 4 => ⟨((89632546245729/140737488355328), (178291986552047/281474976710656)), (109333/1125899906842624), by norm_num⟩
  | 5 => ⟨((4944537825163/1125899906842624), (908401303255985/1125899906842624)), (555543/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1465793671867153/2251799813685248), (7978728086003/1125899906842624)), (450665/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-27079586585/8589934592)), (1/4294967296), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-2107989359/137438953472), (-13907777755/274877906944)), (13/8589934592), by norm_num⟩
  | 1 => ⟨((17895995061/549755813888), (-4092726207/549755813888)), (565/137438953472), by norm_num⟩
  | 2 => ⟨((-370647117/549755813888), (22812351915/2199023255552)), (6531/1099511627776), by norm_num⟩
  | 3 => ⟨((-8961331357/4398046511104), (-763037365/549755813888)), (52001/8796093022208), by norm_num⟩
  | 4 => ⟨((18289372741/35184372088832), (-6649122557/35184372088832)), (158287/35184372088832), by norm_num⟩
  | 5 => ⟨((-2124137415/70368744177664), (15606251521/140737488355328)), (390907/140737488355328), by norm_num⟩
  | 6 => ⟨((-7836798527/562949953421312), (-9617924387/562949953421312)), (407295/281474976710656), by norm_num⟩
  | 7 => ⟨((9017393953/2251799813685248), (-1084125065/4503599627370496)), (1472711/2251799813685248), by norm_num⟩
  | 8 => ⟨((-3318783527/9007199254740992), (10714502593/18014398509481984)), (4716637/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1701683113/36028797018963968), (-7762730643/72057594037927936)), (3399321/36028797018963968), by norm_num⟩
  | 10 => ⟨((21801343013/1152921504606846976), (120824887/36028797018963968)), (558675/18014398509481984), by norm_num⟩
  | 11 => ⟨((-2400083947/1152921504606846976), (5179669183/2305843009213693952)), (43411567/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-4720057583/36893488147419103232), (-17051400341/36893488147419103232)), (98875607/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4156810539/17179869184), (139774601/8589934592)), (1327/68719476736), by norm_num⟩
  | 1 => ⟨((-293057299/274877906944), (17920059297/274877906944)), (7465/137438953472), by norm_num⟩
  | 2 => ⟨((-4726513169/2199023255552), (2776585991/4398046511104)), (758567/8796093022208), by norm_num⟩
  | 3 => ⟨((-150559759/2199023255552), (29682375791/35184372088832)), (1714867/17592186044416), by norm_num⟩
  | 4 => ⟨((-4844890521/70368744177664), (1571183737/281474976710656)), (12104963/140737488355328), by norm_num⟩
  | 5 => ⟨((-2076328775/2251799813685248), (20151178845/4503599627370496)), (284766031/4503599627370496), by norm_num⟩
  | 6 => ⟨((-11140748543/18014398509481984), (152908401/9007199254740992)), (736135353/18014398509481984), by norm_num⟩
  | 7 => ⟨((-925408459/144115188075855872), (1407588035/144115188075855872)), (3573230385/144115188075855872), by norm_num⟩
  | 8 => ⟨((-1870326071/576460752303423488), (-7815523/144115188075855872)), (17753427087/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-58796461/2305843009213693952), (-26832643/2305843009213693952)), (6149524799/576460752303423488), by norm_num⟩
  | 10 => ⟨((-4059747/288230376151711744), (-5758017/2305843009213693952)), (19756008239/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1013899/1152921504606846976), (457249/2305843009213693952)), (17824866051/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-460177/1152921504606846976), (44379/2305843009213693952)), (34242353851/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((259800659/1073741824), (17471825/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1144755/1073741824), (8750029/134217728)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-576967/268435456), (338939/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-73515/1073741824), (452917/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-73927/1073741824), (2997/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-495/536870912), (1201/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-83/134217728), (9/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-7/1073741824), (5/536870912)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-3/1073741824), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨12,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨12,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(7138633/67108864)) (L:=(133318396981/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile012
