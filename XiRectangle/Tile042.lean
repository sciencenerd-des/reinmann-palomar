/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile042Gamma
public import XiRectangle.Tile042Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile042
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55496405/4398046511104), (10580093/34359738368)), (1243/4398046511104), by norm_num⟩
  | 1 => ⟨((-229515545/1099511627776), (337966717/1099511627776)), (317/549755813888), by norm_num⟩
  | 2 => ⟨((-452733977/2199023255552), (327772047/4398046511104)), (2713/4398046511104), by norm_num⟩
  | 3 => ⟨((-1425426605/17592186044416), (-194082847/8796093022208)), (3995/8796093022208), by norm_num⟩
  | 4 => ⟨((-270027873/17592186044416), (-628936405/35184372088832)), (4511/17592186044416), by norm_num⟩
  | 5 => ⟨((-49575417/70368744177664), (-719075651/140737488355328)), (33105/281474976710656), by norm_num⟩
  | 6 => ⟨((204444231/562949953421312), (-950439555/1125899906842624)), (51287/1125899906842624), by norm_num⟩
  | 7 => ⟨((981524711/9007199254740992), (-757469729/9007199254740992)), (137939/9007199254740992), by norm_num⟩
  | 8 => ⟨((1261413495/72057594037927936), (-30625591/9007199254740992)), (329537/72057594037927936), by norm_num⟩
  | 9 => ⟨((1152150363/576460752303423488), (33706641/72057594037927936)), (179857/144115188075855872), by norm_num⟩
  | 10 => ⟨((810820287/4611686018427387904), (284925839/2305843009213693952)), (383415/1152921504606846976), by norm_num⟩
  | 11 => ⟨((436166587/36893488147419103232), (1261222417/73786976294838206464)), (7750329/73786976294838206464), by norm_num⟩
  | 12 => ⟨((9322503/18446744073709551616), (531210507/295147905179352825856)), (7877983/147573952589676412928), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile042Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((38222255/16777216), (565429601/134217728)), (1467/268435456), by norm_num⟩
  | 1 => ⟨((-178487619/67108864), (921222095/134217728)), (863/67108864), by norm_num⟩
  | 2 => ⟨((599347505/268435456), (-156587923/67108864)), (4483/268435456), by norm_num⟩
  | 3 => ⟨((-55321313/67108864), (61459455/134217728)), (16609/1073741824), by norm_num⟩
  | 4 => ⟨((28733975/134217728), (-5347977/134217728)), (23921/2147483648), by norm_num⟩
  | 5 => ⟨((-2803381/67108864), (-1780263/268435456)), (112903/17179869184), by norm_num⟩
  | 6 => ⟨((26181/4194304), (472847/134217728)), (454967/137438953472), by norm_num⟩
  | 7 => ⟨((-185039/268435456), (-449869/536870912)), (1618355/1099511627776), by norm_num⟩
  | 8 => ⟨((48817/1073741824), (305077/2147483648)), (2653899/4398046511104), by norm_num⟩
  | 9 => ⟨((1563/1073741824), (-161403/8589934592)), (17386669/70368744177664), by norm_num⟩
  | 10 => ⟨((-17233/17179869184), (33807/17179869184)), (33338035/281474976710656), by norm_num⟩
  | 11 => ⟨((3179/17179869184), (-2675/17179869184)), (172692885/2251799813685248), by norm_num⟩
  | 12 => ⟨((-409/17179869184), (1985/274877906944)), (1160031399/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile042Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-1057796351/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-18567642843003/1125899906842624), (-1364161706113827/2251799813685248)), (26981297/1125899906842624), by norm_num⟩
  | 1 => ⟨((40540573/4294967296), (1489254641/4294967296)), (61/4294967296), by norm_num⟩
  | 2 => ⟨((-23204003/8589934592), (-213099287/2147483648)), (73/17179869184), by norm_num⟩
  | 3 => ⟨((35416421/68719476736), (162627415/8589934592)), (29/34359738368), by norm_num⟩
  | 4 => ⟨((-10135559/137438953472), (-744657849/274877906944)), (69/549755813888), by norm_num⟩
  | 5 => ⟨((37127927/4398046511104), (170486419/549755813888)), (33/2199023255552), by norm_num⟩
  | 6 => ⟨((-56668597/70368744177664), (-65053633/2199023255552)), (103/70368744177664), by norm_num⟩
  | 7 => ⟨((37068707/562949953421312), (1361715893/562949953421312)), (69/562949953421312), by norm_num⟩
  | 8 => ⟨((-42433657/9007199254740992), (-1558796879/9007199254740992)), (81/9007199254740992), by norm_num⟩
  | 9 => ⟨((43177845/144115188075855872), (1586134555/144115188075855872)), (85/144115188075855872), by norm_num⟩
  | 10 => ⟨((-4942697/288230376151711744), (-1452556503/2305843009213693952)), (5/144115188075855872), by norm_num⟩
  | 11 => ⟨((32919581/36893488147419103232), (604649033/18446744073709551616)), (17/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-50245371/1180591620717411303424), (-1845759517/1180591620717411303424)), (53/590295810358705651712), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-2081588607483/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781195115574585/633825300114114700748351602688), (-154365646185/39614081257132168796771975168)), (2889/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((946235515210485/19807040628566084398385987584), (-173653174839/2475880078570760549798248448)), (6501/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946208062927407/1237940039285380274899124224), (-2951952415049/2475880078570760549798248448)), (13817/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774081754815847/154742504910672534362390528), (-1475890938433/77371252455336267181195264)), (27639/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388065785461341/2417851639229258349412352), (-1383557139889/4835703278458516698824704)), (25917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261159026391735/604462909807314587353088), (-151315232997/37778931862957161709568)), (22683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945821308149649/37778931862957161709568), (-1966928051915/37778931862957161709568)), (36869/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300426300432183/4722366482869645213696), (-1475047269667/2361183241434822606848)), (27661/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625415772115091/590295810358705651712), (-4055896343957/590295810358705651712)), (1189/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1828431554218037/73786976294838206464), (-5069144700525/73786976294838206464)), (47581/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228528726159643/1152921504606846976), (-2850894745599/4611686018427387904)), (26779/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599473765271345/1152921504606846976), (-1425135248041/288230376151711744)), (53595/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599688781465311/72057594037927936), (-4986567944135/144115188075855872)), (23469/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498822375572405/36028797018963968), (-7477038914079/36028797018963968)), (70489/36028797018963968), by norm_num⟩
  | 3 => ⟨((187277627244047/1125899906842624), (-9341371048687/9007199254740992)), (88257/9007199254740992), by norm_num⟩
  | 2 => ⟨((561455293930203/1125899906842624), (-9333969993799/2251799813685248)), (22119/562949953421312), by norm_num⟩
  | 1 => ⟨((1121389819998531/1125899906842624), (-3495604650767/281474976710656)), (66631/562949953421312), by norm_num⟩
  | 0 => ⟨((1116775566823989/1125899906842624), (-1743155608905/70368744177664)), (268721/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116775566823989/1125899906842624), (-1743155608905/70368744177664)), (1025089268210982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553517137563449/562949953421312), (-55328928090071/1125899906842624)), (546401/1125899906842624), by norm_num⟩
  | 2 => ⟨((1085765784855877/1125899906842624), (-108803667945061/1125899906842624)), (564097/562949953421312), by norm_num⟩
  | 3 => ⟨((1036547826598699/1125899906842624), (-52462611997569/281474976710656)), (299251/140737488355328), by norm_num⟩
  | 4 => ⟨((228793470015091/281474976710656), (-386393185492089/1125899906842624)), (2650225/562949953421312), by norm_num⟩
  | 5 => ⟨((611283057017091/1125899906842624), (-314074944536883/562949953421312)), (6127447/562949953421312), by norm_num⟩
  | 6 => ⟨((-18567642843003/1125899906842624), (-1364161706113827/2251799813685248)), (26981297/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1057796351/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1639006897/8796093022208), (-111907463/8796093022208)), (101/549755813888), by norm_num⟩
  | 1 => ⟨((365058851/4398046511104), (1131805179/8796093022208)), (131/274877906944), by norm_num⟩
  | 2 => ⟨((-259364773/8796093022208), (456796267/8796093022208)), (11145/17592186044416), by norm_num⟩
  | 3 => ⟨((-256374483/17592186044416), (-2094587/2199023255552)), (40501/70368744177664), by norm_num⟩
  | 4 => ⟨((-468460819/562949953421312), (-1312789227/562949953421312)), (225265/562949953421312), by norm_num⟩
  | 5 => ⟨((132097853/562949953421312), (-855621475/4503599627370496)), (1017211/4503599627370496), by norm_num⟩
  | 6 => ⟨((731742711/36028797018963968), (304951089/18014398509481984)), (3873141/36028797018963968), by norm_num⟩
  | 7 => ⟨((-384351231/288230376151711744), (161764177/144115188075855872)), (12769035/288230376151711744), by norm_num⟩
  | 8 => ⟨((-10177209/1152921504606846976), (-1451382897/9223372036854775808)), (74382563/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1337473069/73786976294838206464), (339676963/73786976294838206464)), (194816085/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-408261895/590295810358705651712), (935880921/590295810358705651712)), (234543429/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-123338307/1180591620717411303424), (-209104641/2361183241434822606848)), (1089650849/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((96077071/9444732965739290427392), (-48479227/9444732965739290427392)), (1399210791/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((262841633/549755813888), (831227909/1099511627776)), (627/274877906944), by norm_num⟩
  | 1 => ⟨((-104621919/137438953472), (1075094981/549755813888)), (4707/549755813888), by norm_num⟩
  | 2 => ⟨((-1103385751/1099511627776), (-265644135/1099511627776)), (4393/274877906944), by norm_num⟩
  | 3 => ⟨((67244117/2199023255552), (-944022123/4398046511104)), (10955/549755813888), by norm_num⟩
  | 4 => ⟨((724948769/35184372088832), (16296087/70368744177664)), (1315705/70368744177664), by norm_num⟩
  | 5 => ⟨((786646269/2251799813685248), (330596711/2251799813685248)), (1980867/140737488355328), by norm_num⟩
  | 6 => ⟨((1402298933/9007199254740992), (280670145/9007199254740992)), (39880747/4503599627370496), by norm_num⟩
  | 7 => ⟨((69429463/144115188075855872), (1742112283/144115188075855872)), (345571257/72057594037927936), by norm_num⟩
  | 8 => ⟨((87027461/576460752303423488), (123930835/576460752303423488)), (1319637379/576460752303423488), by norm_num⟩
  | 9 => ⟨((-8728493/1152921504606846976), (37204561/576460752303423488)), (568225267/576460752303423488), by norm_num⟩
  | 10 => ⟨((-9958501/4611686018427387904), (1370189/2305843009213693952)), (1825259543/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-174703/4611686018427387904), (40869/288230376151711744)), (182714925/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-46939/4611686018427387904), (-18801/9223372036854775808)), (1334011615/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((513363/1073741824), (405873/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-817359/1073741824), (2099795/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1077525/1073741824), (-129709/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((16417/536870912), (-115237/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((5531/268435456), (249/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((375/1073741824), (79/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((167/1073741824), (33/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (13/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨42,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨42,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/1048576)) (K:=(424117/134217728)) (L:=(983505563/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile042
