/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile037Gamma
public import XiRectangle.Tile037Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile037
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29215999/549755813888), (1038001171/4398046511104)), (1017/4398046511104), by norm_num⟩
  | 1 => ⟨((-263997477/2199023255552), (587140699/2199023255552)), (1059/2199023255552), by norm_num⟩
  | 2 => ⟨((-662947167/4398046511104), (187186395/2199023255552)), (4565/8796093022208), by norm_num⟩
  | 3 => ⟨((-1164895463/17592186044416), (-125433269/17592186044416)), (6737/17592186044416), by norm_num⟩
  | 4 => ⟨((-31189291/2199023255552), (-53810819/4398046511104)), (7597/35184372088832), by norm_num⟩
  | 5 => ⟨((-315423407/281474976710656), (-138988795/35184372088832)), (27805/281474976710656), by norm_num⟩
  | 6 => ⟨((225874671/1125899906842624), (-792027759/1125899906842624)), (85839/2251799813685248), by norm_num⟩
  | 7 => ⟨((175960249/2251799813685248), (-344319469/4503599627370496)), (115021/9007199254740992), by norm_num⟩
  | 8 => ⟨((485438697/36028797018963968), (-298740615/72057594037927936)), (137069/36028797018963968), by norm_num⟩
  | 9 => ⟨((460594513/288230376151711744), (244237025/1152921504606846976)), (1199377/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1341118391/9223372036854775808), (768571847/9223372036854775808)), (2599335/9223372036854775808), by norm_num⟩
  | 11 => ⟨((379903645/36893488147419103232), (914607951/73786976294838206464)), (6915033/73786976294838206464), by norm_num⟩
  | 12 => ⟨((298318429/590295810358705651712), (797804273/590295810358705651712)), (15068591/295147905179352825856), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile037Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((415598177/134217728), (314570403/134217728)), (2545/268435456), by norm_num⟩
  | 1 => ⟨((-264734023/67108864), (136205939/16777216)), (3207/134217728), by norm_num⟩
  | 2 => ⟨((24647377/8388608), (-180553319/67108864)), (8767/268435456), by norm_num⟩
  | 3 => ⟨((-35788899/33554432), (8260851/16777216)), (33281/1073741824), by norm_num⟩
  | 4 => ⟨((18290039/67108864), (-1862471/67108864)), (48801/2147483648), by norm_num⟩
  | 5 => ⟨((-6990077/134217728), (-1765025/134217728)), (233095/17179869184), by norm_num⟩
  | 6 => ⟨((504997/67108864), (1413157/268435456)), (946231/137438953472), by norm_num⟩
  | 7 => ⟨((-51997/67108864), (-313605/268435456)), (3346867/1099511627776), by norm_num⟩
  | 8 => ⟨((1303/33554432), (204331/1073741824)), (5347019/4398046511104), by norm_num⟩
  | 9 => ⟨((10075/2147483648), (-52123/2147483648)), (32566445/70368744177664), by norm_num⟩
  | 10 => ⟨((-6969/4294967296), (20831/8589934592)), (52376243/281474976710656), by norm_num⟩
  | 11 => ⟨((4633/17179869184), (-3015/17179869184)), (216372629/2251799813685248), by norm_num⟩
  | 12 => ⟨((-4517/137438953472), (385/68719476736)), (1252568231/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile037Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-48013451/134217728), (-1057796351/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-10711998755191/562949953421312), (-1574017619932635/2251799813685248)), (62124685/2251799813685248), by norm_num⟩
  | 1 => ⟨((23388567/2147483648), (429588559/1073741824)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((-53547183/17179869184), (-1967051449/17179869184)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((40864707/68719476736), (1501161721/68719476736)), (33/34359738368), by norm_num⟩
  | 4 => ⟨((-46779051/549755813888), (-859212343/274877906944)), (39/274877906944), by norm_num⟩
  | 5 => ⟨((21419751/2199023255552), (393426419/1099511627776)), (37/2199023255552), by norm_num⟩
  | 6 => ⟨((-32693105/35184372088832), (-1200978613/35184372088832)), (59/35184372088832), by norm_num⟩
  | 7 => ⟨((42771171/562949953421312), (1571195555/562949953421312)), (5/35184372088832), by norm_num⟩
  | 8 => ⟨((-24480719/4503599627370496), (-1798594509/9007199254740992)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((12455027/36028797018963968), (915068839/72057594037927936)), (49/72057594037927936), by norm_num⟩
  | 10 => ⟨((-45624453/2305843009213693952), (-1676010637/2305843009213693952)), (23/576460752303423488), by norm_num⟩
  | 11 => ⟨((9495941/9223372036854775808), (1395330521/36893488147419103232)), (79/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-28987433/590295810358705651712), (-133106379/73786976294838206464)), (31/295147905179352825856), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893166141/5070602400912917605986812821504), (-2081588607483/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781416300172707/633825300114114700748351602688), (-1235216045547/316912650057057350374175801344)), (2889/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((946359926031999/19807040628566084398385987584), (-2779140896451/39614081257132168796771975168)), (6501/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892680487096323/2475880078570760549798248448), (-2952728728513/2475880078570760549798248448)), (13817/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774346102821921/154742504910672534362390528), (-738151663837/38685626227668133590597632)), (27639/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552510954026745/9671406556917033397649408), (-691984749211/2417851639229258349412352)), (25917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261375847963015/604462909807314587353088), (-2421816834927/604462909807314587353088)), (22683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891994924910835/75557863725914323419136), (-3935208910439/75557863725914323419136)), (36869/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650345254363207/2361183241434822606848), (-2951193572221/4722366482869645213696)), (27661/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625779020825263/590295810358705651712), (-4057544678845/590295810358705651712)), (1189/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1828885558472831/73786976294838206464), (-2535705406173/36893488147419103232)), (47581/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914370243022593/4611686018427387904), (-2852310803839/4611686018427387904)), (26779/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199998043036719/144115188075855872), (-356482900197/72057594037927936)), (53595/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599912104652905/72057594037927936), (-4989752454281/144115188075855872)), (46937/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499492123833003/36028797018963968), (-7482609777801/36028797018963968)), (70489/36028797018963968), by norm_num⟩
  | 3 => ⟨((374764453570853/2251799813685248), (-9349723280869/9007199254740992)), (88257/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123746797271705/2251799813685248), (-4672201580541/1125899906842624)), (22119/562949953421312), by norm_num⟩
  | 1 => ⟨((1122642654837805/1125899906842624), (-14003263520919/1125899906842624)), (66631/562949953421312), by norm_num⟩
  | 0 => ⟨((1119275247670137/1125899906842624), (-13976458538995/562949953421312)), (16795/70368744177664), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1119275247670137/1125899906842624), (-13976458538995/562949953421312)), (64067840844607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((555997787576369/562949953421312), (-55576890974809/1125899906842624)), (273811/562949953421312), by norm_num⟩
  | 2 => ⟨((547759779023257/562949953421312), (-54890542639837/562949953421312)), (1135783/1125899906842624), by norm_num⟩
  | 3 => ⟨((527627370850879/562949953421312), (-106818843572625/562949953421312)), (2431763/1125899906842624), by norm_num⟩
  | 4 => ⟨((237126209449217/281474976710656), (-400465762535557/1125899906842624)), (5481209/1125899906842624), by norm_num⟩
  | 5 => ⟨((328310090385421/562949953421312), (-674737977734075/1125899906842624)), (13134365/1125899906842624), by norm_num⟩
  | 6 => ⟨((-10711998755191/562949953421312), (-1574017619932635/2251799813685248)), (62124685/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-48013451/134217728), (-1057796351/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((721119767/4398046511104), (-183128289/4398046511104)), (383/2199023255552), by norm_num⟩
  | 1 => ⟨((836261733/8796093022208), (112885577/1099511627776)), (2007/4398046511104), by norm_num⟩
  | 2 => ⟨((-166281015/8796093022208), (911315067/17592186044416)), (10769/17592186044416), by norm_num⟩
  | 3 => ⟨((-957079573/70368744177664), (88355369/70368744177664)), (39279/70368744177664), by norm_num⟩
  | 4 => ⟨((-622456347/562949953421312), (-73158393/35184372088832)), (218717/562949953421312), by norm_num⟩
  | 5 => ⟨((911774487/4503599627370496), (-962714873/4503599627370496)), (987221/4503599627370496), by norm_num⟩
  | 6 => ⟨((101798411/4503599627370496), (529039807/36028797018963968)), (234543/2251799813685248), by norm_num⟩
  | 7 => ⟨((-734350869/576460752303423488), (26020981/18014398509481984)), (12342461/288230376151711744), by norm_num⟩
  | 8 => ⟨((-29553287/576460752303423488), (-1503780577/9223372036854775808)), (17929541/1152921504606846976), by norm_num⟩
  | 9 => ⟨((717998825/36893488147419103232), (6562581/18446744073709551616)), (375034627/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-107181509/295147905179352825856), (266135899/147573952589676412928)), (904291425/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-632728881/4722366482869645213696), (-161363195/2361183241434822606848)), (2125530717/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((88225273/9444732965739290427392), (-19734291/2361183241434822606848)), (177387855/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1331056655/2199023255552), (280766101/1099511627776)), (6371/2199023255552), by norm_num⟩
  | 1 => ⟨((-140193859/549755813888), (1119374011/549755813888)), (1563/137438953472), by norm_num⟩
  | 2 => ⟨((-1120156765/1099511627776), (-88567909/1099511627776)), (24109/1099511627776), by norm_num⟩
  | 3 => ⟨((89232039/8796093022208), (-472336403/2199023255552)), (122805/4398046511104), by norm_num⟩
  | 4 => ⟨((714713139/35184372088832), (4976867/70368744177664)), (467113/17592186044416), by norm_num⟩
  | 5 => ⟨((523774015/4503599627370496), (130358195/1125899906842624)), (90810681/4503599627370496), by norm_num⟩
  | 6 => ⟨((698602293/4503599627370496), (92814665/9007199254740992)), (57483769/4503599627370496), by norm_num⟩
  | 7 => ⟨((23336267/144115188075855872), (1700958567/144115188075855872)), (500092161/72057594037927936), by norm_num⟩
  | 8 => ⟨((5855823/36028797018963968), (317743/4503599627370496)), (478154261/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1473823/576460752303423488), (73112053/1152921504606846976)), (205404723/144115188075855872), by norm_num⟩
  | 10 => ⟨((-1125691/576460752303423488), (145013/1152921504606846976)), (1303280959/2305843009213693952), by norm_num⟩
  | 11 => ⟨((35347/2305843009213693952), (53407/288230376151711744)), (501796367/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-148085/9223372036854775808), (209377/18446744073709551616)), (1676688685/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((324965/536870912), (137093/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-34227/134217728), (2186277/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1093903/1073741824), (-21623/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((10893/1073741824), (-230633/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21811/1073741824), (19/268435456)), (1/10000000), by norm_num⟩
  | 5 => ⟨((125/1073741824), (31/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((167/1073741824), (11/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (13/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨37,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨37,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/1048576)) (K:=(2881885/1073741824)) (L:=(90291001/137438953472)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile037
