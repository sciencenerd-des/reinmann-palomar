/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile027Gamma
public import XiRectangle.Tile027Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile027
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3994617897/4398046511104), (-2693531983/4398046511104)), (1289/4398046511104), by norm_num⟩
  | 1 => ⟨((2734893207/2199023255552), (472878683/4398046511104)), (3133/4398046511104), by norm_num⟩
  | 2 => ⟨((1105025075/2199023255552), (4152015347/8796093022208)), (7281/8796093022208), by norm_num⟩
  | 3 => ⟨((355241239/8796093022208), (66513437/274877906944)), (5583/8796093022208), by norm_num⟩
  | 4 => ⟨((-247418343/8796093022208), (496882345/8796093022208)), (25771/70368744177664), by norm_num⟩
  | 5 => ⟨((-765464681/70368744177664), (1736197521/281474976710656)), (1501/8796093022208), by norm_num⟩
  | 6 => ⟨((-4492056455/2251799813685248), (-64072185/1125899906842624)), (75465/1125899906842624), by norm_num⟩
  | 7 => ⟨((-4205791457/18014398509481984), (-2345627219/18014398509481984)), (102915/4503599627370496), by norm_num⟩
  | 8 => ⟨((-1378596405/72057594037927936), (-901411161/36028797018963968)), (498353/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1155630265/1152921504606846976), (-1878585365/576460752303423488)), (2194271/1152921504606846976), by norm_num⟩
  | 10 => ⟨((105011257/9223372036854775808), (-6348032147/18446744073709551616)), (9212617/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1639960541/147573952589676412928), (-4435383835/147573952589676412928)), (21266459/147573952589676412928), by norm_num⟩
  | 12 => ⟨((488909449/295147905179352825856), (-1288383541/590295810358705651712)), (18258751/295147905179352825856), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile027Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((234086577/33554432), (3664315013/268435456)), (511/268435456), by norm_num⟩
  | 1 => ⟨((-1977372827/536870912), (-1640304515/536870912)), (4833/1073741824), by norm_num⟩
  | 2 => ⟨((344685949/268435456), (467238147/268435456)), (13169/2147483648), by norm_num⟩
  | 3 => ⟨((-9626907/67108864), (-154063811/268435456)), (12529/2147483648), by norm_num⟩
  | 4 => ⟨((-182433/8388608), (34102643/268435456)), (73927/17179869184), by norm_num⟩
  | 5 => ⟨((7204331/536870912), (-5270429/268435456)), (357175/137438953472), by norm_num⟩
  | 6 => ⟨((-1781959/536870912), (523453/268435456)), (1477043/1099511627776), by norm_num⟩
  | 7 => ⟨((149565/268435456), (-50483/1073741824)), (2746059/4398046511104), by norm_num⟩
  | 8 => ⟨((-9271/134217728), (-114353/4294967296)), (19573933/70368744177664), by norm_num⟩
  | 9 => ⟨((26371/4294967296), (56963/8589934592)), (38122163/281474976710656), by norm_num⟩
  | 10 => ⟨((-10017/34359738368), (-4227/4294967296)), (188519829/2251799813685248), by norm_num⟩
  | 11 => ⟨((-647/34359738368), (1849/17179869184)), (1203416231/18014398509481984), by norm_num⟩
  | 12 => ⟨((895/137438953472), (-2423/274877906944)), (4452430491/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile027Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-384107611/1073741824), (-1794022611/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((725130271427773/1125899906842624), (-19164984818245/70368744177664)), (262085/140737488355328), by norm_num⟩
  | 1 => ⟨((-1583248697/4294967296), (1339033867/8589934592)), (11/8589934592), by norm_num⟩
  | 2 => ⟨((453098025/4294967296), (-766416043/17179869184)), (15/34359738368), by norm_num⟩
  | 3 => ⟨((-5532531737/274877906944), (1169785799/137438953472)), (13/137438953472), by norm_num⟩
  | 4 => ⟨((791656803/274877906944), (-334772191/274877906944)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((-5799892491/17592186044416), (613157971/4398046511104)), (17/8796093022208), by norm_num⟩
  | 6 => ⟨((2213103423/70368744177664), (-1871734011/140737488355328)), (7/35184372088832), by norm_num⟩
  | 7 => ⟨((-5790641437/2251799813685248), (2448719841/2251799813685248)), (5/281474976710656), by norm_num⟩
  | 8 => ⟨((3314360155/18014398509481984), (-87597587/1125899906842624)), (25/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1686243165/144115188075855872), (713070761/144115188075855872)), (27/288230376151711744), by norm_num⟩
  | 10 => ⟨((3088468713/4611686018427387904), (-1306037457/4611686018427387904)), (13/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-5142490817/147573952589676412928), (1087316443/73786976294838206464)), (23/73786976294838206464), by norm_num⟩
  | 12 => ⟨((3924508617/2361183241434822606848), (-829789085/1180591620717411303424)), (37/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893164321/5070602400912917605986812821504), (-260567739679/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445354836251165/158456325028528675187087900672), (-309242135401/316912650057057350374175801344)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236590433076391/4951760157141521099596496896), (-173943039743/9903520314283042199192993792)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946342275503527/1237940039285380274899124224), (-369615454489/1237940039285380274899124224)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221793802561233/19342813113834066795298816), (-92400065457/19342813113834066795298816)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552515271427731/9671406556917033397649408), (-692968207555/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261379895242705/604462909807314587353088), (-75789362425/75557863725914323419136)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((946001003541317/37778931862957161709568), (-61575074053/4722366482869645213696)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300696262458627/4722366482869645213696), (-738847930263/4722366482869645213696)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625787650491575/590295810358705651712), (-1015829851385/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457224355687217/18446744073709551616), (-1269658243243/73786976294838206464)), (2963/36893488147419103232), by norm_num⟩
  | 7 => ⟨((14287150891535/72057594037927936), (-714094032103/4611686018427387904)), (1667/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1600001022745947/1152921504606846976), (-713983129827/576460752303423488)), (6669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299960220961423/36028797018963968), (-1249220974235/144115188075855872)), (5837/144115188075855872), by norm_num⟩
  | 4 => ⟨((749760647734505/18014398509481984), (-936666261665/18014398509481984)), (8757/36028797018963968), by norm_num⟩
  | 3 => ⟨((1499101554105121/9007199254740992), (-1170396332711/4503599627370496)), (10951/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123801441160031/2251799813685248), (-1169741743973/1125899906842624)), (5479/1125899906842624), by norm_num⟩
  | 1 => ⟨((1122751849821539/1125899906842624), (-1752976679069/562949953421312)), (16453/1125899906842624), by norm_num⟩
  | 0 => ⟨((1119602367785277/1125899906842624), (-3499412821017/562949953421312)), (16487/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1119602367785277/1125899906842624), (-3499412821017/562949953421312)), (62892915965843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1113296546853021/1125899906842624), (-13919357685199/1125899906842624)), (32995/562949953421312), by norm_num⟩
  | 2 => ⟨((1100662186030103/1125899906842624), (-27527087889723/1125899906842624)), (132135/1125899906842624), by norm_num⟩
  | 3 => ⟨((1075317175026737/1125899906842624), (-26910051726277/562949953421312)), (33101/140737488355328), by norm_num⟩
  | 4 => ⟨((256108561774013/281474976710656), (-102804310138977/1125899906842624)), (132785/281474976710656), by norm_num⟩
  | 5 => ⟨((115340714805801/140737488355328), (-93539625872065/562949953421312)), (2127087/2251799813685248), by norm_num⟩
  | 6 => ⟨((725130271427773/1125899906842624), (-19164984818245/70368744177664)), (262085/140737488355328), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-384107611/1073741824), (-1794022611/268435456)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1839128287/4398046511104), (-2822693403/4398046511104)), (597/2199023255552), by norm_num⟩
  | 1 => ⟨((2598925249/4398046511104), (860930281/8796093022208)), (7135/8796093022208), by norm_num⟩
  | 2 => ⟨((799959391/17592186044416), (1902219691/8796093022208)), (20767/17592186044416), by norm_num⟩
  | 3 => ⟨((-3094605785/70368744177664), (220695197/8796093022208)), (79775/70368744177664), by norm_num⟩
  | 4 => ⟨((-3009383949/562949953421312), (-1669258973/281474976710656)), (7173/8796093022208), by norm_num⟩
  | 5 => ⟨((2970600063/4503599627370496), (-729223383/1125899906842624)), (2120679/4503599627370496), by norm_num⟩
  | 6 => ⟨((1653489225/36028797018963968), (1420454247/18014398509481984)), (4105927/18014398509481984), by norm_num⟩
  | 7 => ⟨((-2947052081/288230376151711744), (129754337/144115188075855872)), (6863339/72057594037927936), by norm_num⟩
  | 8 => ⟨((1396562415/4611686018427387904), (-1366394545/1152921504606846976)), (40485193/1152921504606846976), by norm_num⟩
  | 9 => ⟨((1019383321/9223372036854775808), (2504873725/36893488147419103232)), (214443667/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-2987410817/295147905179352825856), (1160531517/147573952589676412928)), (64975299/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-1599219739/4722366482869645213696), (-5736695165/4722366482869645213696)), (4779161527/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1142728869/9444732965739290427392), (30261581/2361183241434822606848)), (5752664389/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3210119851/274877906944), (338328141/274877906944)), (4189/549755813888), by norm_num⟩
  | 1 => ⟨((-392892989/549755813888), (5407167179/549755813888)), (13549/549755813888), by norm_num⟩
  | 2 => ⟨((-6285179383/2199023255552), (-292023869/2199023255552)), (89579/2199023255552), by norm_num⟩
  | 3 => ⟨((4437149/1099511627776), (-6234729421/17592186044416)), (804045/17592186044416), by norm_num⟩
  | 4 => ⟨((4565978043/562949953421312), (-938372259/562949953421312)), (5512689/140737488355328), by norm_num⟩
  | 5 => ⟨((429290297/2251799813685248), (-6006531753/2251799813685248)), (30777505/1125899906842624), by norm_num⟩
  | 6 => ⟨((2293247259/9007199254740992), (-14871417/9007199254740992)), (291411967/18014398509481984), by norm_num⟩
  | 7 => ⟨((823848133/576460752303423488), (-1080326023/576460752303423488)), (1204929361/144115188075855872), by norm_num⟩
  | 8 => ⟨((1650614521/1152921504606846976), (32276349/576460752303423488)), (4463971327/1152921504606846976), by norm_num⟩
  | 9 => ⟨((2892425/576460752303423488), (228932301/4611686018427387904)), (7650326511/4611686018427387904), by norm_num⟩
  | 10 => ⟨((9344647/2305843009213693952), (4484791/9223372036854775808)), (3215420171/4611686018427387904), by norm_num⟩
  | 11 => ⟨((115349/18446744073709551616), (6196395/18446744073709551616)), (2970703279/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-62527/36893488147419103232), (122667/9223372036854775808)), (6972204265/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12539531/1073741824), (660797/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-767369/1073741824), (10560873/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-3068935/1073741824), (-71295/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((4333/1073741824), (-190269/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((8709/1073741824), (-895/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((205/1073741824), (-179/67108864)), (1/10000000), by norm_num⟩
  | 6 => ⟨((273/1073741824), (-1/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/536870912), (-1/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨27,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨27,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(14368633/1073741824)) (L:=(12911598433/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile027
