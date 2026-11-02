/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile040Gamma
public import XiRectangle.Tile040Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile040
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19940765/4398046511104), (422236001/2199023255552)), (1443/8796093022208), by norm_num⟩
  | 1 => ⟨((-79368391/549755813888), (810809741/4398046511104)), (1527/4398046511104), by norm_num⟩
  | 2 => ⟨((-1181840395/8796093022208), (333775177/8796093022208)), (3299/8796093022208), by norm_num⟩
  | 3 => ⟨((-224476239/4398046511104), (-321238749/17592186044416)), (2425/8796093022208), by norm_num⟩
  | 4 => ⟨((-79204491/8796093022208), (-439647245/35184372088832)), (10887/70368744177664), by norm_num⟩
  | 5 => ⟨((-81475039/562949953421312), (-960129193/281474976710656)), (39693/562949953421312), by norm_num⟩
  | 6 => ⟨((680220507/2251799813685248), (-603820231/1125899906842624)), (61097/2251799813685248), by norm_num⟩
  | 7 => ⟨((721134521/9007199254740992), (-428241575/9007199254740992)), (40847/4503599627370496), by norm_num⟩
  | 8 => ⟨((1747587007/144115188075855872), (-94203489/144115188075855872)), (389463/144115188075855872), by norm_num⟩
  | 9 => ⟨((1497598309/1152921504606846976), (151540697/288230376151711744)), (214873/288230376151711744), by norm_num⟩
  | 10 => ⟨((479700589/4611686018427387904), (952443107/9223372036854775808)), (1937889/9223372036854775808), by norm_num⟩
  | 11 => ⟨((107543195/18446744073709551616), (59453547/4611686018427387904)), (2866681/36893488147419103232), by norm_num⟩
  | 12 => ⟨((125583063/1180591620717411303424), (1496049747/1180591620717411303424)), (56366865/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile040Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((193705185/268435456), (316725011/268435456)), (11453/1073741824), by norm_num⟩
  | 1 => ⟨((-319098011/134217728), (329699031/33554432)), (1811/67108864), by norm_num⟩
  | 2 => ⟨((83893589/33554432), (-243152263/67108864)), (9913/268435456), by norm_num⟩
  | 3 => ⟨((-34569061/33554432), (27256851/33554432)), (37985/1073741824), by norm_num⟩
  | 4 => ⟨((9753173/33554432), (-7041661/67108864)), (55969/2147483648), by norm_num⟩
  | 5 => ⟨((-256497/4194304), (7205/16777216)), (270599/17179869184), by norm_num⟩
  | 6 => ⟨((665421/67108864), (481609/134217728)), (1105975/137438953472), by norm_num⟩
  | 7 => ⟨((-329181/268435456), (-285039/268435456)), (988269/274877906944), by norm_num⟩
  | 8 => ⟨((112345/1073741824), (53871/268435456)), (6317771/4398046511104), by norm_num⟩
  | 9 => ⟨((-371/134217728), (-61967/2147483648)), (19019351/35184372088832), by norm_num⟩
  | 10 => ⟨((-8651/8589934592), (883/268435456)), (59421363/281474976710656), by norm_num⟩
  | 11 => ⟨((4203/17179869184), (-1255/4294967296)), (233936277/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1219/34359738368), (1223/68719476736)), (1290841255/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile040Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((19/32), (7191/512))
  have he : value ((19/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-45612779/134217728), (-539476139/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-147308178391591/1125899906842624), (-24620498670779/35184372088832)), (65866845/2251799813685248), by norm_num⟩
  | 1 => ⟨((321632527/4294967296), (1720203897/4294967296)), (75/4294967296), by norm_num⟩
  | 2 => ⟨((-184091183/8589934592), (-492292203/4294967296)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((70244893/17179869184), (1502777593/68719476736)), (71/68719476736), by norm_num⟩
  | 4 => ⟨((-321645713/549755813888), (-1720274423/549755813888)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((18409873/274877906944), (393849909/1099511627776)), (5/274877906944), by norm_num⟩
  | 6 => ⟨((-224792873/35184372088832), (-300567841/8796093022208)), (63/35184372088832), by norm_num⟩
  | 7 => ⟨((294088137/562949953421312), (1572886813/562949953421312)), (85/562949953421312), by norm_num⟩
  | 8 => ⟨((-42081435/1125899906842624), (-900265271/4503599627370496)), (25/2251799813685248), by norm_num⟩
  | 9 => ⟨((85638891/36028797018963968), (114506729/9007199254740992)), (53/72057594037927936), by norm_num⟩
  | 10 => ⟨((-313706873/2305843009213693952), (-838907359/1152921504606846976)), (25/576460752303423488), by norm_num⟩
  | 11 => ⟨((130585321/18446744073709551616), (698416237/18446744073709551616)), (43/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-99656613/295147905179352825856), (-1065997253/590295810358705651712)), (17/147573952589676412928), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583533085365599/10141204801825835211973625643008), (-571727846779/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781443279461413/633825300114114700748351602688), (-678547331809/158456325028528675187087900672)), (23117/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946375080625799/19807040628566084398385987584), (-3053362154931/39614081257132168796771975168)), (26011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473178159897303/618970019642690137449562112), (-3244083892395/2475880078570760549798248448)), (13821/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887189098959641/77371252455336267181195264), (-810989066467/38685626227668133590597632)), (27/151115727451828646838272), by norm_num⟩
  | 13 => ⟨((776270491101281/4835703278458516698824704), (-380134167613/1208925819614629174706176)), (12963/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630701030822143/302231454903657293676544), (-665200863227/151115727451828646838272)), (22691/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1892037407830801/75557863725914323419136), (-4323551003467/75557863725914323419136)), (36883/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300722270904779/4722366482869645213696), (-1621220169635/2361183241434822606848)), (3459/590295810358705651712), by norm_num⟩
  | 9 => ⟨((25403477051925/9223372036854775808), (-2228996492679/295147905179352825856)), (2379/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1828939702887051/73786976294838206464), (-2785973538963/36893488147419103232)), (11901/18446744073709551616), by norm_num⟩
  | 7 => ⟨((914400531736943/4611686018427387904), (-6267691549393/9223372036854775808)), (53587/9223372036854775808), by norm_num⟩
  | 6 => ⟨((800022251509119/576460752303423488), (-6266754355519/1152921504606846976)), (13407/288230376151711744), by norm_num⟩
  | 5 => ⟨((599938188637425/72057594037927936), (-685294283981/18014398509481984)), (46971/144115188075855872), by norm_num⟩
  | 4 => ⟨((374892358569021/9007199254740992), (-4110708108155/18014398509481984)), (70547/36028797018963968), by norm_num⟩
  | 3 => ⟨((1499152805414789/9007199254740992), (-5136530281207/4503599627370496)), (88343/9007199254740992), by norm_num⟩
  | 2 => ⟨((561919659733627/1125899906842624), (-641717485655/140737488355328)), (11073/281474976710656), by norm_num⟩
  | 1 => ⟨((1122775270886813/1125899906842624), (-3846802735603/281474976710656)), (66739/562949953421312), by norm_num⟩
  | 0 => ⟨((559757920791707/562949953421312), (-30718047202909/1125899906842624)), (134685/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559757920791707/562949953421312), (-30718047202909/1125899906842624)), (513782503368186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2172519319187/2199023255552), (-30543870069767/562949953421312)), (550385/1125899906842624), by norm_num⟩
  | 2 => ⟨((547804501920003/562949953421312), (-60351474357327/562949953421312)), (286807/281474976710656), by norm_num⟩
  | 3 => ⟨((1053192988346721/1125899906842624), (-117455589611571/562949953421312)), (1239353/562949953421312), by norm_num⟩
  | 4 => ⟨((936168661328453/1125899906842624), (-439482773448093/1125899906842624)), (5671609/1125899906842624), by norm_num⟩
  | 5 => ⟨((303431348623153/562949953421312), (-182711623473527/281474976710656)), (1732427/140737488355328), by norm_num⟩
  | 6 => ⟨((-147308178391591/1125899906842624), (-24620498670779/35184372088832)), (65866845/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-45612779/134217728), (-539476139/67108864)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((148383469/1099511627776), (-193067219/8796093022208)), (625/4398046511104), by norm_num⟩
  | 1 => ⟨((4855085/68719476736), (98369469/1099511627776)), (1669/4398046511104), by norm_num⟩
  | 2 => ⟨((-80975377/4398046511104), (364529579/8796093022208)), (8985/17592186044416), by norm_num⟩
  | 3 => ⟨((-1597631507/140737488355328), (29263417/70368744177664)), (65549/140737488355328), by norm_num⟩
  | 4 => ⟨((-486319531/562949953421312), (-1006697333/562949953421312)), (91009/281474976710656), by norm_num⟩
  | 5 => ⟨((396963633/2251799813685248), (-407532951/2251799813685248)), (818721/4503599627370496), by norm_num⟩
  | 6 => ⟨((45346067/2251799813685248), (441270215/36028797018963968)), (1551259/18014398509481984), by norm_num⟩
  | 7 => ⟨((-547779619/576460752303423488), (784816349/576460752303423488)), (1272271/36028797018963968), by norm_num⟩
  | 8 => ⟨((-510535303/9223372036854775808), (-1109990977/9223372036854775808)), (29519233/2305843009213693952), by norm_num⟩
  | 9 => ⟨((1112198715/73786976294838206464), (-62695583/73786976294838206464)), (308818725/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-188521231/1180591620717411303424), (856665521/590295810358705651712)), (1499988121/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-262176073/2361183241434822606848), (-189305747/4722366482869645213696)), (454216517/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((58235505/9444732965739290427392), (-68449359/9444732965739290427392)), (660239573/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((542198113/4398046511104), (630646805/4398046511104)), (4275/2199023255552), by norm_num⟩
  | 1 => ⟨((-87828289/549755813888), (839001005/549755813888)), (4617/549755813888), by norm_num⟩
  | 2 => ⟨((-468032001/549755813888), (-119125701/2199023255552)), (18941/1099511627776), by norm_num⟩
  | 3 => ⟨((65842549/8796093022208), (-1694052661/8796093022208)), (201505/8796093022208), by norm_num⟩
  | 4 => ⟨((702722119/35184372088832), (721531/4398046511104)), (1582689/70368744177664), by norm_num⟩
  | 5 => ⟨((41853049/562949953421312), (395656963/1125899906842624)), (9860167/562949953421312), by norm_num⟩
  | 6 => ⟨((1190033863/9007199254740992), (35411455/4503599627370496)), (101929447/9007199254740992), by norm_num⟩
  | 7 => ⟨((1867345/144115188075855872), (862771107/72057594037927936)), (112735847/18014398509481984), by norm_num⟩
  | 8 => ⟨((470821/36028797018963968), (445921/9007199254740992)), (1748434857/576460752303423488), by norm_num⟩
  | 9 => ⟨((-1093671/576460752303423488), (65470959/1152921504606846976)), (1516720771/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-5717309/2305843009213693952), (52039/144115188075855872)), (301885681/576460752303423488), by norm_num⟩
  | 11 => ⟨((-149097/4611686018427387904), (127953/2305843009213693952)), (1848692645/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-154889/18446744073709551616), (179367/18446744073709551616)), (1506366811/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((132373/1073741824), (76983/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-42885/268435456), (819337/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-914125/1073741824), (-58167/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((8037/1073741824), (-103397/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21445/1073741824), (11/67108864)), (1/10000000), by norm_num⟩
  | 5 => ⟨((5/67108864), (377/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((71/536870912), (1/134217728)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨40,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨40,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/524288)) (K:=(968043/536870912)) (L:=(207920269/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile040
