/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile039Gamma
public import XiRectangle.Tile039Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile039
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34978699/8796093022208), (1588934135/8796093022208)), (625/4398046511104), by norm_num⟩
  | 1 => ⟨((-70459257/549755813888), (197265047/1099511627776)), (1329/4398046511104), by norm_num⟩
  | 2 => ⟨((-1099514441/8796093022208), (90346857/2199023255552)), (2873/8796093022208), by norm_num⟩
  | 3 => ⟨((-858427363/17592186044416), (-134290641/8796093022208)), (4223/17592186044416), by norm_num⟩
  | 4 => ⟨((-629255023/70368744177664), (-403233553/35184372088832)), (9471/70368744177664), by norm_num⟩
  | 5 => ⟨((-70820219/281474976710656), (-1809232067/562949953421312)), (34497/562949953421312), by norm_num⟩
  | 6 => ⟨((151068441/562949953421312), (-290246523/562949953421312)), (13263/562949953421312), by norm_num⟩
  | 7 => ⟨((334070281/4503599627370496), (-424658463/9007199254740992)), (4431/562949953421312), by norm_num⟩
  | 8 => ⟨((822444271/72057594037927936), (-33570469/36028797018963968)), (338255/144115188075855872), by norm_num⟩
  | 9 => ⟨((712041189/576460752303423488), (133717305/288230376151711744)), (375299/576460752303423488), by norm_num⟩
  | 10 => ⟨((922702005/9223372036854775808), (218410485/2305843009213693952)), (26995/144115188075855872), by norm_num⟩
  | 11 => ⟨((423748259/73786976294838206464), (441707583/36893488147419103232)), (2680665/36893488147419103232), by norm_num⟩
  | 12 => ⟨((18495635/147573952589676412928), (1399511065/1180591620717411303424)), (55149033/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile039Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((236282857/268435456), (37005631/67108864)), (13349/1073741824), by norm_num⟩
  | 1 => ⟨((-362703997/134217728), (690437841/67108864)), (4267/134217728), by norm_num⟩
  | 2 => ⟨((5663061/2097152), (-126769343/33554432)), (11825/268435456), by norm_num⟩
  | 3 => ⟨((-37089165/33554432), (14068519/16777216)), (45441/1073741824), by norm_num⟩
  | 4 => ⟨((5207135/16777216), (-109937/1048576)), (67457/2147483648), by norm_num⟩
  | 5 => ⟨((-4360337/67108864), (-67495/67108864)), (325895/17179869184), by norm_num⟩
  | 6 => ⟨((351099/33554432), (546965/134217728)), (1333303/137438953472), by norm_num⟩
  | 7 => ⟨((-343323/268435456), (-78267/67108864)), (1189997/274877906944), by norm_num⟩
  | 8 => ⟨((56907/536870912), (116757/536870912)), (7612107/4398046511104), by norm_num⟩
  | 9 => ⟨((-4467/2147483648), (-33249/1073741824)), (22623831/35184372088832), by norm_num⟩
  | 10 => ⟨((-5087/4294967296), (14997/4294967296)), (68924083/281474976710656), by norm_num⟩
  | 11 => ⟨((4681/17179869184), (-5237/17179869184)), (255169941/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1333/34359738368), (607/34359738368)), (1336192167/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile039Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20405717/67108864), (-539476139/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-305346388561707/2251799813685248), (-1633099899445033/2251799813685248)), (8528455/281474976710656), by norm_num⟩
  | 1 => ⟨((333346497/4294967296), (891427165/2147483648)), (77/4294967296), by norm_num⟩
  | 2 => ⟨((-190795849/8589934592), (-1020443317/8589934592)), (23/4294967296), by norm_num⟩
  | 3 => ⟨((291212947/68719476736), (1557509283/68719476736)), (73/68719476736), by norm_num⟩
  | 4 => ⟨((-83340041/137438953472), (-27858241/8589934592)), (43/274877906944), by norm_num⟩
  | 5 => ⟨((152642937/2199023255552), (816388123/2199023255552)), (81/4398046511104), by norm_num⟩
  | 6 => ⟨((-232979909/35184372088832), (-1246058511/35184372088832)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((304798931/562949953421312), (815085953/281474976710656)), (43/281474976710656), by norm_num⟩
  | 8 => ⟨((-174456223/4503599627370496), (-466526625/2251799813685248)), (51/4503599627370496), by norm_num⟩
  | 9 => ⟨((44378945/18014398509481984), (237354209/18014398509481984)), (27/36028797018963968), by norm_num⟩
  | 10 => ⟨((-162566095/1152921504606846976), (-1738921323/2305843009213693952)), (51/1152921504606846976), by norm_num⟩
  | 11 => ⟨((270682571/36893488147419103232), (723852803/18446744073709551616)), (87/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-103286143/295147905179352825856), (-1104821249/590295810358705651712)), (17/147573952589676412928), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583579683441939/10141204801825835211973625643008), (-571727846779/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781498585375315/633825300114114700748351602688), (-2714349110911/633825300114114700748351602688)), (11559/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946406189088145/19807040628566084398385987584), (-3053551747333/39614081257132168796771975168)), (26011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892778742847833/2475880078570760549798248448), (-3244297173583/2475880078570760549798248448)), (13821/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443611074668119/38685626227668133590597632), (-3244182865841/154742504910672534362390528)), (27647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48518842156031/302231454903657293676544), (-3041299928167/9671406556917033397649408)), (25925/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261456279916093/604462909807314587353088), (-2661015864957/604462909807314587353088)), (22691/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236515688438475/9444732965739290427392), (-540490337189/9444732965739290427392)), (36883/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300788341265905/4722366482869645213696), (-3242742315313/4722366482869645213696)), (3459/590295810358705651712), by norm_num⟩
  | 9 => ⟨((203239171363599/73786976294838206464), (-4458445904991/590295810358705651712)), (38065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1829053241598835/73786976294838206464), (-5572569770149/73786976294838206464)), (11901/18446744073709551616), by norm_num⟩
  | 7 => ⟨((914464389834439/4611686018427387904), (-3134234903071/4611686018427387904)), (53587/9223372036854775808), by norm_num⟩
  | 6 => ⟨((800086100286725/576460752303423488), (-3133814872467/576460752303423488)), (13407/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199988091569605/144115188075855872), (-2741614737091/72057594037927936)), (46971/144115188075855872), by norm_num⟩
  | 4 => ⟨((749868481672743/18014398509481984), (-2055736849661/9007199254740992)), (70547/36028797018963968), by norm_num⟩
  | 3 => ⟨((749681071029123/4503599627370496), (-10275356490369/9007199254740992)), (11043/1125899906842624), by norm_num⟩
  | 2 => ⟨((1124048542989691/2251799813685248), (-10270348196127/2251799813685248)), (11073/281474976710656), by norm_num⟩
  | 1 => ⟨((561544409794225/562949953421312), (-7696471661233/562949953421312)), (133479/1125899906842624), by norm_num⟩
  | 0 => ⟨((1120141770016281/1125899906842624), (-480237841541/17592186044416)), (134685/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1120141770016281/1125899906842624), (-480237841541/17592186044416)), (513782503368186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((556787030291387/562949953421312), (-61156068324241/1125899906842624)), (550693/1125899906842624), by norm_num⟩
  | 2 => ⟨((1098061307400691/1125899906842624), (-60486559168551/562949953421312)), (574577/562949953421312), by norm_num⟩
  | 3 => ⟨((132239124034407/140737488355328), (-58990990084585/281474976710656)), (2488425/1125899906842624), by norm_num⟩
  | 4 => ⟨((472289278195529/562949953421312), (-443430784270499/1125899906842624)), (5719365/1125899906842624), by norm_num⟩
  | 5 => ⟨((617814944763375/1125899906842624), (-372018158559213/562949953421312)), (14101667/1125899906842624), by norm_num⟩
  | 6 => ⟨((-305346388561707/2251799813685248), (-1633099899445033/2251799813685248)), (8528455/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-20405717/67108864), (-539476139/67108864)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((286904673/2199023255552), (-240829139/8796093022208)), (563/4398046511104), by norm_num⟩
  | 1 => ⟨((40033257/549755813888), (741447647/8796093022208)), (377/1099511627776), by norm_num⟩
  | 2 => ⟨((-573641389/35184372088832), (726957919/17592186044416)), (16243/35184372088832), by norm_num⟩
  | 3 => ⟨((-195785159/17592186044416), (30110539/35184372088832)), (59219/140737488355328), by norm_num⟩
  | 4 => ⟨((-258331763/281474976710656), (-974461429/562949953421312)), (41079/140737488355328), by norm_num⟩
  | 5 => ⟨((23736567/140737488355328), (-835240053/4503599627370496)), (92307/562949953421312), by norm_num⟩
  | 6 => ⟨((370143047/18014398509481984), (419336837/36028797018963968)), (1397959/18014398509481984), by norm_num⟩
  | 7 => ⟨((-530600727/576460752303423488), (25606551/18014398509481984)), (4582639/144115188075855872), by norm_num⟩
  | 8 => ⟨((-588952811/9223372036854775808), (-68950771/576460752303423488)), (106282599/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1117772589/73786976294838206464), (-16279035/9223372036854775808)), (278169843/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-24131923/295147905179352825856), (1743603153/1180591620717411303424)), (1357053151/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-545609117/4722366482869645213696), (-162620911/4722366482869645213696)), (1670020649/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((27482771/4722366482869645213696), (-73777725/9444732965739290427392)), (1262685139/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1142959149/8796093022208), (420844623/8796093022208)), (18875/8796093022208), by norm_num⟩
  | 1 => ⟨((-58573561/1099511627776), (841482873/549755813888)), (5017/549755813888), by norm_num⟩
  | 2 => ⟨((-937092687/1099511627776), (-39710593/2199023255552)), (40923/2199023255552), by norm_num⟩
  | 3 => ⟨((5485693/2199023255552), (-1694292445/8796093022208)), (216843/8796093022208), by norm_num⟩
  | 4 => ⟨((1404350721/70368744177664), (1920323/35184372088832)), (1699719/70368744177664), by norm_num⟩
  | 5 => ⟨((55901643/2251799813685248), (393444381/1125899906842624)), (84603045/4503599627370496), by norm_num⟩
  | 6 => ⟨((1189874119/9007199254740992), (1478845/562949953421312)), (54600155/4503599627370496), by norm_num⟩
  | 7 => ⟨((220981/18014398509481984), (861375627/72057594037927936)), (965526923/144115188075855872), by norm_num⟩
  | 8 => ⟨((1698851/144115188075855872), (11199435/576460752303423488)), (467954553/144115188075855872), by norm_num⟩
  | 9 => ⟨((-376297/1152921504606846976), (64152557/1152921504606846976)), (812048899/576460752303423488), by norm_num⟩
  | 10 => ⟨((-5337757/2305843009213693952), (879489/2305843009213693952)), (1292204371/2305843009213693952), by norm_num⟩
  | 11 => ⟨((158441/9223372036854775808), (325535/9223372036854775808)), (985029577/4611686018427387904), by norm_num⟩
  | 12 => ⟨((24977/18446744073709551616), (632421/18446744073709551616)), (792254869/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((139521/1073741824), (51373/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-57201/1073741824), (1643521/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-915129/1073741824), (-9695/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((1339/536870912), (-206823/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21429/1073741824), (59/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((27/1073741824), (375/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((71/536870912), (3/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨39,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨39,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/524288)) (K:=(910873/536870912)) (L:=(152246777/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile039
