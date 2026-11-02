/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile038Gamma
public import XiRectangle.Tile038Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile038
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((188965781/8796093022208), (1765665571/8796093022208)), (447/2199023255552), by norm_num⟩
  | 1 => ⟨((-138009727/1099511627776), (14503269/68719476736)), (949/2199023255552), by norm_num⟩
  | 2 => ⟨((-1182705983/8796093022208), (250463965/4398046511104)), (4113/8796093022208), by norm_num⟩
  | 3 => ⟨((-485120037/8796093022208), (-217552519/17592186044416)), (3033/8796093022208), by norm_num⟩
  | 4 => ⟨((-381784685/35184372088832), (-827607873/70368744177664)), (6817/35184372088832), by norm_num⟩
  | 5 => ⟨((-159569233/281474976710656), (-490726273/140737488355328)), (24853/281474976710656), by norm_num⟩
  | 6 => ⟨((550165065/2251799813685248), (-1317157723/2251799813685248)), (1195/35184372088832), by norm_num⟩
  | 7 => ⟨((682785063/9007199254740992), (-521788173/9007199254740992)), (102219/9007199254740992), by norm_num⟩
  | 8 => ⟨((439444023/36028797018963968), (-151723751/72057594037927936)), (243267/72057594037927936), by norm_num⟩
  | 9 => ⟨((1581231443/1152921504606846976), (107667313/288230376151711744)), (133261/144115188075855872), by norm_num⟩
  | 10 => ⟨((1078622467/9223372036854775808), (838498077/9223372036854775808)), (584563/2305843009213693952), by norm_num⟩
  | 11 => ⟨((274006247/36893488147419103232), (898265881/73786976294838206464)), (6446519/73786976294838206464), by norm_num⟩
  | 12 => ⟨((39047277/147573952589676412928), (1477011093/1180591620717411303424)), (14680217/295147905179352825856), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile038Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((502878475/268435456), (40002673/33554432)), (6071/536870912), by norm_num⟩
  | 1 => ⟨((-222303539/67108864), (39651733/4194304)), (3889/134217728), by norm_num⟩
  | 2 => ⟨((191224579/67108864), (-56045055/16777216)), (10741/268435456), by norm_num⟩
  | 3 => ⟨((-37106995/33554432), (23266097/33554432)), (41217/1073741824), by norm_num⟩
  | 4 => ⟨((2503343/8388608), (-1190757/16777216)), (60833/2147483648), by norm_num⟩
  | 5 => ⟨((-4040341/67108864), (-450129/67108864)), (292615/17179869184), by norm_num⟩
  | 6 => ⟨((1247673/134217728), (633623/134217728)), (1195063/137438953472), by norm_num⟩
  | 7 => ⟨((-286651/268435456), (-160131/134217728)), (1061997/274877906944), by norm_num⟩
  | 8 => ⟨((81997/1073741824), (225043/1073741824)), (6784715/4398046511104), by norm_num⟩
  | 9 => ⟨((1211/1073741824), (-3827/134217728)), (40463533/70368744177664), by norm_num⟩
  | 10 => ⟨((-12263/8589934592), (13175/4294967296)), (62632627/281474976710656), by norm_num⟩
  | 11 => ⟨((4787/17179869184), (-2153/8589934592)), (241014165/2251799813685248), by norm_num⟩
  | 12 => ⟨((-2545/68719476736), (849/68719476736)), (1305783463/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile038Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-21606053/67108864), (-267622477/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-198263510606085/2251799813685248), (-809930029475755/1125899906842624)), (66018957/2251799813685248), by norm_num⟩
  | 1 => ⟨((108222087/2147483648), (1768400403/4294967296)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((-123885057/8589934592), (-253042599/2147483648)), (11/2147483648), by norm_num⟩
  | 3 => ⟨((94543285/34359738368), (772441135/34359738368)), (35/34359738368), by norm_num⟩
  | 4 => ⟨((-27056631/68719476736), (-1768472905/549755813888)), (83/549755813888), by norm_num⟩
  | 5 => ⟨((99112109/2199023255552), (809769515/2199023255552)), (79/4398046511104), by norm_num⟩
  | 6 => ⟨((-75637729/17592186044416), (-617978243/17592186044416)), (63/35184372088832), by norm_num⟩
  | 7 => ⟨((197908043/562949953421312), (1616955803/562949953421312)), (85/562949953421312), by norm_num⟩
  | 8 => ⟨((-56637813/2251799813685248), (-57843051/281474976710656)), (25/2251799813685248), by norm_num⟩
  | 9 => ⟨((230524435/144115188075855872), (1883439479/144115188075855872)), (105/144115188075855872), by norm_num⟩
  | 10 => ⟨((-26388821/288230376151711744), (-107801473/144115188075855872)), (99/2305843009213693952), by norm_num⟩
  | 11 => ⟨((21969507/4611686018427387904), (717984395/18446744073709551616)), (85/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-134128807/590295810358705651712), (-273966065/147573952589676412928)), (67/590295810358705651712), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583556384408621/10141204801825835211973625643008), (-2204782283027/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781471208579023/633825300114114700748351602688), (-2616792552317/633825300114114700748351602688)), (23115/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892781597393889/39614081257132168796771975168), (-2943799600903/39614081257132168796771975168)), (3251/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((946373029920189/1237940039285380274899124224), (-3127683514497/2475880078570760549798248448)), (27639/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774411639936665/154742504910672534362390528), (-390945869883/19342813113834066795298816)), (6911/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552572357216177/9671406556917033397649408), (-2931970134319/9671406556917033397649408)), (12961/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261429537898695/604462909807314587353088), (-641337480471/151115727451828646838272)), (22687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((473020525019817/18889465931478580854784), (-4168461106337/75557863725914323419136)), (36877/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325188956999761/1180591620717411303424), (-3126142259009/4722366482869645213696)), (6917/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812934366954469/295147905179352825856), (-2149057290673/295147905179352825856)), (19029/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828997548457219/73786976294838206464), (-671518287567/9223372036854775808)), (47595/73786976294838206464), by norm_num⟩
  | 7 => ⟨((457216566662573/2305843009213693952), (-6042980682819/9223372036854775808)), (53575/9223372036854775808), by norm_num⟩
  | 6 => ⟨((100006866546867/72057594037927936), (-1510531213467/288230376151711744)), (53615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199933747051499/144115188075855872), (-330368446101/9007199254740992)), (46957/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499655845180785/36028797018963968), (-3963455617237/18014398509481984)), (17631/9007199254740992), by norm_num⟩
  | 3 => ⟨((749630720913571/4503599627370496), (-9905251653509/9007199254740992)), (88309/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123948888773681/2251799813685248), (-9900155955277/2251799813685248)), (88541/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122941952598929/1125899906842624), (-14837443599553/1125899906842624)), (8337/70368744177664), by norm_num⟩
  | 0 => ⟨((1119858489047749/1125899906842624), (-14811709912665/562949953421312)), (134555/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1119858489047749/1125899906842624), (-14811709912665/562949953421312)), (513286592723655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1113070070326713/1125899906842624), (-58928929586737/1125899906842624)), (274747/562949953421312), by norm_num⟩
  | 2 => ⟨((274325531782721/281474976710656), (-116514847191573/1125899906842624)), (571993/562949953421312), by norm_num⟩
  | 3 => ⟨((1057373076731493/1125899906842624), (-227110756273495/1125899906842624)), (308329/140737488355328), by norm_num⟩
  | 4 => ⟨((947205449880699/1125899906842624), (-426575750935359/1125899906842624)), (5628119/1125899906842624), by norm_num⟩
  | 5 => ⟨((317626499767357/562949953421312), (-717745642605159/1125899906842624)), (3433611/281474976710656), by norm_num⟩
  | 6 => ⟨((-198263510606085/2251799813685248), (-809930029475755/1125899906842624)), (66018957/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-21606053/67108864), (-267622477/33554432)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1253515565/8796093022208), (-145697937/4398046511104)), (751/4398046511104), by norm_num⟩
  | 1 => ⟨((715179597/8796093022208), (797565331/8796093022208)), (4013/8796093022208), by norm_num⟩
  | 2 => ⟨((-300377105/17592186044416), (795843171/17592186044416)), (10845/17592186044416), by norm_num⟩
  | 3 => ⟨((-847157137/70368744177664), (148204303/140737488355328)), (39683/70368744177664), by norm_num⟩
  | 4 => ⟨((-140149899/140737488355328), (-1045410693/562949953421312)), (220921/562949953421312), by norm_num⟩
  | 5 => ⟨((406755621/2251799813685248), (-887454601/4503599627370496)), (995193/4503599627370496), by norm_num⟩
  | 6 => ⟨((772362725/36028797018963968), (457954375/36028797018963968)), (1886841/18014398509481984), by norm_num⟩
  | 7 => ⟨((-75553043/72057594037927936), (832730977/576460752303423488)), (12381591/288230376151711744), by norm_num⟩
  | 8 => ⟨((-70117217/1152921504606846976), (-313258449/2305843009213693952)), (71795811/4611686018427387904), by norm_num⟩
  | 9 => ⟨((620105205/36893488147419103232), (-84506549/73786976294838206464)), (187483065/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-101146285/590295810358705651712), (949235965/590295810358705651712)), (1810255077/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-584147077/4722366482869645213696), (-216888615/4722366482869645213696)), (2146106751/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((2086051/295147905179352825856), (-77079745/9444732965739290427392)), (736493767/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((673922623/2199023255552), (474257531/4398046511104)), (5519/2199023255552), by norm_num⟩
  | 1 => ⟨((-31520011/274877906944), (1895299491/1099511627776)), (5835/549755813888), by norm_num⟩
  | 2 => ⟨((-504147469/549755813888), (-83061361/2199023255552)), (47251/2199023255552), by norm_num⟩
  | 3 => ⟨((44257055/8796093022208), (-1771916887/8796093022208)), (248993/8796093022208), by norm_num⟩
  | 4 => ⟨((1416604609/70368744177664), (2849585/35184372088832)), (1941067/70368744177664), by norm_num⟩
  | 5 => ⟨((119403243/2251799813685248), (585028841/2251799813685248)), (96076649/4503599627370496), by norm_num⟩
  | 6 => ⟨((1273081393/9007199254740992), (47066345/9007199254740992)), (15420679/1125899906842624), by norm_num⟩
  | 7 => ⟨((5526971/144115188075855872), (53708669/4503599627370496)), (1085331227/144115188075855872), by norm_num⟩
  | 8 => ⟨((20725949/288230376151711744), (10198599/288230376151711744)), (261676529/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1811591/1152921504606846976), (68228313/1152921504606846976)), (1807352587/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-611759/288230376151711744), (408101/2305843009213693952)), (357801437/576460752303423488), by norm_num⟩
  | 11 => ⟨((-11617/4611686018427387904), (600517/4611686018427387904)), (1086275477/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-180667/18446744073709551616), (161067/18446744073709551616)), (1741037983/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((41133/134217728), (57893/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-123125/1073741824), (925439/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-984663/1073741824), (-40557/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((2701/536870912), (-108149/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((1351/67108864), (87/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((57/1073741824), (279/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((19/134217728), (3/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨38,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨38,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(87353/1048576)) (K:=(1074807/536870912)) (L:=(357212407/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile038
