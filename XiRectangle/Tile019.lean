/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile019Gamma
public import XiRectangle.Tile019Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile019
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2884381561/274877906944), (-695817143/549755813888)), (769/2199023255552), by norm_num⟩
  | 1 => ⟨((-15124461079/2199023255552), (-4462263207/549755813888)), (1919/2199023255552), by norm_num⟩
  | 2 => ⟨((316868923/2199023255552), (-22263550313/4398046511104)), (1137/1099511627776), by norm_num⟩
  | 3 => ⟨((8816272221/8796093022208), (-2464820343/2199023255552)), (7151/8796093022208), by norm_num⟩
  | 4 => ⟨((21397417613/70368744177664), (-4275649641/70368744177664)), (33943/70368744177664), by norm_num⟩
  | 5 => ⟨((25281931529/562949953421312), (2223910265/140737488355328)), (130277/562949953421312), by norm_num⟩
  | 6 => ⟨((10468672761/2251799813685248), (4424529063/1125899906842624)), (211003/2251799813685248), by norm_num⟩
  | 7 => ⟨((8039507049/18014398509481984), (5654340607/9007199254740992)), (74229/2251799813685248), by norm_num⟩
  | 8 => ⟨((7929731895/288230376151711744), (25984505681/288230376151711744)), (1485013/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1482368333/2305843009213693952), (21867216435/2305843009213693952)), (3370831/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-4125743417/18446744073709551616), (14326518101/18446744073709551616)), (14378963/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-8320207747/295147905179352825856), (21354864867/295147905179352825856)), (63425861/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-11432265797/2361183241434822606848), (6828168155/1180591620717411303424)), (92656637/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile019Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-622471501/268435456), (12181340249/1073741824)), (63/268435456), by norm_num⟩
  | 1 => ⟨((12179231057/4294967296), (-1234616841/1073741824)), (509/1073741824), by norm_num⟩
  | 2 => ⟨((-1522744975/2147483648), (178378459/2147483648)), (10719/17179869184), by norm_num⟩
  | 3 => ⟨((335076533/2147483648), (137840773/2147483648)), (82551/137438953472), by norm_num⟩
  | 4 => ⟨((-20760345/1073741824), (-56254209/2147483648)), (127085/274877906944), by norm_num⟩
  | 5 => ⟨((1794519/4294967296), (23289271/4294967296)), (1342155/4398046511104), by norm_num⟩
  | 6 => ⟨((1618527/4294967296), (-191997/268435456)), (821963/4398046511104), by norm_num⟩
  | 7 => ⟨((-50583/536870912), (936651/17179869184)), (8195245/70368744177664), by norm_num⟩
  | 8 => ⟨((115523/8589934592), (8091/17179869184)), (185111957/2251799813685248), by norm_num⟩
  | 9 => ⟨((-87983/68719476736), (-59187/68719476736)), (152933781/2251799813685248), by norm_num⟩
  | 10 => ⟨((9355/137438953472), (41441/274877906944)), (9011291445/144115188075855872), by norm_num⟩
  | 11 => ⟨((2337/1099511627776), (-18193/1099511627776)), (8753866037/144115188075855872), by norm_num⟩
  | 12 => ⟨((-2193/2199023255552), (1365/1099511627776)), (8675878197/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile019Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5499/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5499/640))
  have he : value ((3/4), (5499/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1843716533/4294967296), (-660064923/134217728)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((299091017476595/2251799813685248), (179380456914321/281474976710656)), (1676611/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2612140093/34359738368), (-25066182857/68719476736)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((1495097415/68719476736), (448343885/4294967296)), (21/137438953472), by norm_num⟩
  | 3 => ⟨((-4563953849/1099511627776), (-21897926157/1099511627776)), (35/1099511627776), by norm_num⟩
  | 4 => ⟨((5224494369/8796093022208), (12533605255/4398046511104)), (43/8796093022208), by norm_num⟩
  | 5 => ⟨((-2392253937/35184372088832), (-22956148021/70368744177664)), (21/35184372088832), by norm_num⟩
  | 6 => ⟨((28525881/4398046511104), (273735299/8796093022208)), (17/281474976710656), by norm_num⟩
  | 7 => ⟨((-2388438199/4503599627370496), (-11459766037/4503599627370496)), (47/9007199254740992), by norm_num⟩
  | 8 => ⟨((2734116587/72057594037927936), (26236673335/144115188075855872)), (7/18014398509481984), by norm_num⟩
  | 9 => ⟨((-5564133277/2305843009213693952), (-6674200905/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 10 => ⟨((5095543721/36893488147419103232), (191003931/288230376151711744)), (29/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-4242197223/590295810358705651712), (-20354132539/590295810358705651712)), (51/590295810358705651712), by norm_num⟩
  | 12 => ⟨((3237446629/9444732965739290427392), (15533322545/9444732965739290427392)), (41/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086617/5070602400912917605986812821504), (1778479653505/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445326644630095/158456325028528675187087900672), (2110453466361/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236574559255079/4951760157141521099596496896), (1187082365247/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892549468302495/2475880078570760549798248448), (630609770925/618970019642690137449562112)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1774215163178533/154742504910672534362390528), (1261157125795/77371252455336267181195264)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1552388282204015/9671406556917033397649408), (591134239057/2417851639229258349412352)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261268594206129/604462909807314587353088), (1034418579491/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891820795210381/75557863725914323419136), (210100722725/4722366482869645213696)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325140012347053/1180591620717411303424), (1260495453207/2361183241434822606848)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812799931681651/295147905179352825856), (3466008534253/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828661947802793/73786976294838206464), (1082994891015/18446744073709551616)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228561173275169/1152921504606846976), (2436373240491/4611686018427387904)), (1673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599733822064937/1152921504606846976), (2435916464565/576460752303423488)), (837/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199605652055381/144115188075855872), (1065456382447/36028797018963968)), (733/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499165587063141/36028797018963968), (3195340193067/18014398509481984)), (2201/36028797018963968), by norm_num⟩
  | 3 => ⟨((749325958046215/4503599627370496), (1996186531595/2251799813685248)), (2755/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123344306903315/2251799813685248), (249354174001/70368744177664)), (2761/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122047434140277/1125899906842624), (11955447911815/1125899906842624)), (4155/1125899906842624), by norm_num⟩
  | 0 => ⟨((1118118837239615/1125899906842624), (23856560111303/1125899906842624)), (8369/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118118837239615/1125899906842624), (23856560111303/1125899906842624)), (31925205710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1109886048604491/1125899906842624), (23691687946747/562949953421312)), (8489/562949953421312), by norm_num⟩
  | 2 => ⟨((546052916916929/562949953421312), (93418868800603/1125899906842624)), (34903/1125899906842624), by norm_num⟩
  | 3 => ⟨((525787443470965/562949953421312), (181229771824751/1125899906842624)), (2297/35184372088832), by norm_num⟩
  | 4 => ⟨((476492406709675/562949953421312), (169266091647135/562949953421312)), (160967/1125899906842624), by norm_num⟩
  | 5 => ⟨((704837091342661/1125899906842624), (286540595280669/562949953421312)), (369291/1125899906842624), by norm_num⟩
  | 6 => ⟨((299091017476595/2251799813685248), (179380456914321/281474976710656)), (1676611/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-1843716533/4294967296), (-660064923/134217728)), (1/2147483648), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-1291157857/2199023255552), (-1884390327/274877906944)), (153/549755813888), by norm_num⟩
  | 1 => ⟨((20210224611/4398046511104), (-1690461621/1099511627776)), (927/1099511627776), by norm_num⟩
  | 2 => ⟨((6255633083/8796093022208), (12511276209/8796093022208)), (10889/8796093022208), by norm_num⟩
  | 3 => ⟨((-20686446673/70368744177664), (9980820639/70368744177664)), (84941/70368744177664), by norm_num⟩
  | 4 => ⟨((-2844408959/281474976710656), (-7001723489/140737488355328)), (498245/562949953421312), by norm_num⟩
  | 5 => ⟨((16568009743/2251799813685248), (2133988207/1125899906842624)), (1175897/2251799813685248), by norm_num⟩
  | 6 => ⟨((-13687300985/18014398509481984), (15811807427/18014398509481984)), (4660191/18014398509481984), by norm_num⟩
  | 7 => ⟨((-9629432527/144115188075855872), (-21647963829/144115188075855872)), (15963925/144115188075855872), by norm_num⟩
  | 8 => ⟨((12525506683/576460752303423488), (1135397255/1152921504606846976)), (48291269/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-100270539/72057594037927936), (2779422625/1152921504606846976)), (8202613/576460752303423488), by norm_num⟩
  | 10 => ⟨((-6887377865/36893488147419103232), (-10685197151/36893488147419103232)), (40741371/9223372036854775808), by norm_num⟩
  | 11 => ⟨((24200552603/590295810358705651712), (-2441451925/590295810358705651712)), (189890649/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-8138105921/4722366482869645213696), (21102549561/4722366482869645213696)), (1778886369/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21752206813/274877906944), (2538704271/274877906944)), (1527/274877906944), by norm_num⟩
  | 1 => ⟨((-758996357/274877906944), (20304033429/549755813888)), (9675/549755813888), by norm_num⟩
  | 2 => ⟨((-12175562935/2199023255552), (-270066887/4398046511104)), (7847/274877906944), by norm_num⟩
  | 3 => ⟨((-8098300933/140737488355328), (-11783830185/140737488355328)), (2221293/70368744177664), by norm_num⟩
  | 4 => ⟨((-16229394341/281474976710656), (-784007929/140737488355328)), (3766035/140737488355328), by norm_num⟩
  | 5 => ⟨((-314673775/1125899906842624), (-20204928983/4503599627370496)), (41933027/2251799813685248), by norm_num⟩
  | 6 => ⟨((-13406920523/72057594037927936), (-2154029345/36028797018963968)), (50427827/4503599627370496), by norm_num⟩
  | 7 => ⟨((138490797/288230376151711744), (-2477075511/72057594037927936)), (882614051/144115188075855872), by norm_num⟩
  | 8 => ⟨((2283644133/9223372036854775808), (-1465828603/4611686018427387904)), (1887737277/576460752303423488), by norm_num⟩
  | 9 => ⟨((51403595/4611686018427387904), (-1313930261/9223372036854775808)), (4380541271/2305843009213693952), by norm_num⟩
  | 10 => ⟨((662247/144115188075855872), (-9243789/9223372036854775808)), (24231191809/18446744073709551616), by norm_num⟩
  | 11 => ⟨((711357/18446744073709551616), (-854155/2305843009213693952)), (10040094957/9223372036854775808), by norm_num⟩
  | 12 => ⟨((537363/18446744073709551616), (-22151/4611686018427387904)), (18627343953/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((42484779/536870912), (4958407/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1482415/536870912), (39656315/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-5945099/1073741824), (-32967/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-61785/1073741824), (-5619/67108864)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-30955/536870912), (-5981/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-75/268435456), (-4817/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-25/134217728), (-1/16777216)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (-37/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨19,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨19,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(43716471/536870912)) (L:=(5474963029/68719476736)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile019
