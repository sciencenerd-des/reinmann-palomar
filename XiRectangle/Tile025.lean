/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile025Gamma
public import XiRectangle.Tile025Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile025
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1839355173/2199023255552), (-1370340379/1099511627776)), (973/2199023255552), by norm_num⟩
  | 1 => ⟨((3550906179/2199023255552), (-1065449581/2199023255552)), (2265/2199023255552), by norm_num⟩
  | 2 => ⟨((3732569499/4398046511104), (1511117011/4398046511104)), (2567/2199023255552), by norm_num⟩
  | 3 => ⟨((2829428971/17592186044416), (303475889/1099511627776)), (15529/17592186044416), by norm_num⟩
  | 4 => ⟨((-295432713/35184372088832), (5619484659/70368744177664)), (35545/70368744177664), by norm_num⟩
  | 5 => ⟨((-701072789/70368744177664), (3339972701/281474976710656)), (32907/140737488355328), by norm_num⟩
  | 6 => ⟨((-5109814887/2251799813685248), (888570803/1125899906842624)), (102801/1125899906842624), by norm_num⟩
  | 7 => ⟨((-5602747843/18014398509481984), (-45338007/1125899906842624)), (278975/9007199254740992), by norm_num⟩
  | 8 => ⟨((-2284421451/72057594037927936), (-2583276893/144115188075855872)), (1345261/144115188075855872), by norm_num⟩
  | 9 => ⟨((-186761559/72057594037927936), (-1706929459/576460752303423488)), (2946537/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1398397991/9223372036854775808), (-211036537/576460752303423488)), (6096529/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-410527783/147573952589676412928), (-5354759813/147573952589676412928)), (26738403/147573952589676412928), by norm_num⟩
  | 12 => ⟨((1453097311/2361183241434822606848), (-7102551389/2361183241434822606848)), (82410695/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile025Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((728635421/134217728), (4007168559/268435456)), (31/16777216), by norm_num⟩
  | 1 => ⟨((-565449961/268435456), (-2074148281/536870912)), (4781/1073741824), by norm_num⟩
  | 2 => ⟨((151837523/268435456), (481741225/268435456)), (13265/2147483648), by norm_num⟩
  | 3 => ⟨((13898819/268435456), (-16883379/33554432)), (12849/2147483648), by norm_num⟩
  | 4 => ⟨((-7430917/134217728), (25068153/268435456)), (76807/17179869184), by norm_num⟩
  | 5 => ⟨((8834457/536870912), (-1471807/134217728)), (747629/274877906944), by norm_num⟩
  | 6 => ⟨((-842311/268435456), (110811/268435456)), (1563059/1099511627776), by norm_num⟩
  | 7 => ⟨((461897/1073741824), (159293/1073741824)), (2922187/4398046511104), by norm_num⟩
  | 8 => ⟨((-178761/4294967296), (-91859/2147483648)), (20901037/70368744177664), by norm_num⟩
  | 9 => ⟨((4609/2147483648), (29617/4294967296)), (40153779/281474976710656), by norm_num⟩
  | 10 => ⟨((2373/17179869184), (-27531/34359738368)), (194221461/2251799813685248), by norm_num⟩
  | 11 => ⟨((-7095/137438953472), (9409/137438953472)), (1217047719/18014398509481984), by norm_num⟩
  | 12 => ⟨((1057/137438953472), (-1005/274877906944)), (4468421275/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile025Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-384107611/1073741824), (-3452647289/536870912)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((1557416983513349/2251799813685248), (-231990827718253/2251799813685248)), (5093445/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3400462657/8589934592), (506528537/8589934592)), (25/17179869184), by norm_num⟩
  | 2 => ⟨((3892611229/34359738368), (-289919177/17179869184)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-5941317877/274877906944), (885011057/274877906944)), (27/274877906944), by norm_num⟩
  | 4 => ⟨((3400602067/1099511627776), (-506549303/1099511627776)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((-6228433305/17592186044416), (927779401/17592186044416)), (33/17592186044416), by norm_num⟩
  | 6 => ⟨((1188312291/35184372088832), (-44252367/8796093022208)), (27/140737488355328), by norm_num⟩
  | 7 => ⟨((-6218498711/2251799813685248), (926299557/2251799813685248)), (19/1125899906842624), by norm_num⟩
  | 8 => ⟨((7118501319/36028797018963968), (-530181393/18014398509481984)), (23/18014398509481984), by norm_num⟩
  | 9 => ⟨((-3621671645/288230376151711744), (1078959085/576460752303423488)), (49/576460752303423488), by norm_num⟩
  | 10 => ⟨((6633337229/9223372036854775808), (-123511671/1152921504606846976)), (47/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-2761228861/73786976294838206464), (205654547/36893488147419103232)), (41/147573952589676412928), by norm_num⟩
  | 12 => ⟨((2107240799/1180591620717411303424), (-313891875/1180591620717411303424)), (33/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893164321/5070602400912917605986812821504), (-48154757865/2535301200456458802993406410752)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1781419520793407/633825300114114700748351602688), (-57150129829/158456325028528675187087900672)), (1081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59147614786751/1237940039285380274899124224), (-64291809863/9903520314283042199192993792)), (19/154742504910672534362390528), by norm_num⟩
  | 15 => ⟨((1892684785631155/2475880078570760549798248448), (-68307552951/618970019642690137449562112)), (323/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1774350669764311/154742504910672534362390528), (-273218984721/154742504910672534362390528)), (5169/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552515520686809/9671406556917033397649408), (-256130870017/9671406556917033397649408)), (2423/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315345032226691/151115727451828646838272), (-224102583799/604462909807314587353088)), (265/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((946001207981041/37778931862957161709568), (-91036084037/18889465931478580854784)), (6889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300696594642569/4722366482869645213696), (-273088686375/4722366482869645213696)), (5167/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625788148713923/590295810358705651712), (-187732576103/295147905179352825856)), (7105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457224526929391/18446744073709551616), (-58660469719/9223372036854775808)), (4441/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114297260637301/576460752303423488), (-263939335939/4611686018427387904)), (9993/9223372036854775808), by norm_num⟩
  | 6 => ⟨((800000992828431/576460752303423488), (-527796739165/1152921504606846976)), (9993/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599920923266157/72057594037927936), (-461729988659/144115188075855872)), (8745/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499522979666035/36028797018963968), (-346205353621/18014398509481984)), (6559/18014398509481984), by norm_num⟩
  | 3 => ⟨((749552039695885/4503599627370496), (-216297748135/2251799813685248)), (1025/562949953421312), by norm_num⟩
  | 2 => ⟨((561902298001663/1125899906842624), (-1729415174621/4503599627370496)), (32807/4503599627370496), by norm_num⟩
  | 1 => ⟨((561379077107617/562949953421312), (-1295853504807/1125899906842624)), (49229/2251799813685248), by norm_num⟩
  | 0 => ⟨((2239242509033915/2251799813685248), (-5173758649353/2251799813685248)), (98533/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((2239242509033915/2251799813685248), (-5173758649353/2251799813685248)), (375873574263762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1113371671853867/1125899906842624), (-5144906855709/1125899906842624)), (196421/2251799813685248), by norm_num⟩
  | 2 => ⟨((275239833063017/281474976710656), (-20350631570925/2251799813685248)), (390267/2251799813685248), by norm_num⟩
  | 3 => ⟨((1076479273917373/1125899906842624), (-39799661779997/2251799813685248)), (770299/2251799813685248), by norm_num⟩
  | 4 => ⟨((2057752410963019/2251799813685248), (-19026340953893/562949953421312)), (1500205/2251799813685248), by norm_num⟩
  | 5 => ⟨((1877854742115045/2251799813685248), (-69547032967559/1125899906842624)), (2843259/2251799813685248), by norm_num⟩
  | 6 => ⟨((1557416983513349/2251799813685248), (-231990827718253/2251799813685248)), (5093445/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-384107611/1073741824), (-3452647289/536870912)), (3/1073741824), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((989799437/2199023255552), (-4170083201/4398046511104)), (49/137438953472), by norm_num⟩
  | 1 => ⟨((889813289/1099511627776), (181349675/4398046511104)), (9039/8796093022208), by norm_num⟩
  | 2 => ⟨((751590845/8796093022208), (4959421027/17592186044416)), (25693/17592186044416), by norm_num⟩
  | 3 => ⟨((-1965382193/35184372088832), (1261319679/35184372088832)), (48603/35184372088832), by norm_num⟩
  | 4 => ⟨((-3888887705/562949953421312), (-4304997927/562949953421312)), (553729/562949953421312), by norm_num⟩
  | 5 => ⟨((2062631253/2251799813685248), (-3471655499/4503599627370496)), (317401/562949953421312), by norm_num⟩
  | 6 => ⟨((1673396925/36028797018963968), (4240207091/36028797018963968)), (2443709/9007199254740992), by norm_num⟩
  | 7 => ⟨((-2199126285/144115188075855872), (-54937993/72057594037927936)), (32514461/288230376151711744), by norm_num⟩
  | 8 => ⟨((1568300131/2305843009213693952), (-978001321/576460752303423488)), (95475699/2305843009213693952), by norm_num⟩
  | 9 => ⟨((2737070785/18446744073709551616), (2361844897/18446744073709551616)), (125911561/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-5263031497/295147905179352825856), (677262353/73786976294838206464)), (1214336703/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-23913635/147573952589676412928), (-2394847591/1180591620717411303424)), (1378016353/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((3612427563/18889465931478580854784), (286358335/4722366482869645213696)), (6376582823/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71286333/4294967296), (432051185/274877906944)), (1353/137438953472), by norm_num⟩
  | 1 => ⟨((-458188555/549755813888), (6906588337/549755813888)), (8479/274877906944), by norm_num⟩
  | 2 => ⟨((-7330815143/2199023255552), (-149564609/1099511627776)), (109533/2199023255552), by norm_num⟩
  | 3 => ⟨((6440065/8796093022208), (-6387510955/17592186044416)), (120699/2199023255552), by norm_num⟩
  | 4 => ⟨((3303469/2199023255552), (-2339302843/1125899906842624)), (104449513/2251799813685248), by norm_num⟩
  | 5 => ⟨((50703511/281474976710656), (-7488949569/2251799813685248)), (18026237/562949953421312), by norm_num⟩
  | 6 => ⟨((542069719/2251799813685248), (-114702415/18014398509481984)), (338914987/18014398509481984), by norm_num⟩
  | 7 => ⟨((228653955/144115188075855872), (-4158705979/576460752303423488)), (2792267729/288230376151711744), by norm_num⟩
  | 8 => ⟨((1836940983/1152921504606846976), (8080857/288230376151711744)), (5174237415/1152921504606846976), by norm_num⟩
  | 9 => ⟨((994869/144115188075855872), (36958011/1152921504606846976)), (4458017319/2305843009213693952), by norm_num⟩
  | 10 => ⟨((2819225/576460752303423488), (-201763/2305843009213693952)), (7599462839/9223372036854775808), by norm_num⟩
  | 11 => ⟨((403085/4611686018427387904), (6916863/18446744073709551616)), (7203818749/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-259625/9223372036854775808), (-23565/1152921504606846976)), (4361529479/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17821583/1073741824), (421925/268435456)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-894899/1073741824), (6744715/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-894875/268435456), (-146059/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((393/536870912), (-389863/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((1613/1073741824), (-2231/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((193/1073741824), (-3571/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((129/536870912), (-7/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/536870912), (-1/134217728)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨25,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨25,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(17685827/1073741824)) (L:=(18330948653/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile025
