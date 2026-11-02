/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile030Gamma
public import XiRectangle.Tile030Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile030
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((275215617/274877906944), (-44606455/2199023255552)), (929/4398046511104), by norm_num⟩
  | 1 => ⟨((1013318869/1099511627776), (3038867445/4398046511104)), (283/549755813888), by norm_num⟩
  | 2 => ⟨((1543863927/8796093022208), (5446835169/8796093022208)), (2653/4398046511104), by norm_num⟩
  | 3 => ⟨((-1433030093/17592186044416), (3829524671/17592186044416)), (8199/17592186044416), by norm_num⟩
  | 4 => ⟨((-3533363611/70368744177664), (1213774007/35184372088832)), (1189/4398046511104), by norm_num⟩
  | 5 => ⟨((-869679641/70368744177664), (82270801/281474976710656)), (17763/140737488355328), by norm_num⟩
  | 6 => ⟨((-3988760519/2251799813685248), (-2236367435/2251799813685248)), (27877/562949953421312), by norm_num⟩
  | 7 => ⟨((-2773328415/18014398509481984), (-4229818597/18014398509481984)), (303101/18014398509481984), by norm_num⟩
  | 8 => ⟨((-786995413/144115188075855872), (-4836389817/144115188075855872)), (365415/72057594037927936), by norm_num⟩
  | 9 => ⟨((885582387/1152921504606846976), (-2110233185/576460752303423488)), (1607001/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1822061977/9223372036854775808), (-187790677/576460752303423488)), (427971/1152921504606846976), by norm_num⟩
  | 11 => ⟨((4038060253/147573952589676412928), (-3430396965/147573952589676412928)), (8442629/73786976294838206464), by norm_num⟩
  | 12 => ⟨((424368453/147573952589676412928), (-1452056145/1180591620717411303424)), (65510293/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile030Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1845198995/268435456), (3057291071/268435456)), (335/268435456), by norm_num⟩
  | 1 => ⟨((-2219412193/536870912), (-265063095/268435456)), (749/268435456), by norm_num⟩
  | 2 => ⟨((950130755/536870912), (546624901/536870912)), (7949/2147483648), by norm_num⟩
  | 3 => ⟨((-745715/2097152), (-116949693/268435456)), (7513/2147483648), by norm_num⟩
  | 4 => ⟨((2411327/67108864), (63205431/536870912)), (44199/17179869184), by norm_num⟩
  | 5 => ⟨((2659193/1073741824), (-12156591/536870912)), (430957/274877906944), by norm_num⟩
  | 6 => ⟨((-995569/536870912), (6862025/2147483648)), (906675/1099511627776), by norm_num⟩
  | 7 => ⟨((469777/1073741824), (-670093/2147483648)), (1749707/4398046511104), by norm_num⟩
  | 8 => ⟨((-601075/8589934592), (114087/8589934592)), (13454509/70368744177664), by norm_num⟩
  | 9 => ⟨((36219/4294967296), (36915/17179869184)), (29782707/281474976710656), by norm_num⟩
  | 10 => ⟨((-26197/34359738368), (-21645/34359738368)), (167581077/2251799813685248), by norm_num⟩
  | 11 => ⟨((1529/34359738368), (26223/274877906944)), (1156426919/18014398509481984), by norm_num⟩
  | 12 => ⟨((109/1099511627776), (-5795/549755813888)), (4403606171/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile030Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (1551/128))
  have he : value ((7/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-3723443155/536870912)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((1084513434899015/2251799813685248), (-207084946246983/562949953421312)), (6533677/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4735851061/17179869184), (3617192487/17179869184)), (1/536870912), by norm_num⟩
  | 2 => ⟨((1355317561/17179869184), (-2070354171/34359738368)), (5/8589934592), by norm_num⟩
  | 3 => ⟨((-4137260045/274877906944), (1579997529/137438953472)), (33/274877906944), by norm_num⟩
  | 4 => ⟨((4736045219/2199023255552), (-1808670391/1099511627776)), (41/2199023255552), by norm_num⟩
  | 5 => ⟨((-2168597001/8796093022208), (207043905/1099511627776)), (5/2199023255552), by norm_num⟩
  | 6 => ⟨((1654971865/70368744177664), (-316012461/17592186044416)), (33/140737488355328), by norm_num⟩
  | 7 => ⟨((-4330276009/2251799813685248), (3307418591/2251799813685248)), (45/2251799813685248), by norm_num⟩
  | 8 => ⟨((619624545/4503599627370496), (-1893050453/18014398509481984)), (7/4503599627370496), by norm_num⟩
  | 9 => ⟨((-2521965279/288230376151711744), (1926250159/288230376151711744)), (15/144115188075855872), by norm_num⟩
  | 10 => ⟨((4619150441/9223372036854775808), (-3528057799/9223372036854775808)), (57/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-961396283/36893488147419103232), (1468608437/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 12 => ⟨((2934770819/2361183241434822606848), (-17512083/18446744073709551616)), (5/295147905179352825856), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-849651927257/10141204801825835211973625643008)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((111324863925199/39614081257132168796771975168), (-252032641439/158456325028528675187087900672)), (541/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1892474241282765/39614081257132168796771975168), (-567047603915/19807040628566084398385987584)), (1217/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473104934455567/618970019642690137449562112), (-1204914508673/2475880078570760549798248448)), (5173/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774085592235997/154742504910672534362390528), (-1204845154631/154742504910672534362390528)), (5173/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552266978933291/9671406556917033397649408), (-564734323131/4835703278458516698824704)), (4851/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630581311654323/302231454903657293676544), (-30881605689/18889465931478580854784)), (4245/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472912227549443/18889465931478580854784), (-200713168161/9444732965739290427392)), (3449/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300431413562621/4722366482869645213696), (-1204158133139/4722366482869645213696)), (5175/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406355860162989/147573952589676412928), (-827760510451/295147905179352825856)), (7115/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828442096572875/73786976294838206464), (-1034553338617/36893488147419103232)), (139/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1828242984395121/9223372036854775808), (-290917496233/1152921504606846976)), (5005/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599488583393023/1152921504606846976), (-581708428633/288230376151711744)), (10013/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199392376193413/144115188075855872), (-127213126743/9007199254740992)), (8765/144115188075855872), by norm_num⟩
  | 4 => ⟨((374712071961537/9007199254740992), (-95374258111/1125899906842624)), (13153/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498259864481609/9007199254740992), (-3812977820997/9007199254740992)), (4113/2251799813685248), by norm_num⟩
  | 2 => ⟨((561479553854549/1125899906842624), (-3809989797427/2251799813685248)), (4117/562949953421312), by norm_num⟩
  | 1 => ⟨((1121486744675875/1125899906842624), (-5707517200049/1125899906842624)), (3093/140737488355328), by norm_num⟩
  | 0 => ⟨((1117065765187437/1125899906842624), (-11385179810723/1125899906842624)), (49655/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117065765187437/1125899906842624), (-11385179810723/1125899906842624)), (189418797019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1108185811057957/1125899906842624), (-11295848342973/562949953421312)), (6221/70368744177664), by norm_num⟩
  | 2 => ⟨((545148551665445/562949953421312), (-22236255250521/562949953421312)), (199935/1125899906842624), by norm_num⟩
  | 3 => ⟨((263515868979317/281474976710656), (-86132433411625/1125899906842624)), (403021/1125899906842624), by norm_num⟩
  | 4 => ⟨((980221250992295/1125899906842624), (-161273753731219/1125899906842624)), (408139/562949953421312), by norm_num⟩
  | 5 => ⟨((830290926904757/1125899906842624), (-561627049345641/2251799813685248)), (3310339/2251799813685248), by norm_num⟩
  | 6 => ⟨((1084513434899015/2251799813685248), (-207084946246983/562949953421312)), (6533677/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-3723443155/536870912)), (3/1073741824), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((2087975101/4398046511104), (-1662805591/4398046511104)), (1605/8796093022208), by norm_num⟩
  | 1 => ⟨((1874925615/4398046511104), (462144175/2199023255552)), (4809/8796093022208), by norm_num⟩
  | 2 => ⟨((-83095439/8796093022208), (3084130365/17592186044416)), (28079/35184372088832), by norm_num⟩
  | 3 => ⟨((-1351607119/35184372088832), (1668340791/140737488355328)), (108347/140737488355328), by norm_num⟩
  | 4 => ⟨((-1916240995/562949953421312), (-2979558703/562949953421312)), (39135/70368744177664), by norm_num⟩
  | 5 => ⟨((1219928779/2251799813685248), (-2027817263/4503599627370496)), (1450471/4503599627370496), by norm_num⟩
  | 6 => ⟨((2188619167/72057594037927936), (1960861067/36028797018963968)), (11246887/72057594037927936), by norm_num⟩
  | 7 => ⟨((-7333591597/1152921504606846976), (3597349/72057594037927936)), (75164931/1152921504606846976), by norm_num⟩
  | 8 => ⟨((621770835/2305843009213693952), (-1655860249/2305843009213693952)), (55322901/2305843009213693952), by norm_num⟩
  | 9 => ⟨((2389163201/36893488147419103232), (1741587477/36893488147419103232)), (584773561/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-3672686087/590295810358705651712), (2489110391/590295810358705651712)), (708786505/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-644033851/4722366482869645213696), (-6583655157/9444732965739290427392)), (6592461015/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((620874317/9444732965739290427392), (477099767/37778931862957161709568)), (4166308581/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2080670149/274877906944), (1543825691/549755813888)), (1209/274877906944), by norm_num⟩
  | 1 => ⟨((-989062131/549755813888), (1016244017/137438953472)), (7749/549755813888), by norm_num⟩
  | 2 => ⟨((-5258557147/2199023255552), (-103900369/274877906944)), (25341/1099511627776), by norm_num⟩
  | 3 => ⟨((352619659/17592186044416), (-5943641309/17592186044416)), (226355/8796093022208), by norm_num⟩
  | 4 => ⟨((3861587975/281474976710656), (-262753605/70368744177664)), (775499/35184372088832), by norm_num⟩
  | 5 => ⟨((643535225/1125899906842624), (-4471921497/2251799813685248)), (34743229/2251799813685248), by norm_num⟩
  | 6 => ⟨((2316762723/9007199254740992), (132169/17592186044416)), (165449909/18014398509481984), by norm_num⟩
  | 7 => ⟨((1042847117/288230376151711744), (886452245/288230376151711744)), (5518693733/1152921504606846976), by norm_num⟩
  | 8 => ⟨((351391371/288230376151711744), (502992619/2305843009213693952)), (323528341/144115188075855872), by norm_num⟩
  | 9 => ⟨((39292907/4611686018427387904), (305355937/4611686018427387904)), (567391909/576460752303423488), by norm_num⟩
  | 10 => ⟨((47291077/18446744073709551616), (5242027/4611686018427387904)), (7997859595/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-554313/36893488147419103232), (12368895/36893488147419103232)), (8038638447/36893488147419103232), by norm_num⟩
  | 12 => ⟨((177899/18446744073709551616), (-16723/18446744073709551616)), (325503683/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4063809/536870912), (3015285/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-965881/536870912), (3969703/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-2567655/1073741824), (-405861/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((10761/536870912), (-362771/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((14731/1073741824), (-4009/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((307/536870912), (-533/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((69/268435456), (1/134217728)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/268435456), (3/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/1073741824), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨30,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨30,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(1598925/134217728)) (L:=(8876970773/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile030
