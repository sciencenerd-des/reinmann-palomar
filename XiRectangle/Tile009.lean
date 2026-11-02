/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile009Gamma
public import XiRectangle.Tile009Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile009
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39256704879/274877906944), (7718133211/68719476736)), (309/274877906944), by norm_num⟩
  | 1 => ⟨((-4148504495/549755813888), (17748841731/137438953472)), (1675/549755813888), by norm_num⟩
  | 2 => ⟨((-66768725125/2199023255552), (42311751519/2199023255552)), (8825/2199023255552), by norm_num⟩
  | 3 => ⟨((-123774787381/35184372088832), (-3381256927/8796093022208)), (15053/4398046511104), by norm_num⟩
  | 4 => ⟨((-19061682673/35184372088832), (46514099533/70368744177664)), (38649/17592186044416), by norm_num⟩
  | 5 => ⟨((-17628874451/70368744177664), (-2904147621/140737488355328)), (20257/17592186044416), by norm_num⟩
  | 6 => ⟨((3038616403/1125899906842624), (-13002845209/562949953421312)), (580889/1125899906842624), by norm_num⟩
  | 7 => ⟨((-1617224049/2251799813685248), (83640836601/18014398509481984)), (458267/2251799813685248), by norm_num⟩
  | 8 => ⟨((-41941121233/36028797018963968), (-10244964175/18014398509481984)), (5194885/72057594037927936), by norm_num⟩
  | 9 => ⟨((50346536649/288230376151711744), (-34531916075/288230376151711744)), (6716177/288230376151711744), by norm_num⟩
  | 10 => ⟨((-12238356961/2305843009213693952), (96216293901/2305843009213693952)), (8041905/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-61275095781/9223372036854775808), (-25682025167/4611686018427387904)), (18182301/9223372036854775808), by norm_num⟩
  | 12 => ⟨((59133852833/36893488147419103232), (-2213061869/4611686018427387904)), (5053385/9223372036854775808), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile009Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4963236447/8589934592), (93837096601/34359738368)), (631/8589934592), by norm_num⟩
  | 1 => ⟨((4075412897/4294967296), (6094068135/8589934592)), (1643/17179869184), by norm_num⟩
  | 2 => ⟨((691842317/8589934592), (-1204746067/8589934592)), (30541/274877906944), by norm_num⟩
  | 3 => ⟨((-103507073/4294967296), (2468079/268435456)), (122803/1099511627776), by norm_num⟩
  | 4 => ⟨((29735003/8589934592), (7646363/4294967296)), (442571/4398046511104), by norm_num⟩
  | 5 => ⟨((-1444931/8589934592), (-4659791/8589934592)), (6032557/70368744177664), by norm_num⟩
  | 6 => ⟨((-563457/17179869184), (1138311/17179869184)), (83020491/1125899906842624), by norm_num⟩
  | 7 => ⟨((286527/34359738368), (-51977/17179869184)), (149525909/2251799813685248), by norm_num⟩
  | 8 => ⟨((-63639/68719476736), (-26609/68719476736)), (4514296475/72057594037927936), by norm_num⟩
  | 9 => ⟨((6365/137438953472), (26175/274877906944)), (35147584723/576460752303423488), by norm_num⟩
  | 10 => ⟨((2987/1099511627776), (-87/8589934592)), (69540194725/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-1791/2199023255552), (619/1099511627776)), (69284866469/1152921504606846976), by norm_num⟩
  | 12 => ⟨((195/2199023255552), (61/8796093022208)), (69205305765/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile009Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-3687433067/8589934592), (-41160971609/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-538423187203381/1125899906842624), (-994589168863449/2251799813685248)), (254429/2251799813685248), by norm_num⟩
  | 1 => ⟨((37618964455/137438953472), (4343169959/17179869184)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((-43063552887/549755813888), (-39774051611/549755813888)), (15/549755813888), by norm_num⟩
  | 3 => ⟨((16432045327/1099511627776), (60707394081/4398046511104)), (25/4398046511104), by norm_num⟩
  | 4 => ⟨((-37620506743/17592186044416), (-8686696037/4398046511104)), (1/1099511627776), by norm_num⟩
  | 5 => ⟨((4306531839/17592186044416), (31820545801/140737488355328)), (1/8796093022208), by norm_num⟩
  | 6 => ⟨((-52584700805/2251799813685248), (-24283953175/1125899906842624)), (27/2251799813685248), by norm_num⟩
  | 7 => ⟨((68794604057/36028797018963968), (63539581591/36028797018963968)), (19/18014398509481984), by norm_num⟩
  | 8 => ⟨((-39375619625/288230376151711744), (-36367828991/288230376151711744)), (23/288230376151711744), by norm_num⟩
  | 9 => ⟨((40066176497/4611686018427387904), (9251409051/1152921504606846976)), (25/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-18345979859/36893488147419103232), (-16944583083/36893488147419103232)), (25/73786976294838206464), by norm_num⟩
  | 11 => ⟨((61094375069/2361183241434822606848), (28213775503/1180591620717411303424)), (11/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-46624371333/37778931862957161709568), (-10765717337/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-780226563323/2535301200456458802993406410752)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781301647721387/633825300114114700748351602688), (-3703459529305/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892590624917999/39614081257132168796771975168), (-1041553247641/9903520314283042199192993792)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473135722114419/618970019642690137449562112), (-4426405196035/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774208172557417/154742504910672534362390528), (-2213092214869/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552381292105209/9671406556917033397649408), (-4149313196049/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261262041543731/604462909807314587353088), (-3630414179345/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945904664581141/37778931862957161709568), (-5898982324755/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162568841783307/590295810358705651712), (-4423850775897/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406396473126519/147573952589676412928), (-1520541745263/147573952589676412928)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57145085651341/2305843009213693952), (-7601765855969/73786976294838206464)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828465381959111/9223372036854775808), (-1068836040947/1152921504606846976)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599706823428785/1152921504606846976), (-1068632847891/144115188075855872)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199578661100415/144115188075855872), (-7478597461645/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((749559185102053/18014398509481984), (-5607110956267/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498581125501837/9007199254740992), (-109463487677/70368744177664)), (87/2251799813685248), by norm_num⟩
  | 2 => ⟨((1123255879552043/2251799813685248), (-7000804032923/1125899906842624)), (349/2251799813685248), by norm_num⟩
  | 1 => ⟨((280467690689961/281474976710656), (-2622246221491/140737488355328)), (263/562949953421312), by norm_num⟩
  | 0 => ⟨((279397436082077/281474976710656), (-20928646743457/562949953421312)), (133/140737488355328), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279397436082077/281474976710656), (-20928646743457/562949953421312)), (507355273199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((553892400216755/562949953421312), (-41548348696021/562949953421312)), (2193/1125899906842624), by norm_num⟩
  | 2 => ⟨((1083828229790071/1125899906842624), (-81759717518117/562949953421312)), (145/35184372088832), by norm_num⟩
  | 3 => ⟨((127447499893053/140737488355328), (-314818357714575/1125899906842624)), (5141/562949953421312), by norm_num⟩
  | 4 => ⟨((417636048544719/562949953421312), (-570179460782461/1125899906842624)), (24373/1125899906842624), by norm_num⟩
  | 5 => ⟨((41364118650079/140737488355328), (-52874925984835/70368744177664)), (30425/562949953421312), by norm_num⟩
  | 6 => ⟨((-538423187203381/1125899906842624), (-994589168863449/2251799813685248)), (254429/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-41160971609/17179869184)), (1/17179869184), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-10274406693/549755813888), (-64205768293/549755813888)), (585/549755813888), by norm_num⟩
  | 1 => ⟨((78444546095/1099511627776), (9260716895/1099511627776)), (3773/1099511627776), by norm_num⟩
  | 2 => ⟨((-32447606829/2199023255552), (20361745473/1099511627776)), (12071/2199023255552), by norm_num⟩
  | 3 => ⟨((-20130055957/17592186044416), (-28990759757/4398046511104)), (99/17179869184), by norm_num⟩
  | 4 => ⟨((51963220289/35184372088832), (8107329425/8796093022208)), (39783/8796093022208), by norm_num⟩
  | 5 => ⟨((-55667508319/140737488355328), (16337640475/140737488355328)), (6291/2199023255552), by norm_num⟩
  | 6 => ⟨((11011560217/281474976710656), (-5839570425/70368744177664)), (860443/562949953421312), by norm_num⟩
  | 7 => ⟨((35574612639/4503599627370496), (40144212947/2251799813685248)), (1602519/2251799813685248), by norm_num⟩
  | 8 => ⟨((-34588607695/9007199254740992), (-19896110459/18014398509481984)), (2658581/9007199254740992), by norm_num⟩
  | 9 => ⟨((47020457583/72057594037927936), (-16492247351/36028797018963968)), (7986329/72057594037927936), by norm_num⟩
  | 10 => ⟨((-4291045309/576460752303423488), (44913025359/288230376151711744)), (22006963/576460752303423488), by norm_num⟩
  | 11 => ⟨((-53748591695/2305843009213693952), (-11033743471/576460752303423488)), (28155673/2305843009213693952), by norm_num⟩
  | 12 => ⟨((103260566643/18446744073709551616), (-27724214625/18446744073709551616)), (67944941/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((45320922223/137438953472), (4519143023/274877906944)), (463/34359738368), by norm_num⟩
  | 1 => ⟨((246519001/274877906944), (72457251523/1099511627776)), (17557/549755813888), by norm_num⟩
  | 2 => ⟨((62895420327/35184372088832), (14501915595/17592186044416)), (432891/8796093022208), by norm_num⟩
  | 3 => ⟨((-1710706789/70368744177664), (38797338759/35184372088832)), (3990469/70368744177664), by norm_num⟩
  | 4 => ⟨((-3454067683/140737488355328), (3016153177/281474976710656)), (119364279/2251799813685248), by norm_num⟩
  | 5 => ⟨((-5015467877/9007199254740992), (38769869243/4503599627370496)), (193312921/4503599627370496), by norm_num⟩
  | 6 => ⟨((-53928482335/144115188075855872), (2621834339/36028797018963968)), (1166907035/36028797018963968), by norm_num⟩
  | 7 => ⟨((-11382418223/2305843009213693952), (96267880915/2305843009213693952)), (56616308849/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-11587048783/4611686018427387904), (11919401/36028797018963968)), (45733779465/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-111198953/4611686018427387904), (612656059/4611686018427387904)), (80219314943/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-51180279/4611686018427387904), (4800105/1152921504606846976)), (75075970117/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-344141/1152921504606846976), (-741611/1152921504606846976)), (36478991591/2305843009213693952), by norm_num⟩
  | 12 => ⟨((97435/1152921504606846976), (1387363/4611686018427387904)), (72161071911/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354069705/1073741824), (8826451/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((962965/1073741824), (70759035/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((239927/134217728), (885127/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-3263/134217728), (1184001/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-1647/67108864), (5753/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-299/536870912), (2311/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-201/536870912), (39/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-5/1073741824), (45/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨9,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨9,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(114745267/1073741824)) (L:=(363017721295/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile009
