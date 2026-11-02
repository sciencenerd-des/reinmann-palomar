/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile017Gamma
public import XiRectangle.Tile017Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile017
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18473658417/1099511627776), (10280947007/1099511627776)), (137/137438953472), by norm_num⟩
  | 1 => ⟨((-9797999209/549755813888), (-21028439/4294967296)), (2327/1099511627776), by norm_num⟩
  | 2 => ⟨((-9446264041/2199023255552), (-15595681395/2199023255552)), (5275/2199023255552), by norm_num⟩
  | 3 => ⟨((1748853989/4398046511104), (-19701202325/8796093022208)), (255/137438953472), by norm_num⟩
  | 4 => ⟨((10777565755/35184372088832), (-10202139227/35184372088832)), (38521/35184372088832), by norm_num⟩
  | 5 => ⟨((7742563611/140737488355328), (-1212444011/70368744177664)), (147781/281474976710656), by norm_num⟩
  | 6 => ⟨((8297251893/1125899906842624), (-808447005/1125899906842624)), (239991/1125899906842624), by norm_num⟩
  | 7 => ⟨((18612545073/18014398509481984), (2999918615/18014398509481984)), (679047/9007199254740992), by norm_num⟩
  | 8 => ⟨((14571006157/144115188075855872), (9646071653/144115188075855872)), (3419701/144115188075855872), by norm_num⟩
  | 9 => ⟨((1833946919/288230376151711744), (17870089089/2305843009213693952)), (1951245/288230376151711744), by norm_num⟩
  | 10 => ⟨((6204526359/9223372036854775808), (6264054553/9223372036854775808)), (8251627/4611686018427387904), by norm_num⟩
  | 11 => ⟨((3977046523/73786976294838206464), (15761524661/147573952589676412928)), (67938431/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-4026646401/2361183241434822606848), (2611559229/295147905179352825856)), (158406015/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile017Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-760852945/268435456), (19053230245/2147483648)), (439/2147483648), by norm_num⟩
  | 1 => ⟨((5775801373/2147483648), (-93981063/1073741824)), (849/2147483648), by norm_num⟩
  | 2 => ⟨((-518136681/1073741824), (-112725723/536870912)), (8927/17179869184), by norm_num⟩
  | 3 => ⟨((36671951/536870912), (51633885/536870912)), (68535/137438953472), by norm_num⟩
  | 4 => ⟨((-678821/1073741824), (-46965643/2147483648)), (420275/1099511627776), by norm_num⟩
  | 5 => ⟨((-4130525/2147483648), (6409903/2147483648)), (1121995/4398046511104), by norm_num⟩
  | 6 => ⟨((510299/1073741824), (-857929/4294967296)), (5625431/35184372088832), by norm_num⟩
  | 7 => ⟨((-572467/8589934592), (-115733/8589934592)), (29274803/281474976710656), by norm_num⟩
  | 8 => ⟨((99497/17179869184), (202025/34359738368)), (174101909/2251799813685248), by norm_num⟩
  | 9 => ⟨((-12017/68719476736), (-3927/4294967296)), (1189653671/18014398509481984), by norm_num⟩
  | 10 => ⟨((-10399/274877906944), (3117/34359738368)), (8925832501/144115188075855872), by norm_num⟩
  | 11 => ⟨((2223/274877906944), (-3017/549755813888)), (8728700213/144115188075855872), by norm_num⟩
  | 12 => ⟨((-2019/2199023255552), (5/274877906944)), (8668472629/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile017Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1843716533/4294967296), (-18955710609/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-107920692902727/562949953421312), (1400876766203145/2251799813685248)), (965737/1125899906842624), by norm_num⟩
  | 1 => ⟨((7540285795/68719476736), (-12234691625/34359738368)), (9/17179869184), by norm_num⟩
  | 2 => ⟨((-4315795249/137438953472), (14005417147/137438953472)), (23/137438953472), by norm_num⟩
  | 3 => ⟨((1646806601/274877906944), (-21376559429/1099511627776)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((-3770297465/4398046511104), (24470386435/8796093022208)), (23/4398046511104), by norm_num⟩
  | 5 => ⟨((6905555499/70368744177664), (-2801198267/8796093022208)), (45/70368744177664), by norm_num⟩
  | 6 => ⟨((-1317499293/140737488355328), (17101948653/562949953421312)), (9/140737488355328), by norm_num⟩
  | 7 => ⟨((3447270435/4503599627370496), (-22373841977/9007199254740992)), (25/4503599627370496), by norm_num⟩
  | 8 => ⟨((-7892386983/144115188075855872), (6403001393/36028797018963968)), (15/36028797018963968), by norm_num⟩
  | 9 => ⟨((8030801111/2305843009213693952), (-6515295159/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 10 => ⟨((-7354478431/36893488147419103232), (5966602467/9223372036854775808)), (61/36893488147419103232), by norm_num⟩
  | 11 => ⟨((1530707501/147573952589676412928), (-19869521923/590295810358705651712)), (53/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-4672657661/9444732965739290427392), (15163490375/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086617/5070602400912917605986812821504), (1217756274499/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781304502813969/633825300114114700748351602688), (2890129156817/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473148502937439/9903520314283042199192993792), (3251260841045/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473136674599209/618970019642690137449562112), (3454312247723/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887106110174275/77371252455336267181195264), (863535184217/38685626227668133590597632)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388096334898311/2417851639229258349412352), (809518661851/2417851639229258349412352)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261265835741521/604462909807314587353088), (2833132952085/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118238498022717/4722366482869645213696), (4603498963103/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81284758000769/295147905179352825856), (1726162374025/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625593982064919/590295810358705651712), (4746459600327/590295810358705651712)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828653862262117/73786976294838206464), (5932343613813/73786976294838206464)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228559910142953/1152921504606846976), (3336440396873/4611686018427387904)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((799861228222813/576460752303423488), (3335811187813/576460752303423488)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((37487321551635/4503599627370496), (729531525599/18014398509481984)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499145710102475/36028797018963968), (4375769714569/18014398509481984)), (2207/36028797018963968), by norm_num⟩
  | 3 => ⟨((749311057580555/4503599627370496), (10934446966175/9007199254740992)), (691/2251799813685248), by norm_num⟩
  | 2 => ⟨((1123307081176711/2251799813685248), (10926962442233/2251799813685248)), (693/562949953421312), by norm_num⟩
  | 1 => ⟨((1121973059181839/1125899906842624), (8185833778963/562949953421312)), (4177/1125899906842624), by norm_num⟩
  | 0 => ⟨((139737012013791/140737488355328), (32667842776945/1125899906842624)), (4217/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139737012013791/140737488355328), (32667842776945/1125899906842624)), (16086580516624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((554500664827545/562949953421312), (64871226450501/1125899906842624)), (17239/1125899906842624), by norm_num⟩
  | 2 => ⟨((1088618682448197/1125899906842624), (31948788676833/281474976710656)), (8987/281474976710656), by norm_num⟩
  | 3 => ⟨((1038066552013619/1125899906842624), (30890888278625/140737488355328)), (77677/1125899906842624), by norm_num⟩
  | 4 => ⟨((902842564954941/1125899906842624), (113924151477925/281474976710656)), (177335/1125899906842624), by norm_num⟩
  | 5 => ⟨((67442196322595/140737488355328), (91354100400527/140737488355328)), (427955/1125899906842624), by norm_num⟩
  | 6 => ⟨((-107920692902727/562949953421312), (1400876766203145/2251799813685248)), (965737/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-1843716533/4294967296), (-18955710609/4294967296)), (1/2147483648), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-5708837607/2199023255552), (-26927284013/2199023255552)), (917/1099511627776), by norm_num⟩
  | 1 => ⟨((2184862139/274877906944), (-6905655935/2199023255552)), (4883/2199023255552), by norm_num⟩
  | 2 => ⟨((9776009285/8796093022208), (2738195643/1099511627776)), (13621/4398046511104), by norm_num⟩
  | 3 => ⟨((-9496345847/17592186044416), (2610970431/17592186044416)), (51857/17592186044416), by norm_num⟩
  | 4 => ⟨((3319247059/281474976710656), (-6602381313/70368744177664)), (300781/140737488355328), by norm_num⟩
  | 5 => ⟨((3629786535/281474976710656), (5293759945/562949953421312)), (353265/281474976710656), by norm_num⟩
  | 6 => ⟨((-20906134513/9007199254740992), (10264100407/9007199254740992)), (349661/562949953421312), by norm_num⟩
  | 7 => ⟨((474499631/36028797018963968), (-13900078925/36028797018963968)), (9597115/36028797018963968), by norm_num⟩
  | 8 => ⟨((6766183637/144115188075855872), (8178894213/288230376151711744)), (29129993/288230376151711744), by norm_num⟩
  | 9 => ⟨((-3769592555/576460752303423488), (4289642747/1152921504606846976)), (79513803/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-57031543/4611686018427387904), (-18344841827/18446744073709551616)), (198023059/18446744073709551616), by norm_num⟩
  | 11 => ⟨((16604720095/147573952589676412928), (2200258327/36893488147419103232)), (457792301/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-15554650529/1180591620717411303424), (5226442315/590295810358705651712)), (509162849/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7971545411/68719476736), (1604489207/137438953472)), (55/4294967296), by norm_num⟩
  | 1 => ⟨((-1495975519/549755813888), (3210288729/68719476736)), (20037/549755813888), by norm_num⟩
  | 2 => ⟨((-3002140755/549755813888), (62794689/549755813888)), (245555/4398046511104), by norm_num⟩
  | 3 => ⟨((-1305156187/17592186044416), (21263239517/140737488355328)), (4187741/70368744177664), by norm_num⟩
  | 4 => ⟨((-10475847975/140737488355328), (-1026090483/281474976710656)), (13820965/281474976710656), by norm_num⟩
  | 5 => ⟨((-2659396651/4503599627370496), (-3314495769/1125899906842624)), (37669509/1125899906842624), by norm_num⟩
  | 6 => ⟨((-7112960331/18014398509481984), (-3987079919/72057594037927936)), (1425937377/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1139787751/576460752303423488), (-18360695083/576460752303423488)), (6174569991/576460752303423488), by norm_num⟩
  | 8 => ⟨((-2289163427/2305843009213693952), (-843818339/2305843009213693952)), (26424821063/4611686018427387904), by norm_num⟩
  | 9 => ⟨((11785155/9223372036854775808), (-23442349/144115188075855872)), (31096691093/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-3054863/4611686018427387904), (-12327093/9223372036854775808)), (10988634619/4611686018427387904), by norm_num⟩
  | 11 => ⟨((325185/2305843009213693952), (-6493587/9223372036854775808)), (9265402253/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-11679/9223372036854775808), (15657/576460752303423488)), (17339619397/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((124555397/1073741824), (391721/33554432)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2921827/1073741824), (50160761/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1465889/268435456), (61323/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-19915/268435456), (81113/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-19981/268435456), (-1957/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-317/536870912), (-3161/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-53/134217728), (-59/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-1/536870912), (-17/536870912)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-1/1073741824), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨17,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨17,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(48955083/536870912)) (L:=(128188993077/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile017
