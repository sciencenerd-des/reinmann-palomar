/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile018Gamma
public import XiRectangle.Tile018Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile018
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-60087401/4294967296), (1556000399/549755813888)), (701/1099511627776), by norm_num⟩
  | 1 => ⟨((-13076479887/1099511627776), (-8229191303/1099511627776)), (803/549755813888), by norm_num⟩
  | 2 => ⟨((-3743729419/2199023255552), (-13800642511/2199023255552)), (1857/1099511627776), by norm_num⟩
  | 3 => ⟨((7054116031/8796093022208), (-14766283799/8796093022208)), (361/274877906944), by norm_num⟩
  | 4 => ⟨((11384359199/35184372088832), (-1491576763/8796093022208)), (3409/4398046511104), by norm_num⟩
  | 5 => ⟨((29863307799/562949953421312), (158896277/140737488355328)), (6525/17592186044416), by norm_num⟩
  | 6 => ⟨((14335800161/2251799813685248), (2324856669/1125899906842624)), (337963/2251799813685248), by norm_num⟩
  | 7 => ⟨((6848345511/9007199254740992), (8343551243/18014398509481984)), (476239/9007199254740992), by norm_num⟩
  | 8 => ⟨((4753428201/72057594037927936), (6170669325/72057594037927936)), (2388173/144115188075855872), by norm_num⟩
  | 9 => ⟨((3412360715/1152921504606846976), (22163577741/2305843009213693952)), (5429911/1152921504606846976), by norm_num⟩
  | 10 => ⟨((843033221/4611686018427387904), (15288429973/18446744073709551616)), (11489737/9223372036854775808), by norm_num⟩
  | 11 => ⟨((636234399/73786976294838206464), (27731473555/295147905179352825856)), (24159611/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-3842698883/1180591620717411303424), (18851638643/2361183241434822606848)), (245050815/2361183241434822606848), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile018Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2892653229/1073741824), (21671351595/2147483648)), (235/1073741824), by norm_num⟩
  | 1 => ⟨((6070921821/2147483648), (-1219699407/2147483648)), (117/268435456), by norm_num⟩
  | 2 => ⟨((-1301638165/2147483648), (-99525489/1073741824)), (9791/17179869184), by norm_num⟩
  | 3 => ⟨((236550027/2147483648), (94963141/1073741824)), (75895/137438953472), by norm_num⟩
  | 4 => ⟨((-9250659/1073741824), (-54355713/2147483648)), (116589/274877906944), by norm_num⟩
  | 5 => ⟨((-2355093/2147483648), (9156863/2147483648)), (1236683/4398046511104), by norm_num⟩
  | 6 => ⟨((64223/134217728), (-1869307/4294967296)), (6108759/35184372088832), by norm_num⟩
  | 7 => ⟨((-731129/8589934592), (7323/536870912)), (31175347/281474976710656), by norm_num⟩
  | 8 => ⟨((41455/4294967296), (147109/34359738368)), (180327829/2251799813685248), by norm_num⟩
  | 9 => ⟨((-45239/68719476736), (-34505/34359738368)), (1207479463/18014398509481984), by norm_num⟩
  | 10 => ⟨((187/137438953472), (8779/68719476736)), (8972494133/144115188075855872), by norm_num⟩
  | 11 => ⟨((29/4294967296), (-1495/137438953472)), (8743118133/144115188075855872), by norm_num⟩
  | 12 => ⟨((-1203/1099511627776), (1169/2199023255552)), (8672929077/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile018Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5217/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5217/640))
  have he : value ((3/4), (5217/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1843716533/4294967296), (-20038894073/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-8557696983789/281474976710656), (1464280964167377/2251799813685248)), (1819831/2251799813685248), by norm_num⟩
  | 1 => ⟨((1195831481/68719476736), (-25576876541/68719476736)), (17/34359738368), by norm_num⟩
  | 2 => ⟨((-1368904035/274877906944), (29278614963/274877906944)), (21/137438953472), by norm_num⟩
  | 3 => ⟨((1044683573/1099511627776), (-2793008797/137438953472)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((-1195880507/8796093022208), (25577925131/8796093022208)), (41/8796093022208), by norm_num⟩
  | 5 => ⟨((1095168125/70368744177664), (-5855963063/17592186044416)), (5/8796093022208), by norm_num⟩
  | 6 => ⟨((-417890561/281474976710656), (17875989143/562949953421312)), (1/17592186044416), by norm_num⟩
  | 7 => ⟨((546710645/4503599627370496), (-23386490299/9007199254740992)), (45/9007199254740992), by norm_num⟩
  | 8 => ⟨((-312918007/36028797018963968), (26771214371/144115188075855872)), (27/72057594037927936), by norm_num⟩
  | 9 => ⟨((1273623447/2305843009213693952), (-27240719263/2305843009213693952)), (57/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-583181929/18446744073709551616), (12473306181/18446744073709551616)), (55/36893488147419103232), by norm_num⟩
  | 11 => ⟨((485516933/295147905179352825856), (-10384411899/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-1482095315/18889465931478580854784), (31699591061/18889465931478580854784)), (19/4722366482869645213696), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086617/5070602400912917605986812821504), (526749025275/2535301200456458802993406410752)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781305621576639/633825300114114700748351602688), (2500291311409/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473148834718357/9903520314283042199192993792), (1406356584491/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236568523914711/309485009821345068724781056), (2988376120159/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887106903235937/77371252455336267181195264), (2988228005467/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1552386925598299/9671406556917033397649408), (2801306344985/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261267322495549/604462909807314587353088), (1225492799337/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945909284965745/37778931862957161709568), (995639070417/18889465931478580854784)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650279120775195/2361183241434822606848), (746664679545/1180591620717411303424)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812798575979469/295147905179352825856), (4106235514919/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228582277524331/9223372036854775808), (1283040940019/18446744073709551616)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828484727550899/9223372036854775808), (5772816622159/9223372036854775808)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599728582266025/1152921504606846976), (2885865691277/576460752303423488)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199600413736109/144115188075855872), (5049043062573/144115188075855872)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((1499156423336577/36028797018963968), (7571118295207/36028797018963968)), (551/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498638177174327/9007199254740992), (2364902804411/2251799813685248)), (2759/9007199254740992), by norm_num⟩
  | 2 => ⟨((280831786236977/562949953421312), (2363292499547/562949953421312)), (1383/1125899906842624), by norm_num⟩
  | 1 => ⟨((1122013145372701/1125899906842624), (7081806333953/562949953421312)), (2083/562949953421312), by norm_num⟩
  | 0 => ⟨((1118016147118035/1125899906842624), (28262420875713/1125899906842624)), (8401/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118016147118035/1125899906842624), (28262420875713/1125899906842624)), (32047276023482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1109478145607045/1125899906842624), (56129044338059/1125899906842624)), (17107/1125899906842624), by norm_num⟩
  | 2 => ⟨((1090497724086731/1125899906842624), (110620753494013/1125899906842624)), (17711/562949953421312), by norm_num⟩
  | 3 => ⟨((522670056184341/562949953421312), (26785613709719/140737488355328)), (37789/562949953421312), by norm_num⟩
  | 4 => ⟨((929761093014895/1125899906842624), (99476254594257/281474976710656)), (84555/562949953421312), by norm_num⟩
  | 5 => ⟨((627167017372647/1125899906842624), (82146868152741/140737488355328)), (24927/70368744177664), by norm_num⟩
  | 6 => ⟨((-8557696983789/281474976710656), (1464280964167377/2251799813685248)), (1819831/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-1843716533/4294967296), (-20038894073/4294967296)), (1/2147483648), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-3111947961/2199023255552), (-20194664493/2199023255552)), (985/2199023255552), by norm_num⟩
  | 1 => ⟨((1659839337/274877906944), (-77303409/34359738368)), (1393/1099511627776), by norm_num⟩
  | 2 => ⟨((7989809649/8796093022208), (16499090825/8796093022208)), (15907/8796093022208), by norm_num⟩
  | 3 => ⟨((-3496709535/8796093022208), (5434118539/35184372088832)), (7643/4398046511104), by norm_num⟩
  | 4 => ⟨((-450992685/140737488355328), (-4835061291/70368744177664)), (177907/140737488355328), by norm_num⟩
  | 5 => ⟨((5594548035/562949953421312), (10432256627/2251799813685248)), (104495/140737488355328), by norm_num⟩
  | 6 => ⟨((-12250237077/9007199254740992), (4800069763/4503599627370496)), (3304971/9007199254740992), by norm_num⟩
  | 7 => ⟨((-3608173181/72057594037927936), (-2212118349/9007199254740992)), (5656027/36028797018963968), by norm_num⟩
  | 8 => ⟨((18986157583/576460752303423488), (2796908319/288230376151711744)), (34234553/576460752303423488), by norm_num⟩
  | 9 => ⟨((-3689306249/1152921504606846976), (3726346745/1152921504606846976)), (93148621/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-99328795/576460752303423488), (-10240351297/18446744073709551616)), (14460089/2305843009213693952), by norm_num⟩
  | 11 => ⟨((20844390469/295147905179352825856), (243841129/18446744073709551616)), (267665827/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-12593124591/2361183241434822606848), (8025357947/1180591620717411303424)), (75603887/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((26522276877/274877906944), (2875004691/274877906944)), (2213/274877906944), by norm_num⟩
  | 1 => ⟨((-1528301299/549755813888), (11500986117/274877906944)), (13279/549755813888), by norm_num⟩
  | 2 => ⟨((-6131533441/1099511627776), (22950643/1099511627776)), (167117/4398046511104), by norm_num⟩
  | 3 => ⟨((-9389314237/140737488355328), (3692988501/140737488355328)), (5804461/140737488355328), by norm_num⟩
  | 4 => ⟨((-18829917247/281474976710656), (-42047401/8796093022208)), (2428273/70368744177664), by norm_num⟩
  | 5 => ⟨((-1972483571/4503599627370496), (-8678182325/2251799813685248)), (107121271/4503599627370496), by norm_num⟩
  | 6 => ⟨((-5266385127/18014398509481984), (-2142418109/36028797018963968)), (1024178027/72057594037927936), by norm_num⟩
  | 7 => ⟨((-26002257/36028797018963968), (-9859403653/288230376151711744)), (1120006341/144115188075855872), by norm_num⟩
  | 8 => ⟨((-1602309935/4611686018427387904), (-1640406769/4611686018427387904)), (19348365037/4611686018427387904), by norm_num⟩
  | 9 => ⟨((5891455/1152921504606846976), (-723630925/4611686018427387904)), (5724164119/2305843009213693952), by norm_num⟩
  | 10 => ⟨((24510077/9223372036854775808), (-3932871/2305843009213693952)), (16201004905/9223372036854775808), by norm_num⟩
  | 11 => ⟨((169573/18446744073709551616), (-6302567/18446744073709551616)), (27295148183/18446744073709551616), by norm_num⟩
  | 12 => ⟨((4729/1152921504606846976), (-338525/9223372036854775808)), (25517007679/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((25900661/268435456), (11230487/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2984963/1073741824), (44925727/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-2993913/536870912), (22413/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-71635/1073741824), (28175/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-71831/1073741824), (-5133/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-235/536870912), (-2069/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-157/536870912), (-1/16777216)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-1/1073741824), (-37/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨18,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨18,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(92705991/1073741824)) (L:=(106710585935/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile018
