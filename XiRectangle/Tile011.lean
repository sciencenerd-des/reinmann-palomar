/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile011Gamma
public import XiRectangle.Tile011Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile011
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14296917365/274877906944), (51349918219/549755813888)), (317/549755813888), by norm_num⟩
  | 1 => ⟨((-35331683831/1099511627776), (85694280707/1099511627776)), (1429/1099511627776), by norm_num⟩
  | 2 => ⟨((-29661934517/1099511627776), (4597988013/549755813888)), (211/137438953472), by norm_num⟩
  | 3 => ⟨((-4642063929/1099511627776), (-18495731463/8796093022208)), (22143/17592186044416), by norm_num⟩
  | 4 => ⟨((-58011540419/140737488355328), (-12117205609/70368744177664)), (27859/35184372088832), by norm_num⟩
  | 5 => ⟨((-36460160335/281474976710656), (-26167669195/562949953421312)), (57111/140737488355328), by norm_num⟩
  | 6 => ⟨((-33029505827/4503599627370496), (-95974926073/4503599627370496)), (398081/2251799813685248), by norm_num⟩
  | 7 => ⟨((53719348191/72057594037927936), (-14845113447/36028797018963968)), (2433011/36028797018963968), by norm_num⟩
  | 8 => ⟨((-98673343059/288230376151711744), (-4084162379/72057594037927936)), (3335289/144115188075855872), by norm_num⟩
  | 9 => ⟨((4635602263/576460752303423488), (-83462560361/1152921504606846976)), (8362331/1152921504606846976), by norm_num⟩
  | 10 => ⟨((67739085665/9223372036854775808), (42908282325/9223372036854775808)), (19562603/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-28234060007/18446744073709551616), (14391422241/36893488147419103232)), (22162759/36893488147419103232), by norm_num⟩
  | 12 => ⟨((4243297489/73786976294838206464), (-84449746621/295147905179352825856)), (53843293/295147905179352825856), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile011Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21592680601/17179869184), (63455262901/17179869184)), (703/8589934592), by norm_num⟩
  | 1 => ⟨((337248153/268435456), (7033199463/8589934592)), (2029/17179869184), by norm_num⟩
  | 2 => ⟨((77614201/2147483648), (-225928049/1073741824)), (40173/274877906944), by norm_num⟩
  | 3 => ⟨((-120159297/4294967296), (111510127/4294967296)), (162995/1099511627776), by norm_num⟩
  | 4 => ⟨((52534453/8589934592), (118951/2147483648)), (569035/4398046511104), by norm_num⟩
  | 5 => ⟨((-1426661/2147483648), (-2678375/4294967296)), (7343277/70368744177664), by norm_num⟩
  | 6 => ⟨((199997/17179869184), (2095537/17179869184)), (23507635/281474976710656), by norm_num⟩
  | 7 => ⟨((301771/34359738368), (-422151/34359738368)), (159552917/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1807/1073741824), (29091/68719476736)), (1161342119/18014398509481984), by norm_num⟩
  | 9 => ⟨((11565/68719476736), (5483/68719476736)), (8876549429/144115188075855872), by norm_num⟩
  | 10 => ⟨((-559/68719476736), (-581/34359738368)), (69775075749/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-869/2199023255552), (959/549755813888)), (69354596773/1152921504606846976), by norm_num⟩
  | 12 => ⟨((1103/8796093022208), (-225/2199023255552)), (69224311205/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile011Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-12456609829/4294967296)), (3/34359738368), by norm_num⟩
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
  | 0 => ⟨((-22240734107099/35184372088832), (-175155852067987/1125899906842624)), (360917/2251799813685248), by norm_num⟩
  | 1 => ⟨((24862922867/68719476736), (12237923495/137438953472)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((-56922661711/549755813888), (-7004558383/274877906944)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((86881429391/4398046511104), (10691103091/2199023255552)), (15/2199023255552), by norm_num⟩
  | 4 => ⟨((-49727884375/17592186044416), (-12238425221/17592186044416)), (37/35184372088832), by norm_num⟩
  | 5 => ⟨((91079992647/281474976710656), (11207752885/140737488355328)), (9/70368744177664), by norm_num⟩
  | 6 => ⟨((-34753996529/1125899906842624), (-17106466241/2251799813685248)), (29/2251799813685248), by norm_num⟩
  | 7 => ⟨((90934716525/36028797018963968), (22379752169/36028797018963968)), (5/4503599627370496), by norm_num⟩
  | 8 => ⟨((-26023921917/144115188075855872), (-12809385573/288230376151711744)), (3/36028797018963968), by norm_num⟩
  | 9 => ⟨((6620080259/576460752303423488), (13034032431/4611686018427387904)), (51/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-48500503803/73786976294838206464), (-23872714331/147573952589676412928)), (49/147573952589676412928), by norm_num⟩
  | 11 => ⟨((2523635281/73786976294838206464), (19874770583/2361183241434822606848)), (43/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-61629455513/37778931862957161709568), (-15167495907/37778931862957161709568)), (35/37778931862957161709568), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-1888969574355/5070602400912917605986812821504)), (115/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781298249523921/633825300114114700748351602688), (-4483135219671/633825300114114700748351602688)), (137/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892586593832209/39614081257132168796771975168), (-5043300837513/39614081257132168796771975168)), (77/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892538353795549/2475880078570760549798248448), (-1339567140225/618970019642690137449562112)), (41/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774203354801287/154742504910672534362390528), (-1339499972989/38685626227668133590597632)), (163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776188237356087/4835703278458516698824704), (-627854897035/1208925819614629174706176)), (153/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315314381405985/151115727451828646838272), (-4394698262689/604462909807314587353088)), (67/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472950356768971/18889465931478580854784), (-1785211942745/18889465931478580854784)), (109/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300544314547097/4722366482869645213696), (-5355165410931/4722366482869645213696)), (41/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625576264199121/590295810358705651712), (-7362586841113/590295810358705651712)), (225/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828629503991477/73786976294838206464), (-9202083104957/73786976294838206464)), (281/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114278052437929/576460752303423488), (-5175379151355/4611686018427387904)), (79/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599688216896489/1152921504606846976), (-5174385913865/576460752303423488)), (317/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299890014986053/36028797018963968), (-4526466856125/72057594037927936)), (277/144115188075855872), by norm_num⟩
  | 4 => ⟨((749542915158903/18014398509481984), (-6787450088093/18014398509481984)), (417/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498532340048513/9007199254740992), (-16960711055213/9007199254740992)), (261/4503599627370496), by norm_num⟩
  | 2 => ⟨((561597470311431/1125899906842624), (-16948762943439/2251799813685248)), (525/2251799813685248), by norm_num⟩
  | 1 => ⟨((560874507239759/562949953421312), (-12696502765525/562949953421312)), (793/1125899906842624), by norm_num⟩
  | 0 => ⟨((558612576887073/562949953421312), (-1583245227187/35184372088832)), (1607/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558612576887073/562949953421312), (-1583245227187/35184372088832)), (6130222800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106337438377263/1125899906842624), (-100546992166879/1125899906842624)), (3335/1125899906842624), by norm_num⟩
  | 2 => ⟨((539067825898235/562949953421312), (-197599983931773/1125899906842624)), (7151/1125899906842624), by norm_num⟩
  | 3 => ⟨((997718112593981/1125899906842624), (-189217164133785/562949953421312)), (8103/562949953421312), by norm_num⟩
  | 4 => ⟨((378465654987345/562949953421312), (-167675111013517/281474976710656)), (39617/1125899906842624), by norm_num⟩
  | 5 => ⟨((218680047164945/2251799813685248), (-1803620952921577/2251799813685248)), (200937/2251799813685248), by norm_num⟩
  | 6 => ⟨((-22240734107099/35184372088832), (-175155852067987/1125899906842624)), (360917/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-12456609829/4294967296)), (3/34359738368), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-10086237029/549755813888), (-4613453349/68719476736)), (263/549755813888), by norm_num⟩
  | 1 => ⟨((94422597595/2199023255552), (-12846480957/2199023255552)), (2895/2199023255552), by norm_num⟩
  | 2 => ⟨((-14149269183/4398046511104), (58275902213/4398046511104)), (8319/4398046511104), by norm_num⟩
  | 3 => ⟨((-20028231419/8796093022208), (-44739421753/17592186044416)), (32981/17592186044416), by norm_num⟩
  | 4 => ⟨((113174149027/140737488355328), (-1039172531/17592186044416)), (100351/70368744177664), by norm_num⟩
  | 5 => ⟨((-26664773123/281474976710656), (82365334315/562949953421312)), (496689/562949953421312), by norm_num⟩
  | 6 => ⟨((-3298500663/281474976710656), (-4639126145/140737488355328)), (32471/70368744177664), by norm_num⟩
  | 7 => ⟨((28660147975/4503599627370496), (9162385489/4503599627370496)), (472593/2251799813685248), by norm_num⟩
  | 8 => ⟨((-17912618469/18014398509481984), (3211297097/4503599627370496)), (6113211/72057594037927936), by norm_num⟩
  | 9 => ⟨((396072485/576460752303423488), (-124854284139/576460752303423488)), (8939417/288230376151711744), by norm_num⟩
  | 10 => ⟨((70473689933/2305843009213693952), (12361059487/576460752303423488)), (24004521/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-13561645359/2305843009213693952), (20978614651/9223372036854775808)), (30091439/9223372036854775808), by norm_num⟩
  | 12 => ⟨((15481984315/73786976294838206464), (-37943798235/36893488147419103232)), (36294277/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((74499171919/274877906944), (570834435/34359738368)), (2575/274877906944), by norm_num⟩
  | 1 => ⟨((-259477361/549755813888), (73197680871/1099511627776)), (5937/274877906944), by norm_num⟩
  | 2 => ⟨((-33712758173/35184372088832), (50281780251/70368744177664)), (2238817/70368744177664), by norm_num⟩
  | 3 => ⟨((-1000561847/17592186044416), (67219243663/70368744177664)), (627987/17592186044416), by norm_num⟩
  | 4 => ⟨((-16108607877/281474976710656), (8494387845/1125899906842624)), (36961281/1125899906842624), by norm_num⟩
  | 5 => ⟨((-3831000311/4503599627370496), (109062247399/18014398509481984)), (14861357/562949953421312), by norm_num⟩
  | 6 => ⟨((-82260831035/144115188075855872), (166140679/4503599627370496)), (2855543697/144115188075855872), by norm_num⟩
  | 7 => ⟨((-29369360871/4611686018427387904), (48800378597/2305843009213693952)), (68931772373/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-29598133345/9223372036854775808), (679385559/9223372036854775808)), (110946713999/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-139838641/4611686018427387904), (173178755/4611686018427387904)), (97051485081/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-15047887/1152921504606846976), (-10694189/9223372036854775808)), (90739124401/9223372036854775808), by norm_num⟩
  | 11 => ⟨((1069423/4611686018427387904), (1299259/9223372036854775808)), (5510249953/576460752303423488), by norm_num⟩
  | 12 => ⟨((-67349/576460752303423488), (-65797/4611686018427387904)), (43602501039/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((145506195/536870912), (1114911/67108864)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-63349/134217728), (35741055/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-32151/33554432), (767239/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-61069/1073741824), (256421/268435456)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-61449/1073741824), (8101/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-913/1073741824), (6501/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-613/1073741824), (5/134217728)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-7/1073741824), (23/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨11,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨11,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(114303531/1073741824)) (L:=(149278010833/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile011
