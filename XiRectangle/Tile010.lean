/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile010Gamma
public import XiRectangle.Tile010Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile010
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50442749207/549755813888), (58040371545/549755813888)), (423/549755813888), by norm_num⟩
  | 1 => ⟨((-12244192507/549755813888), (14127070727/137438953472)), (1039/549755813888), by norm_num⟩
  | 2 => ⟨((-64302044089/2199023255552), (30834795415/2199023255552)), (4959/2199023255552), by norm_num⟩
  | 3 => ⟨((-37265128361/8796093022208), (-22847027253/17592186044416)), (32327/17592186044416), by norm_num⟩
  | 4 => ⟨((-69394714717/140737488355328), (24952686757/140737488355328)), (40883/35184372088832), by norm_num⟩
  | 5 => ⟨((-26539865461/140737488355328), (-7720739961/281474976710656)), (85121/140737488355328), by norm_num⟩
  | 6 => ⟨((-13878075969/2251799813685248), (-26113569953/1125899906842624)), (604935/2251799813685248), by norm_num⟩
  | 7 => ⟨((30153087385/72057594037927936), (99418812957/72057594037927936)), (1881881/18014398509481984), by norm_num⟩
  | 8 => ⟨((-25118450563/36028797018963968), (-2828153561/18014398509481984)), (1307243/36028797018963968), by norm_num⟩
  | 9 => ⟨((924779747/18014398509481984), (-61515864563/576460752303423488)), (825427/72057594037927936), by norm_num⟩
  | 10 => ⟨((2130971723/288230376151711744), (38549573495/2305843009213693952)), (3861275/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-67530955405/18446744073709551616), (-6389291609/9223372036854775808)), (17228687/18446744073709551616), by norm_num⟩
  | 12 => ⟨((15947944863/36893488147419103232), (-19298303587/36893488147419103232)), (19741623/73786976294838206464), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile010Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-15549600107/17179869184), (54605782557/17179869184)), (333/4294967296), by norm_num⟩
  | 1 => ⟨((9337984113/8589934592), (6646673255/8589934592)), (1837/17179869184), by norm_num⟩
  | 2 => ⟨((137167341/2147483648), (-747311947/4294967296)), (36141/274877906944), by norm_num⟩
  | 3 => ⟨((-57522779/2147483648), (70436649/4294967296)), (147123/1099511627776), by norm_num⟩
  | 4 => ⟨((40721025/8589934592), (639347/536870912)), (522443/4398046511104), by norm_num⟩
  | 5 => ⟨((-1627673/4294967296), (-41067/67108864)), (6859949/70368744177664), by norm_num⟩
  | 6 => ⟨((-152305/8589934592), (1609149/17179869184)), (90294987/1125899906842624), by norm_num⟩
  | 7 => ⟨((318381/34359738368), (-239661/34359738368)), (156472725/2251799813685248), by norm_num⟩
  | 8 => ⟨((-90551/68719476736), (-7117/68719476736)), (4603425435/72057594037927936), by norm_num⟩
  | 9 => ⟨((13687/137438953472), (27313/274877906944)), (35403437267/576460752303423488), by norm_num⟩
  | 10 => ⟨((-697/549755813888), (-481/34359738368)), (69716355493/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-411/549755813888), (2423/2199023255552)), (69337819557/1152921504606846976), by norm_num⟩
  | 12 => ⟨((251/2199023255552), (-39/1099511627776)), (69219854757/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile010Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-90987410925/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1290964784768629/2251799813685248), (-694417492133139/2251799813685248)), (125503/1125899906842624), by norm_num⟩
  | 1 => ⟨((45099059165/137438953472), (24259047135/137438953472)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((-25813120425/274877906944), (-13885028129/274877906944)), (7/274877906944), by norm_num⟩
  | 3 => ⟨((78797467727/4398046511104), (21192808887/2199023255552)), (3/549755813888), by norm_num⟩
  | 4 => ⟨((-22550454059/8796093022208), (-12130020849/8796093022208)), (1/1099511627776), by norm_num⟩
  | 5 => ⟨((82605371843/281474976710656), (22216955811/140737488355328)), (31/281474976710656), by norm_num⟩
  | 6 => ⟨((-63040558587/2251799813685248), (-16954942193/1125899906842624)), (13/1125899906842624), by norm_num⟩
  | 7 => ⟨((82473613069/36028797018963968), (44363037809/36028797018963968)), (37/36028797018963968), by norm_num⟩
  | 8 => ⟨((-47205004837/288230376151711744), (-6347961901/72057594037927936)), (23/288230376151711744), by norm_num⟩
  | 9 => ⟨((12008217733/1152921504606846976), (3229645201/576460752303423488)), (25/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-87975460575/147573952589676412928), (-47322513693/147573952589676412928)), (49/147573952589676412928), by norm_num⟩
  | 11 => ⟨((73242282867/2361183241434822606848), (39397451417/2361183241434822606848)), (43/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-55895086737/37778931862957161709568), (-234892917/295147905179352825856)), (35/37778931862957161709568), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-3449422701001/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781300029532117/633825300114114700748351602688), (-511662171811/79228162514264337593543950336)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892588705353337/39614081257132168796771975168), (-4604757541739/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892540729092599/2475880078570760549798248448), (-4892337622809/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221775734798159/19342813113834066795298816), (-611511624769/19342813113834066795298816)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776189499052823/4835703278458516698824704), (-4586077075721/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315314972775669/151115727451828646838272), (-1003139277621/151115727451828646838272)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236475695782235/9444732965739290427392), (-6519916715427/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300547677251503/4722366482869645213696), (-2444754776169/2361183241434822606848)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625581307587969/590295810358705651712), (-3361189640737/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828636437564023/73786976294838206464), (-2100482008855/18446744073709551616)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828457504338357/9223372036854775808), (-9450728202183/9223372036854775808)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799848981570853/576460752303423488), (-4724461706343/576460752303423488)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199569803364993/144115188075855872), (-8265772455485/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((749551437462853/18014398509481984), (-3098643694025/9007199254740992)), (139/18014398509481984), by norm_num⟩
  | 3 => ⟨((93659868384049/562949953421312), (-967877672339/562949953421312)), (87/2251799813685248), by norm_num⟩
  | 2 => ⟨((1123226860684137/2251799813685248), (-7737610754071/1125899906842624)), (349/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121812786398479/1125899906842624), (-23185577574857/1125899906842624)), (527/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117416124835575/1125899906842624), (-5782616194395/140737488355328)), (267/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117416124835575/1125899906842624), (-5782616194395/140737488355328)), (1018525243663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((34596734433935/35184372088832), (-11478087066323/140737488355328)), (2209/1125899906842624), by norm_num⟩
  | 2 => ⟨((1081116241333205/1125899906842624), (-5643191941021/35184372088832)), (2353/562949953421312), by norm_num⟩
  | 3 => ⟨((1009150467389861/1125899906842624), (-173399327547897/562949953421312)), (10549/1125899906842624), by norm_num⟩
  | 4 => ⟨((797686679960317/1125899906842624), (-621675199994513/1125899906842624)), (12705/562949953421312), by norm_num⟩
  | 5 => ⟨((443776544574873/2251799813685248), (-1761797912171265/2251799813685248)), (128133/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1290964784768629/2251799813685248), (-694417492133139/2251799813685248)), (125503/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-90987410925/34359738368)), (1/17179869184), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-11020324041/549755813888), (-97660904395/1099511627776)), (771/1099511627776), by norm_num⟩
  | 1 => ⟨((123013990287/2199023255552), (-671654469/549755813888)), (573/274877906944), by norm_num⟩
  | 2 => ⟨((-33629635919/4398046511104), (71367155191/4398046511104)), (3379/1099511627776), by norm_num⟩
  | 3 => ⟨((-37501042117/17592186044416), (-74957046077/17592186044416)), (53845/17592186044416), by norm_num⟩
  | 4 => ⟨((81022600907/70368744177664), (9377619537/35184372088832)), (82159/35184372088832), by norm_num⟩
  | 5 => ⟨((-59426329563/281474976710656), (5737496001/35184372088832)), (409703/281474976710656), by norm_num⟩
  | 6 => ⟨((499752483/281474976710656), (-126641718765/2251799813685248)), (27107/35184372088832), by norm_num⟩
  | 7 => ⟨((38569067505/4503599627370496), (16642635541/2251799813685248)), (1600635/4503599627370496), by norm_num⟩
  | 8 => ⟨((-77290275955/36028797018963968), (15057374307/36028797018963968)), (5249049/36028797018963968), by norm_num⟩
  | 9 => ⟨((3259661211/18014398509481984), (-52935222319/144115188075855872)), (485457/9007199254740992), by norm_num⟩
  | 10 => ⟨((40021020783/1152921504606846976), (76598386131/1152921504606846976)), (21031047/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-7715063911/576460752303423488), (-2023765689/1152921504606846976)), (26431741/4611686018427387904), by norm_num⟩
  | 12 => ⟨((29339175019/18446744073709551616), (-66583591187/36893488147419103232)), (31557975/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((82590462603/274877906944), (4584452441/274877906944)), (777/68719476736), by norm_num⟩
  | 1 => ⟨((206815129/1099511627776), (73494133521/1099511627776)), (7117/274877906944), by norm_num⟩
  | 2 => ⟨((25734555145/70368744177664), (13726057945/17592186044416)), (2735417/70368744177664), by norm_num⟩
  | 3 => ⟨((-1477672321/35184372088832), (18355853313/17592186044416)), (385929/8796093022208), by norm_num⟩
  | 4 => ⟨((-95252610933/2251799813685248), (10462347543/1125899906842624)), (91355153/2251799813685248), by norm_num⟩
  | 5 => ⟨((-6553782589/9007199254740992), (8401140615/1125899906842624)), (147636645/4503599627370496), by norm_num⟩
  | 6 => ⟨((-35195909569/72057594037927936), (2016128377/36028797018963968)), (3572385853/144115188075855872), by norm_num⟩
  | 7 => ⟨((-13598367435/2305843009213693952), (36976798339/1152921504606846976)), (5429071327/288230376151711744), by norm_num⟩
  | 8 => ⟨((-3400323113/1152921504606846976), (948756563/4611686018427387904)), (70155973123/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-327801035/9223372036854775808), (822353187/9223372036854775808)), (122880733907/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-94630973/9223372036854775808), (611625/9223372036854775808)), (57433438779/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-6486457/9223372036854775808), (575241/1152921504606846976)), (111553079091/9223372036854775808), by norm_num⟩
  | 12 => ⟨((755989/9223372036854775808), (-1365567/9223372036854775808)), (110303328145/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((322618995/1073741824), (17908017/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((12623/67108864), (71771615/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((196339/536870912), (209443/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-45095/1073741824), (1120353/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-11355/268435456), (4989/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-781/1073741824), (2003/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-131/268435456), (15/268435456)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-3/536870912), (17/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨10,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨10,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(113935459/1073741824)) (L:=(165435204665/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile010
