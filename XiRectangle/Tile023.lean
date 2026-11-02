/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile023Gamma
public import XiRectangle.Tile023Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile023
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-116251495/549755813888), (-6830499729/2199023255552)), (1597/2199023255552), by norm_num⟩
  | 1 => ⟨((2202954307/1099511627776), (-1496257583/549755813888)), (13/8589934592), by norm_num⟩
  | 2 => ⟨((470188123/274877906944), (-950371329/2199023255552)), (1827/1099511627776), by norm_num⟩
  | 3 => ⟨((4720827805/8796093022208), (2107596437/8796093022208)), (5501/4398046511104), by norm_num⟩
  | 4 => ⟨((2434007491/35184372088832), (1070538177/8796093022208)), (25319/35184372088832), by norm_num⟩
  | 5 => ⟨((-232975409/140737488355328), (1785248325/70368744177664)), (94631/281474976710656), by norm_num⟩
  | 6 => ⟨((-35215829/17592186044416), (3519459277/1125899906842624)), (74715/562949953421312), by norm_num⟩
  | 7 => ⟨((-3472900081/9007199254740992), (586264269/2251799813685248)), (205075/4503599627370496), by norm_num⟩
  | 8 => ⟨((-468378163/9007199254740992), (501930587/36028797018963968)), (999943/72057594037927936), by norm_num⟩
  | 9 => ⟨((-6753746727/1152921504606846976), (-383784173/1152921504606846976)), (4416949/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-4962514993/9223372036854775808), (-992190767/4611686018427387904)), (9104083/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-2978754881/73786976294838206464), (-146156615/4611686018427387904)), (19025293/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-1608772557/590295810358705651712), (-3968452261/1180591620717411303424)), (102135625/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile023Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((530418187/268435456), (1007364283/67108864)), (295/268435456), by norm_num⟩
  | 1 => ⟨((5258941/8388608), (-1901426505/536870912)), (2749/1073741824), by norm_num⟩
  | 2 => ⟨((-49476123/134217728), (332573013/268435456)), (7513/2147483648), by norm_num⟩
  | 3 => ⟨((29701957/134217728), (-66881711/268435456)), (58055/17179869184), by norm_num⟩
  | 4 => ⟨((-34389335/536870912), (13706607/536870912)), (43655/17179869184), by norm_num⟩
  | 5 => ⟨((1625123/134217728), (661761/536870912)), (429677/274877906944), by norm_num⟩
  | 6 => ⟨((-845255/536870912), (-1131895/1073741824)), (913843/1099511627776), by norm_num⟩
  | 7 => ⟨((33447/268435456), (7875/33554432)), (1783499/4398046511104), by norm_num⟩
  | 8 => ⟨((65/268435456), (-146329/4294967296)), (13790381/70368744177664), by norm_num⟩
  | 9 => ⟨((-8373/4294967296), (30385/8589934592)), (121293515/1125899906842624), by norm_num⟩
  | 10 => ⟨((1615/4294967296), (-4137/17179869184)), (169383317/2251799813685248), by norm_num⟩
  | 11 => ⟨((-6357/137438953472), (457/137438953472)), (4641174171/72057594037927936), by norm_num⟩
  | 12 => ⟨((285/68719476736), (129/68719476736)), (4408652443/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile023Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-460929133/1073741824), (-6363702847/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1373699011651283/2251799813685248), (511621692056317/2251799813685248)), (472185/281474976710656), by norm_num⟩
  | 1 => ⟨((-5998666049/17179869184), (-558537141/4294967296)), (19/17179869184), by norm_num⟩
  | 2 => ⟨((1716713075/17179869184), (1278748315/34359738368)), (13/34359738368), by norm_num⟩
  | 3 => ⟨((-5240460699/274877906944), (-1951761883/274877906944)), (11/137438953472), by norm_num⟩
  | 4 => ⟨((5998911977/2199023255552), (2234240157/2199023255552)), (7/549755813888), by norm_num⟩
  | 5 => ⟨((-2746853529/8796093022208), (-63940037/549755813888)), (7/4398046511104), by norm_num⟩
  | 6 => ⟨((4192540435/140737488355328), (97592095/8796093022208)), (23/140737488355328), by norm_num⟩
  | 7 => ⟨((-5484944381/2251799813685248), (-2042817605/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | 8 => ⟨((3139389877/18014398509481984), (584618591/9007199254740992)), (21/18014398509481984), by norm_num⟩
  | 9 => ⟨((-399305935/36028797018963968), (-1189742885/288230376151711744)), (23/288230376151711744), by norm_num⟩
  | 10 => ⟨((2925423599/4611686018427387904), (2179094779/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-4871010651/147573952589676412928), (-226770447/18446744073709551616)), (39/147573952589676412928), by norm_num⟩
  | 12 => ⟨((929331911/590295810358705651712), (692242421/1180591620717411303424)), (31/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173537/10141204801825835211973625643008), (116103465781/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781308788106437/633825300114114700748351602688), (551102086169/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946299547572597/19807040628566084398385987584), (619965699473/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473138104217389/618970019642690137449562112), (329342340097/1237940039285380274899124224)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443554573956135/38685626227668133590597632), (658652196775/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((48512231706803/302231454903657293676544), (19295372581/302231454903657293676544)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((630635765298547/302231454903657293676544), (270117961175/302231454903657293676544)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((118239120837551/4722366482869645213696), (438909335951/37778931862957161709568)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300564223705011/4722366482869645213696), (82288424241/590295810358705651712)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812803062014151/295147905179352825856), (452540341619/295147905179352825856)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((914335277450227/36893488147419103232), (35350402895/2305843009213693952)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828500143098109/9223372036854775808), (1272424829563/9223372036854775808)), (6667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799872960428657/576460752303423488), (636093884829/576460752303423488)), (1667/288230376151711744), by norm_num⟩
  | 5 => ⟨((74976109215721/9007199254740992), (34778051625/4503599627370496)), (1459/36028797018963968), by norm_num⟩
  | 4 => ⟨((749593373181589/18014398509481984), (1668813299947/36028797018963968)), (8755/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498683639751639/9007199254740992), (1042541910857/4503599627370496)), (2737/2251799813685248), by norm_num⟩
  | 2 => ⟨((2246767869416899/4503599627370496), (4167370267107/4503599627370496)), (5477/1125899906842624), by norm_num⟩
  | 1 => ⟨((561063304702119/562949953421312), (3122032787923/1125899906842624)), (32891/2251799813685248), by norm_num⟩
  | 0 => ⟨((559177980511065/562949953421312), (12460193542737/2251799813685248)), (65903/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559177980511065/562949953421312), (12460193542737/2251799813685248)), (251400002486418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((138853511072229/140737488355328), (3094176409315/281474976710656)), (131653/2251799813685248), by norm_num⟩
  | 2 => ⟨((2191643949933295/2251799813685248), (48844101264677/2251799813685248)), (262677/2251799813685248), by norm_num⟩
  | 3 => ⟨((2132035640057089/2251799813685248), (95078504204567/2251799813685248)), (130679/562949953421312), by norm_num⟩
  | 4 => ⟨((2014626709239959/2251799813685248), (90021661044417/1125899906842624)), (258493/562949953421312), by norm_num⟩
  | 5 => ⟨((447009671473069/562949953421312), (322160152333291/2251799813685248)), (251935/281474976710656), by norm_num⟩
  | 6 => ⟨((1373699011651283/2251799813685248), (511621692056317/2251799813685248)), (472185/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-460929133/1073741824), (-6363702847/1073741824)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1268253757/2199023255552), (-1068140895/549755813888)), (675/1099511627776), by norm_num⟩
  | 1 => ⟨((3321730973/2199023255552), (-204624241/2199023255552)), (7155/4398046511104), by norm_num⟩
  | 2 => ⟨((1606533461/8796093022208), (4367340859/8796093022208)), (9791/4398046511104), by norm_num⟩
  | 3 => ⟨((-3413646001/35184372088832), (526777345/8796093022208)), (18259/8796093022208), by norm_num⟩
  | 4 => ⟨((-2708043713/281474976710656), (-3953549391/281474976710656)), (207517/140737488355328), by norm_num⟩
  | 5 => ⟨((2102034717/1125899906842624), (-218280979/281474976710656)), (954881/1125899906842624), by norm_num⟩
  | 6 => ⟨((-183417837/18014398509481984), (2228121863/9007199254740992)), (3699741/9007199254740992), by norm_num⟩
  | 7 => ⟨((-529417065/18014398509481984), (-253137573/18014398509481984)), (6202989/36028797018963968), by norm_num⟩
  | 8 => ⟨((815187325/288230376151711744), (-196229965/72057594037927936)), (9187427/144115188075855872), by norm_num⟩
  | 9 => ⟨((728658869/4611686018427387904), (3768087735/9223372036854775808)), (195543893/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-110245411/2305843009213693952), (-397714239/147573952589676412928)), (29663119/4611686018427387904), by norm_num⟩
  | 11 => ⟨((692073671/295147905179352825856), (-5365037071/1180591620717411303424)), (2150175727/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((3116484965/9444732965739290427392), (3883740193/9444732965739290427392)), (601890955/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2082532347/68719476736), (80835/16777216)), (1815/137438953472), by norm_num⟩
  | 1 => ⟨((-587721447/274877906944), (5285943567/274877906944)), (10559/274877906944), by norm_num⟩
  | 2 => ⟨((-2353046605/549755813888), (-280120701/1099511627776)), (65149/1099511627776), by norm_num⟩
  | 3 => ⟨((-276230795/17592186044416), (-6008283113/17592186044416)), (69799/1099511627776), by norm_num⟩
  | 4 => ⟨((-1097873169/70368744177664), (-1555227785/281474976710656)), (14840701/281474976710656), by norm_num⟩
  | 5 => ⟨((135734297/562949953421312), (-39025163/8796093022208)), (2534149/70368744177664), by norm_num⟩
  | 6 => ⟨((5858579445/36028797018963968), (-296692431/9007199254740992)), (378828609/18014398509481984), by norm_num⟩
  | 7 => ⟨((468298345/144115188075855872), (-1358939497/72057594037927936)), (1559172939/144115188075855872), by norm_num⟩
  | 8 => ⟨((1884998755/1152921504606846976), (-33188905/576460752303423488)), (2911176809/576460752303423488), by norm_num⟩
  | 9 => ⟨((43398653/2305843009213693952), (-3611237/144115188075855872)), (5151591527/2305843009213693952), by norm_num⟩
  | 10 => ⟨((8011447/1152921504606846976), (635515/1152921504606846976)), (1173192511/1152921504606846976), by norm_num⟩
  | 11 => ⟨((321259/4611686018427387904), (929513/9223372036854775808)), (5024267057/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-18875/4611686018427387904), (125405/18446744073709551616)), (3481534727/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2033723/67108864), (80835/16777216)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2295787/1073741824), (20648217/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-2297897/536870912), (-273555/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-4215/268435456), (-366717/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-1047/67108864), (-5933/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((259/1073741824), (-1191/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((175/1073741824), (-35/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((3/1073741824), (-5/268435456)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨23,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨23,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(67065477/1073741824)) (L:=(8434755065/274877906944)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile023
