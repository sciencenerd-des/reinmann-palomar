/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile032Gamma
public import XiRectangle.Tile032Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile032
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((747046935/1099511627776), (601753707/2199023255552)), (1817/2199023255552), by norm_num⟩
  | 1 => ⟨((238008839/549755813888), (202286985/274877906944)), (2073/1099511627776), by norm_num⟩
  | 2 => ⟨((-14956049/274877906944), (1058464115/2199023255552)), (1177/549755813888), by norm_num⟩
  | 3 => ⟨((-264184309/2199023255552), (288808677/2199023255552)), (7137/4398046511104), by norm_num⟩
  | 4 => ⟨((-204102341/4398046511104), (370707057/35184372088832)), (8153/8796093022208), by norm_num⟩
  | 5 => ⟨((-1303430801/140737488355328), (-240926061/70368744177664)), (30033/70368744177664), by norm_num⟩
  | 6 => ⟨((-586618755/562949953421312), (-364069567/281474976710656)), (46505/281474976710656), by norm_num⟩
  | 7 => ⟨((-198221331/4503599627370496), (-1039182405/4503599627370496)), (124691/2251799813685248), by norm_num⟩
  | 8 => ⟨((254214859/36028797018963968), (-505679377/18014398509481984)), (592001/36028797018963968), by norm_num⟩
  | 9 => ⟨((273080817/144115188075855872), (-748361043/288230376151711744)), (634753/144115188075855872), by norm_num⟩
  | 10 => ⟨((157521669/576460752303423488), (-845860355/4611686018427387904)), (79127/72057594037927936), by norm_num⟩
  | 11 => ⟨((1113228369/36893488147419103232), (-299261513/36893488147419103232)), (10182367/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1621007723/590295810358705651712), (75904333/590295810358705651712)), (52438781/590295810358705651712), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile032Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((116263839/16777216), (631156101/67108864)), (43/8388608), by norm_num⟩
  | 1 => ⟨((-1284118811/268435456), (217214761/268435456)), (785/67108864), by norm_num⟩
  | 2 => ⟨((306487131/134217728), (55139855/134217728)), (8329/536870912), by norm_num⟩
  | 3 => ⟨((-4713259/8388608), (-21856363/67108864)), (31425/2147483648), by norm_num⟩
  | 4 => ⟨((3023127/33554432), (7558039/67108864)), (22961/2147483648), by norm_num⟩
  | 5 => ⟨((-1026619/134217728), (-6961059/268435456)), (110727/17179869184), by norm_num⟩
  | 6 => ⟨((-134989/268435456), (2366281/536870912)), (907885/274877906944), by norm_num⟩
  | 7 => ⟨((350025/1073741824), (-606387/1073741824)), (1641907/1099511627776), by norm_num⟩
  | 8 => ⟨((-75707/1073741824), (110391/2147483648)), (2709195/4398046511104), by norm_num⟩
  | 9 => ⟨((5651/536870912), (-9485/4294967296)), (17902765/70368744177664), by norm_num⟩
  | 10 => ⟨((-10323/8589934592), (-4635/17179869184)), (136760011/1125899906842624), by norm_num⟩
  | 11 => ⟨((7205/68719476736), (5495/68719476736)), (175183253/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1697/274877906944), (-3223/274877906944)), (1166060711/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile032Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-1929420545/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((421753891928407/1125899906842624), (-1072758504251239/2251799813685248)), (20255103/2251799813685248), by norm_num⟩
  | 1 => ⟨((-920857019/4294967296), (585564957/2147483648)), (25/4294967296), by norm_num⟩
  | 2 => ⟨((527066275/8589934592), (-670313707/8589934592)), (1/536870912), by norm_num⟩
  | 3 => ⟨((-804464689/68719476736), (511552089/34359738368)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((230223693/137438953472), (-1171177929/549755813888)), (33/549755813888), by norm_num⟩
  | 5 => ⟨((-421670307/2199023255552), (536272951/2199023255552)), (1/137438953472), by norm_num⟩
  | 6 => ⟨((643598137/35184372088832), (-818516899/35184372088832)), (13/17592186044416), by norm_num⟩
  | 7 => ⟨((-420997727/281474976710656), (535417575/281474976710656)), (37/562949953421312), by norm_num⟩
  | 8 => ⟨((60241085/562949953421312), (-153227125/1125899906842624)), (23/4503599627370496), by norm_num⟩
  | 9 => ⟨((-490380589/72057594037927936), (623657491/72057594037927936)), (25/72057594037927936), by norm_num⟩
  | 10 => ⟨((898165305/2305843009213693952), (-571135495/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 11 => ⟨((-23367197/1152921504606846976), (950975811/36893488147419103232)), (21/18446744073709551616), by norm_num⟩
  | 12 => ⟨((35665505/36893488147419103232), (-2834923/2305843009213693952)), (17/295147905179352825856), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-147271047501/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890598661688287/316912650057057350374175801344), (-1397922510843/633825300114114700748351602688)), (11543/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892473648946447/39614081257132168796771975168), (-1572590723465/39614081257132168796771975168)), (12987/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118276191968099/154742504910672534362390528), (-417698025757/618970019642690137449562112)), (1725/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774084884311891/154742504910672534362390528), (-1670695868047/154742504910672534362390528)), (13801/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552266271070351/9671406556917033397649408), (-1566175125973/9671406556917033397649408)), (3235/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630580979876063/302231454903657293676544), (-685150492085/302231454903657293676544)), (11325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945823874551917/37778931862957161709568), (-1113273688495/37778931862957161709568)), (18405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300430470295643/4722366482869645213696), (-834871387095/2361183241434822606848)), (6903/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812711012982357/295147905179352825856), (-573905925991/147573952589676412928)), (18987/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828440151724397/73786976294838206464), (-358640088635/9223372036854775808)), (5935/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828240553854225/9223372036854775808), (-806799630835/2305843009213693952)), (26715/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799742924874537/576460752303423488), (-1613247834089/576460752303423488)), (13363/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199389643442617/144115188075855872), (-1411196490473/72057594037927936)), (23397/144115188075855872), by norm_num⟩
  | 4 => ⟨((749421753770863/18014398509481984), (-2116003986347/18014398509481984)), (17559/18014398509481984), by norm_num⟩
  | 3 => ⟨((93640793627725/562949953421312), (-82613160173/140737488355328)), (43939/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122950156693475/2251799813685248), (-2641545248547/1125899906842624)), (44001/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121468863737445/1125899906842624), (-3957127867321/562949953421312)), (16539/281474976710656), by norm_num⟩
  | 0 => ⟨((279253056954047/281474976710656), (-15786987750469/1125899906842624)), (132931/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279253056954047/281474976710656), (-15786987750469/1125899906842624)), (507091526511764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553986673472129/562949953421312), (-31324735441377/1125899906842624)), (66873/281474976710656), by norm_num⟩
  | 2 => ⟨((272365174522535/281474976710656), (-30825983516115/562949953421312)), (541351/1125899906842624), by norm_num⟩
  | 3 => ⟨((1050824891674395/1125899906842624), (-29828315391695/281474976710656)), (276737/281474976710656), by norm_num⟩
  | 4 => ⟨((968112078127349/1125899906842624), (-222714904582997/1125899906842624)), (575221/281474976710656), by norm_num⟩
  | 5 => ⟨((788381863874435/1125899906842624), (-383005607861583/1125899906842624)), (2433569/562949953421312), by norm_num⟩
  | 6 => ⟨((421753891928407/1125899906842624), (-1072758504251239/2251799813685248)), (20255103/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1929420545/268435456)), (1/134217728), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((846352417/2199023255552), (-486374483/2199023255552)), (783/1099511627776), by norm_num⟩
  | 1 => ⟨((643159975/2199023255552), (431035437/2199023255552)), (2225/1099511627776), by norm_num⟩
  | 2 => ⟨((-94644087/4398046511104), (1145809799/8796093022208)), (6309/2199023255552), by norm_num⟩
  | 3 => ⟨((-1057394717/35184372088832), (58734737/8796093022208)), (95579/35184372088832), by norm_num⟩
  | 4 => ⟨((-703580251/281474976710656), (-1193572129/281474976710656)), (544487/281474976710656), by norm_num⟩
  | 5 => ⟨((59202079/140737488355328), (-26125225/70368744177664)), (622929/562949953421312), by norm_num⟩
  | 6 => ⟨((130821659/4503599627370496), (689523469/18014398509481984)), (9550979/18014398509481984), by norm_num⟩
  | 7 => ⟨((-305573559/72057594037927936), (52349961/72057594037927936)), (63125687/288230376151711744), by norm_num⟩
  | 8 => ⟨((18460059/144115188075855872), (-1143808445/2305843009213693952)), (183734135/2305843009213693952), by norm_num⟩
  | 9 => ⟨((881720799/18446744073709551616), (60240733/2305843009213693952)), (479069533/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-527080533/147573952589676412928), (510417965/147573952589676412928)), (142088157/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-97731877/590295810358705651712), (-246625633/590295810358705651712)), (156779503/73786976294838206464), by norm_num⟩
  | 12 => ⟨((24487977/590295810358705651712), (540241/2361183241434822606848)), (1358771425/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1304929977/274877906944), (35854689/17179869184)), (1013/68719476736), by norm_num⟩
  | 1 => ⟨((-203249967/137438953472), (752965357/137438953472)), (12819/274877906944), by norm_num⟩
  | 2 => ⟨((-1078756453/549755813888), (-191109083/549755813888)), (10445/137438953472), by norm_num⟩
  | 3 => ⟨((112294461/4398046511104), (-170565151/549755813888)), (373461/4398046511104), by norm_num⟩
  | 4 => ⟨((1221436381/70368744177664), (-176403755/70368744177664)), (5130527/70368744177664), by norm_num⟩
  | 5 => ⟨((151436843/281474976710656), (-745329385/562949953421312)), (57642585/1125899906842624), by norm_num⟩
  | 6 => ⟨((1088118501/4503599627370496), (78485243/4503599627370496)), (68792665/2251799813685248), by norm_num⟩
  | 7 => ⟨((201516237/72057594037927936), (496912701/72057594037927936)), (572855365/36028797018963968), by norm_num⟩
  | 8 => ⟨((270592527/288230376151711744), (69307201/288230376151711744)), (530497459/72057594037927936), by norm_num⟩
  | 9 => ⟨((1944227/576460752303423488), (10701207/144115188075855872)), (891225015/288230376151711744), by norm_num⟩
  | 10 => ⟨((1189087/1152921504606846976), (991513/1152921504606846976)), (349196047/288230376151711744), by norm_num⟩
  | 11 => ⟨((9329/2305843009213693952), (440069/1152921504606846976)), (1081745093/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-64399/4611686018427387904), (-205107/9223372036854775808)), (936531491/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5097383/1073741824), (1120459/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-793945/536870912), (2941271/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1053473/536870912), (-93315/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((3427/134217728), (-333135/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((9319/536870912), (-673/268435456)), (1/10000000), by norm_num⟩
  | 5 => ⟨((289/536870912), (-711/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((259/1073741824), (19/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((3/1073741824), (7/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨32,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨32,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(10136333/1073741824)) (L:=(2850926477/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile032
