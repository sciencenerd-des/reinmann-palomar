/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile028Gamma
public import XiRectangle.Tile028Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile028
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5502435763/4398046511104), (-303492081/549755813888)), (1905/4398046511104), by norm_num⟩
  | 1 => ⟨((3299697963/2199023255552), (1726477693/4398046511104)), (4467/4398046511104), by norm_num⟩
  | 2 => ⟨((286107967/549755813888), (185721619/274877906944)), (1263/1099511627776), by norm_num⟩
  | 3 => ⟨((84494741/17592186044416), (5317793547/17592186044416)), (15191/17592186044416), by norm_num⟩
  | 4 => ⟨((-1538571031/35184372088832), (1127086143/17592186044416)), (34575/70368744177664), by norm_num⟩
  | 5 => ⟨((-3995220583/281474976710656), (103589283/17592186044416)), (63797/281474976710656), by norm_num⟩
  | 6 => ⟨((-2745197295/1125899906842624), (-93767607/281474976710656)), (199033/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2467525149/9007199254740992), (-105983727/562949953421312)), (540025/18014398509481984), by norm_num⟩
  | 8 => ⟨((-3072975627/144115188075855872), (-601704049/18014398509481984)), (1302223/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1071610397/1152921504606846976), (-2438634359/576460752303423488)), (1426137/576460752303423488), by norm_num⟩
  | 10 => ⟨((457673185/9223372036854775808), (-4025246177/9223372036854775808)), (2951337/4611686018427387904), by norm_num⟩
  | 11 => ⟨((2512657659/147573952589676412928), (-1376363327/36893488147419103232)), (25978059/147573952589676412928), by norm_num⟩
  | 12 => ⟨((2739452905/1180591620717411303424), (-786672893/295147905179352825856)), (40491509/590295810358705651712), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile028Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((411610677/67108864), (871550069/67108864)), (305/268435456), by norm_num⟩
  | 1 => ⟨((-3295452389/1073741824), (-1226777247/536870912)), (2625/1073741824), by norm_num⟩
  | 2 => ⟨((628259199/536870912), (181842817/134217728)), (6877/2147483648), by norm_num⟩
  | 3 => ⟨((-21176543/134217728), (-246187363/536870912)), (6425/2147483648), by norm_num⟩
  | 4 => ⟨((-261691/33554432), (55993377/536870912)), (37223/17179869184), by norm_num⟩
  | 5 => ⟨((611643/67108864), (-18029007/1073741824)), (359533/274877906944), by norm_num⟩
  | 6 => ⟨((-5276755/2147483648), (1963959/1073741824)), (750515/1099511627776), by norm_num⟩
  | 7 => ⟨((928305/2147483648), (-186949/2147483648)), (1452747/4398046511104), by norm_num⟩
  | 8 => ⟨((-482053/8589934592), (-61039/4294967296)), (11504813/70368744177664), by norm_num⟩
  | 9 => ⟨((92203/17179869184), (38759/8589934592)), (26948275/281474976710656), by norm_num⟩
  | 10 => ⟨((-22019/68719476736), (-24829/34359738368)), (160109973/2251799813685248), by norm_num⟩
  | 11 => ⟨((-905/274877906944), (22945/274877906944)), (4552831643/72057594037927936), by norm_num⟩
  | 12 => ⟨((1091/274877906944), (-8037/1099511627776)), (4383617691/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile028Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7473/640))
  have he : value ((7/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-1794022611/268435456)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((1256904546000913/2251799813685248), (-531514018735665/2251799813685248)), (5463485/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2744324107/8589934592), (2321014335/17179869184)), (27/17179869184), by norm_num⟩
  | 2 => ⟨((3141509821/34359738368), (-1328467237/34359738368)), (9/17179869184), by norm_num⟩
  | 3 => ⟨((-4794906905/274877906944), (1013824099/137438953472)), (15/137438953472), by norm_num⟩
  | 4 => ⟨((5488873233/2199023255552), (-1160554745/1099511627776)), (37/2199023255552), by norm_num⟩
  | 5 => ⟨((-5026621783/17592186044416), (2125634721/17592186044416)), (9/4398046511104), by norm_num⟩
  | 6 => ⟨((1918041393/70368744177664), (-1622185061/140737488355328)), (29/140737488355328), by norm_num⟩
  | 7 => ⟨((-5018604125/2251799813685248), (2122244251/2251799813685248)), (5/281474976710656), by norm_num⟩
  | 8 => ⟨((5744946127/36028797018963968), (-2429396419/36028797018963968)), (3/2251799813685248), by norm_num⟩
  | 9 => ⟨((-1461424783/144115188075855872), (2472002387/576460752303423488)), (51/576460752303423488), by norm_num⟩
  | 10 => ⟨((334587325/576460752303423488), (-282977501/1152921504606846976)), (49/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-4456868193/147573952589676412928), (1884699941/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 12 => ⟨((1700636739/1180591620717411303424), (-1438314899/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-260567739679/5070602400912917605986812821504)), (3641/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781198160410857/633825300114114700748351602688), (-618338626427/633825300114114700748351602688)), (2163/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892474641696525/39614081257132168796771975168), (-695599389445/39614081257132168796771975168)), (4867/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473105047064271/618970019642690137449562112), (-739036554597/2475880078570760549798248448)), (5171/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887043035393131/77371252455336267181195264), (-738994035707/154742504910672534362390528)), (5171/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24254179022535/151115727451828646838272), (-692761734883/9671406556917033397649408)), (303/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((630581535933445/302231454903657293676544), (-606121347501/604462909807314587353088)), (2121/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891649695086913/75557863725914323419136), (-492431250743/37778931862957161709568)), (3447/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300432051202757/4722366482869645213696), (-184643195115/1180591620717411303424)), (5171/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812712198484081/295147905179352825856), (-1015417179927/590295810358705651712)), (7111/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828443411273687/73786976294838206464), (-1269090906503/73786976294838206464)), (8889/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828244627420221/9223372036854775808), (-1427479023037/9223372036854775808)), (5001/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49984075978557/36028797018963968), (-178396095841/144115188075855872)), (10003/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199394223511273/144115188075855872), (-19506620379/2251799813685248)), (8755/144115188075855872), by norm_num⟩
  | 4 => ⟨((374712879824019/9007199254740992), (-935968901195/18014398509481984)), (13135/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498264708944567/9007199254740992), (-2338701586789/9007199254740992)), (8213/4503599627370496), by norm_num⟩
  | 2 => ⟨((2245930317087079/4503599627370496), (-4673742787819/4503599627370496)), (32871/4503599627370496), by norm_num⟩
  | 1 => ⟨((2242997664236991/2251799813685248), (-7001468860805/2251799813685248)), (24679/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117101956429539/1125899906842624), (-3491597571775/562949953421312)), (98921/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117101956429539/1125899906842624), (-3491597571775/562949953421312)), (377353676802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2216658884969097/2251799813685248), (-13857254822705/1125899906842624)), (49381/562949953421312), by norm_num⟩
  | 2 => ⟨((2181725253022095/2251799813685248), (-54564010241673/2251799813685248)), (196873/1125899906842624), by norm_num⟩
  | 3 => ⟨((2112509211320855/2251799813685248), (-52866013367143/1125899906842624)), (782069/2251799813685248), by norm_num⟩
  | 4 => ⟨((988435090762545/1125899906842624), (-198383425605011/2251799813685248)), (1540829/2251799813685248), by norm_num⟩
  | 5 => ⟨((1718030043139979/2251799813685248), (-174162141858213/1125899906842624)), (2976903/2251799813685248), by norm_num⟩
  | 6 => ⟨((1256904546000913/2251799813685248), (-531514018735665/2251799813685248)), (5463485/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1794022611/268435456)), (3/1073741824), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1249123951/2199023255552), (-2654013167/4398046511104)), (1533/4398046511104), by norm_num⟩
  | 1 => ⟨((665310901/1099511627776), (1850052961/8796093022208)), (4447/4398046511104), by norm_num⟩
  | 2 => ⟨((372622773/35184372088832), (8189320091/35184372088832)), (6321/4398046511104), by norm_num⟩
  | 3 => ⟨((-3440856835/70368744177664), (330374933/17592186044416)), (2979/2199023255552), by norm_num⟩
  | 4 => ⟨((-2524100511/562949953421312), (-1876283987/281474976710656)), (135187/140737488355328), by norm_num⟩
  | 5 => ⟨((3221618583/4503599627370496), (-2383412923/4503599627370496)), (2470415/4503599627370496), by norm_num⟩
  | 6 => ⟨((516418899/18014398509481984), (5652749075/72057594037927936)), (1185557/4503599627370496), by norm_num⟩
  | 7 => ⟨((-2706375541/288230376151711744), (-375854433/288230376151711744)), (31497811/288230376151711744), by norm_num⟩
  | 8 => ⟨((2409100743/4611686018427387904), (-292084855/288230376151711744)), (184832989/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1557896915/18446744073709551616), (192421301/2305843009213693952)), (243672943/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-780651057/73786976294838206464), (681499807/147573952589676412928)), (1174925261/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-21598411/4722366482869645213696), (-5345951969/4722366482869645213696)), (2667765119/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((1903450077/18889465931478580854784), (770946541/18889465931478580854784)), (193449819/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6223862747/549755813888), (1010417915/274877906944)), (4397/549755813888), by norm_num⟩
  | 1 => ⟨((-588921407/274877906944), (5334046649/549755813888)), (13739/549755813888), by norm_num⟩
  | 2 => ⟨((-6271736871/2199023255552), (-878821049/2199023255552)), (43757/1099511627776), by norm_num⟩
  | 3 => ⟨((6786939/549755813888), (-786674525/2199023255552)), (379585/8796093022208), by norm_num⟩
  | 4 => ⟨((4835156049/562949953421312), (-2816838801/562949953421312)), (1261233/35184372088832), by norm_num⟩
  | 5 => ⟨((648151771/1125899906842624), (-1504379347/562949953421312)), (54792663/2251799813685248), by norm_num⟩
  | 6 => ⟨((4676900409/18014398509481984), (-85839641/18014398509481984)), (126591191/9007199254740992), by norm_num⟩
  | 7 => ⟨((4970803043/1152921504606846976), (-951315433/576460752303423488)), (8203971229/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1676737137/1152921504606846976), (98971739/576460752303423488)), (1872046903/576460752303423488), by norm_num⟩
  | 9 => ⟨((65517521/4611686018427387904), (119555713/2305843009213693952)), (6401235521/4611686018427387904), by norm_num⟩
  | 10 => ⟨((37238875/9223372036854775808), (11318095/9223372036854775808)), (1376735921/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-52709/9223372036854775808), (5977235/18446744073709551616)), (5424577425/18446744073709551616), by norm_num⟩
  | 12 => ⟨((20057/18446744073709551616), (108071/18446744073709551616)), (6944264877/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6077991/536870912), (3946945/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1150237/536870912), (2604515/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-3062371/1073741824), (-53639/134217728)), (1/10000000), by norm_num⟩
  | 3 => ⟨((1657/134217728), (-192059/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((4611/536870912), (-5373/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((309/536870912), (-2869/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((279/1073741824), (-5/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((5/1073741824), (-1/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨28,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨28,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(15903435/1073741824)) (L:=(13087436027/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile028
