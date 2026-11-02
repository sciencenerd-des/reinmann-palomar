/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile029Gamma
public import XiRectangle.Tile029Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile029
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6886326207/8796093022208), (-346542411/2199023255552)), (225/1099511627776), by norm_num⟩
  | 1 => ⟨((3612921269/4398046511104), (1847234041/4398046511104)), (527/1099511627776), by norm_num⟩
  | 2 => ⟨((965862081/4398046511104), (4123681565/8796093022208)), (4867/8796093022208), by norm_num⟩
  | 3 => ⟨((-1352406489/35184372088832), (3230777503/17592186044416)), (7471/17592186044416), by norm_num⟩
  | 4 => ⟨((-1278654433/35184372088832), (2344740479/70368744177664)), (8637/35184372088832), by norm_num⟩
  | 5 => ⟨((-1393131167/140737488355328), (845250729/562949953421312)), (16089/140737488355328), by norm_num⟩
  | 6 => ⟨((-3405545963/2251799813685248), (-716549675/1125899906842624)), (100797/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2551521163/18014398509481984), (-3158616469/18014398509481984)), (273487/18014398509481984), by norm_num⟩
  | 8 => ⟨((-241350857/36028797018963968), (-943280921/36028797018963968)), (164651/36028797018963968), by norm_num⟩
  | 9 => ⟨((414007975/1152921504606846976), (-3368876361/1152921504606846976)), (724729/576460752303423488), by norm_num⟩
  | 10 => ⟨((2455343383/18446744073709551616), (-2460386155/9223372036854775808)), (1556671/4611686018427387904), by norm_num⟩
  | 11 => ⟨((366439515/18446744073709551616), (-1455855411/73786976294838206464)), (7885495/73786976294838206464), by norm_num⟩
  | 12 => ⟨((2545388313/1180591620717411303424), (-2621707553/2361183241434822606848)), (127348449/2361183241434822606848), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile029Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((538461361/67108864), (3142595809/268435456)), (573/268435456), by norm_num⟩
  | 1 => ⟨((-2731445375/536870912), (-851492883/536870912)), (5555/1073741824), by norm_num⟩
  | 2 => ⟨((275067727/134217728), (373877465/268435456)), (15409/2147483648), by norm_num⟩
  | 3 => ⟨((-104508667/268435456), (-76315507/134217728)), (14897/2147483648), by norm_num⟩
  | 4 => ⟨((8278005/268435456), (20025711/134217728)), (88967/17179869184), by norm_num⟩
  | 5 => ⟨((1583209/268435456), (-14955293/536870912)), (437047/137438953472), by norm_num⟩
  | 6 => ⟨((-1478643/536870912), (493/131072)), (1831347/1099511627776), by norm_num⟩
  | 7 => ⟨((160501/268435456), (-356961/1073741824)), (3397323/4398046511104), by norm_num⟩
  | 8 => ⟨((-391709/4294967296), (13755/2147483648)), (23915693/70368744177664), by norm_num⟩
  | 9 => ⟨((45049/4294967296), (35145/8589934592)), (44479155/281474976710656), by norm_num⟩
  | 10 => ⟨((-30297/34359738368), (-32307/34359738368)), (205362581/2251799813685248), by norm_num⟩
  | 11 => ⟨((5705/137438953472), (18113/137438953472)), (1243917479/18014398509481984), by norm_num⟩
  | 12 => ⟨((551/274877906944), (-3791/274877906944)), (4497519259/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile029Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-384107611/1073741824), (-3723443155/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((156418704172391/281474976710656), (-477883746250919/1125899906842624)), (1253687/562949953421312), by norm_num⟩
  | 1 => ⟨((-683048879/2147483648), (2086821771/8589934592)), (13/8589934592), by norm_num⟩
  | 2 => ⟨((3127625861/34359738368), (-2388847247/34359738368)), (17/34359738368), by norm_num⟩
  | 3 => ⟨((-2386857863/137438953472), (3646113115/274877906944)), (7/68719476736), by norm_num⟩
  | 4 => ⟨((2732307529/1099511627776), (-2086907325/1099511627776)), (9/549755813888), by norm_num⟩
  | 5 => ⟨((-625550817/2199023255552), (1911156147/8796093022208)), (9/4398046511104), by norm_num⟩
  | 6 => ⟨((954782287/35184372088832), (-2917010077/140737488355328)), (29/140737488355328), by norm_num⟩
  | 7 => ⟨((-624553039/281474976710656), (954053889/562949953421312)), (21/1125899906842624), by norm_num⟩
  | 8 => ⟨((714944529/4503599627370496), (-2184267999/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 9 => ⟨((-2909931979/288230376151711744), (277821873/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 10 => ⟨((2664868881/4611686018427387904), (-1017699203/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-4437170981/147573952589676412928), (423632979/18446744073709551616)), (49/147573952589676412928), by norm_num⟩
  | 12 => ⟨((3386241487/2361183241434822606848), (-1293187551/1180591620717411303424)), (39/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893164321/5070602400912917605986812821504), (-849651927257/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890709503698493/316912650057057350374175801344), (-1008368022289/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892723064055839/39614081257132168796771975168), (-283594222207/9903520314283042199192993792)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892684100404409/2475880078570760549798248448), (-1205231381191/2475880078570760549798248448)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774349941750807/154742504910672534362390528), (-1205181809525/154742504910672534362390528)), (3449/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12129021818111/75557863725914323419136), (-564902638115/4835703278458516698824704)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261379446483907/604462909807314587353088), (-61782934135/37778931862957161709568)), (1415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((946000610908747/37778931862957161709568), (-1606257529519/75557863725914323419136)), (4599/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300695624489535/4722366482869645213696), (-1204606733173/4722366482869645213696)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625786693640893/590295810358705651712), (-1656193834063/590295810358705651712)), (593/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828896107246481/73786976294838206464), (-2070031654137/73786976294838206464)), (5931/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914376834994719/4611686018427387904), (-1164247989607/4611686018427387904)), (3337/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599999173448055/1152921504606846976), (-2328133933867/1152921504606846976)), (1669/288230376151711744), by norm_num⟩
  | 5 => ⟨((299959758744767/36028797018963968), (-1018354941633/72057594037927936)), (1461/36028797018963968), by norm_num⟩
  | 4 => ⟨((749759030461355/18014398509481984), (-1527125093811/18014398509481984)), (8769/36028797018963968), by norm_num⟩
  | 3 => ⟨((749548352113055/4503599627370496), (-954096768891/2251799813685248)), (1371/1125899906842624), by norm_num⟩
  | 2 => ⟨((561897691103355/1125899906842624), (-3814248500281/2251799813685248)), (10979/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122739742099911/1125899906842624), (-2858013005519/562949953421312)), (16497/1125899906842624), by norm_num⟩
  | 0 => ⟨((279891523884063/281474976710656), (-178291613743/17592186044416)), (2069/70368744177664), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279891523884063/281474976710656), (-178291613743/17592186044416)), (7892608911013581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1113152271725867/1125899906842624), (-22692943942401/1125899906842624)), (66507/1125899906842624), by norm_num⟩
  | 2 => ⟨((1100091582578675/1125899906842624), (-44872020946285/1125899906842624)), (67095/562949953421312), by norm_num⟩
  | 3 => ⟨((134135812656827/140737488355328), (-87686893366449/1125899906842624)), (272925/1125899906842624), by norm_num⟩
  | 4 => ⟨((126990157046271/140737488355328), (-83573700500929/562949953421312)), (281379/562949953421312), by norm_num⟩
  | 5 => ⟨((891871239512789/1125899906842624), (-301640663779807/1125899906842624)), (591333/562949953421312), by norm_num⟩
  | 6 => ⟨((156418704172391/281474976710656), (-477883746250919/1125899906842624)), (1253687/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-384107611/1073741824), (-3723443155/536870912)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((809613031/2199023255552), (-1846591681/4398046511104)), (223/1099511627776), by norm_num⟩
  | 1 => ⟨((1865002545/4398046511104), (549962287/4398046511104)), (1295/2199023255552), by norm_num⟩
  | 2 => ⟨((79187571/4398046511104), (5788200771/35184372088832)), (7459/8796093022208), by norm_num⟩
  | 3 => ⟨((-152536715/4398046511104), (592809403/35184372088832)), (57149/70368744177664), by norm_num⟩
  | 4 => ⟨((-2279443637/562949953421312), (-2634117779/562949953421312)), (328899/562949953421312), by norm_num⟩
  | 5 => ⟨((1098081613/2251799813685248), (-2392254077/4503599627370496)), (1519665/4503599627370496), by norm_num⟩
  | 6 => ⟨((1509123599/36028797018963968), (3820678997/72057594037927936)), (5879799/36028797018963968), by norm_num⟩
  | 7 => ⟨((-3887093819/576460752303423488), (912857555/576460752303423488)), (39228545/576460752303423488), by norm_num⟩
  | 8 => ⟨((123278997/1152921504606846976), (-7476965899/9223372036854775808)), (230645965/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1468541153/18446744073709551616), (2526444215/73786976294838206464)), (304455617/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-820879191/147573952589676412928), (3636961941/590295810358705651712)), (369253457/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-1640342747/4722366482869645213696), (-3341921069/4722366482869645213696)), (3454533903/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1401195885/18889465931478580854784), (-119375039/18889465931478580854784)), (4454858765/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((540787235/68719476736), (517489369/549755813888)), (1563/274877906944), by norm_num⟩
  | 1 => ⟨((-330142467/549755813888), (2067078689/274877906944)), (5009/274877906944), by norm_num⟩
  | 2 => ⟨((-660058173/274877906944), (-8636959/68719476736)), (66509/2199023255552), by norm_num⟩
  | 3 => ⟨((116148875/17592186044416), (-5899821705/17592186044416)), (302283/8796093022208), by norm_num⟩
  | 4 => ⟨((3727887191/281474976710656), (-350759489/281474976710656)), (16861461/562949953421312), by norm_num⟩
  | 5 => ⟨((213310719/1125899906842624), (-2244267889/1125899906842624)), (23993255/1125899906842624), by norm_num⟩
  | 6 => ⟨((4557530285/18014398509481984), (5462685/2251799813685248)), (57935601/4503599627370496), by norm_num⟩
  | 7 => ⟨((1380334791/1152921504606846976), (1606082247/576460752303423488)), (1951552851/288230376151711744), by norm_num⟩
  | 8 => ⟨((347584399/288230376151711744), (164953677/2305843009213693952)), (7342020607/2305843009213693952), by norm_num⟩
  | 9 => ⟨((12801517/4611686018427387904), (148382715/2305843009213693952)), (6357785827/4611686018427387904), by norm_num⟩
  | 10 => ⟨((11649727/4611686018427387904), (1175863/2305843009213693952)), (2674536281/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1801479/18446744073709551616), (6217599/18446744073709551616)), (608119249/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-20349/9223372036854775808), (-839591/36893488147419103232)), (1384755251/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8449801/1073741824), (1010721/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-644809/1073741824), (4037263/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-161147/67108864), (-134953/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((7089/1073741824), (-11253/33554432)), (1/10000000), by norm_num⟩
  | 4 => ⟨((14221/1073741824), (-669/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((203/1073741824), (-535/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((17/67108864), (3/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (3/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨29,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨29,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(5752117/536870912)) (L:=(4357137865/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile029
