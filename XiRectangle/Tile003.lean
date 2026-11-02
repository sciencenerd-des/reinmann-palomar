/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile003Gamma
public import XiRectangle.Tile003Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile003
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((366361568893/549755813888), (697301013/549755813888)), (983/549755813888), by norm_num⟩
  | 1 => ⟨((7295904945/137438953472), (254257869465/1099511627776)), (5223/1099511627776), by norm_num⟩
  | 2 => ⟨((151725733843/8796093022208), (-219219840101/8796093022208)), (56301/8796093022208), by norm_num⟩
  | 3 => ⟨((30064608033/2199023255552), (185063770013/8796093022208)), (25/4294967296), by norm_num⟩
  | 4 => ⟨((-338691890891/70368744177664), (-138248353805/70368744177664)), (140781/35184372088832), by norm_num⟩
  | 5 => ⟨((288582033589/140737488355328), (3258892635/17592186044416)), (79895/35184372088832), by norm_num⟩
  | 6 => ⟨((-39661494903/70368744177664), (175401918051/562949953421312)), (319941/281474976710656), by norm_num⟩
  | 7 => ⟨((130710575307/1125899906842624), (-187879204525/1125899906842624)), (585751/1125899906842624), by norm_num⟩
  | 8 => ⟨((-14119949719/2251799813685248), (9159890561/140737488355328)), (989421/4503599627370496), by norm_num⟩
  | 9 => ⟨((-73823792863/9007199254740992), (-341575791611/18014398509481984)), (193991/2251799813685248), by norm_num⟩
  | 10 => ⟨((23404219119/4503599627370496), (72082631517/18014398509481984)), (574369/18014398509481984), by norm_num⟩
  | 11 => ⟨((-296277549999/144115188075855872), (-43918561069/144115188075855872)), (817427/72057594037927936), by norm_num⟩
  | 12 => ⟨((177526518405/288230376151711744), (-33654326551/144115188075855872)), (1135691/288230376151711744), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile003Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((185890918549/274877906944), (233615029085/274877906944)), (16757/274877906944), by norm_num⟩
  | 1 => ⟨((19745175853/34359738368), (4156094607/17179869184)), (17357/274877906944), by norm_num⟩
  | 2 => ⟨((1416689293/17179869184), (-421548269/17179869184)), (286027/4398046511104), by norm_num⟩
  | 3 => ⟨((-121437627/17179869184), (-41345569/17179869184)), (2305623/35184372088832), by norm_num⟩
  | 4 => ⟨((-7278241/34359738368), (15140791/17179869184)), (18150067/281474976710656), by norm_num⟩
  | 5 => ⟨((2191535/17179869184), (-2735627/34359738368)), (141464981/2251799813685248), by norm_num⟩
  | 6 => ⟨((-485405/34359738368), (-209675/68719476736)), (1107864743/18014398509481984), by norm_num⟩
  | 7 => ⟨((703/2147483648), (208771/137438953472)), (8750720309/144115188075855872), by norm_num⟩
  | 8 => ⟨((30655/274877906944), (-2835/17179869184)), (69531806117/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-2409/137438953472), (5665/1099511627776)), (138610627401/2305843009213693952), by norm_num⟩
  | 10 => ⟨((2641/2199023255552), (4033/4398046511104)), (138434990921/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-37/8796093022208), (-1371/8796093022208)), (138376270665/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-299/35184372088832), (401/35184372088832)), (138357723977/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile003Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-29499464535/68719476736), (-30329136975/34359738368)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((930940291956061/2251799813685248), (-283080808004593/562949953421312)), (10667/1125899906842624), by norm_num⟩
  | 1 => ⟨((-130087301531/549755813888), (158228057145/549755813888)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((18614352729/274877906944), (-90564192897/1099511627776)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-227289662663/17592186044416), (34557179399/2199023255552)), (15/17592186044416), by norm_num⟩
  | 4 => ⟨((65046317399/35184372088832), (-158234544115/70368744177664)), (5/35184372088832), by norm_num⟩
  | 5 => ⟨((-59568370793/281474976710656), (72454324649/281474976710656)), (21/1125899906842624), by norm_num⟩
  | 6 => ⟨((181839184795/9007199254740992), (-110587507713/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 7 => ⟨((-118946713859/72057594037927936), (72338757189/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 8 => ⟨((68080929089/576460752303423488), (-165616674519/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-138549820773/18446744073709551616), (168521206149/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 10 => ⟨((126881696415/295147905179352825856), (-154329008863/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-52816461765/2361183241434822606848), (32120914309/1180591620717411303424)), (9/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((80614109663/75557863725914323419136), (-98052721521/75557863725914323419136)), (29/151115727451828646838272), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173101/10141204801825835211973625643008), (-143725945875/1267650600228229401496703205376)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890653979329781/316912650057057350374175801344), (-1364432458163/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892598111220205/39614081257132168796771975168), (-767463007767/19807040628566084398385987584)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892551310019019/2475880078570760549798248448), (-1630787312651/2475880078570760549798248448)), (7/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774217119873283/154742504910672534362390528), (-815353391737/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((97024389922097/604462909807314587353088), (-1528702044981/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261270428317011/604462909807314587353088), (-41797772571/18889465931478580854784)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891824004595763/75557863725914323419136), (-2173323729971/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300562656724417/4722366482869645213696), (-814926201895/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812801886930517/295147905179352825856), (-1120409452647/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((457166830978455/18446744073709551616), (-2800681388953/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1828496105104803/9223372036854775808), (-1575147975019/4611686018427387904)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599741379132255/1152921504606846976), (-3149707641123/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599806603499073/72057594037927936), (-2755332279085/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((1499178803430767/36028797018963968), (-4131674456703/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((374667932768635/2251799813685248), (-645284475627/1125899906842624)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((280842264718411/562949953421312), (-5158799243225/2251799813685248)), (11/562949953421312), by norm_num⟩
  | 1 => ⟨((561048443882631/562949953421312), (-7729505148835/1125899906842624)), (33/562949953421312), by norm_num⟩
  | 0 => ⟨((559133473115621/562949953421312), (-3856055409045/281474976710656)), (131/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559133473115621/562949953421312), (-3856055409045/281474976710656)), (499729636764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((555237214614597/562949953421312), (-30639308383025/1125899906842624)), (265/1125899906842624), by norm_num⟩
  | 2 => ⟨((68401656047807/70368744177664), (-60439064399661/1125899906842624)), (269/562949953421312), by norm_num⟩
  | 3 => ⟨((530294242435941/562949953421312), (-117499101148635/1125899906842624)), (1105/1125899906842624), by norm_num⟩
  | 4 => ⟨((986803434941039/1125899906842624), (-221366380623491/1125899906842624)), (2313/1125899906842624), by norm_num⟩
  | 5 => ⟨((410683906766835/562949953421312), (-388036455908971/1125899906842624)), (4965/1125899906842624), by norm_num⟩
  | 6 => ⟨((930940291956061/2251799813685248), (-283080808004593/562949953421312)), (10667/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-29499464535/68719476736), (-30329136975/34359738368)), (1/137438953472), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((151812036739/549755813888), (-183937563033/549755813888)), (905/549755813888), by norm_num⟩
  | 1 => ⟨((-10899673543/549755813888), (286324136843/1099511627776)), (5827/1099511627776), by norm_num⟩
  | 2 => ⟨((-86390555755/2199023255552), (-3890292495/34359738368)), (9489/1099511627776), by norm_num⟩
  | 3 => ⟨((146610834367/4398046511104), (151417604053/4398046511104)), (5199/549755813888), by norm_num⟩
  | 4 => ⟨((-35707722787/2199023255552), (-13619855237/2199023255552)), (68819/8796093022208), by norm_num⟩
  | 5 => ⟨((418665176831/70368744177664), (-35451511697/70368744177664)), (369897/70368744177664), by norm_num⟩
  | 6 => ⟨((-59507681245/35184372088832), (36187569701/35184372088832)), (426183/140737488355328), by norm_num⟩
  | 7 => ⟨((94561129263/281474976710656), (-154065007685/281474976710656)), (875551/562949953421312), by norm_num⟩
  | 8 => ⟨((-15285972623/1125899906842624), (57779564429/281474976710656)), (1642017/2251799813685248), by norm_num⟩
  | 9 => ⟨((-121997127923/4503599627370496), (-268277497075/4503599627370496)), (1424281/4503599627370496), by norm_num⟩
  | 10 => ⟨((298660857483/18014398509481984), (56157128389/4503599627370496)), (72165/562949953421312), by norm_num⟩
  | 11 => ⟨((-468515922991/72057594037927936), (-16651635703/18014398509481984)), (3539419/72057594037927936), by norm_num⟩
  | 12 => ⟨((34970560487/18014398509481984), (-53523195793/72057594037927936)), (649111/36028797018963968), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((517983121201/1099511627776), (4632059537/549755813888)), (43699/1099511627776), by norm_num⟩
  | 1 => ⟨((43124450085/8796093022208), (297225058237/8796093022208)), (572449/8796093022208), by norm_num⟩
  | 2 => ⟨((345834811579/35184372088832), (9286581535/17592186044416)), (742265/8796093022208), by norm_num⟩
  | 3 => ⟨((53750561743/562949953421312), (198925820951/281474976710656)), (52956411/562949953421312), by norm_num⟩
  | 4 => ⟨((107912258373/1125899906842624), (19512597047/2251799813685248)), (423101671/4503599627370496), by norm_num⟩
  | 5 => ⟨((15802383561/18014398509481984), (62779642801/9007199254740992)), (397034525/4503599627370496), by norm_num⟩
  | 6 => ⟨((21178174191/36028797018963968), (10914278655/144115188075855872)), (5859877957/72057594037927936), by norm_num⟩
  | 7 => ⟨((5869614251/1152921504606846976), (3136058721/72057594037927936)), (349928456777/4611686018427387904), by norm_num⟩
  | 8 => ⟨((2970072435/1152921504606846976), (1029058111/2305843009213693952)), (333735431823/4611686018427387904), by norm_num⟩
  | 9 => ⟨((75384033/4611686018427387904), (878795347/4611686018427387904)), (40583912041/576460752303423488), by norm_num⟩
  | 10 => ⟨((50804637/4611686018427387904), (6933565/2305843009213693952)), (320119426295/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4426681/4611686018427387904), (538293/1152921504606846976)), (79506719791/1152921504606846976), by norm_num⟩
  | 12 => ⟨((1801145/4611686018427387904), (-115371/4611686018427387904)), (317134220111/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((126460723/268435456), (9046991/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((5264215/1073741824), (9070589/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((10554041/1073741824), (70851/134217728)), (1/5000000), by norm_num⟩
  | 3 => ⟨((102521/1073741824), (379421/536870912)), (1/5000000), by norm_num⟩
  | 4 => ⟨((102913/1073741824), (1163/134217728)), (1/5000000), by norm_num⟩
  | 5 => ⟨((471/536870912), (1871/268435456)), (1/5000000), by norm_num⟩
  | 6 => ⟨((631/1073741824), (81/1073741824)), (1/5000000), by norm_num⟩
  | 7 => ⟨((5/1073741824), (47/1073741824)), (1/5000000), by norm_num⟩
  | 8 => ⟨((3/1073741824), 0), (1/5000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨3,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨3,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(22501775/268435456)) (L:=(259032979541/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile003
