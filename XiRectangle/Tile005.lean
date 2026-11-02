/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile005Gamma
public import XiRectangle.Tile005Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile005
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((253339250525/549755813888), (15882111925/274877906944)), (281/274877906944), by norm_num⟩
  | 1 => ⟨((71214793441/1099511627776), (247488646835/1099511627776)), (2835/1099511627776), by norm_num⟩
  | 2 => ⟨((-158615000621/8796093022208), (171724755883/17592186044416)), (61003/17592186044416), by norm_num⟩
  | 3 => ⟨((43411961861/4398046511104), (62815157313/8796093022208)), (56139/17592186044416), by norm_num⟩
  | 4 => ⟨((-178229298079/70368744177664), (189124806847/70368744177664)), (155407/70368744177664), by norm_num⟩
  | 5 => ⟨((25974714717/140737488355328), (-180787673947/281474976710656)), (348245/281474976710656), by norm_num⟩
  | 6 => ⟨((47370056967/562949953421312), (63717883023/281474976710656)), (334755/562949953421312), by norm_num⟩
  | 7 => ⟨((-257094170781/4503599627370496), (-29079953425/1125899906842624)), (1143885/4503599627370496), by norm_num⟩
  | 8 => ⟨((296564674437/18014398509481984), (-8862433889/2251799813685248)), (1774065/18014398509481984), by norm_num⟩
  | 9 => ⟨((-97397571661/36028797018963968), (274933725323/72057594037927936)), (2541521/72057594037927936), by norm_num⟩
  | 10 => ⟨((-35291565/281474976710656), (-362341892931/288230376151711744)), (3416419/288230376151711744), by norm_num⟩
  | 11 => ⟨((144263795417/576460752303423488), (135848863057/576460752303423488)), (2189679/576460752303423488), by norm_num⟩
  | 12 => ⟨((-430831844469/4611686018427387904), (-7500398607/2305843009213693952)), (2737981/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile005Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54606257055/137438953472), (189775675307/137438953472)), (16969/274877906944), by norm_num⟩
  | 1 => ⟨((10946687941/17179869184), (27017234233/68719476736)), (17837/274877906944), by norm_num⟩
  | 2 => ⟨((3062164287/34359738368), (-414258567/8589934592)), (74323/1099511627776), by norm_num⟩
  | 3 => ⟨((-384660383/34359738368), (-9906447/4294967296)), (2391639/35184372088832), by norm_num⟩
  | 4 => ⟨((2956341/8589934592), (25131801/17179869184)), (18739891/281474976710656), by norm_num⟩
  | 5 => ⟨((2243419/17179869184), (-1570007/8589934592)), (72436427/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1747717/68719476736), (126231/34359738368)), (1123331239/18014398509481984), by norm_num⟩
  | 7 => ⟨((35213/17179869184), (139383/68719476736)), (4405244571/72057594037927936), by norm_num⟩
  | 8 => ⟨((607/68719476736), (-11389/34359738368)), (69720549797/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-3193/137438953472), (12909/549755813888)), (138749039433/2305843009213693952), by norm_num⟩
  | 10 => ⟨((839/274877906944), (151/2199023255552)), (138481128265/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-1727/8796093022208), (-1853/8796093022208)), (138390688585/2305843009213693952), by norm_num⟩
  | 12 => ⟨((3/4398046511104), (113/4398046511104)), (138361787209/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile005Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1551/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1551/640))
  have he : value ((3/4), (1551/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-29499464535/68719476736), (-190640289557/137438953472)), (3/274877906944), by norm_num⟩
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
  | 0 => ⟨((66944611356889/562949953421312), (-1441214915659811/2251799813685248)), (19987/1125899906842624), by norm_num⟩
  | 1 => ⟨((-18709349931/274877906944), (402783639133/1099511627776)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((85668608043/4398046511104), (-461078469247/4398046511104)), (19/4398046511104), by norm_num⟩
  | 3 => ⟨((-65378277271/17592186044416), (175936767823/8796093022208)), (17/17592186044416), by norm_num⟩
  | 4 => ⟨((37420233939/70368744177664), (-201400076147/70368744177664)), (11/70368744177664), by norm_num⟩
  | 5 => ⟨((-68537696201/1125899906842624), (368877897885/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 6 => ⟨((52304766099/9007199254740992), (-281510369293/9007199254740992)), (19/9007199254740992), by norm_num⟩
  | 7 => ⟨((-68428375915/144115188075855872), (184144761661/72057594037927936)), (27/144115188075855872), by norm_num⟩
  | 8 => ⟨((39166003475/1152921504606846976), (-421592023993/2305843009213693952)), (17/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-79705768333/36893488147419103232), (214492884223/18446744073709551616)), (37/36893488147419103232), by norm_num⟩
  | 10 => ⟨((18248315017/147573952589676412928), (-98214565949/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-30384569551/4722366482869645213696), (40883326861/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 12 => ⟨((46376166445/151115727451828646838272), (-62400488121/37778931862957161709568)), (13/75557863725914323419136), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173101/10141204801825835211973625643008), (-451710115607/2535301200456458802993406410752)), (15/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781306502289219/633825300114114700748351602688), (-536027037135/158456325028528675187087900672)), (9/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892596383612009/39614081257132168796771975168), (-2412024623067/39614081257132168796771975168)), (5/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473137341644123/618970019642690137449562112), (-2562663437663/2475880078570760549798248448)), (21/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887107527550903/77371252455336267181195264), (-2562536599603/154742504910672534362390528)), (21/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776194087067667/4835703278458516698824704), (-1201121637443/4835703278458516698824704)), (5/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261268492900289/604462909807314587353088), (-2101828053763/604462909807314587353088)), (9/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472955154485565/18889465931478580854784), (-3415217763225/75557863725914323419136)), (7/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300559905373895/4722366482869645213696), (-2561192049227/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625599647369887/590295810358705651712), (-3521279401165/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828661650857455/73786976294838206464), (-4401059580981/73786976294838206464)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((114280563443007/576460752303423488), (-1237612426121/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599733404656673/1152921504606846976), (-2474760691891/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((1199605234764835/144115188075855872), (-2164893139541/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 4 => ⟨((1499164857069721/36028797018963968), (-3246294064583/18014398509481984)), (53/36028797018963968), by norm_num⟩
  | 3 => ⟨((749325410816399/4503599627370496), (-2028018050019/2251799813685248)), (33/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123342939758141/2251799813685248), (-4053285678773/1125899906842624)), (65/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122044702642091/1125899906842624), (-12146082569801/1125899906842624)), (49/562949953421312), by norm_num⟩
  | 0 => ⟨((1118110656734689/1125899906842624), (-6059233360917/281474976710656)), (197/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118110656734689/1125899906842624), (-6059233360917/281474976710656)), (751499656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1109853552848361/1125899906842624), (-6017314106973/140737488355328)), (401/1125899906842624), by norm_num⟩
  | 2 => ⟨((1091977701461889/1125899906842624), (-47452441551091/562949953421312)), (413/562949953421312), by norm_num⟩
  | 3 => ⟨((1051077770289545/1125899906842624), (-184090993306949/1125899906842624)), (871/562949953421312), by norm_num⟩
  | 4 => ⟨((475564026105647/562949953421312), (-85928575710639/281474976710656)), (3823/1125899906842624), by norm_num⟩
  | 5 => ⟨((349278406075329/562949953421312), (-580720032736443/1125899906842624)), (8795/1125899906842624), by norm_num⟩
  | 6 => ⟨((66944611356889/562949953421312), (-1441214915659811/2251799813685248)), (19987/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-29499464535/68719476736), (-190640289557/137438953472)), (3/274877906944), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((25228233695/274877906944), (-316733778845/1099511627776)), (27/34359738368), by norm_num⟩
  | 1 => ⟨((13638665287/137438953472), (80634075/536870912)), (5307/2199023255552), by norm_num⟩
  | 2 => ⟨((-297873775929/4398046511104), (-57344427331/2199023255552)), (17089/4398046511104), by norm_num⟩
  | 3 => ⟨((111653261861/4398046511104), (-54024146371/8796093022208)), (4701/1099511627776), by norm_num⟩
  | 4 => ⟨((-97272209443/17592186044416), (55608614525/8796093022208)), (3913/1099511627776), by norm_num⟩
  | 5 => ⟨((8553048789/35184372088832), (-354118017029/140737488355328)), (335893/140737488355328), by norm_num⟩
  | 6 => ⟨((105740556231/281474976710656), (175476394825/281474976710656)), (380513/281474976710656), by norm_num⟩
  | 7 => ⟨((-53318719085/281474976710656), (-41741347729/562949953421312)), (753855/1125899906842624), by norm_num⟩
  | 8 => ⟨((60059298319/1125899906842624), (-4621443491/281474976710656)), (1338555/4503599627370496), by norm_num⟩
  | 9 => ⟨((-150945119383/18014398509481984), (227451954565/18014398509481984)), (2169197/18014398509481984), by norm_num⟩
  | 10 => ⟨((-33125209615/72057594037927936), (-36644353491/9007199254740992)), (3255243/72057594037927936), by norm_num⟩
  | 11 => ⟨((232894638101/288230376151711744), (217188265675/288230376151711744)), (4582471/288230376151711744), by norm_num⟩
  | 12 => ⟨((-42977674595/144115188075855872), (-12409570507/1152921504606846976)), (6134165/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((238719965381/549755813888), (6749084421/549755813888)), (3415/137438953472), by norm_num⟩
  | 1 => ⟨((4151703135/1099511627776), (433017585255/8796093022208)), (6205/137438953472), by norm_num⟩
  | 2 => ⟨((133114946033/17592186044416), (25848625165/35184372088832)), (2011005/35184372088832), by norm_num⟩
  | 3 => ⟨((16678115349/281474976710656), (276800859665/281474976710656)), (17637699/281474976710656), by norm_num⟩
  | 4 => ⟨((267622505879/4503599627370496), (12999842885/1125899906842624)), (282210747/4503599627370496), by norm_num⟩
  | 5 => ⟨((3708964911/9007199254740992), (167268591549/18014398509481984)), (2127361401/36028797018963968), by norm_num⟩
  | 6 => ⟨((317635197489/1152921504606846976), (111506894347/1152921504606846976)), (1966488993/36028797018963968), by norm_num⟩
  | 7 => ⟨((3668262821/2305843009213693952), (64156684545/1152921504606846976)), (469943219183/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1861231451/2305843009213693952), (2426502719/4611686018427387904)), (448319060663/9223372036854775808), by norm_num⟩
  | 9 => ⟨((10288549/4611686018427387904), (140222033/576460752303423488)), (218201048683/4611686018427387904), by norm_num⟩
  | 10 => ⟨((11485309/9223372036854775808), (4524473/9223372036854775808)), (215302131585/4611686018427387904), by norm_num⟩
  | 11 => ⟨((1976041/9223372036854775808), (6414359/4611686018427387904)), (26753805741/576460752303423488), by norm_num⟩
  | 12 => ⟨((-1166527/9223372036854775808), (-336191/2305843009213693952)), (13344804493/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((116562483/268435456), (6590903/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((2027199/536870912), (1651831/33554432)), (1/10000000), by norm_num⟩
  | 2 => ⟨((2031173/268435456), (788837/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((31811/536870912), (1055911/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((31903/536870912), (6199/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((221/536870912), (4985/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((37/134217728), (13/134217728)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/536870912), (15/268435456)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/1073741824), (1/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨5,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨5,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(25995777/268435456)) (L:=(477630702201/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile005
