/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile033Gamma
public import XiRectangle.Tile033Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile033
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((380213135/1099511627776), (268010065/1099511627776)), (173/274877906944), by norm_num⟩
  | 1 => ⟨((40829337/274877906944), (65832077/137438953472)), (2905/2199023255552), by norm_num⟩
  | 2 => ⟨((-430893035/4398046511104), (74950383/274877906944)), (6327/4398046511104), by norm_num⟩
  | 3 => ⟨((-395679059/4398046511104), (534727801/8796093022208)), (9389/8796093022208), by norm_num⟩
  | 4 => ⟨((-130367963/4398046511104), (-38510423/70368744177664)), (42455/70368744177664), by norm_num⟩
  | 5 => ⟨((-727435907/140737488355328), (-503780035/140737488355328)), (9731/35184372088832), by norm_num⟩
  | 6 => ⟨((-486733099/1125899906842624), (-69668491/70368744177664)), (120479/1125899906842624), by norm_num⟩
  | 7 => ⟨((137478975/9007199254740992), (-1394419745/9007199254740992)), (161891/4503599627370496), by norm_num⟩
  | 8 => ⟨((46148951/4503599627370496), (-296475707/18014398509481984)), (772201/72057594037927936), by norm_num⟩
  | 9 => ⟨((63916897/36028797018963968), (-710593869/576460752303423488)), (52163/18014398509481984), by norm_num⟩
  | 10 => ⟨((494878097/2305843009213693952), (-244090137/4611686018427387904)), (1695719/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1543569843/73786976294838206464), (152308729/73786976294838206464)), (7219265/36893488147419103232), by norm_num⟩
  | 12 => ⟨((250270893/147573952589676412928), (223898067/295147905179352825856)), (42676179/590295810358705651712), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile033Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((125412997/16777216), (109042617/16777216)), (1265/134217728), by norm_num⟩
  | 1 => ⟨((-208813937/33554432), (106534469/33554432)), (3179/134217728), by norm_num⟩
  | 2 => ⟨((214636631/67108864), (-22254787/67108864)), (17465/536870912), by norm_num⟩
  | 3 => ⟨((-30118861/33554432), (-7237733/33554432)), (33537/1073741824), by norm_num⟩
  | 4 => ⟨((2913889/16777216), (7926279/67108864)), (49601/2147483648), by norm_num⟩
  | 5 => ⟨((-3031503/134217728), (-559319/16777216)), (240263/17179869184), by norm_num⟩
  | 6 => ⟨((184013/134217728), (886507/134217728)), (986167/137438953472), by norm_num⟩
  | 7 => ⟨((105673/536870912), (-266121/268435456)), (3522995/1099511627776), by norm_num⟩
  | 8 => ⟨((-84015/1073741824), (7601/67108864)), (5662411/4398046511104), by norm_num⟩
  | 9 => ⟨((493/33554432), (-19403/2147483648)), (34335917/70368744177664), by norm_num⟩
  | 10 => ⟨((-17083/8589934592), (141/536870912)), (55030451/281474976710656), by norm_num⟩
  | 11 => ⟨((3585/17179869184), (2163/34359738368)), (223384981/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1149/68719476736), (-63/4294967296)), (1268821159/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile033Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-96026903/268435456), (-1997119511/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((316805866920167/1125899906842624), (-1441493520902153/2251799813685248)), (19817353/1125899906842624), by norm_num⟩
  | 1 => ⟨((-86464201/536870912), (98354859/268435456)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((98978155/2147483648), (-225179493/2147483648)), (7/2147483648), by norm_num⟩
  | 3 => ⟨((-604284011/68719476736), (1374771709/68719476736)), (45/68719476736), by norm_num⟩
  | 4 => ⟨((43233873/34359738368), (-786871131/274877906944)), (7/68719476736), by norm_num⟩
  | 5 => ⟨((-633486163/4398046511104), (45037745/137438953472)), (27/2199023255552), by norm_num⟩
  | 6 => ⟨((483447029/35184372088832), (-549931229/17592186044416)), (43/35184372088832), by norm_num⟩
  | 7 => ⟨((-632475729/562949953421312), (1438909059/562949953421312)), (59/562949953421312), by norm_num⟩
  | 8 => ⟨((362006935/4503599627370496), (-411790551/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 9 => ⟨((-23022231/4503599627370496), (838024801/72057594037927936)), (39/72057594037927936), by norm_num⟩
  | 10 => ⟨((337334219/1152921504606846976), (-191862407/288230376151711744)), (37/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-17552571/1152921504606846976), (638925473/18446744073709551616)), (1/576460752303423488), by norm_num⟩
  | 12 => ⟨((53581207/73786976294838206464), (-60949757/36893488147419103232)), (51/590295810358705651712), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583509786327429/10141204801825835211973625643008), (-188335603185/1267650600228229401496703205376)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445354461680853/158456325028528675187087900672), (-894067764069/316912650057057350374175801344)), (8661/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((29573776358945/618970019642690137449562112), (-1005792652267/19807040628566084398385987584)), (609/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1892682551262861/2475880078570760549798248448), (-2137231086919/2475880078570760549798248448)), (20709/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774348295878435/154742504910672534362390528), (-2137142987391/154742504910672534362390528)), (2589/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552513146947673/9671406556917033397649408), (-1001738966135/4835703278458516698824704)), (4855/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261377903682229/604462909807314587353088), (-219118694761/75557863725914323419136)), (4249/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891998522130953/75557863725914323419136), (-1424183720215/37778931862957161709568)), (27623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300693431197093/4722366482869645213696), (-2136121907553/4722366482869645213696)), (10361/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625783404057269/590295810358705651712), (-2936917847955/590295810358705651712)), (7125/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828891584645973/73786976294838206464), (-1835386274201/36893488147419103232)), (8909/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828748017604351/9223372036854775808), (-4129103658793/9223372036854775808)), (10027/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599992815705127/1152921504606846976), (-4128459094667/1152921504606846976)), (40127/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599916339362145/72057594037927936), (-451459530181/18014398509481984)), (17567/72057594037927936), by norm_num⟩
  | 4 => ⟨((374876735206511/9007199254740992), (-5416062600685/36028797018963968)), (26373/18014398509481984), by norm_num⟩
  | 3 => ⟨((1499080030781789/9007199254740992), (-6767535805423/9007199254740992)), (16503/2251799813685248), by norm_num⟩
  | 2 => ⟨((1123774552132911/2251799813685248), (-6763718416057/2251799813685248)), (66131/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122698117169561/1125899906842624), (-5068010573213/562949953421312)), (99493/1125899906842624), by norm_num⟩
  | 0 => ⟨((559720698496115/562949953421312), (-10116869258411/562949953421312)), (100087/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559720698496115/562949953421312), (-10116869258411/562949953421312)), (381801607372093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((556328155598939/562949953421312), (-40235343077993/1125899906842624)), (405247/1125899906842624), by norm_num⟩
  | 2 => ⟨((274532659719965/281474976710656), (-39762067779617/562949953421312)), (829925/1125899906842624), by norm_num⟩
  | 3 => ⟨((133178669415895/140737488355328), (-155125494295359/1125899906842624)), (868075/562949953421312), by norm_num⟩
  | 4 => ⟨((986833541294335/1125899906842624), (-293587830281281/1125899906842624)), (3764219/1125899906842624), by norm_num⟩
  | 5 => ⟨((788388575875707/1125899906842624), (-64331277690987/140737488355328)), (4280831/562949953421312), by norm_num⟩
  | 6 => ⟨((316805866920167/1125899906842624), (-1441493520902153/2251799813685248)), (19817353/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-96026903/268435456), (-1997119511/268435456)), (3/268435456), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1114206107/4398046511104), (-671925535/4398046511104)), (2597/4398046511104), by norm_num⟩
  | 1 => ⟨((447322533/2199023255552), (279578967/2199023255552)), (6891/4398046511104), by norm_num⟩
  | 2 => ⟨((-192568863/17592186044416), (1613156995/17592186044416)), (37519/17592186044416), by norm_num⟩
  | 3 => ⟨((-375967233/17592186044416), (433678417/70368744177664)), (138559/70368744177664), by norm_num⟩
  | 4 => ⟨((-606827587/281474976710656), (-848939311/281474976710656)), (194303/140737488355328), by norm_num⟩
  | 5 => ⟨((328185581/1125899906842624), (-760313121/2251799813685248)), (1762415/2251799813685248), by norm_num⟩
  | 6 => ⟨((562095729/18014398509481984), (113383601/4503599627370496)), (13447417/36028797018963968), by norm_num⟩
  | 7 => ⟨((-810799827/288230376151711744), (496536885/288230376151711744)), (44363443/288230376151711744), by norm_num⟩
  | 8 => ⟨((-146948641/4611686018427387904), (-825706399/2305843009213693952)), (129198573/2305843009213693952), by norm_num⟩
  | 9 => ⟨((44611929/1152921504606846976), (244976969/36893488147419103232)), (675518691/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-435965597/295147905179352825856), (122519999/36893488147419103232)), (805948169/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-271240081/1180591620717411303424), (-16187115/73786976294838206464)), (901729849/590295810358705651712), by norm_num⟩
  | 12 => ⟨((121766147/4722366482869645213696), (-57081519/4722366482869645213696)), (1018551995/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((198375849/68719476736), (277368387/549755813888)), (3321/274877906944), by norm_num⟩
  | 1 => ⟨((-27298175/68719476736), (553549263/137438953472)), (5523/137438953472), by norm_num⟩
  | 2 => ⟨((-1745766093/1099511627776), (-114003111/1099511627776)), (18863/274877906944), by norm_num⟩
  | 3 => ⟨((10533091/1099511627776), (-1216373073/4398046511104)), (43913/549755813888), by norm_num⟩
  | 4 => ⟨((1350600203/70368744177664), (-16367305/35184372088832)), (78053/1099511627776), by norm_num⟩
  | 5 => ⟨((360296749/2251799813685248), (-1671017331/2251799813685248)), (115455939/2251799813685248), by norm_num⟩
  | 6 => ⟨((1923324665/9007199254740992), (73281399/9007199254740992)), (281955859/9007199254740992), by norm_num⟩
  | 7 => ⟨((46534739/72057594037927936), (673861207/72057594037927936)), (597849557/36028797018963968), by norm_num⟩
  | 8 => ⟨((92673371/144115188075855872), (11491215/144115188075855872)), (1123397817/144115188075855872), by norm_num⟩
  | 9 => ⟨((58627/288230376151711744), (42144521/576460752303423488)), (476230379/144115188075855872), by norm_num⟩
  | 10 => ⟨((-320807/1152921504606846976), (344175/1152921504606846976)), (1490152437/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-2899/1152921504606846976), (717123/2305843009213693952)), (280305729/576460752303423488), by norm_num⟩
  | 12 => ⟨((-159663/4611686018427387904), (-20815/4611686018427387904)), (445704223/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3099623/1073741824), (541735/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-213267/536870912), (1081151/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-852425/536870912), (-111331/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((5143/536870912), (-148483/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((161/8388608), (-499/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((43/268435456), (-797/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((229/1073741824), (9/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/1073741824), (5/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨33,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨33,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(7070343/1073741824)) (L:=(3222126209/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile033
