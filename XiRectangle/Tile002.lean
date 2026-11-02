/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile002Gamma
public import XiRectangle.Tile002Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile002
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((104862918319/137438953472), (-557442019/34359738368)), (159/34359738368), by norm_num⟩
  | 1 => ⟨((6663247185/274877906944), (27796085115/137438953472)), (6389/549755813888), by norm_num⟩
  | 2 => ⟨((55124887359/1099511627776), (-21347212895/549755813888)), (17579/1099511627776), by norm_num⟩
  | 3 => ⟨((6499973595/1099511627776), (7695920533/274877906944)), (4283/274877906944), by norm_num⟩
  | 4 => ⟨((-20471304075/8796093022208), (-7544248619/1099511627776)), (52281/4398046511104), by norm_num⟩
  | 5 => ⟨((36488526195/17592186044416), (38996556115/17592186044416)), (131765/17592186044416), by norm_num⟩
  | 6 => ⟨((-61509188113/70368744177664), (-28936592991/70368744177664)), (283543/70368744177664), by norm_num⟩
  | 7 => ⟨((94436400683/281474976710656), (7756562659/281474976710656)), (534005/281474976710656), by norm_num⟩
  | 8 => ⟨((-61030438027/562949953421312), (4725251063/140737488355328)), (453649/562949953421312), by norm_num⟩
  | 9 => ⟨((67544670669/2251799813685248), (-27003979171/1125899906842624)), (721029/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1805889569/281474976710656), (50796256261/4503599627370496)), (138067/1125899906842624), by norm_num⟩
  | 11 => ⟨((2714583641/4503599627370496), (-78163613493/18014398509481984)), (206147/4503599627370496), by norm_num⟩
  | 12 => ⟨((25531437609/72057594037927936), (103451018047/72057594037927936)), (149999/9007199254740992), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile002Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((26355579261/34359738368), (1290352507/2147483648)), (273/4294967296), by norm_num⟩
  | 1 => ⟨((1195882071/2147483648), (1465119391/8589934592)), (9927/137438953472), by norm_num⟩
  | 2 => ⟨((42728639/536870912), (-34602087/2147483648)), (87731/1099511627776), by norm_num⟩
  | 3 => ⟨((-24728053/4294967296), (-1020583/536870912)), (356043/4398046511104), by norm_num⟩
  | 4 => ⟨((-752337/2147483648), (5237593/8589934592)), (5377197/70368744177664), by norm_num⟩
  | 5 => ⟨((1021119/8589934592), (-102881/2147483648)), (19870387/281474976710656), by norm_num⟩
  | 6 => ⟨((-173119/17179869184), (-28197/8589934592)), (148215189/2251799813685248), by norm_num⟩
  | 7 => ⟨((-4851/34359738368), (37809/34359738368)), (4526879387/72057594037927936), by norm_num⟩
  | 8 => ⟨((8487/68719476736), (-7105/68719476736)), (35275510995/576460752303423488), by norm_num⟩
  | 9 => ⟨((-937/68719476736), (187/137438953472)), (69686995365/1152921504606846976), by norm_num⟩
  | 10 => ⟨((153/274877906944), (7/8589934592)), (69347256741/1152921504606846976), by norm_num⟩
  | 11 => ⟨((47/1099511627776), (-241/2199023255552)), (69228243365/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-77/8796093022208), (7/1099511627776)), (69190494629/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile002Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-29499464535/68719476736), (-5415917317/8589934592)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((592021751410031/1125899906842624), (-216050733680991/562949953421312)), (36139/1125899906842624), by norm_num⟩
  | 1 => ⟨((-41363830073/137438953472), (30190396937/137438953472)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((23675206239/274877906944), (-4319981205/68719476736)), (7/549755813888), by norm_num⟩
  | 3 => ⟨((-18067810757/1099511627776), (52748923645/4398046511104)), (13/4398046511104), by norm_num⟩
  | 4 => ⟨((41365525891/17592186044416), (-1886977167/1099511627776)), (9/17592186044416), by norm_num⟩
  | 5 => ⟨((-37881882985/140737488355328), (55298026419/281474976710656)), (19/281474976710656), by norm_num⟩
  | 6 => ⟨((57819364781/2251799813685248), (-10550217245/562949953421312)), (17/2251799813685248), by norm_num⟩
  | 7 => ⟨((-4727682489/2251799813685248), (55209823921/36028797018963968)), (25/36028797018963968), by norm_num⟩
  | 8 => ⟨((1352979859/9007199254740992), (-15800083859/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 9 => ⟨((-44054655419/4611686018427387904), (32154361231/4611686018427387904)), (9/2305843009213693952), by norm_num⟩
  | 10 => ⟨((40344544535/73786976294838206464), (-29446446609/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-67176153979/2361183241434822606848), (49030149041/2361183241434822606848)), (17/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((25632850359/18889465931478580854784), (-37417517943/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173101/10141204801825835211973625643008), (-821291119291/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781308444116343/633825300114114700748351602688), (-243648653245/158456325028528675187087900672)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473149671772401/9903520314283042199192993792), (-548188012147/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946275978916951/1237940039285380274899124224), (-1164848434921/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774217808131279/154742504910672534362390528), (-1164790958355/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552390926960567/9671406556917033397649408), (-545965227871/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157658884182115/75557863725914323419136), (-29855565073/18889465931478580854784)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891825133482265/75557863725914323419136), (-1552374886941/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650281786921567/2361183241434822606848), (-1164180983173/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625605149361367/590295810358705651712), (-1600586061155/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828669214937943/73786976294838206464), (-250061049913/9223372036854775808)), (93/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828498468451701/9223372036854775808), (-2250213720157/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399936009325445/288230376151711744), (-2249794080607/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199615864422993/144115188075855872), (-492024439001/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1499183452248693/36028797018963968), (-737800644985/9007199254740992)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498678700950247/9007199254740992), (-1843675649619/4503599627370496)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123377765353553/2251799813685248), (-3684873749073/2251799813685248)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122114283130281/1125899906842624), (-5521117934769/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 0 => ⟨((1118319044348083/1125899906842624), (-5508736125939/562949953421312)), (259/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118319044348083/1125899906842624), (-5508736125939/562949953421312)), (988008739280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((555340706867819/562949953421312), (-21886579730527/1125899906842624)), (65/70368744177664), by norm_num⟩
  | 2 => ⟨((1095243167666289/1125899906842624), (-43181489170045/1125899906842624)), (1047/562949953421312), by norm_num⟩
  | 3 => ⟨((531882518167823/562949953421312), (-42005715335545/562949953421312)), (1059/281474976710656), by norm_num⟩
  | 4 => ⟨((998790501013835/1125899906842624), (-79375104356353/562949953421312)), (4319/562949953421312), by norm_num⟩
  | 5 => ⟨((863647674397629/1125899906842624), (-281655943894447/1125899906842624)), (17763/1125899906842624), by norm_num⟩
  | 6 => ⟨((592021751410031/1125899906842624), (-216050733680991/562949953421312)), (36139/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-29499464535/68719476736), (-5415917317/8589934592)), (1/34359738368), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((54283371135/137438953472), (-41417084943/137438953472)), (583/137438953472), by norm_num⟩
  | 1 => ⟨((-18650390711/137438953472), (37042830005/137438953472)), (3577/274877906944), by norm_num⟩
  | 2 => ⟨((6716443129/274877906944), (-79474274647/549755813888)), (183/8589934592), by norm_num⟩
  | 3 => ⟨((670203135/68719476736), (66482231565/1099511627776)), (13397/549755813888), by norm_num⟩
  | 4 => ⟨((-753643327/68719476736), (-45560947987/2199023255552)), (47631/2199023255552), by norm_num⟩
  | 5 => ⟨((27540487559/4398046511104), (50936179019/8796093022208)), (139229/8796093022208), by norm_num⟩
  | 6 => ⟨((-12178419229/4398046511104), (-1284083867/1099511627776)), (5415/549755813888), by norm_num⟩
  | 7 => ⟨((36515854531/35184372088832), (3151401625/70368744177664)), (188197/35184372088832), by norm_num⟩
  | 8 => ⟨((-23712958655/70368744177664), (31447391833/281474976710656)), (729131/281474976710656), by norm_num⟩
  | 9 => ⟨((1636960165/17592186044416), (-43147027749/562949953421312)), (644453/562949953421312), by norm_num⟩
  | 10 => ⟨((-44745454527/2251799813685248), (40112303685/1125899906842624)), (1064461/2251799813685248), by norm_num⟩
  | 11 => ⟨((513944817/281474976710656), (-61514149961/4503599627370496)), (837985/4503599627370496), by norm_num⟩
  | 12 => ⟨((20319199763/18014398509481984), (81292746997/18014398509481984)), (637019/9007199254740992), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66524136367/137438953472), (1696385417/274877906944)), (6881/137438953472), by norm_num⟩
  | 1 => ⟨((23351306217/4398046511104), (108856034701/4398046511104)), (426335/4398046511104), by norm_num⟩
  | 2 => ⟨((11705570829/1099511627776), (1725639877/4398046511104)), (1183815/8796093022208), by norm_num⟩
  | 3 => ⟨((3832533565/35184372088832), (36966652333/70368744177664)), (5470551/35184372088832), by norm_num⟩
  | 4 => ⟨((123135230195/1125899906842624), (3675156081/562949953421312)), (175732581/1125899906842624), by norm_num⟩
  | 5 => ⟨((18997168063/18014398509481984), (23651820589/4503599627370496)), (1282406223/9007199254740992), by norm_num⟩
  | 6 => ⟨((101858688165/144115188075855872), (8312273483/144115188075855872)), (8931934723/72057594037927936), by norm_num⟩
  | 7 => ⟨((7489821161/1152921504606846976), (38354849415/1152921504606846976)), (7766516459/72057594037927936), by norm_num⟩
  | 8 => ⟨((1865429289/576460752303423488), (368411763/1152921504606846976)), (111243824443/1152921504606846976), by norm_num⟩
  | 9 => ⟨((2746965/72057594037927936), (44824261/288230376151711744)), (103516511657/1152921504606846976), by norm_num⟩
  | 10 => ⟨((7685055/1152921504606846976), (818247/1152921504606846976)), (6217541759/72057594037927936), by norm_num⟩
  | 11 => ⟨((2442085/1152921504606846976), (-106569/1152921504606846976)), (48786109213/576460752303423488), by norm_num⟩
  | 12 => ⟨((-698453/1152921504606846976), (141513/288230376151711744)), (96735174193/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519719815/1073741824), (6626505/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((5701003/1073741824), (6644045/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((11431221/1073741824), (421299/1073741824)), (1/5000000), by norm_num⟩
  | 3 => ⟨((3655/33554432), (282033/536870912)), (1/5000000), by norm_num⟩
  | 4 => ⟨((117431/1073741824), (3505/536870912)), (1/5000000), by norm_num⟩
  | 5 => ⟨((283/268435456), (5639/1073741824)), (1/5000000), by norm_num⟩
  | 6 => ⟨((759/1073741824), (31/536870912)), (1/5000000), by norm_num⟩
  | 7 => ⟨((7/1073741824), (9/268435456)), (1/5000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨2,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨2,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(10145871/134217728)) (L:=(532236347131/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile002
