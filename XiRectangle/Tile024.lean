/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile024Gamma
public import XiRectangle.Tile024Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile024
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1491766797/2199023255552), (-2397807357/1099511627776)), (715/1099511627776), by norm_num⟩
  | 1 => ⟨((2323132615/1099511627776), (-3019103311/2199023255552)), (775/549755813888), by norm_num⟩
  | 2 => ⟨((5865719283/4398046511104), (76161709/549755813888)), (3441/2199023255552), by norm_num⟩
  | 3 => ⟨((726190201/2199023255552), (2779548357/8796093022208)), (10391/8796093022208), by norm_num⟩
  | 4 => ⟨((695212333/35184372088832), (3875029209/35184372088832)), (11949/17592186044416), by norm_num⟩
  | 5 => ⟨((-146147695/17592186044416), (5421650277/281474976710656)), (44571/140737488355328), by norm_num⟩
  | 6 => ⟨((-2846863021/1125899906842624), (2140379819/1125899906842624)), (35075/281474976710656), by norm_num⟩
  | 7 => ⟨((-3570442649/9007199254740992), (380446731/4503599627370496)), (383239/9007199254740992), by norm_num⟩
  | 8 => ⟨((-6697154293/144115188075855872), (-498277781/72057594037927936)), (1856393/144115188075855872), by norm_num⟩
  | 9 => ⟨((-2620290451/576460752303423488), (-2677919163/1152921504606846976)), (1017093/288230376151711744), by norm_num⟩
  | 10 => ⟨((-3297650065/9223372036854775808), (-841412359/2305843009213693952)), (8330547/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1552910243/73786976294838206464), (-758760993/18446744073709551616)), (17452215/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-251148167/295147905179352825856), (-279982709/73786976294838206464)), (96246373/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile024Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((481082963/134217728), (1008567857/67108864)), (89/67108864), by norm_num⟩
  | 1 => ⟨((-156409779/268435456), (-1986117433/536870912)), (1683/536870912), by norm_num⟩
  | 2 => ⟨((19018717/536870912), (800374447/536870912)), (9341/2147483648), by norm_num⟩
  | 3 => ⟨((10145841/67108864), (-97024067/268435456)), (9129/2147483648), by norm_num⟩
  | 4 => ⟨((-33012339/536870912), (29425671/536870912)), (55559/17179869184), by norm_num⟩
  | 5 => ⟨((7631999/536870912), (-2077373/536870912)), (553581/274877906944), by norm_num⟩
  | 6 => ⟨((-1219373/536870912), (-507765/1073741824)), (1180083/1099511627776), by norm_num⟩
  | 7 => ⟨((548149/2147483648), (444665/2147483648)), (2268875/4398046511104), by norm_num⟩
  | 8 => ⟨((-36373/2147483648), (-41893/1073741824)), (16952493/70368744177664), by norm_num⟩
  | 9 => ⟨((-6329/17179869184), (87127/17179869184)), (140036811/1125899906842624), by norm_num⟩
  | 10 => ⟨((2569/8589934592), (-8265/17179869184)), (181638549/2251799813685248), by norm_num⟩
  | 11 => ⟨((-439/8589934592), (2059/68719476736)), (4757566107/72057594037927936), by norm_num⟩
  | 12 => ⟨((803/137438953472), (-37/137438953472)), (4440240795/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile024Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-460929133/1073741824), (-6634498713/1073741824)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((1457910369389701/2251799813685248), (152653480865043/2251799813685248)), (4560609/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3183200017/8589934592), (-333303455/8589934592)), (11/8589934592), by norm_num⟩
  | 2 => ⟨((7287808383/68719476736), (190771213/17179869184)), (7/17179869184), by norm_num⟩
  | 3 => ⟨((-5561714705/274877906944), (-291175345/137438953472)), (23/274877906944), by norm_num⟩
  | 4 => ⟨((6366661039/2199023255552), (666634239/2199023255552)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((-5830485731/17592186044416), (-610492909/17592186044416)), (7/4398046511104), by norm_num⟩
  | 6 => ⟨((17381071/549755813888), (116474913/35184372088832)), (23/140737488355328), by norm_num⟩
  | 7 => ⟨((-2910592939/1125899906842624), (-609519149/2251799813685248)), (1/70368744177664), by norm_num⟩
  | 8 => ⟨((6663685445/36028797018963968), (348867393/18014398509481984)), (39/36028797018963968), by norm_num⟩
  | 9 => ⟨((-6780551003/576460752303423488), (-709971433/576460752303423488)), (21/288230376151711744), by norm_num⟩
  | 10 => ⟨((1552379875/2305843009213693952), (325090207/4611686018427387904)), (41/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-2584808199/73786976294838206464), (-541295237/147573952589676412928)), (9/36893488147419103232), by norm_num⟩
  | 12 => ⟨((493151199/295147905179352825856), (413091223/2361183241434822606848)), (29/2361183241434822606848), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173537/10141204801825835211973625643008), (135897415225/10141204801825835211973625643008)), (3641/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222663616994443/79228162514264337593543950336), (161264240761/633825300114114700748351602688)), (1081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((473149817632517/9903520314283042199192993792), (181415219855/39614081257132168796771975168)), (19/154742504910672534362390528), by norm_num⟩
  | 15 => ⟨((1892552614166055/2475880078570760549798248448), (192745223367/2475880078570760549798248448)), (323/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((887109252719143/77371252455336267181195264), (3011495629/2417851639229258349412352)), (323/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1552391624215937/9671406556917033397649408), (180679641335/9671406556917033397649408)), (4845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315317931769743/151115727451828646838272), (158084590495/604462909807314587353088)), (265/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((236478284651395/9444732965739290427392), (64217132931/18889465931478580854784)), (6889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300564503020035/4722366482869645213696), (6019838703/147573952589676412928)), (5167/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812803271473401/295147905179352825856), (264845995365/590295810358705651712)), (7105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828671130825595/73786976294838206464), (331017137959/73786976294838206464)), (555/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828500862872861/9223372036854775808), (93084699663/2305843009213693952)), (9991/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199968341302861/144115188075855872), (186134729573/576460752303423488)), (1249/144115188075855872), by norm_num⟩
  | 5 => ⟨((599809278395441/72057594037927936), (162828893449/72057594037927936)), (8743/144115188075855872), by norm_num⟩
  | 4 => ⟨((749594081099077/18014398509481984), (488330743357/36028797018963968)), (13115/36028797018963968), by norm_num⟩
  | 3 => ⟨((749342881243337/4503599627370496), (610140635551/9007199254740992)), (16395/9007199254740992), by norm_num⟩
  | 2 => ⟨((280846646586873/562949953421312), (609731637189/2251799813685248)), (8199/1125899906842624), by norm_num⟩
  | 1 => ⟨((280532976836513/281474976710656), (1827151263885/2251799813685248)), (24603/1125899906842624), by norm_num⟩
  | 0 => ⟨((1118371828187113/1125899906842624), (3646135996857/2251799813685248)), (49233/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118371828187113/1125899906842624), (3646135996857/2251799813685248)), (187808994773482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1110891132421495/1125899906842624), (3621756921589/1125899906842624)), (195935/2251799813685248), by norm_num⟩
  | 2 => ⟨((2192141563329941/2251799813685248), (14293908804957/2251799813685248)), (96977/562949953421312), by norm_num⟩
  | 3 => ⟨((2133973139461937/2251799813685248), (27830423826631/2251799813685248)), (190047/562949953421312), by norm_num⟩
  | 4 => ⟨((1010983924899437/1125899906842624), (52748362927233/2251799813685248)), (1459613/2251799813685248), by norm_num⟩
  | 5 => ⟨((907179130888731/1125899906842624), (94729108085179/2251799813685248)), (336207/281474976710656), by norm_num⟩
  | 6 => ⟨((1457910369389701/2251799813685248), (152653480865043/2251799813685248)), (4560609/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-460929133/1073741824), (-6634498713/1073741824)), (3/1073741824), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((322734013/549755813888), (-6007508291/4398046511104)), (259/549755813888), by norm_num⟩
  | 1 => ⟨((1236986139/1099511627776), (159054003/4398046511104)), (5653/4398046511104), by norm_num⟩
  | 2 => ⟨((1002933449/8796093022208), (842563871/2199023255552)), (15667/8796093022208), by norm_num⟩
  | 3 => ⟨((-5313102667/70368744177664), (3127025299/70368744177664)), (7345/4398046511104), by norm_num⟩
  | 4 => ⟨((-1114380329/140737488355328), (-185982857/17592186044416)), (41811/35184372088832), by norm_num⟩
  | 5 => ⟨((2973557171/2251799813685248), (-852205123/1125899906842624)), (769383/1125899906842624), by norm_num⟩
  | 6 => ⟨((734079847/36028797018963968), (6138902305/36028797018963968)), (11906573/36028797018963968), by norm_num⟩
  | 7 => ⟨((-6023093373/288230376151711744), (-1873314093/288230376151711744)), (39825345/288230376151711744), by norm_num⟩
  | 8 => ⟨((56477819/36028797018963968), (-4841178197/2305843009213693952)), (29388325/576460752303423488), by norm_num⟩
  | 9 => ⟨((2792001147/18446744073709551616), (1109401893/4611686018427387904)), (155655539/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-4377991075/147573952589676412928), (661005967/147573952589676412928)), (751576921/147573952589676412928), by norm_num⟩
  | 11 => ⟨((951231427/1180591620717411303424), (-111297735/36893488147419103232)), (1694447777/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((4662799079/18889465931478580854784), (3664455175/18889465931478580854784)), (7593893459/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6221260041/274877906944), (539672687/137438953472)), (3123/274877906944), by norm_num⟩
  | 1 => ⟨((-130999943/68719476736), (4305054931/274877906944)), (4619/137438953472), by norm_num⟩
  | 2 => ⟨((-4193787879/1099511627776), (-296111237/1099511627776)), (28681/549755813888), by norm_num⟩
  | 3 => ⟨((-28515747/4398046511104), (-3172901347/8796093022208)), (123115/2199023255552), by norm_num⟩
  | 4 => ⟨((-3576373085/562949953421312), (-2762963183/562949953421312)), (13093539/281474976710656), by norm_num⟩
  | 5 => ⟨((88600377/281474976710656), (-4433526515/1125899906842624)), (17908715/562949953421312), by norm_num⟩
  | 6 => ⟨((7629428799/36028797018963968), (-12798565/562949953421312)), (670799667/36028797018963968), by norm_num⟩
  | 7 => ⟨((60034545/18014398509481984), (-935773223/72057594037927936)), (1383578993/144115188075855872), by norm_num⟩
  | 8 => ⟨((1929101125/1152921504606846976), (13593051/1152921504606846976)), (161532839/36028797018963968), by norm_num⟩
  | 9 => ⟨((36555403/2305843009213693952), (10413223/2305843009213693952)), (4546978383/2305843009213693952), by norm_num⟩
  | 10 => ⟨((7102089/1152921504606846976), (5993111/9223372036854775808)), (8107625775/9223372036854775808), by norm_num⟩
  | 11 => ⟨((1168173/18446744073709551616), (2361285/18446744073709551616)), (8312020989/18446744073709551616), by norm_num⟩
  | 12 => ⟨((267419/18446744073709551616), (498121/18446744073709551616)), (85782255/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24301797/1073741824), (4216193/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1023437/536870912), (16816621/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-511937/134217728), (-289171/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-3481/536870912), (-387317/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-6821/1073741824), (-2635/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((169/536870912), (-1057/268435456)), (1/10000000), by norm_num⟩
  | 6 => ⟨((227/1073741824), (-3/134217728)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/268435456), (-7/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨24,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨24,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(62663923/1073741824)) (L:=(1578548837/68719476736)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile024
