/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile008Gamma
public import XiRectangle.Tile008Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile008
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((56521590127/274877906944), (15342479717/137438953472)), (629/274877906944), by norm_num⟩
  | 1 => ⟨((1537052691/137438953472), (85724088785/549755813888)), (2797/549755813888), by norm_num⟩
  | 2 => ⟨((-66452022597/2199023255552), (3146579403/137438953472)), (6935/1099511627776), by norm_num⟩
  | 3 => ⟨((-16084218347/8796093022208), (5474835129/8796093022208)), (96145/17592186044416), by norm_num⟩
  | 4 => ⟨((-43086508325/70368744177664), (89798496955/70368744177664)), (253729/70368744177664), by norm_num⟩
  | 5 => ⟨((-21455819085/70368744177664), (-7431017957/140737488355328)), (271697/140737488355328), by norm_num⟩
  | 6 => ⟨((54293833705/2251799813685248), (-18185498037/1125899906842624)), (1978131/2251799813685248), by norm_num⟩
  | 7 => ⟨((-40164323397/9007199254740992), (21244794315/2251799813685248)), (1579933/4503599627370496), by norm_num⟩
  | 8 => ⟨((-26601909895/18014398509481984), (-62154997519/36028797018963968)), (4533199/36028797018963968), by norm_num⟩
  | 9 => ⟨((124973121831/288230376151711744), (437892861/144115188075855872)), (11891383/288230376151711744), by norm_num⟩
  | 10 => ⟨((-17883028687/288230376151711744), (43206415847/576460752303423488)), (7235159/576460752303423488), by norm_num⟩
  | 11 => ⟨((-24243522315/4611686018427387904), (-92314051451/4611686018427387904)), (16591061/4611686018427387904), by norm_num⟩
  | 12 => ⟨((37268468101/9223372036854775808), (1913715207/1152921504606846976)), (9198825/9223372036854775808), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile008Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1209034983/4294967296), (20084605415/8589934592)), (605/8589934592), by norm_num⟩
  | 1 => ⟨((28141667/33554432), (5447706957/8589934592)), (1507/17179869184), by norm_num⟩
  | 2 => ⟨((382711593/4294967296), (-949852331/8589934592)), (27245/274877906944), by norm_num⟩
  | 3 => ⟨((-44534493/2147483648), (17554093/4294967296)), (438987/4398046511104), by norm_num⟩
  | 4 => ⟨((20347861/8589934592), (8511777/4294967296)), (398027/4398046511104), by norm_num⟩
  | 5 => ⟨((-107397/4294967296), (-3843347/8589934592)), (22295219/281474976710656), by norm_num⟩
  | 6 => ⟨((-648613/17179869184), (368519/8589934592)), (79088331/1125899906842624), by norm_num⟩
  | 7 => ⟨((231743/34359738368), (-13493/34359738368)), (1166322855/18014398509481984), by norm_num⟩
  | 8 => ⟨((-39765/68719476736), (-33925/68719476736)), (4460819099/72057594037927936), by norm_num⟩
  | 9 => ⟨((2787/274877906944), (21657/274877906944)), (69984790949/1152921504606846976), by norm_num⟩
  | 10 => ⟨((2433/549755813888), (-7029/1099511627776)), (69437434277/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-1555/2199023255552), (191/1099511627776)), (69252360613/1152921504606846976), by norm_num⟩
  | 12 => ⟨((1/17179869184), (1/34359738368)), (69196523941/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile008Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2397/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2397/640))
  have he : value ((3/4), (2397/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-73656475511/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-794598504509857/2251799813685248), (-1231835600039191/2251799813685248)), (7859/70368744177664), by norm_num⟩
  | 1 => ⟨((27758809063/137438953472), (672397149/2147483648)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((-15888169165/274877906944), (-6157704893/68719476736)), (7/274877906944), by norm_num⟩
  | 3 => ⟨((48500432199/4398046511104), (75188360739/4398046511104)), (3/549755813888), by norm_num⟩
  | 4 => ⟨((-6939986777/4398046511104), (-43035181803/17592186044416)), (1/1099511627776), by norm_num⟩
  | 5 => ⟨((50844225735/281474976710656), (78821854005/281474976710656)), (1/8796093022208), by norm_num⟩
  | 6 => ⟨((-38801936481/2251799813685248), (-60153154625/2251799813685248)), (27/2251799813685248), by norm_num⟩
  | 7 => ⟨((25381563611/18014398509481984), (78696130089/36028797018963968)), (19/18014398509481984), by norm_num⟩
  | 8 => ⟨((-29055034415/288230376151711744), (-45042906007/288230376151711744)), (23/288230376151711744), by norm_num⟩
  | 9 => ⟨((7391148051/1152921504606846976), (45832853913/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-27074777807/73786976294838206464), (-41972990103/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 11 => ⟨((45081174267/2361183241434822606848), (69887616247/2361183241434822606848)), (11/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-17201922491/18889465931478580854784), (-53334961979/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-2792389805583/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890651552045865/316912650057057350374175801344), (-1656810842061/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946296176263097/19807040628566084398385987584), (-3727667303551/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946272415944801/1237940039285380274899124224), (-1980235711179/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221776279664541/19342813113834066795298816), (-990068586549/38685626227668133590597632)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552383356709291/9671406556917033397649408), (-464068463337/1208925819614629174706176)), (103/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315315994236359/151115727451828646838272), (-3248269638687/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945906357892877/37778931862957161709568), (-5278044916581/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300553485588827/4722366482869645213696), (-3958189359487/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625590018947969/590295810358705651712), (-5441950391327/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457162103454813/18446744073709551616), (-425099827731/4611686018427387904)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828472471855793/9223372036854775808), (-3825319804843/4611686018427387904)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399928699434849/288230376151711744), (-3824595551119/576460752303423488)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199586633127575/144115188075855872), (-209106563715/4503599627370496)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499132316101489/36028797018963968), (-5016922100351/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498602034016691/9007199254740992), (-391767707033/281474976710656)), (347/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123281997046479/2251799813685248), (-6263964736377/1125899906842624)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((560961471511883/562949953421312), (-18770199244911/1125899906842624)), (525/1125899906842624), by norm_num⟩
  | 0 => ⟨((139718251194541/140737488355328), (-37453007446211/1125899906842624)), (265/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139718251194541/140737488355328), (-37453007446211/1125899906842624)), (1010895849132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((34637665350177/35184372088832), (-4647721054561/70368744177664)), (17/8796093022208), by norm_num⟩
  | 2 => ⟨((33945966980599/35184372088832), (-146416101896517/1125899906842624)), (4573/1125899906842624), by norm_num⟩
  | 3 => ⟨((514498171859799/562949953421312), (-35315651987895/140737488355328)), (5007/562949953421312), by norm_num⟩
  | 4 => ⟨((434769099729581/562949953421312), (-129104466749715/281474976710656)), (23331/1125899906842624), by norm_num⟩
  | 5 => ⟨((108670687329455/281474976710656), (-797664267506679/1125899906842624)), (57441/1125899906842624), by norm_num⟩
  | 6 => ⟨((-794598504509857/2251799813685248), (-1231835600039191/2251799813685248)), (7859/70368744177664), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-73656475511/34359738368)), (1/17179869184), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-789717799/68719476736), (-20873864807/137438953472)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((48341444441/549755813888), (3544210611/137438953472)), (1595/274877906944), by norm_num⟩
  | 2 => ⟨((-55546164165/2199023255552), (20417979309/1099511627776)), (2381/274877906944), by norm_num⟩
  | 3 => ⟨((12306482811/8796093022208), (-2563463327/274877906944)), (39547/4398046511104), by norm_num⟩
  | 4 => ⟨((54686091109/35184372088832), (36132673005/17592186044416)), (251389/35184372088832), by norm_num⟩
  | 5 => ⟨((-11224090163/17592186044416), (-5663593499/70368744177664)), (647365/140737488355328), by norm_num⟩
  | 6 => ⟨((66441042707/562949953421312), (-3350835605/35184372088832)), (87895/35184372088832), by norm_num⟩
  | 7 => ⟨((-2766633133/1125899906842624), (76923055043/2251799813685248)), (1327809/1125899906842624), by norm_num⟩
  | 8 => ⟨((-11688087075/2251799813685248), (-3038739737/562949953421312)), (4458963/9007199254740992), by norm_num⟩
  | 9 => ⟨((57600967743/36028797018963968), (-5968364055/72057594037927936)), (13550415/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1821174731/9007199254740992), (77797492103/288230376151711744)), (18897283/288230376151711744), by norm_num⟩
  | 11 => ⟨((-20225051893/1152921504606846976), (-39350571191/576460752303423488)), (24485999/1152921504606846976), by norm_num⟩
  | 12 => ⟨((62184842287/4611686018427387904), (3364707049/576460752303423488)), (14931479/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((49250959875/137438953472), (4366069287/274877906944)), (4673/274877906944), by norm_num⟩
  | 1 => ⟨((1796244461/1099511627776), (17502896361/274877906944)), (44671/1099511627776), by norm_num⟩
  | 2 => ⟨((28730134593/8796093022208), (14840033351/17592186044416)), (1071567/17592186044416), by norm_num⟩
  | 3 => ⟨((-39355623/8796093022208), (39710712393/35184372088832)), (2452451/35184372088832), by norm_num⟩
  | 4 => ⟨((-5199706207/1125899906842624), (13191636983/1125899906842624)), (295072237/4503599627370496), by norm_num⟩
  | 5 => ⟨((-779107481/2251799813685248), (84814373743/9007199254740992)), (943773/17592186044416), by norm_num⟩
  | 6 => ⟨((-33551796821/144115188075855872), (1551757697/18014398509481984)), (11807629693/288230376151711744), by norm_num⟩
  | 7 => ⟨((-8452735295/2305843009213693952), (7133875713/144115188075855872)), (72331506283/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-8559073401/4611686018427387904), (958670731/2305843009213693952)), (117648194693/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-3200311/144115188075855872), (846903129/4611686018427387904)), (12952014297/576460752303423488), by norm_num⟩
  | 10 => ⟨((-5053351/576460752303423488), (5991529/4611686018427387904)), (97191992673/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-34697/1152921504606846976), (1191567/2305843009213693952)), (94544033351/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-144509/4611686018427387904), (2921/576460752303423488)), (93546416923/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((96193281/268435456), (8527479/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((1754145/1073741824), (68370689/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((3507097/1073741824), (226441/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-1201/268435456), (1211875/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-4959/1073741824), (12581/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-93/268435456), (10111/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-125/536870912), (23/268435456)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-1/268435456), (53/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-1/536870912), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨8,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨8,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(57109589/536870912)) (L:=(394394538581/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile008
