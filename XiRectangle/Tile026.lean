/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile026Gamma
public import XiRectangle.Tile026Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile026
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22259031/17179869184), (-2949625241/2199023255552)), (327/549755813888), by norm_num⟩
  | 1 => ⟨((4548750919/2199023255552), (-562371663/2199023255552)), (2929/2199023255552), by norm_num⟩
  | 2 => ⟨((4241778801/4398046511104), (2561604769/4398046511104)), (1637/1099511627776), by norm_num⟩
  | 3 => ⟨((1279457671/8796093022208), (1598794149/4398046511104)), (2465/2199023255552), by norm_num⟩
  | 4 => ⟨((-1629509797/70368744177664), (6713369277/70368744177664)), (11263/17592186044416), by norm_num⟩
  | 5 => ⟨((-3885459297/281474976710656), (1826729341/140737488355328)), (83303/281474976710656), by norm_num⟩
  | 6 => ⟨((-6468288013/2251799813685248), (769178055/1125899906842624)), (129861/1125899906842624), by norm_num⟩
  | 7 => ⟨((-6855188297/18014398509481984), (-1504497447/18014398509481984)), (702581/18014398509481984), by norm_num⟩
  | 8 => ⟨((-2735782365/72057594037927936), (-463271475/18014398509481984)), (842973/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1716700143/576460752303423488), (-289095259/72057594037927936)), (3665665/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1440702545/9223372036854775808), (-4421178625/9223372036854775808)), (7475865/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-50613211/147573952589676412928), (-6860939381/147573952589676412928)), (15802217/73786976294838206464), by norm_num⟩
  | 12 => ⟨((612822201/590295810358705651712), (-564853931/147573952589676412928)), (90384743/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile026Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1325561425/268435456), (117999797/8388608)), (141/134217728), by norm_num⟩
  | 1 => ⟨((-487772511/268435456), (-205004651/67108864)), (2487/1073741824), by norm_num⟩
  | 2 => ⟨((314663169/536870912), (778777585/536870912)), (6673/2147483648), by norm_num⟩
  | 3 => ⟨((3099431/536870912), (-223598285/536870912)), (50855/17179869184), by norm_num⟩
  | 4 => ⟨((-20139587/536870912), (21511367/268435456)), (37607/17179869184), by norm_num⟩
  | 5 => ⟨((13183337/1073741824), (-10937243/1073741824)), (367725/274877906944), by norm_num⟩
  | 6 => ⟨((-5272013/2147483648), (1301325/2147483648)), (781235/1099511627776), by norm_num⟩
  | 7 => ⟨((47239/134217728), (330309/4294967296)), (1523403/4398046511104), by norm_num⟩
  | 8 => ⟨((-313719/8589934592), (-15755/536870912)), (12020909/70368744177664), by norm_num⟩
  | 9 => ⟨((20085/8589934592), (87887/17179869184)), (111069899/1125899906842624), by norm_num⟩
  | 10 => ⟨((847/34359738368), (-43179/68719476736)), (162403733/2251799813685248), by norm_num⟩
  | 11 => ⟨((-8841/274877906944), (15817/274877906944)), (4576948891/72057594037927936), by norm_num⟩
  | 12 => ⟨((5963/1099511627776), (-1985/549755813888)), (4390695579/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile026Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-3452647289/536870912)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((168721794183843/281474976710656), (-201060649016541/2251799813685248)), (4424231/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1473547975/4294967296), (877991233/17179869184)), (21/17179869184), by norm_num⟩
  | 2 => ⟨((1686814405/17179869184), (-251265701/17179869184)), (13/34359738368), by norm_num⟩
  | 3 => ⟨((-2574595815/137438953472), (767016953/274877906944)), (11/137438953472), by norm_num⟩
  | 4 => ⟨((2947216773/1099511627776), (-878027229/2199023255552)), (27/2199023255552), by norm_num⟩
  | 5 => ⟨((-42172089/137438953472), (100510401/2199023255552)), (27/17592186044416), by norm_num⟩
  | 6 => ⟨((2059761093/70368744177664), (-613638719/140737488355328)), (23/140737488355328), by norm_num⟩
  | 7 => ⟨((-5389417327/2251799813685248), (100350083/281474976710656)), (1/70368744177664), by norm_num⟩
  | 8 => ⟨((6169427081/36028797018963968), (-114873739/4503599627370496)), (39/36028797018963968), by norm_num⟩
  | 9 => ⟨((-392351531/36028797018963968), (233776715/144115188075855872)), (43/576460752303423488), by norm_num⟩
  | 10 => ⟨((2874473749/4611686018427387904), (-856355815/9223372036854775808)), (21/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4786176009/147573952589676412928), (356471307/73786976294838206464)), (37/147573952589676412928), by norm_num⟩
  | 12 => ⟨((7305171621/4722366482869645213696), (-272042239/1180591620717411303424)), (59/4722366482869645213696), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-48154757865/2535301200456458802993406410752)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((445299584049901/158456325028528675187087900672), (-114273343549/316912650057057350374175801344)), (1081/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236559356273467/4951760157141521099596496896), (-257103381395/39614081257132168796771975168)), (19/154742504910672534362390528), by norm_num⟩
  | 15 => ⟨((946210211396899/1237940039285380274899124224), (-136579187833/1237940039285380274899124224)), (323/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((887043159981203/77371252455336267181195264), (-273142663843/154742504910672534362390528)), (5169/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552267706596881/9671406556917033397649408), (-256054554783/9671406556917033397649408)), (4845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261163305426521/604462909807314587353088), (-28003880533/75557863725914323419136)), (265/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1891650103770583/75557863725914323419136), (-364019153955/75557863725914323419136)), (6889/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650216191607707/2361183241434822606848), (-272986987085/4722366482869645213696)), (5167/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812712447456107/295147905179352825856), (-187656311471/295147905179352825856)), (3553/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828444095825011/73786976294838206464), (-469074061975/73786976294838206464)), (4441/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828245482926787/9223372036854775808), (-263808300045/4611686018427387904)), (1249/1152921504606846976), by norm_num⟩
  | 6 => ⟨((799745696753851/576460752303423488), (-263750987149/576460752303423488)), (9993/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199395185391469/144115188075855872), (-230717653071/72057594037927936)), (8745/144115188075855872), by norm_num⟩
  | 4 => ⟨((93678325117553/2251799813685248), (-691895198069/36028797018963968)), (6559/18014398509481984), by norm_num⟩
  | 3 => ⟨((749133615705563/4503599627370496), (-864418099111/9007199254740992)), (1025/562949953421312), by norm_num⟩
  | 2 => ⟨((1122968309159403/2251799813685248), (-1727484236605/4503599627370496)), (32807/4503599627370496), by norm_num⟩
  | 1 => ⟨((2243010251906135/2251799813685248), (-2587849017843/2251799813685248)), (49229/2251799813685248), by norm_num⟩
  | 0 => ⟨((2234241601962849/2251799813685248), (-5162204078507/2251799813685248)), (98533/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((2234241601962849/2251799813685248), (-5162204078507/2251799813685248)), (375873574263762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((277101058076577/281474976710656), (-640244030571/140737488355328)), (97991/1125899906842624), by norm_num⟩
  | 2 => ⟨((1091157127141909/1125899906842624), (-20169443166473/2251799813685248)), (387657/2251799813685248), by norm_num⟩
  | 3 => ⟨((2114792207136369/2251799813685248), (-19547058781893/1125899906842624)), (758335/2251799813685248), by norm_num⟩
  | 4 => ⟨((124090119550297/140737488355328), (-36715490722713/1125899906842624)), (1450723/2251799813685248), by norm_num⟩
  | 5 => ⟨((437049005884233/562949953421312), (-64745075194555/1125899906842624)), (2652861/2251799813685248), by norm_num⟩
  | 6 => ⟨((168721794183843/281474976710656), (-201060649016541/2251799813685248)), (4424231/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-3452647289/536870912)), (3/1073741824), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((2888946051/4398046511104), (-2022462931/2199023255552)), (913/2199023255552), by norm_num⟩
  | 1 => ⟨((3699268113/4398046511104), (414337125/2199023255552)), (5101/4398046511104), by norm_num⟩
  | 2 => ⟨((723150773/17592186044416), (1344992155/4398046511104)), (14289/8796093022208), by norm_num⟩
  | 3 => ⟨((-4375712209/70368744177664), (488296519/17592186044416)), (26845/17592186044416), by norm_num⟩
  | 4 => ⟨((-1612193091/281474976710656), (-4785818471/562949953421312)), (304815/281474976710656), by norm_num⟩
  | 5 => ⟨((4351815223/4503599627370496), (-1343757889/2251799813685248)), (2790235/4503599627370496), by norm_num⟩
  | 6 => ⟨((760650353/36028797018963968), (4091460667/36028797018963968)), (10724759/36028797018963968), by norm_num⟩
  | 7 => ⟨((-979901939/72057594037927936), (-1110497549/288230376151711744)), (35610949/288230376151711744), by norm_num⟩
  | 8 => ⟨((1111154539/1152921504606846976), (-3199959861/2305843009213693952)), (104315791/2305843009213693952), by norm_num⟩
  | 9 => ⟨((1915917049/18446744073709551616), (1330522691/9223372036854775808)), (68547403/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-1294679595/73786976294838206464), (1153949679/295147905179352825856)), (41093451/9223372036854775808), by norm_num⟩
  | 11 => ⟨((205436305/590295810358705651712), (-4212576661/2361183241434822606848)), (92250389/73786976294838206464), by norm_num⟩
  | 12 => ⟨((1395951193/9444732965739290427392), (234523887/2361183241434822606848)), (6642144003/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((277986535/17179869184), (322868805/68719476736)), (2625/274877906944), by norm_num⟩
  | 1 => ⟨((-343602663/137438953472), (6831663251/549755813888)), (15833/549755813888), by norm_num⟩
  | 2 => ⟨((-7328275937/2199023255552), (-3518811/8589934592)), (49497/1099511627776), by norm_num⟩
  | 3 => ⟨((21308989/8796093022208), (-3230340921/8796093022208)), (424117/8796093022208), by norm_num⟩
  | 4 => ⟨((1100211783/562949953421312), (-878880433/140737488355328)), (5581953/140737488355328), by norm_num⟩
  | 5 => ⟨((613302853/1125899906842624), (-3765845729/1125899906842624)), (30054617/1125899906842624), by norm_num⟩
  | 6 => ⟨((4436835407/18014398509481984), (-340392985/18014398509481984)), (275892445/18014398509481984), by norm_num⟩
  | 7 => ⟨((172894647/36028797018963968), (-1021734097/144115188075855872)), (2226018627/288230376151711744), by norm_num⟩
  | 8 => ⟨((467546745/288230376151711744), (232675285/2305843009213693952)), (4064915395/1152921504606846976), by norm_num⟩
  | 9 => ⟨((90629637/4611686018427387904), (148445787/4611686018427387904)), (3507821883/2305843009213693952), by norm_num⟩
  | 10 => ⟨((48323481/9223372036854775808), (3829129/4611686018427387904)), (6204257555/9223372036854775808), by norm_num⟩
  | 11 => ⟨((940741/9223372036854775808), (2870827/9223372036854775808)), (804249061/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-109425/18446744073709551616), (17789/2305843009213693952)), (2176109145/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8687079/536870912), (5044825/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-671099/268435456), (3335773/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-894565/268435456), (-439851/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((2601/1073741824), (-394329/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((1049/536870912), (-6705/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((585/1073741824), (-3591/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((33/134217728), (-5/268435456)), (1/10000000), by norm_num⟩
  | 7 => ⟨((5/1073741824), (-1/134217728)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨26,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨26,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(19478735/1073741824)) (L:=(9262978935/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile026
