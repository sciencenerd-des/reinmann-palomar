/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile006Gamma
public import XiRectangle.Tile006Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile006
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50256991607/137438953472), (23002094069/274877906944)), (1085/274877906944), by norm_num⟩
  | 1 => ⟨((14115723033/274877906944), (7071030337/34359738368)), (2847/274877906944), by norm_num⟩
  | 2 => ⟨((-1719199953/68719476736), (21583111679/1099511627776)), (29437/2199023255552), by norm_num⟩
  | 3 => ⟨((11198220441/2199023255552), (8266632265/2199023255552)), (100375/8796093022208), by norm_num⟩
  | 4 => ⟨((-1544047049/1099511627776), (45590852809/17592186044416)), (65721/8796093022208), by norm_num⟩
  | 5 => ⟨((-29331988419/140737488355328), (-52970507565/140737488355328)), (574139/140737488355328), by norm_num⟩
  | 6 => ⟨((55999140831/562949953421312), (46739024385/562949953421312)), (1085263/562949953421312), by norm_num⟩
  | 7 => ⟨((-19280413625/562949953421312), (19653045589/2251799813685248)), (908001/1125899906842624), by norm_num⟩
  | 8 => ⟨((39222580513/9007199254740992), (-62814430579/9007199254740992)), (2743229/9007199254740992), by norm_num⟩
  | 9 => ⟨((15995695015/36028797018963968), (18697865039/9007199254740992)), (3808975/36028797018963968), by norm_num⟩
  | 10 => ⟨((-65143656883/144115188075855872), (-40128959569/144115188075855872)), (1235189/36028797018963968), by norm_num⟩
  | 11 => ⟨((74096928837/576460752303423488), (-9208890575/288230376151711744)), (1518785/144115188075855872), by norm_num⟩
  | 12 => ⟨((-2400071597/144115188075855872), (66301587519/2305843009213693952)), (1799477/576460752303423488), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile006Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3549293179/17179869184), (28723638089/17179869184)), (2355/34359738368), by norm_num⟩
  | 1 => ⟨((5898928017/8589934592), (4061997191/8589934592)), (1433/17179869184), by norm_num⟩
  | 2 => ⟨((196703675/2147483648), (-278474921/4294967296)), (26605/274877906944), by norm_num⟩
  | 3 => ⟨((-120410305/8589934592), (-5578737/4294967296)), (434379/4398046511104), by norm_num⟩
  | 4 => ⟨((3551695/4294967296), (14884623/8589934592)), (3216983/35184372088832), by norm_num⟩
  | 5 => ⟨((951909/8589934592), (-4435805/17179869184)), (22590131/281474976710656), by norm_num⟩
  | 6 => ⟨((-270945/8589934592), (205537/17179869184)), (160011669/2251799813685248), by norm_num⟩
  | 7 => ⟨((232161/68719476736), (127901/68719476736)), (1173138599/18014398509481984), by norm_num⟩
  | 8 => ⟨((-7827/68719476736), (-28921/68719476736)), (8950998325/144115188075855872), by norm_num⟩
  | 9 => ⟨((-5751/274877906944), (10749/274877906944)), (70060288421/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1105/274877906944), (-679/549755813888)), (69461551525/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-771/2199023255552), (-787/4398046511104)), (69261535653/1152921504606846976), by norm_num⟩
  | 12 => ⟨((57/4398046511104), (145/4398046511104)), (69199800741/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile006Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1833/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1833/640))
  have he : value ((3/4), (1833/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-56325540097/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-25080886978973/562949953421312), (-45701358562305/70368744177664)), (229187/2251799813685248), by norm_num⟩
  | 1 => ⟨((7009482639/274877906944), (102179122989/274877906944)), (9/137438953472), by norm_num⟩
  | 2 => ⟨((-8023964261/1099511627776), (-29241873949/274877906944)), (23/1099511627776), by norm_num⟩
  | 3 => ⟨((3061757231/2199023255552), (2789503919/137438953472)), (5/1099511627776), by norm_num⟩
  | 4 => ⟨((-7009770011/35184372088832), (-102183312089/35184372088832)), (25/35184372088832), by norm_num⟩
  | 5 => ⟨((1604858645/70368744177664), (93577832947/281474976710656)), (25/281474976710656), by norm_num⟩
  | 6 => ⟨((-4899012409/2251799813685248), (-71414228019/2251799813685248)), (21/2251799813685248), by norm_num⟩
  | 7 => ⟨((1602298833/9007199254740992), (93428572673/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 8 => ⟨((-7336797441/576460752303423488), (-26737619833/144115188075855872)), (37/576460752303423488), by norm_num⟩
  | 9 => ⟨((1866366955/2305843009213693952), (27206535555/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1709188825/36893488147419103232), (-99661229889/147573952589676412928)), (39/147573952589676412928), by norm_num⟩
  | 11 => ⟨((2845904769/1180591620717411303424), (82971046047/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-8687445977/75557863725914323419136), (-63319624047/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-2135356910165/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781305531375635/633825300114114700748351602688), (-633486498439/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892595231873187/39614081257132168796771975168), (-712643250065/9903520314283042199192993792)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236568508868735/309485009821345068724781056), (-3028600401413/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443553419647389/38685626227668133590597632), (-3028450271663/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552386797725519/9671406556917033397649408), (-354876572087/1208925819614629174706176)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261267202624955/604462909807314587353088), (-2483976406493/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891818360178227/75557863725914323419136), (-4036162318217/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300558071144879/4722366482869645213696), (-1513429859143/2361183241434822606848)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203199612047995/73786976294838206464), (-4161506149915/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828657868833169/73786976294838206464), (-5201243429115/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((457121072107567/2305843009213693952), (-5850519367335/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599728088367061/1152921504606846976), (-5849419239349/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199599919976941/144115188075855872), (-639625392423/18014398509481984)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((374788889893225/9007199254740992), (-7673024693611/36028797018963968)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498636882159367/9007199254740992), (-4793467469565/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123325527284569/2251799813685248), (-9580404261361/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((561004956684871/562949953421312), (-14354238517439/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | 0 => ⟨((139750808472703/140737488355328), (-14321379510351/562949953421312)), (1051/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((139750808472703/140737488355328), (-14321379510351/562949953421312)), (4009251121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((138679962442237/140737488355328), (-28441950874707/562949953421312)), (1071/562949953421312), by norm_num⟩
  | 2 => ⟨((1090346185457225/1125899906842624), (-112104563615057/1125899906842624)), (4439/1125899906842624), by norm_num⟩
  | 3 => ⟨((1044753058250513/1125899906842624), (-108564520315845/562949953421312)), (9483/1125899906842624), by norm_num⟩
  | 4 => ⟨((927581507104735/1125899906842624), (-402959850793675/1125899906842624)), (10629/562949953421312), by norm_num⟩
  | 5 => ⟨((619975902590247/1125899906842624), (-663963294481633/1125899906842624)), (12561/281474976710656), by norm_num⟩
  | 6 => ⟨((-25080886978973/562949953421312), (-45701358562305/70368744177664)), (229187/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-56325540097/34359738368)), (1/17179869184), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((5230336819/137438953472), (-16576037263/68719476736)), (767/274877906944), by norm_num⟩
  | 1 => ⟨((60244667413/549755813888), (52524751657/549755813888)), (4845/549755813888), by norm_num⟩
  | 2 => ⟨((-60574953577/1099511627776), (27394461/137438953472)), (7633/549755813888), by norm_num⟩
  | 3 => ⟨((32124080633/2199023255552), (-51459179773/4398046511104)), (31911/2199023255552), by norm_num⟩
  | 4 => ⟨((-2608623719/2199023255552), (48850878523/8796093022208)), (50491/4398046511104), by norm_num⟩
  | 5 => ⟨((-25925296091/35184372088832), (-12491056431/8796093022208)), (130555/17592186044416), by norm_num⟩
  | 6 => ⟨((27966013393/70368744177664), (22859671339/140737488355328)), (288573/70368744177664), by norm_num⟩
  | 7 => ⟨((-59185699443/562949953421312), (5130159585/140737488355328)), (1121323/562949953421312), by norm_num⟩
  | 8 => ⟨((30287421089/2251799813685248), (-13947582627/562949953421312)), (1952507/2251799813685248), by norm_num⟩
  | 9 => ⟨((2035692741/1125899906842624), (30660711341/4503599627370496)), (3094733/9007199254740992), by norm_num⟩
  | 10 => ⟨((-54037043381/36028797018963968), (-16159017445/18014398509481984)), (282875/2251799813685248), by norm_num⟩
  | 11 => ⟨((60471207735/144115188075855872), (-15169001457/144115188075855872)), (6183289/144115188075855872), by norm_num⟩
  | 12 => ⟨((-1954542857/36028797018963968), (53289340977/576460752303423488)), (7985657/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((28254353365/68719476736), (1895699527/137438953472)), (6703/274877906944), by norm_num⟩
  | 1 => ⟨((1703164413/549755813888), (121617471831/2199023255552)), (3927/68719476736), by norm_num⟩
  | 2 => ⟨((109170791277/17592186044416), (3515091339/4398046511104)), (744747/8796093022208), by norm_num⟩
  | 3 => ⟨((2692988011/70368744177664), (75273769339/70368744177664)), (3470353/35184372088832), by norm_num⟩
  | 4 => ⟨((86319838805/2251799813685248), (13700156563/1125899906842624)), (53204161/562949953421312), by norm_num⟩
  | 5 => ⟨((684276819/4503599627370496), (22032097013/2251799813685248)), (358691625/4503599627370496), by norm_num⟩
  | 6 => ⟨((29207662113/288230376151711744), (14215750347/144115188075855872)), (18215655347/288230376151711744), by norm_num⟩
  | 7 => ⟨((-748711931/2305843009213693952), (16389523781/288230376151711744)), (116245039381/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-304708951/2305843009213693952), (282736429/576460752303423488)), (97701477351/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-18267753/2305843009213693952), (588102149/2305843009213693952)), (21929321441/576460752303423488), by norm_num⟩
  | 10 => ⟨((-2130975/576460752303423488), (-2876345/576460752303423488)), (20737691649/576460752303423488), by norm_num⟩
  | 11 => ⟨((1392015/1152921504606846976), (1780815/576460752303423488)), (80899930005/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-704275/1152921504606846976), (-314679/576460752303423488)), (80090442733/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((441474271/1073741824), (14810153/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((3326493/1073741824), (59383531/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((832907/134217728), (858177/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((10273/268435456), (574293/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((5145/134217728), (6533/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((163/1073741824), (5253/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((109/1073741824), (53/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (61/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨(0, (1/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨6,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨6,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(108872509/1073741824)) (L:=(226161981189/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile006
