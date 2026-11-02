/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile034Gamma
public import XiRectangle.Tile034Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile034
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103157799/274877906944), (419449729/1099511627776)), (1669/2199023255552), by norm_num⟩
  | 1 => ⟨((177515087/2199023255552), (344484461/549755813888)), (3605/2199023255552), by norm_num⟩
  | 2 => ⟨((-390100957/2199023255552), (698048533/2199023255552)), (1993/1099511627776), by norm_num⟩
  | 3 => ⟨((-1081674209/8796093022208), (253659703/4398046511104)), (11903/8796093022208), by norm_num⟩
  | 4 => ⟨((-1284126873/35184372088832), (-212486089/35184372088832)), (26949/35184372088832), by norm_num⟩
  | 5 => ⟨((-407243241/70368744177664), (-743495853/140737488355328)), (49323/140737488355328), by norm_num⟩
  | 6 => ⟨((-433638617/1125899906842624), (-727010709/562949953421312)), (2377/17592186044416), by norm_num⟩
  | 7 => ⟨((361907643/9007199254740992), (-1716741499/9007199254740992)), (203505/4503599627370496), by norm_num⟩
  | 8 => ⟨((134204689/9007199254740992), (-697992533/36028797018963968)), (241411/18014398509481984), by norm_num⟩
  | 9 => ⟨((688487515/288230376151711744), (-390551949/288230376151711744)), (1036805/288230376151711744), by norm_num⟩
  | 10 => ⟨((1289805341/4611686018427387904), (-50301917/1152921504606846976)), (4162335/4611686018427387904), by norm_num⟩
  | 11 => ⟨((245387931/9223372036854775808), (90275923/18446744073709551616)), (4286911/18446744073709551616), by norm_num⟩
  | 12 => ⟨((1244210523/590295810358705651712), (678855831/590295810358705651712)), (11775369/147573952589676412928), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile034Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((819525339/134217728), (243924741/33554432)), (357/67108864), by norm_num⟩
  | 1 => ⟨((-1283618833/268435456), (49920393/16777216)), (827/67108864), by norm_num⟩
  | 2 => ⟨((86798987/33554432), (-7615985/16777216)), (8725/536870912), by norm_num⟩
  | 3 => ⟨((-98998451/134217728), (-7817663/67108864)), (32785/2147483648), by norm_num⟩
  | 4 => ⟨((19706049/134217728), (11021725/134217728)), (23953/2147483648), by norm_num⟩
  | 5 => ⟨((-5458183/268435456), (-1653361/67108864)), (114759/17179869184), by norm_num⟩
  | 6 => ⟨((856995/536870912), (1357397/268435456)), (936557/274877906944), by norm_num⟩
  | 7 => ⟨((75087/1073741824), (-842485/1073741824)), (1678771/1099511627776), by norm_num⟩
  | 8 => ⟨((-107965/2147483648), (100733/1073741824)), (2758347/4398046511104), by norm_num⟩
  | 9 => ⟨((22299/2147483648), (-35257/4294967296)), (18132141/70368744177664), by norm_num⟩
  | 10 => ⟨((-12713/8589934592), (3295/8589934592)), (137546443/1125899906842624), by norm_num⟩
  | 11 => ⟨((11193/68719476736), (937/34359738368)), (175478165/2251799813685248), by norm_num⟩
  | 12 => ⟨((-3835/274877906944), (-639/68719476736)), (1166781607/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile034Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8319/640))
  have he : value ((7/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-1997119511/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((274567722788981/1125899906842624), (-1249306388473287/2251799813685248)), (8606885/562949953421312), by norm_num⟩
  | 1 => ⟨((-599490887/4294967296), (1363867149/4294967296)), (5/536870912), by norm_num⟩
  | 2 => ⟨((343127567/8589934592), (-780629743/8589934592)), (25/8589934592), by norm_num⟩
  | 3 => ⟨((-523717841/68719476736), (595740131/34359738368)), (41/68719476736), by norm_num⟩
  | 4 => ⟨((599515465/549755813888), (-1363923065/549755813888)), (25/274877906944), by norm_num⟩
  | 5 => ⟨((-68628327/549755813888), (312264699/1099511627776)), (3/274877906944), by norm_num⟩
  | 6 => ⟨((209495725/17592186044416), (-953223289/35184372088832)), (39/35184372088832), by norm_num⟩
  | 7 => ⟨((-548150897/562949953421312), (311766625/140737488355328)), (53/562949953421312), by norm_num⟩
  | 8 => ⟨((313742357/4503599627370496), (-1427554293/9007199254740992)), (63/9007199254740992), by norm_num⟩
  | 9 => ⟨((-319244669/72057594037927936), (1452590279/144115188075855872)), (67/144115188075855872), by norm_num⟩
  | 10 => ⟨((292359131/1152921504606846976), (-332564701/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 11 => ⟨((-243397989/18446744073709551616), (1107481461/36893488147419103232)), (7/4611686018427387904), by norm_num⟩
  | 12 => ⟨((11609373/18446744073709551616), (-845178085/590295810358705651712)), (45/590295810358705651712), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-188335603185/1267650600228229401496703205376)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781196662131049/633825300114114700748351602688), (-1787714447293/633825300114114700748351602688)), (17321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892472864687595/39614081257132168796771975168), (-2011085800597/39614081257132168796771975168)), (609/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((59138068414357/77371252455336267181195264), (-1068334589357/1237940039285380274899124224)), (20709/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887041973507201/77371252455336267181195264), (-2136545999303/154742504910672534362390528)), (20711/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552265333853931/9671406556917033397649408), (-500720247123/2417851639229258349412352)), (4855/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78822567574867/37778931862957161709568), (-1752389970381/604462909807314587353088)), (4249/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945823105903089/37778931862957161709568), (-2847388256125/75557863725914323419136)), (27623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650214610701413/2361183241434822606848), (-1067663204307/2361183241434822606848)), (10361/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625420152908181/590295810358705651712), (-733931188529/147573952589676412928)), (7125/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1828437576731075/73786976294838206464), (-3669132295599/73786976294838206464)), (35637/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114264833487609/576460752303423488), (-2063526859859/4611686018427387904)), (10027/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599482230387741/1152921504606846976), (-4126153431633/1152921504606846976)), (40127/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599693012633031/72057594037927936), (-451171403333/18014398509481984)), (17567/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498837178398891/36028797018963968), (-5412030283979/36028797018963968)), (26373/18014398509481984), by norm_num⟩
  | 3 => ⟨((374560802415649/2251799813685248), (-845186281275/1125899906842624)), (16503/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122938305552581/2251799813685248), (-3378083292561/1125899906842624)), (33065/1125899906842624), by norm_num⟩
  | 1 => ⟨((70090324341901/70368744177664), (-5060466418667/562949953421312)), (99493/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116941345149305/1125899906842624), (-10094275223831/562949953421312)), (200175/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1116941345149305/1125899906842624), (-10094275223831/562949953421312)), (763607029441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107692063348829/1125899906842624), (-40055828331777/1125899906842624)), (404345/1125899906842624), by norm_num⟩
  | 2 => ⟨((544176809312909/562949953421312), (-9852013234995/140737488355328)), (824383/1125899906842624), by norm_num⟩
  | 3 => ⟨((261635517835275/281474976710656), (-76187761913049/562949953421312)), (854601/562949953421312), by norm_num⟩
  | 4 => ⟨((952155693690353/1125899906842624), (-283271000126195/1125899906842624)), (1820049/562949953421312), by norm_num⟩
  | 5 => ⟨((733953347444383/1125899906842624), (-479115583877951/1125899906842624)), (7988409/1125899906842624), by norm_num⟩
  | 6 => ⟨((274567722788981/1125899906842624), (-1249306388473287/2251799813685248)), (8606885/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1997119511/268435456)), (3/268435456), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((333338531/1099511627776), (-506560261/4398046511104)), (1359/2199023255552), by norm_num⟩
  | 1 => ⟨((426191881/2199023255552), (765027329/4398046511104)), (1841/1099511627776), by norm_num⟩
  | 2 => ⟨((-243967185/8796093022208), (418418289/4398046511104)), (2543/1099511627776), by norm_num⟩
  | 3 => ⟨((-821048543/35184372088832), (25895329/8796093022208)), (151481/70368744177664), by norm_num⟩
  | 4 => ⟨((-62058743/35184372088832), (-120107093/35184372088832)), (213267/140737488355328), by norm_num⟩
  | 5 => ⟨((753429419/2251799813685248), (-167720111/562949953421312)), (484099/562949953421312), by norm_num⟩
  | 6 => ⟨((473301557/18014398509481984), (496758451/18014398509481984)), (14760439/36028797018963968), by norm_num⟩
  | 7 => ⟨((-804952961/288230376151711744), (296128423/288230376151711744)), (48584369/288230376151711744), by norm_num⟩
  | 8 => ⟨((116451271/2305843009213693952), (-1542144367/4611686018427387904)), (141044927/2305843009213693952), by norm_num⟩
  | 9 => ⟨((1265477247/36893488147419103232), (65273279/4611686018427387904)), (734563445/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-590953621/295147905179352825856), (395287035/147573952589676412928)), (1743527151/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-179852197/1180591620717411303424), (-287856679/1180591620717411303424)), (965976089/590295810358705651712), by norm_num⟩
  | 12 => ⟨((120267505/4722366482869645213696), (-20672263/4722366482869645213696)), (2128614513/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((369494737/137438953472), (412488947/274877906944)), (2885/274877906944), by norm_num⟩
  | 1 => ⟨((-326588757/274877906944), (1078581845/274877906944)), (4715/137438953472), by norm_num⟩
  | 2 => ⟨((-1729911331/1099511627776), (-42798945/137438953472)), (15885/274877906944), by norm_num⟩
  | 3 => ⟨((63639303/2199023255552), (-610220911/2199023255552)), (291905/4398046511104), by norm_num⟩
  | 4 => ⟨((1378797527/70368744177664), (-97108161/70368744177664)), (1023883/17592186044416), by norm_num⟩
  | 5 => ⟨((271165927/562949953421312), (-807825019/1125899906842624)), (23337689/562949953421312), by norm_num⟩
  | 6 => ⟨((971817881/4503599627370496), (27848671/1125899906842624)), (112373029/4503599627370496), by norm_num⟩
  | 7 => ⟨((34781067/18014398509481984), (87162013/9007199254740992)), (1880126173/144115188075855872), by norm_num⟩
  | 8 => ⟨((185357249/288230376151711744), (71144701/288230376151711744)), (109042211/18014398509481984), by norm_num⟩
  | 9 => ⟨((-98693/72057594037927936), (2712133/36028797018963968)), (1465943349/576460752303423488), by norm_num⟩
  | 10 => ⟨((-275049/576460752303423488), (132091/144115188075855872)), (1145764999/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-101973/2305843009213693952), (145223/576460752303423488)), (1757233477/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-72249/9223372036854775808), (-52681/9223372036854775808)), (371171355/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2886677/1073741824), (1611285/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-1275737/1073741824), (2106605/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1689367/1073741824), (-334367/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((15537/536870912), (-297959/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21039/1073741824), (-741/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((517/1073741824), (-385/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((29/134217728), (27/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/536870912), (5/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨34,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨34,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(7917591/1073741824)) (L:=(1692633859/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile034
