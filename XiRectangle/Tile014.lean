/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile014Gamma
public import XiRectangle.Tile014Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile014
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10740037445/1099511627776), (99230228059/2199023255552)), (967/2199023255552), by norm_num⟩
  | 1 => ⟨((-77398887111/2199023255552), (1414950021/68719476736)), (2453/2199023255552), by norm_num⟩
  | 2 => ⟨((-34428615201/2199023255552), (-19733555121/4398046511104)), (5885/4398046511104), by norm_num⟩
  | 3 => ⟨((-34154077899/17592186044416), (-28373611917/8796093022208)), (9417/8796093022208), by norm_num⟩
  | 4 => ⟨((1458248349/140737488355328), (-2378249521/4398046511104)), (91753/140737488355328), by norm_num⟩
  | 5 => ⟨((6425707975/1125899906842624), (-4692606849/70368744177664)), (363909/1125899906842624), by norm_num⟩
  | 6 => ⟨((27904458055/9007199254740992), (-54155248651/4503599627370496)), (306057/2251799813685248), by norm_num⟩
  | 7 => ⟨((22211424609/18014398509481984), (-4913716509/4503599627370496)), (1796961/36028797018963968), by norm_num⟩
  | 8 => ⟨((56018865691/576460752303423488), (-17123358049/576460752303423488)), (9405167/576460752303423488), by norm_num⟩
  | 9 => ⟨((14820291215/2305843009213693952), (-14258904571/1152921504606846976)), (11180295/2305843009213693952), by norm_num⟩
  | 10 => ⟨((92518879983/36893488147419103232), (-30127069493/36893488147419103232)), (12374105/9223372036854775808), by norm_num⟩
  | 11 => ⟨((29333817735/295147905179352825856), (25565763559/147573952589676412928)), (27015643/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-60981311249/4722366482869645213696), (-31002751907/2361183241434822606848)), (68648867/590295810358705651712), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile014Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4985024841/2147483648), (49678874297/8589934592)), (387/4294967296), by norm_num⟩
  | 1 => ⟨((33439030591/17179869184), (12249916735/17179869184)), (1155/8589934592), by norm_num⟩
  | 2 => ⟨((-616323559/4294967296), (-1290103393/4294967296)), (45613/274877906944), by norm_num⟩
  | 3 => ⟨((-2757801/268435456), (287505253/4294967296)), (180915/1099511627776), by norm_num⟩
  | 4 => ⟨((73466117/8589934592), (-8640631/1073741824)), (614603/4398046511104), by norm_num⟩
  | 5 => ⟨((-15608945/8589934592), (1328753/8589934592)), (3843671/35184372088832), by norm_num⟩
  | 6 => ⟨((1839041/8589934592), (1193911/8589934592)), (24113843/281474976710656), by norm_num⟩
  | 7 => ⟨((-374411/34359738368), (-527753/17179869184)), (161256853/2251799813685248), by norm_num⟩
  | 8 => ⟨((-79645/68719476736), (126087/34359738368)), (1165274279/18014398509481984), by norm_num⟩
  | 9 => ⟨((2947/8589934592), (-8531/34359738368)), (8886510901/144115188075855872), by norm_num⟩
  | 10 => ⟨((-6009/137438953472), (-109/549755813888)), (69798144421/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1895/549755813888), (5511/2199023255552)), (69359839653/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-277/2199023255552), (-3287/8796093022208)), (69225228709/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile014Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-62824640877/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-637770484509529/1125899906842624), (722357920457207/2251799813685248)), (502205/2251799813685248), by norm_num⟩
  | 1 => ⟨((44560237667/137438953472), (-25235128779/137438953472)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((-25504717889/274877906944), (28887406087/549755813888)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((4866002133/274877906944), (-44091036097/4398046511104)), (39/4398046511104), by norm_num⟩
  | 4 => ⟨((-22281032265/8796093022208), (25236163359/17592186044416)), (3/2199023255552), by norm_num⟩
  | 5 => ⟨((81618443269/281474976710656), (-23110872321/140737488355328)), (47/281474976710656), by norm_num⟩
  | 6 => ⟨((-62287380831/2251799813685248), (35274274979/2251799813685248)), (19/1125899906842624), by norm_num⟩
  | 7 => ⟨((20372064671/9007199254740992), (-23074009583/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 8 => ⟨((-46641022531/288230376151711744), (6603377089/72057594037927936)), (31/288230376151711744), by norm_num⟩
  | 9 => ⟨((47458997687/4611686018427387904), (-6719184979/1152921504606846976)), (33/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-10865546601/18446744073709551616), (24613285933/73786976294838206464)), (63/147573952589676412928), by norm_num⟩
  | 11 => ⟨((18091804975/590295810358705651712), (-10245659635/590295810358705651712)), (55/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-1725852487/1180591620717411303424), (7819008523/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (3421061892011/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890650087806111/316912650057057350374175801344), (2029821346115/316912650057057350374175801344)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892588878639745/39614081257132168796771975168), (570862257465/4951760157141521099596496896)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946270462013271/1237940039285380274899124224), (2426056877851/1237940039285380274899124224)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443551521372183/38685626227668133590597632), (606483899727/19342813113834066795298816)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552379205193503/9671406556917033397649408), (4548371338929/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261260085230947/604462909807314587353088), (3979566797521/604462909807314587353088)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891805905949125/75557863725914323419136), (404144475413/4722366482869645213696)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650273976609725/2361183241434822606848), (4849309363871/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406395430371307/147573952589676412928), (6667109965167/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828637006583781/73786976294838206464), (8332850344031/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((457114553869835/2305843009213693952), (4686514087833/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799849381495517/576460752303423488), (4685619476657/576460752303423488)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199570602983347/144115188075855872), (4098908099777/72057594037927936)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((374776068434103/9007199254740992), (6146338008219/18014398509481984)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498559991313709/9007199254740992), (15358732396991/9007199254740992)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123229480303137/2251799813685248), (15348007273117/2251799813685248)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((560909010035691/562949953421312), (5748750437183/281474976710656)), (1053/1125899906842624), by norm_num⟩
  | 0 => ⟨((279357949439733/281474976710656), (22940395610705/562949953421312)), (2133/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279357949439733/281474976710656), (22940395610705/562949953421312)), (8136753562545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276789430406689/281474976710656), (91071425986553/1125899906842624)), (4409/1125899906842624), by norm_num⟩
  | 2 => ⟨((1081360970479861/1125899906842624), (44777707098019/281474976710656)), (9385/1125899906842624), by norm_num⟩
  | 3 => ⟨((1010090553092847/1125899906842624), (344050937452613/1125899906842624)), (10507/562949953421312), by norm_num⟩
  | 4 => ⟨((200264666602255/281474976710656), (617324150382399/1125899906842624)), (50549/1125899906842624), by norm_num⟩
  | 5 => ⟨((462929038007415/2251799813685248), (1756862604364805/2251799813685248)), (254723/2251799813685248), by norm_num⟩
  | 6 => ⟨((-637770484509529/1125899906842624), (722357920457207/2251799813685248)), (502205/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-62824640877/17179869184)), (1/8589934592), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-19664725691/2199023255552), (-31549990061/1099511627776)), (443/1099511627776), by norm_num⟩
  | 1 => ⟨((81146775373/4398046511104), (-14360807909/2199023255552)), (339/274877906944), by norm_num⟩
  | 2 => ⟨((21325731709/17592186044416), (818757769/137438953472)), (32233/17592186044416), by norm_num⟩
  | 3 => ⟨((-91626469043/70368744177664), (-16807677655/70368744177664)), (7963/4398046511104), by norm_num⟩
  | 4 => ⟨((12503739047/70368744177664), (-27732814105/140737488355328)), (380425/281474976710656), by norm_num⟩
  | 5 => ⟨((15680117833/1125899906842624), (55435010717/1125899906842624)), (918451/1125899906842624), by norm_num⟩
  | 6 => ⟨((-78463149625/9007199254740992), (-22780122671/9007199254740992)), (3739053/9007199254740992), by norm_num⟩
  | 7 => ⟨((41079168051/36028797018963968), (-17898323679/18014398509481984)), (3301173/18014398509481984), by norm_num⟩
  | 8 => ⟨((5071841397/144115188075855872), (8613324409/36028797018963968)), (20653889/288230376151711744), by norm_num⟩
  | 9 => ⟨((-19567457261/576460752303423488), (-2164813953/144115188075855872)), (29093953/1152921504606846976), by norm_num⟩
  | 10 => ⟨((41952749543/9223372036854775808), (-28742300589/9223372036854775808)), (37471007/4611686018427387904), by norm_num⟩
  | 11 => ⟨((6974181127/147573952589676412928), (117347975425/147573952589676412928)), (359997251/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-59248012841/590295810358705651712), (-7473388795/147573952589676412928)), (105240461/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51322459547/274877906944), (4093431021/274877906944)), (915/137438953472), by norm_num⟩
  | 1 => ⟨((-551641887/274877906944), (131147617285/2199023255552)), (1263/68719476736), by norm_num⟩
  | 2 => ⟨((-8870694159/2199023255552), (3788454011/8796093022208)), (502413/17592186044416), by norm_num⟩
  | 3 => ⟨((-11383291849/140737488355328), (80889477021/140737488355328)), (4442593/140737488355328), by norm_num⟩
  | 4 => ⟨((-45746594129/562949953421312), (1656469433/1125899906842624)), (15472593/562949953421312), by norm_num⟩
  | 5 => ⟨((-32823710671/36028797018963968), (42042021357/36028797018963968)), (730167443/36028797018963968), by norm_num⟩
  | 6 => ⟨((-21994639839/36028797018963968), (-1452694697/72057594037927936)), (244763059/18014398509481984), by norm_num⟩
  | 7 => ⟨((-24914393427/4611686018427387904), (-13470566583/1152921504606846976)), (20746979353/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-25010287721/9223372036854775808), (-4429926323/18446744073709551616)), (118300630355/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-6126185/288230376151711744), (-1995575877/18446744073709551616)), (23794364567/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-72304875/9223372036854775808), (-24582225/18446744073709551616)), (85261454911/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-3513561/18446744073709551616), (-8711661/18446744073709551616)), (81433793707/18446744073709551616), by norm_num⟩
  | 12 => ⟨((136799/9223372036854775808), (-78279/2305843009213693952)), (80083795925/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((100239179/536870912), (15989965/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2154851/1073741824), (64036923/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-2165697/536870912), (231229/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-1357/16777216), (308569/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-87255/1073741824), (395/268435456)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-489/536870912), (1253/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-41/67108864), (-11/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-3/536870912), (-13/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-3/1073741824), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨14,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨14,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(55189647/536870912)) (L:=(205941779811/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile014
