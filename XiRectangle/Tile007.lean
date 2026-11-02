/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile007Gamma
public import XiRectangle.Tile007Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile007
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((76999110273/274877906944), (28080255693/274877906944)), (111/34359738368), by norm_num⟩
  | 1 => ⟨((8776516285/274877906944), (100042734565/549755813888)), (4193/549755813888), by norm_num⟩
  | 2 => ⟨((-31468537707/1099511627776), (12950573631/549755813888)), (19959/2199023255552), by norm_num⟩
  | 3 => ⟨((18162391321/17592186044416), (32706402363/17592186044416)), (16687/2199023255552), by norm_num⟩
  | 4 => ⟨((-7308319129/8796093022208), (34761580703/17592186044416)), (175765/35184372088832), by norm_num⟩
  | 5 => ⟨((-89727823273/281474976710656), (-5690458193/35184372088832)), (763875/281474976710656), by norm_num⟩
  | 6 => ⟨((8520584827/140737488355328), (6030737893/562949953421312)), (1416785/1125899906842624), by norm_num⟩
  | 7 => ⟨((-64722346425/4503599627370496), (61582755611/4503599627370496)), (2307477/4503599627370496), by norm_num⟩
  | 8 => ⟨((-10007088151/18014398509481984), (-1159822599/281474976710656)), (3376365/18014398509481984), by norm_num⟩
  | 9 => ⟨((54719060731/72057594037927936), (20795473089/36028797018963968)), (565089/9007199254740992), by norm_num⟩
  | 10 => ⟨((-31692678861/144115188075855872), (7273882023/144115188075855872)), (351601/18014398509481984), by norm_num⟩
  | 11 => ⟨((13535173265/576460752303423488), (-52859938363/1152921504606846976)), (3301077/576460752303423488), by norm_num⟩
  | 12 => ⟨((10536297723/2305843009213693952), (25317654483/2305843009213693952)), (7456103/4611686018427387904), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile007Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-168579173/8589934592), (68320172249/34359738368)), (2403/34359738368), by norm_num⟩
  | 1 => ⟨((808141769/1073741824), (4758999821/8589934592)), (1527/17179869184), by norm_num⟩
  | 2 => ⟨((791232831/8589934592), (-734201697/8589934592)), (28589/274877906944), by norm_num⟩
  | 3 => ⟨((-74137497/4294967296), (3075929/4294967296)), (464075/4398046511104), by norm_num⟩
  | 4 => ⟨((6411647/4294967296), (4146431/2147483648)), (3393111/35184372088832), by norm_num⟩
  | 5 => ⟨((543783/8589934592), (-2992967/8589934592)), (23442099/281474976710656), by norm_num⟩
  | 6 => ⟨((-312245/8589934592), (426225/17179869184)), (81578699/1125899906842624), by norm_num⟩
  | 7 => ⟨((42871/8589934592), (39281/34359738368)), (1184672935/18014398509481984), by norm_num⟩
  | 8 => ⟨((-42103/137438953472), (-4187/8589934592)), (8989795637/144115188075855872), by norm_num⟩
  | 9 => ⟨((-95/8589934592), (8027/137438953472)), (70169340325/1152921504606846976), by norm_num⟩
  | 10 => ⟨((2551/549755813888), (-29/8589934592)), (69494057381/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-585/1099511627776), (-137/2199023255552)), (69271759269/1152921504606846976), by norm_num⟩
  | 12 => ⟨((281/8796093022208), (311/8796093022208)), (69202028965/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile007Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/128))
  have he : value ((3/4), (423/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-3687433067/8589934592), (-16247751951/8589934592)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-462078313559429/2251799813685248), (-1391146779111179/2251799813685248)), (30365/281474976710656), by norm_num⟩
  | 1 => ⟨((4035605279/34359738368), (97197710795/274877906944)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((-9239355941/274877906944), (-3477035137/34359738368)), (13/549755813888), by norm_num⟩
  | 3 => ⟨((28204178325/4398046511104), (42456171045/2199023255552)), (23/4398046511104), by norm_num⟩
  | 4 => ⟨((-32286165835/35184372088832), (-24300423917/8796093022208)), (29/35184372088832), by norm_num⟩
  | 5 => ⟨((29567151145/281474976710656), (44507874395/140737488355328)), (29/281474976710656), by norm_num⟩
  | 6 => ⟨((-2820533463/281474976710656), (-33966329317/1125899906842624)), (25/2251799813685248), by norm_num⟩
  | 7 => ⟨((3689998799/4503599627370496), (2777305163/1125899906842624)), (35/36028797018963968), by norm_num⟩
  | 8 => ⟨((-66000811/1125899906842624), (-101736455111/576460752303423488)), (43/576460752303423488), by norm_num⟩
  | 9 => ⟨((4298131959/1152921504606846976), (51760338065/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-7872320171/36893488147419103232), (-11850321177/18446744073709551616)), (45/147573952589676412928), by norm_num⟩
  | 11 => ⟨((6553949215/590295810358705651712), (39463030715/1180591620717411303424)), (5/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-20006670765/37778931862957161709568), (-60232680861/37778931862957161709568)), (1/1180591620717411303424), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (-1231936678937/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890652199321573/316912650057057350374175801344), (-2923783838939/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473148472044481/9903520314283042199192993792), (-3289120600263/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946273279693659/1237940039285380274899124224), (-1747268221779/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887106036330373/77371252455336267181195264), (-3494362907009/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24256018623695/151115727451828646838272), (-818945194275/2417851639229258349412352)), (103/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261265697306289/604462909807314587353088), (-1433061828965/302231454903657293676544)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472953931531323/18889465931478580854784), (-4657104808527/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650277965607901/2361183241434822606848), (-3492525580989/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625593686908723/590295810358705651712), (-4801729963783/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828653456485043/73786976294838206464), (-3000711437853/36893488147419103232)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114279923376025/576460752303423488), (-6750582979327/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799860943028521/576460752303423488), (-6749309533231/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199593719425859/144115188075855872), (-5904211495383/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1499144712571491/36028797018963968), (-4426722127961/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((187327577449583/1125899906842624), (-11061767939013/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123305213005351/2251799813685248), (-5527096292777/1125899906842624)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((70123082919023/70368744177664), (-16562283118135/1125899906842624)), (523/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117884918093105/1125899906842624), (-16524069912055/562949953421312)), (33/35184372088832), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117884918093105/1125899906842624), (-16524069912055/562949953421312)), (125885143983353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1108956935661881/1125899906842624), (-65625757415697/1125899906842624)), (135/70368744177664), by norm_num⟩
  | 2 => ⟨((272110943803351/281474976710656), (-129276391981039/1125899906842624)), (1127/281474976710656), by norm_num⟩
  | 3 => ⟨((1037390143811809/1125899906842624), (-124975660161839/562949953421312)), (1219/140737488355328), by norm_num⟩
  | 4 => ⟨((900348815898809/1125899906842624), (-230302031788671/562949953421312)), (22301/1125899906842624), by norm_num⟩
  | 5 => ⟨((531549814747503/1125899906842624), (-736662860916297/1125899906842624)), (53915/1125899906842624), by norm_num⟩
  | 6 => ⟨((-462078313559429/2251799813685248), (-1391146779111179/2251799813685248)), (30365/281474976710656), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-16247751951/8589934592)), (1/17179869184), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((3094536399/549755813888), (-106663426043/549755813888)), (1485/549755813888), by norm_num⟩
  | 1 => ⟨((28216285997/274877906944), (14838545841/274877906944)), (1079/137438953472), by norm_num⟩
  | 2 => ⟨((-21577401349/549755813888), (30193780649/2199023255552)), (3169/274877906944), by norm_num⟩
  | 3 => ⟨((28197609153/4398046511104), (-51268849405/4398046511104)), (6401/549755813888), by norm_num⟩
  | 4 => ⟨((8070267805/8796093022208), (65293605915/17592186044416)), (160453/17592186044416), by norm_num⟩
  | 5 => ⟨((-1858520765/2199023255552), (-19560113929/35184372088832)), (206649/35184372088832), by norm_num⟩
  | 6 => ⟨((70362094743/281474976710656), (-6278411679/140737488355328)), (906219/281474976710656), by norm_num⟩
  | 7 => ⟨((-20001552713/562949953421312), (56201687831/1125899906842624)), (1734867/1125899906842624), by norm_num⟩
  | 8 => ⟨((-1412599259/562949953421312), (-3986136883/281474976710656)), (2958955/4503599627370496), by norm_num⟩
  | 9 => ⟨((49875280195/18014398509481984), (8215997193/4503599627370496)), (4571817/18014398509481984), by norm_num⟩
  | 10 => ⟨((-52836239213/72057594037927936), (26763451517/144115188075855872)), (6489725/72057594037927936), by norm_num⟩
  | 11 => ⟨((354697371/4503599627370496), (-22001562771/144115188075855872)), (4284275/144115188075855872), by norm_num⟩
  | 12 => ⟨((33627296193/2305843009213693952), (83428954317/2305843009213693952)), (10652147/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((106013277289/274877906944), (2061600305/137438953472)), (2665/137438953472), by norm_num⟩
  | 1 => ⟨((2612000843/1099511627776), (66124219421/1099511627776)), (52771/1099511627776), by norm_num⟩
  | 2 => ⟨((41828745825/8796093022208), (229681941/274877906944)), (635779/8796093022208), by norm_num⟩
  | 3 => ⟨((587443673/35184372088832), (39342205645/35184372088832)), (5855863/70368744177664), by norm_num⟩
  | 4 => ⟨((74995118241/4503599627370496), (6878188795/562949953421312)), (22221687/281474976710656), by norm_num⟩
  | 5 => ⟨((-118594187/1125899906842624), (88468486519/9007199254740992)), (592006351/9007199254740992), by norm_num⟩
  | 6 => ⟨((-20594479169/288230376151711744), (54823981955/576460752303423488)), (3686770747/72057594037927936), by norm_num⟩
  | 7 => ⟨((-2406786743/1152921504606846976), (125994758661/2305843009213693952)), (91893777187/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-299873441/288230376151711744), (1126835277/2305843009213693952)), (75581978155/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-40306009/2305843009213693952), (504869649/2305843009213693952)), (133746359441/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-12152611/2305843009213693952), (5112993/4611686018427387904)), (125543105455/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-905377/4611686018427387904), (4333983/4611686018427387904)), (122074869239/4611686018427387904), by norm_num⟩
  | 12 => ⟨((7353/2305843009213693952), (-346827/4611686018427387904)), (120735644975/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103528591/268435456), (4026563/268435456)), (1/10000000), by norm_num⟩
  | 1 => ⟨((1275391/536870912), (64574433/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((39891/8388608), (897195/1073741824)), (1/10000000), by norm_num⟩
  | 3 => ⟨((17927/1073741824), (1200629/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((2235/134217728), (13119/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-113/1073741824), (5273/536870912)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-77/1073741824), (51/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-1/536870912), (59/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-1/1073741824), (1/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨7,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨7,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(14035261/134217728)) (L:=(106093429211/274877906944)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile007
