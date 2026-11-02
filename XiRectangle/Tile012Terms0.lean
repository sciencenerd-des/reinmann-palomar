/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile012Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (705/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (705/128))
  have he : value ((3/4), (705/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/2147483648), (-16397002755/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1044362688119599/2251799813685248), (837875436293377/2251799813685248)), (231957/281474976710656), by norm_num⟩
  | 1 => ⟨((11045792431/34359738368), (-8861862127/34359738368)), (21/34359738368), by norm_num⟩
  | 2 => ⟨((-15312719761/137438953472), (1535643687/17179869184)), (31/137438953472), by norm_num⟩
  | 3 => ⟨((14151958039/549755813888), (-11353888981/549755813888)), (31/549755813888), by norm_num⟩
  | 4 => ⟨((-4904694907/1099511627776), (983739517/274877906944)), (23/2199023255552), by norm_num⟩
  | 5 => ⟨((2719740357/4398046511104), (-4364008145/8796093022208)), (7/4398046511104), by norm_num⟩
  | 6 => ⟨((-10054295255/140737488355328), (8066399845/140737488355328)), (7/35184372088832), by norm_num⟩
  | 7 => ⟨((15929386077/2251799813685248), (-6389945497/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 8 => ⟨((-1380176131/2251799813685248), (8858345411/18014398509481984)), (17/9007199254740992), by norm_num⟩
  | 9 => ⟨((3401476245/72057594037927936), (-10915799371/288230376151711744)), (11/72057594037927936), by norm_num⟩
  | 10 => ⟨((-7544715741/2305843009213693952), (3026502223/1152921504606846976)), (51/4611686018427387904), by norm_num⟩
  | 11 => ⟨((3803344323/18446744073709551616), (-3051362157/18446744073709551616)), (27/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-14060146103/1180591620717411303424), (11280229739/1180591620717411303424)), (13/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455309/5070602400912917605986812821504), (3211537703871/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781161202705043/633825300114114700748351602688), (3810440181103/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892432606735797/39614081257132168796771975168), (2143262633649/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892374970638129/2475880078570760549798248448), (4554189100269/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443510057079583/38685626227668133590597632), (1138478611163/38685626227668133590597632)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388055954083423/2417851639229258349412352), (4269002821387/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630562111111283/302231454903657293676544), (1867542665429/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891585320281709/75557863725914323419136), (3034482774305/37778931862957161709568)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300382681738667/4722366482869645213696), (2275622103131/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625354745850655/590295810358705651712), (3128590095159/295147905179352825856)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914176848031191/36893488147419103232), (7820303182887/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828140053619693/9223372036854775808), (2199056903251/2305843009213693952)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((6247583220057/4503599627370496), (8794207942153/1152921504606846976)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599646808954191/72057594037927936), (7692655923171/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498690378983225/36028797018963968), (11534422100767/36028797018963968)), (1107/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498045393675541/9007199254740992), (14410022634643/9007199254740992)), (1387/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122719040440843/2251799813685248), (14397971475789/2251799813685248)), (2785/2251799813685248), by norm_num⟩
  | 1 => ⟨((560531380044219/562949953421312), (21566676765841/1125899906842624)), (4203/1125899906842624), by norm_num⟩
  | 0 => ⟨((278990727060455/281474976710656), (10752829711633/281474976710656)), (8511/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278990727060455/281474976710656), (10752829711633/281474976710656)), (32466892722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((552235252647747/562949953421312), (5328963544581/70368744177664)), (17523/1125899906842624), by norm_num⟩
  | 2 => ⟨((1076992048288313/1125899906842624), (167281173696229/1125899906842624)), (18517/562949953421312), by norm_num⟩
  | 3 => ⟨((251338701185559/281474976710656), (160014662763763/562949953421312)), (1279/17592186044416), by norm_num⟩
  | 4 => ⟨((806749790723323/1125899906842624), (571530414243987/1125899906842624)), (192719/1125899906842624), by norm_num⟩
  | 5 => ⟨((575891708411941/2251799813685248), (409523119489697/562949953421312)), (943675/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1044362688119599/2251799813685248), (837875436293377/2251799813685248)), (231957/281474976710656), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/2147483648), (-16397002755/4294967296)), (1/2147483648), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/67108864), (-12994317245/2147483648)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((240331463769325/562949953421312), (227355420982339/2251799813685248)), (866977/2251799813685248), by norm_num⟩
  | 1 => ⟨((-8057589705/17179869184), (-476408881/4294967296)), (17/34359738368), by norm_num⟩
  | 2 => ⟨((8852167067/34359738368), (4187109209/68719476736)), (21/68719476736), by norm_num⟩
  | 3 => ⟨((-25933598723/274877906944), (-6133346175/274877906944)), (17/137438953472), by norm_num⟩
  | 4 => ⟨((14245485123/549755813888), (3369084739/549755813888)), (5/137438953472), by norm_num⟩
  | 5 => ⟨((-12520212011/2199023255552), (-5922108633/4398046511104)), (19/2199023255552), by norm_num⟩
  | 6 => ⟨((1146238231/1099511627776), (4337400879/17592186044416)), (15/8796093022208), by norm_num⟩
  | 7 => ⟨((-2878334643/17592186044416), (-5445853607/140737488355328)), (5/17592186044416), by norm_num⟩
  | 8 => ⟨((25297390477/1125899906842624), (5982881695/1125899906842624)), (23/562949953421312), by norm_num⟩
  | 9 => ⟨((-24704021377/9007199254740992), (-5842548757/9007199254740992)), (47/9007199254740992), by norm_num⟩
  | 10 => ⟨((21712113171/72057594037927936), (5134956689/72057594037927936)), (11/18014398509481984), by norm_num⟩
  | 11 => ⟨((-17347777703/576460752303423488), (-1025695731/144115188075855872)), (37/576460752303423488), by norm_num⟩
  | 12 => ⟨((6352827255/2305843009213693952), (6009823651/9223372036854775808)), (57/9223372036854775808), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (302511770723/10141204801825835211973625643008)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780698990599761/633825300114114700748351602688), (179372948475/316912650057057350374175801344)), (541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945956558729799/19807040628566084398385987584), (50444909897/4951760157141521099596496896)), (1217/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891823619107981/2475880078570760549798248448), (107186418269/618970019642690137449562112)), (1293/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773489558278169/154742504910672534362390528), (428705109409/154742504910672534362390528)), (1293/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551708287140753/9671406556917033397649408), (401867946469/9671406556917033397649408)), (303/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630336929010469/302231454903657293676544), (43948920689/75557863725914323419136)), (1061/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890854835387087/75557863725914323419136), (571255192267/75557863725914323419136)), (1723/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81239750319555/295147905179352825856), (428370727245/4722366482869645213696)), (1293/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406151248482453/147573952589676412928), (294447469935/295147905179352825856)), (889/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827419397929813/73786976294838206464), (735946501185/73786976294838206464)), (1111/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456773235738361/2305843009213693952), (413851571227/4611686018427387904)), (625/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1598339159909535/1152921504606846976), (413703702145/576460752303423488)), (625/288230376151711744), by norm_num⟩
  | 5 => ⟨((599193662782215/72057594037927936), (723648912225/144115188075855872)), (547/36028797018963968), by norm_num⟩
  | 4 => ⟨((93583881314455/2251799813685248), (1084808582389/36028797018963968)), (1641/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496379560342205/9007199254740992), (42339004161/281474976710656)), (4103/9007199254740992), by norm_num⟩
  | 2 => ⟨((2242164888896265/4503599627370496), (338276450249/562949953421312)), (513/281474976710656), by norm_num⟩
  | 1 => ⟨((2237361681641465/2251799813685248), (2025308326693/1125899906842624)), (12319/2251799813685248), by norm_num⟩
  | 0 => ⟨((2222980509429447/2251799813685248), (4033247849771/1125899906842624)), (24667/2251799813685248), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222980509429447/2251799813685248), (4033247849771/1125899906842624)), (94097146041106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2194501148333897/2251799813685248), (7963257928391/1125899906842624)), (3055/140737488355328), by norm_num⟩
  | 2 => ⟨((1069273921879045/1125899906842624), (31042508418603/2251799813685248)), (95965/2251799813685248), by norm_num⟩
  | 3 => ⟨((253820478119585/281474976710656), (58962514376267/2251799813685248)), (46231/562949953421312), by norm_num⟩
  | 4 => ⟨((914760016428569/1125899906842624), (106339069746163/2251799813685248)), (343197/2251799813685248), by norm_num⟩
  | 5 => ⟨((1481408574864275/2251799813685248), (172794630493909/2251799813685248)), (295045/1125899906842624), by norm_num⟩
  | 6 => ⟨((240331463769325/562949953421312), (227355420982339/2251799813685248)), (866977/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-12994317245/2147483648)), (3/4294967296), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/1073741824), (-16397002755/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((345197805977693/4503599627370496), (-1554393667924921/4503599627370496)), (3658809/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3651014495/34359738368), (16440179267/34359738368)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((5061380807/68719476736), (-11395463907/34359738368)), (57/68719476736), by norm_num⟩
  | 3 => ⟨((-4677709115/137438953472), (21063289809/137438953472)), (55/137438953472), by norm_num⟩
  | 4 => ⟨((3242340885/274877906944), (-14599959945/274877906944)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((-3595871109/1099511627776), (4047968429/274877906944)), (23/549755813888), by norm_num⟩
  | 6 => ⟨((3323290561/4398046511104), (-14964468819/4398046511104)), (11/1099511627776), by norm_num⟩
  | 7 => ⟨((-2632605123/17592186044416), (23708752847/35184372088832)), (9/4398046511104), by norm_num⟩
  | 8 => ⟨((3649565637/140737488355328), (-16433655191/140737488355328)), (13/35184372088832), by norm_num⟩
  | 9 => ⟨((-2248609895/562949953421312), (20250563133/1125899906842624)), (33/562949953421312), by norm_num⟩
  | 10 => ⟨((4987576349/9007199254740992), (-22458593185/9007199254740992)), (75/9007199254740992), by norm_num⟩
  | 11 => ⟨((-78571011/1125899906842624), (22643069885/72057594037927936)), (39/36028797018963968), by norm_num⟩
  | 12 => ⟨((72615033/9007199254740992), (-20926640067/576460752303423488)), (37/288230376151711744), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357927/5070602400912917605986812821504), (-110092186009/633825300114114700748351602688)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890181746762043/316912650057057350374175801344), (-522043624695/158456325028528675187087900672)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945767790170701/19807040628566084398385987584), (-2348975122495/39614081257132168796771975168)), (813/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59106948659377/77371252455336267181195264), (-1247760443333/1237940039285380274899124224)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221636018925645/19342813113834066795298816), (-2495222571823/154742504910672534362390528)), (27/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((387832953583905/2417851639229258349412352), (-2338954223739/9671406556917033397649408)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260344290519409/604462909807314587353088), (-255783504171/75557863725914323419136)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945159499982499/37778931862957161709568), (-3324591396481/75557863725914323419136)), (9/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1299433876480531/4722366482869645213696), (-623230928093/1180591620717411303424)), (1729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812025828855407/295147905179352825856), (-3426925472139/590295810358705651712)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826727114082045/73786976294838206464), (-2141195032897/36893488147419103232)), (2973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456578320172951/2305843009213693952), (-2407973646223/4611686018427387904)), (3345/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798779222539169/576460752303423488), (-1203442700763/288230376151711744)), (3347/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37428219295417/4503599627370496), (-4209601487023/144115188075855872)), (733/36028797018963968), by norm_num⟩
  | 4 => ⟨((374078319340509/9007199254740992), (-3154753881435/18014398509481984)), (4401/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495089406590513/9007199254740992), (-3939161341005/4503599627370496)), (5509/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119786121360791/2251799813685248), (-7865486252443/2251799813685248)), (5521/2251799813685248), by norm_num⟩
  | 1 => ⟨((279180247991779/281474976710656), (-11766161455549/1125899906842624)), (8309/1125899906842624), by norm_num⟩
  | 0 => ⟨((276877363552741/281474976710656), (-11702095225225/562949953421312)), (16733/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276877363552741/281474976710656), (-11702095225225/562949953421312)), (63831333640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088932886116135/1125899906842624), (-46043812659539/1125899906842624)), (2101/70368744177664), by norm_num⟩
  | 2 => ⟨((525648323881795/562949953421312), (-22266020941305/281474976710656)), (67775/1125899906842624), by norm_num⟩
  | 3 => ⟨((974591279307567/1125899906842624), (-83162608087505/562949953421312)), (34323/281474976710656), by norm_num⟩
  | 4 => ⟨((1638092477958779/2251799813685248), (-143972927102985/562949953421312)), (556493/2251799813685248), by norm_num⟩
  | 5 => ⟨((1044362688119587/2251799813685248), (-837875436293371/2251799813685248)), (136787/281474976710656), by norm_num⟩
  | 6 => ⟨((345197805977693/4503599627370496), (-1554393667924921/4503599627370496)), (3658809/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/1073741824), (-16397002755/2147483648)), (1/1073741824), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/134217728), (-4759082671/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-285237049180721/1125899906842624), (-715787032932707/4503599627370496)), (1874897/2251799813685248), by norm_num⟩
  | 1 => ⟨((14009744903/34359738368), (2197293831/8589934592)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((-11273907295/34359738368), (-7072815993/34359738368)), (5/4294967296), by norm_num⟩
  | 3 => ⟨((12096435881/68719476736), (1897209701/17179869184)), (45/68719476736), by norm_num⟩
  | 4 => ⟨((-1216778907/17179869184), (-6106882441/137438953472)), (37/137438953472), by norm_num⟩
  | 5 => ⟨((12533312665/549755813888), (3931459251/274877906944)), (49/549755813888), by norm_num⟩
  | 6 => ⟨((-6723862857/1099511627776), (-8436586093/2199023255552)), (27/1099511627776), by norm_num⟩
  | 7 => ⟨((12367588343/8796093022208), (3879474717/4398046511104)), (51/8796093022208), by norm_num⟩
  | 8 => ⟨((-4976216391/17592186044416), (-3121886845/17592186044416)), (85/70368744177664), by norm_num⟩
  | 9 => ⟨((14238064569/281474976710656), (8932414305/281474976710656)), (31/140737488355328), by norm_num⟩
  | 10 => ⟨((-18332224733/2251799813685248), (-11500932985/2251799813685248)), (41/1125899906842624), by norm_num⟩
  | 11 => ⟨((5364468637/4503599627370496), (3365461377/4503599627370496)), (25/4503599627370496), by norm_num⟩
  | 12 => ⟨((-5755852803/36028797018963968), (-7222001511/72057594037927936)), (7/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (-3362427473835/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445024736144403/158456325028528675187087900672), (-3984955450001/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945618815203289/19807040628566084398385987584), (-1120643020801/9903520314283042199192993792)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236388170889787/309485009821345068724781056), (-2381071826693/1237940039285380274899124224)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443192672788207/38685626227668133590597632), (-4761480688899/154742504910672534362390528)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551033695891641/9671406556917033397649408), (-4463183679839/9671406556917033397649408)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630041468827005/302231454903657293676544), (-3904581179333/604462909807314587353088)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472473341499513/18889465931478580854784), (-6343623244839/75557863725914323419136)), (1155/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81194614554969/295147905179352825856), (-4756561250717/4722366482869645213696)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811805134611611/295147905179352825856), (-6538392627311/590295810358705651712)), (1193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228271673409395/9223372036854775808), (-8170171630215/73786976294838206464)), (373/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912843801374313/4611686018427387904), (-9187565912445/9223372036854775808)), (105/288230376151711744), by norm_num⟩
  | 6 => ⟨((1596929351944509/1152921504606846976), (-4591359099961/576460752303423488)), (3363/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197148724255903/144115188075855872), (-4014711519573/72057594037927936)), (2947/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495474177613877/36028797018963968), (-6016609767457/18014398509481984)), (4429/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494027157266687/9007199254740992), (-15022413616505/9007199254740992)), (5551/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118703870621901/2251799813685248), (-14993728534811/2251799813685248)), (5573/2251799813685248), by norm_num⟩
  | 1 => ⟨((557523912083395/562949953421312), (-11209407331821/562949953421312)), (4207/562949953421312), by norm_num⟩
  | 0 => ⟨((551982611235265/562949953421312), (-44550129282205/1125899906842624)), (17051/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((551982611235265/562949953421312), (-44550129282205/1125899906842624)), (65044407371139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((540347543778339/562949953421312), (-21841103762963/281474976710656)), (8697/281474976710656), by norm_num⟩
  | 2 => ⟨((515263090528865/562949953421312), (-167713477192775/1125899906842624)), (36091/562949953421312), by norm_num⟩
  | 3 => ⟨((114781117878475/140737488355328), (-153506655532161/562949953421312)), (153641/1125899906842624), by norm_num⟩
  | 4 => ⟨((665178088788737/1125899906842624), (-500781013777425/1125899906842624)), (334401/1125899906842624), by norm_num⟩
  | 5 => ⟨((340492551566547/2251799813685248), (-295859832318749/562949953421312)), (1385197/2251799813685248), by norm_num⟩
  | 6 => ⟨((-285237049180721/1125899906842624), (-715787032932707/4503599627370496)), (1874897/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-4759082671/536870912)), (1/1073741824), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2885830621/2147483648), (-21192818623/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1060901035096447/4503599627370496), (504511811798945/4503599627370496)), (1619409/2251799813685248), by norm_num⟩
  | 1 => ⟨((3625639869/8589934592), (-6896696595/34359738368)), (23/17179869184), by norm_num⟩
  | 2 => ⟨((-12992549135/34359738368), (6178610715/34359738368)), (43/34359738368), by norm_num⟩
  | 3 => ⟨((7759840981/34359738368), (-57659293/536870912)), (53/68719476736), by norm_num⟩
  | 4 => ⟨((-6951884279/68719476736), (3305970695/68719476736)), (49/137438953472), by norm_num⟩
  | 5 => ⟨((9964883589/274877906944), (-9477606877/549755813888)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((-5951558177/549755813888), (5660530623/1099511627776)), (45/1099511627776), by norm_num⟩
  | 7 => ⟨((12187155109/4398046511104), (-1448901335/1099511627776)), (47/4398046511104), by norm_num⟩
  | 8 => ⟨((-10918225285/17592186044416), (2596082687/8796093022208)), (43/17592186044416), by norm_num⟩
  | 9 => ⟨((17389185371/140737488355328), (-4134716211/70368744177664)), (35/70368744177664), by norm_num⟩
  | 10 => ⟨((-3115723755/140737488355328), (5926733539/562949953421312)), (13/140737488355328), by norm_num⟩
  | 11 => ⟨((8120185515/2251799813685248), (-7723113411/4503599627370496)), (69/4503599627370496), by norm_num⟩
  | 12 => ⟨((-9699612859/18014398509481984), (2306326931/9007199254740992)), (21/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (3514049474291/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889943544193433/316912650057057350374175801344), (4163710608991/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890999276714245/39614081257132168796771975168), (4683591755391/39614081257132168796771975168)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890852091931363/2475880078570760549798248448), (4975631027139/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772517388584909/154742504910672534362390528), (4974860023417/154742504910672534362390528)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550796195693991/9671406556917033397649408), (4663112025087/9671406556917033397649408)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259875095999367/604462909807314587353088), (509925464087/75557863725914323419136)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889555569092897/75557863725914323419136), (6627494696037/75557863725914323419136)), (2311/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649430218942797/2361183241434822606848), (2484638297601/2361183241434822606848)), (1735/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405815443613137/147573952589676412928), (3415285189177/295147905179352825856)), (1193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912868827119049/36893488147419103232), (4267467566577/36893488147419103232)), (2985/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825197246204595/9223372036854775808), (9597294299779/9223372036854775808)), (3361/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798219400147685/576460752303423488), (9591658605745/1152921504606846976)), (3365/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598359636715935/72057594037927936), (1048294963221/18014398509481984)), (2949/144115188075855872), by norm_num⟩
  | 4 => ⟨((373707392129427/9007199254740992), (1570856611161/4503599627370496)), (277/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493220646035847/9007199254740992), (7843178293949/4503599627370496)), (5555/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117896249864679/2251799813685248), (489157086607/70368744177664)), (2789/1125899906842624), by norm_num⟩
  | 1 => ⟨((556916836265043/562949953421312), (2924520254807/140737488355328)), (8425/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101526356195155/1125899906842624), (46458496370795/1125899906842624)), (8541/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101526356195155/1125899906842624), (46458496370795/1125899906842624)), (32581331493186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((537881704291161/562949953421312), (45452759975031/562949953421312)), (34835/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020519755534423/1125899906842624), (86857482984139/562949953421312)), (36097/562949953421312), by norm_num⟩
  | 3 => ⟨((898200342578085/1125899906842624), (157455874652095/562949953421312)), (2393/17592186044416), by norm_num⟩
  | 4 => ⟨((2454961392359/4398046511104), (502449355200851/1125899906842624)), (330031/1125899906842624), by norm_num⟩
  | 5 => ⟨((1977853058017/17592186044416), (560928023621165/1125899906842624)), (663005/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1060901035096447/4503599627370496), (504511811798945/4503599627370496)), (1619409/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-21192818623/2147483648)), (1/1073741824), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3134107669/2147483648), (-5754025799/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-287057340250531/4503599627370496), (125794056844423/562949953421312)), (1395429/2251799813685248), by norm_num⟩
  | 1 => ⟨((1065421661/8589934592), (-14940425531/34359738368)), (43/34359738368), by norm_num⟩
  | 2 => ⟨((-2073214823/17179869184), (3634090709/8589934592)), (43/34359738368), by norm_num⟩
  | 3 => ⟨((1344763255/17179869184), (-4714409329/17179869184)), (29/34359738368), by norm_num⟩
  | 4 => ⟨((-1308394233/34359738368), (71670445/536870912)), (29/68719476736), by norm_num⟩
  | 5 => ⟨((4073628187/274877906944), (-14281138823/274877906944)), (47/274877906944), by norm_num⟩
  | 6 => ⟨((-2642304811/549755813888), (578954437/34359738368)), (31/549755813888), by norm_num⟩
  | 7 => ⟨((2938107285/2199023255552), (-20600563471/4398046511104)), (35/2199023255552), by norm_num⟩
  | 8 => ⟨((-5717292785/17592186044416), (20043422767/17592186044416)), (35/8796093022208), by norm_num⟩
  | 9 => ⟨((4944594691/70368744177664), (-8667266619/35184372088832)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((-3848694797/281474976710656), (13492577663/281474976710656)), (49/281474976710656), by norm_num⟩
  | 11 => ⟨((5446701285/2251799813685248), (-19094795499/2251799813685248)), (71/2251799813685248), by norm_num⟩
  | 12 => ⟨((-7065860873/18014398509481984), (3096396363/2251799813685248)), (47/9007199254740992), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182135/10141204801825835211973625643008), (2408089142847/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779713574765847/633825300114114700748351602688), (2852741709031/633825300114114700748351602688)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890804387842015/39614081257132168796771975168), (1604456119669/19807040628566084398385987584)), (1627/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890645415191115/2475880078570760549798248448), (53265010561/38685626227668133590597632)), (1729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443077788369139/38685626227668133590597632), (852097140663/38685626227668133590597632)), (1729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775301659669965/4835703278458516698824704), (3194756470947/9671406556917033397649408)), (811/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629853399027099/302231454903657293676544), (1397402088623/302231454903657293676544)), (1419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889282963637971/75557863725914323419136), (2270208718825/37778931862957161709568)), (2307/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298656752246895/4722366482869645213696), (425539537395/590295810358705651712)), (1731/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202872869332005/73786976294838206464), (4679315431423/590295810358705651712)), (595/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825391000064879/73786976294838206464), (5846715570305/73786976294838206464)), (2977/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912404915041179/4611686018427387904), (6574216342497/9223372036854775808)), (3351/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798027296564755/576460752303423488), (6570044222517/1152921504606846976)), (1677/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196386697669611/144115188075855872), (718012092789/18014398509481984)), (1469/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494337904468693/36028797018963968), (4303382709761/18014398509481984)), (1103/9007199254740992), by norm_num⟩
  | 3 => ⟨((46644332486355/281474976710656), (2685512949089/2251799813685248)), (2763/4503599627370496), by norm_num⟩
  | 2 => ⟨((69832065772789/140737488355328), (5358731665931/1125899906842624)), (2771/1125899906842624), by norm_num⟩
  | 1 => ⟨((278251429684709/281474976710656), (4003697619863/281474976710656)), (261/35184372088832), by norm_num⟩
  | 0 => ⟨((1100056738350621/1125899906842624), (3973045476135/140737488355328)), (16863/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100056738350621/1125899906842624), (3973045476135/140737488355328)), (64327244285201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536954739253241/562949953421312), (31054806355227/562949953421312)), (33905/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020893559942079/1125899906842624), (29620795503559/281474976710656)), (17105/281474976710656), by norm_num⟩
  | 3 => ⟨((228303020113561/281474976710656), (6714557658759/35184372088832)), (138479/1125899906842624), by norm_num⟩
  | 4 => ⟨((1399394329314245/2251799813685248), (697106676044005/2251799813685248)), (138747/562949953421312), by norm_num⟩
  | 5 => ⟨((653853314217187/2251799813685248), (433221072075033/1125899906842624)), (516713/1125899906842624), by norm_num⟩
  | 6 => ⟨((-287057340250531/4503599627370496), (125794056844423/562949953421312)), (1395429/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3134107669/2147483648), (-5754025799/536870912)), (1/1073741824), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3349175031/2147483648), (-24595504133/2147483648)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((209138609662697/2251799813685248), (212339425098787/1125899906842624)), (2976225/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1658979465/8589934592), (-13474957931/34359738368)), (49/34359738368), by norm_num⟩
  | 2 => ⟨((6899501633/34359738368), (14010193647/34359738368)), (53/34359738368), by norm_num⟩
  | 3 => ⟨((-597796263/4294967296), (-19422252451/68719476736)), (19/17179869184), by norm_num⟩
  | 4 => ⟨((4972329531/68719476736), (10096859645/68719476736)), (81/137438953472), by norm_num⟩
  | 5 => ⟨((-8271734869/274877906944), (-16796663509/274877906944)), (35/137438953472), by norm_num⟩
  | 6 => ⟨((5733529703/549755813888), (5821279977/274877906944)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((-6812879911/2199023255552), (-6917149377/1099511627776)), (31/1099511627776), by norm_num⟩
  | 8 => ⟨((7083492753/8796093022208), (14383807765/8796093022208)), (67/8796093022208), by norm_num⟩
  | 9 => ⟨((-3273268687/17592186044416), (-1661682633/4398046511104)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((1361314177/35184372088832), (22114380135/281474976710656)), (109/281474976710656), by norm_num⟩
  | 11 => ⟨((-4117488365/562949953421312), (-16722022081/1125899906842624)), (85/1125899906842624), by norm_num⟩
  | 12 => ⟨((2854025451/2251799813685248), (11590822459/4503599627370496)), (61/4503599627370496), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521089/10141204801825835211973625643008), (5664307529/39614081257132168796771975168)), (1821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779561815503759/633825300114114700748351602688), (1717532515173/633825300114114700748351602688)), (1083/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890633843663847/39614081257132168796771975168), (965978197899/19807040628566084398385987584)), (2437/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890464444700927/2475880078570760549798248448), (2052376885357/2475880078570760549798248448)), (2589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772130444658155/154742504910672534362390528), (2052009326901/154742504910672534362390528)), (1295/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550434182735899/9671406556917033397649408), (1923368290591/9671406556917033397649408)), (607/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259559081311749/604462909807314587353088), (1682556888041/604462909807314587353088)), (2125/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889043444510283/75557863725914323419136), (1366711595777/37778931862957161709568)), (3453/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298477568137547/4722366482869645213696), (2049427296217/4722366482869645213696)), (2591/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622737315758737/590295810358705651712), (1408461360483/295147905179352825856)), (3563/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912542529718723/36893488147419103232), (3519594291335/73786976294838206464)), (4455/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228058396116301/1152921504606846976), (3957400787939/9223372036854775808)), (5013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595713832388907/1152921504606846976), (3954723779519/1152921504606846976)), (627/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196090667021607/144115188075855872), (3457373705131/144115188075855872)), (549/18014398509481984), by norm_num⟩
  | 4 => ⟨((46684316284229/1125899906842624), (2590023216217/18014398509481984)), (6593/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492076353256101/9007199254740992), (404034046307/562949953421312)), (8251/9007199254740992), by norm_num⟩
  | 2 => ⟨((139597737147835/281474976710656), (12897595224515/4503599627370496)), (1033/281474976710656), by norm_num⟩
  | 1 => ⟨((2224473395223985/2251799813685248), (19267816773703/2251799813685248)), (777/70368744177664), by norm_num⟩
  | 0 => ⟨((2197257694057813/2251799813685248), (38222285454003/2251799813685248)), (50015/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197257694057813/2251799813685248), (38222285454003/2251799813685248)), (190792092330168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((66980871279861/70368744177664), (18648240906645/562949953421312)), (49653/1125899906842624), by norm_num⟩
  | 2 => ⟨((509431108187079/562949953421312), (142003435003497/2251799813685248)), (97815/1125899906842624), by norm_num⟩
  | 3 => ⟨((917522921698811/1125899906842624), (32125842990373/281474976710656)), (189369/1125899906842624), by norm_num⟩
  | 4 => ⟨((366522454714357/562949953421312), (104720489426897/562949953421312)), (175935/562949953421312), by norm_num⟩
  | 5 => ⟨((876613120965637/2251799813685248), (545446864118093/2251799813685248)), (294549/562949953421312), by norm_num⟩
  | 6 => ⟨((209138609662697/2251799813685248), (212339425098787/1125899906842624)), (2976225/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3349175031/2147483648), (-24595504133/2147483648)), (3/2147483648), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile012Terms0
