/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile003Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-159311114973/68719476736), (-163791740081/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((96739795189079/18014398509481984), (1770743284799343/18014398509481984)), (137843/18014398509481984), by norm_num⟩
  | 1 => ⟨((-18251148307/1099511627776), (-334072428425/1099511627776)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((881485535/34359738368), (516316029379/1099511627776)), (45/1099511627776), by norm_num⟩
  | 3 => ⟨((-14531782457/549755813888), (-265992461027/549755813888)), (25/549755813888), by norm_num⟩
  | 4 => ⟨((22459178249/1099511627776), (205548497327/549755813888)), (41/1099511627776), by norm_num⟩
  | 5 => ⟨((-13884454687/1099511627776), (-508287305169/2199023255552)), (53/2199023255552), by norm_num⟩
  | 6 => ⟨((447056655/68719476736), (130928136565/1099511627776)), (29/2199023255552), by norm_num⟩
  | 7 => ⟨((-6317125027/2199023255552), (-462519346813/8796093022208)), (53/8796093022208), by norm_num⟩
  | 8 => ⟨((9763250821/8796093022208), (357416734125/17592186044416)), (43/17592186044416), by norm_num⟩
  | 9 => ⟨((-26825442463/70368744177664), (-491017910543/70368744177664)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((16583716297/140737488355328), (303551441369/140737488355328)), (5/17592186044416), by norm_num⟩
  | 11 => ⟨((-9320176565/281474976710656), (-42649563275/70368744177664)), (47/562949953421312), by norm_num⟩
  | 12 => ⟨((19206040957/2251799813685248), (351550961867/2251799813685248)), (25/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580955946171239/10141204801825835211973625643008), (1975043588077/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889195306468913/316912650057057350374175801344), (2336421472397/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889316392333607/39614081257132168796771975168), (2627941271047/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889064830587895/2475880078570760549798248448), (697881770077/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770731030759449/154742504910672534362390528), (1395392123881/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549122444950193/9671406556917033397649408), (2615571213001/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258411523512371/604462909807314587353088), (2287836062411/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887179062056931/75557863725914323419136), (1858127635667/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297079630436497/4722366482869645213696), (2785898488701/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810407859422339/295147905179352825856), (3828510430021/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455670978640309/18446744073709551616), (4782489931495/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455441762911129/2305843009213693952), (5375975583565/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199126897348601/144115188075855872), (2685286589323/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193730992192559/144115188075855872), (4693180121111/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490361904045889/36028797018963968), (7027643085689/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487661850875791/9007199254740992), (2190841695235/2251799813685248)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224752105639675/4503599627370496), (17463313509705/4503599627370496)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((552824795999201/562949953421312), (26036913393229/2251799813685248)), (521/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171082745169697/2251799813685248), (51444551996731/2251799813685248)), (525/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2171082745169697/2251799813685248), (51444551996731/2251799813685248)), (2002720359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046041863005041/1125899906842624), (99200984469661/2251799813685248)), (1037/1125899906842624), by norm_num⟩
  | 2 => ⟨((484831450688503/562949953421312), (184329676156697/2251799813685248)), (2019/1125899906842624), by norm_num⟩
  | 3 => ⟨((1655123655781781/2251799813685248), (158750922267347/1125899906842624)), (7617/2251799813685248), by norm_num⟩
  | 4 => ⟨((1171785732732251/2251799813685248), (466742034926889/2251799813685248)), (6673/1125899906842624), by norm_num⟩
  | 5 => ⟨((1026053620971337/4503599627370496), (485764013363751/2251799813685248)), (19423/2251799813685248), by norm_num⟩
  | 6 => ⟨((96739795189079/18014398509481984), (1770743284799343/18014398509481984)), (137843/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-159311114973/68719476736), (-163791740081/34359738368)), (1/34359738368), by norm_num⟩, -1, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-161602141371/68719476736), (-332294403193/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((105332734140095/9007199254740992), (851124942654319/9007199254740992)), (130441/18014398509481984), by norm_num⟩
  | 1 => ⟨((-40316183917/1099511627776), (-162884358809/549755813888)), (27/1099511627776), by norm_num⟩
  | 2 => ⟨((15801395185/274877906944), (31920185307/68719476736)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((-33030122137/549755813888), (-266894817071/549755813888)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((6472859807/137438953472), (209211788797/549755813888)), (21/549755813888), by norm_num⟩
  | 5 => ⟨((-32472983177/1099511627776), (-262392941471/1099511627776)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((33939616975/2199023255552), (137121925047/1099511627776)), (31/2199023255552), by norm_num⟩
  | 7 => ⟨((-30404992205/4398046511104), (-122841429389/2199023255552)), (15/2199023255552), by norm_num⟩
  | 8 => ⟨((47667338597/17592186044416), (192584295663/8796093022208)), (49/17592186044416), by norm_num⟩
  | 9 => ⟨((-33213480991/35184372088832), (-134188210029/17592186044416)), (35/35184372088832), by norm_num⟩
  | 10 => ⟨((41656271015/140737488355328), (168298542557/70368744177664)), (23/70368744177664), by norm_num⟩
  | 11 => ⟨((-47495635209/562949953421312), (-47972646067/70368744177664)), (27/281474976710656), by norm_num⟩
  | 12 => ⟨((6205095395/281474976710656), (401114544709/2251799813685248)), (29/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633377/10141204801825835211973625643008), (942872856673/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444584874812785/158456325028528675187087900672), (2230661787367/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944629457897885/19807040628566084398385987584), (2508979249783/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944501897691685/1237940039285380274899124224), (41642981681/38685626227668133590597632)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770670033350845/154742504910672534362390528), (2664431506019/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549065300017799/9671406556917033397649408), (1248570249087/4835703278458516698824704)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78647597613263/37778931862957161709568), (2184234167669/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887097949463293/75557863725914323419136), (3547949031609/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297018861716507/4722366482869645213696), (2659709793575/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810366134284365/295147905179352825856), (28555215429/4611686018427387904)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822579761630889/73786976294838206464), (2282893132315/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455412524806593/2305843009213693952), (5132321325099/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592898500525547/1152921504606846976), (1281772657653/288230376151711744)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193629206613511/144115188075855872), (4480326068179/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490209840174309/36028797018963968), (13103024149/70368744177664)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487472843473155/9007199254740992), (8365424513457/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224377296437045/4503599627370496), (16669457393549/4503599627370496)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105372471664223/1125899906842624), (3106400031799/281474976710656)), (521/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170005912000327/2251799813685248), (49093409252503/2251799813685248)), (1049/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170005912000327/2251799813685248), (49093409252503/2251799813685248)), (4001626021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090112747447897/2251799813685248), (11827537651297/281474976710656)), (2069/2251799813685248), by norm_num⟩
  | 2 => ⟨((1936059444160001/2251799813685248), (175652468327995/2251799813685248)), (251/140737488355328), by norm_num⟩
  | 3 => ⟨((1650889372624771/2251799813685248), (151023025283883/1125899906842624)), (7533/2251799813685248), by norm_num⟩
  | 4 => ⟨((1169821530303239/2251799813685248), (442885386076605/2251799813685248)), (13067/2251799813685248), by norm_num⟩
  | 5 => ⟨((520621300541885/2251799813685248), (920324900891023/4503599627370496)), (37435/4503599627370496), by norm_num⟩
  | 6 => ⟨((105332734140095/9007199254740992), (851124942654319/9007199254740992)), (130441/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-161602141371/68719476736), (-332294403193/68719476736)), (1/34359738368), by norm_num⟩, -1, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-163795647195/68719476736), (-336804799545/68719476736)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9742102241613/562949953421312), (815919724551477/9007199254740992)), (184933/18014398509481984), by norm_num⟩
  | 1 => ⟨((-30235278657/549755813888), (-9891650413/34359738368)), (19/549755813888), by norm_num⟩
  | 2 => ⟨((24022335787/274877906944), (62872394967/137438953472)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((-50896184175/549755813888), (-266415807531/549755813888)), (9/137438953472), by norm_num⟩
  | 4 => ⟨((40437703267/549755813888), (423341888795/1099511627776)), (59/1099511627776), by norm_num⟩
  | 5 => ⟨((-51405279103/1099511627776), (-269080662247/1099511627776)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((54456248051/2199023255552), (285050943109/2199023255552)), (11/549755813888), by norm_num⟩
  | 7 => ⟨((-49447110773/4398046511104), (-258830640455/4398046511104)), (41/4398046511104), by norm_num⟩
  | 8 => ⟨((9821598737/2199023255552), (411288854155/17592186044416)), (67/17592186044416), by norm_num⟩
  | 9 => ⟨((-27745395099/17592186044416), (-290466248517/35184372088832)), (49/35184372088832), by norm_num⟩
  | 10 => ⟨((70541087335/140737488355328), (369246949475/140737488355328)), (1/2199023255552), by norm_num⟩
  | 11 => ⟨((-81521226473/562949953421312), (-426722429863/562949953421312)), (19/140737488355328), by norm_num⟩
  | 12 => ⟨((86359615349/2251799813685248), (452048950907/2251799813685248)), (83/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455775/1267650600228229401496703205376), (1800248920939/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778290552732295/633825300114114700748351602688), (2129414800677/633825300114114700748351602688)), (17/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889203875677769/39614081257132168796771975168), (2395093833661/39614081257132168796771975168)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888945346810951/2475880078570760549798248448), (636042093453/618970019642690137449562112)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885305810126609/77371252455336267181195264), (635868113975/38685626227668133590597632)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387252643852931/2417851639229258349412352), (2383766254185/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258313715433447/604462909807314587353088), (2085056568695/604462909807314587353088)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887020269649029/75557863725914323419136), (3386832052153/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296960663542711/4722366482869645213696), (317364106049/590295810358705651712)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620652346235873/590295810358705651712), (218064878381/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822480008800159/73786976294838206464), (4358348774803/73786976294838206464)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910769041708753/4611686018427387904), (2449545413957/4611686018427387904)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796393371005855/576460752303423488), (4894030964549/1152921504606846976)), (79/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193531706873489/144115188075855872), (4276591021063/144115188075855872)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490064167241863/36028797018963968), (6403530053271/36028797018963968)), (13/2251799813685248), by norm_num⟩
  | 3 => ⟨((185911469838067/1125899906842624), (1996143484427/2251799813685248)), (259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112009067479423/2251799813685248), (1988721575391/562949953421312)), (259/2251799813685248), by norm_num⟩
  | 1 => ⟨((552553420600877/562949953421312), (11858355946275/1125899906842624)), (195/562949953421312), by norm_num⟩
  | 0 => ⟨((1084486541517431/1125899906842624), (46844574905609/2251799813685248)), (785/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1084486541517431/1125899906842624), (46844574905609/2251799813685248)), (2994541648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2088218407406325/2251799813685248), (45121516326175/1125899906842624)), (3091/2251799813685248), by norm_num⟩
  | 2 => ⟨((1932903753537969/2251799813685248), (167374702475349/2251799813685248)), (5981/2251799813685248), by norm_num⟩
  | 3 => ⟨((823364183369359/1125899906842624), (17958922719047/140737488355328)), (5579/1125899906842624), by norm_num⟩
  | 4 => ⟨((583788228888031/1125899906842624), (420264249747833/2251799813685248)), (599/70368744177664), by norm_num⟩
  | 5 => ⟨((1053923832771619/4503599627370496), (13619401274825/70368744177664)), (27033/2251799813685248), by norm_num⟩
  | 6 => ⟨((9742102241613/562949953421312), (815919724551477/9007199254740992)), (184933/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163795647195/68719476736), (-336804799545/68719476736)), (3/68719476736), by norm_num⟩, -1, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41474899193/17179869184), (-341131045863/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((401317610444371/18014398509481984), (780239162827553/9007199254740992)), (116933/18014398509481984), by norm_num⟩
  | 1 => ⟨((-39422349681/549755813888), (-306578732769/1099511627776)), (25/1099511627776), by norm_num⟩
  | 2 => ⟨((31723912087/274877906944), (30838714729/68719476736)), (11/274877906944), by norm_num⟩
  | 3 => ⟨((-68076889125/549755813888), (-33088664437/68719476736)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((54782763159/549755813888), (213016604067/549755813888)), (11/274877906944), by norm_num⟩
  | 5 => ⟨((-70535564781/1099511627776), (-274269598851/1099511627776)), (15/549755813888), by norm_num⟩
  | 6 => ⟨((37840870711/1099511627776), (294279927079/2199023255552)), (17/1099511627776), by norm_num⟩
  | 7 => ⟨((-69602893671/4398046511104), (-270643012291/4398046511104)), (33/4398046511104), by norm_num⟩
  | 8 => ⟨((112021535889/17592186044416), (108895781179/4398046511104)), (55/17592186044416), by norm_num⟩
  | 9 => ⟨((-80129647497/35184372088832), (-77893777215/8796093022208)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((103170954073/140737488355328), (50146079277/17592186044416)), (55/140737488355328), by norm_num⟩
  | 11 => ⟨((-7547602043/35184372088832), (-58696000835/70368744177664)), (17/140737488355328), by norm_num⟩
  | 12 => ⟨((1012283073/17592186044416), (7872297421/35184372088832)), (19/562949953421312), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (859121391727/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889121798367409/316912650057057350374175801344), (508077883165/158456325028528675187087900672)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944575536705063/19807040628566084398385987584), (1142934956541/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118055579630297/154742504910672534362390528), (2428138640987/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770555580899127/154742504910672534362390528), (1213732996257/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774479036978515/4835703278458516698824704), (284379364595/1208925819614629174706176)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314566953019997/151115727451828646838272), (1989941368461/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471736435766943/18889465931478580854784), (1616158098781/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324226206658909/1180591620717411303424), (1211533252885/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810287832352273/295147905179352825856), (3329815216029/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911192149034099/36893488147419103232), (2079709518881/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455357650684895/2305843009213693952), (292214419711/576460752303423488)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592679503358557/1152921504606846976), (2335270309801/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((596719072428271/72057594037927936), (255076744385/9007199254740992)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489924366643995/36028797018963968), (1527716787247/9007199254740992)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487117954551551/9007199254740992), (476213319965/562949953421312)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111836677921909/2251799813685248), (3795363326639/1125899906842624)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209703549740783/2251799813685248), (22629234915197/2251799813685248)), (65/281474976710656), by norm_num⟩
  | 0 => ⟨((1083990370390343/1125899906842624), (44689605165569/2251799813685248)), (523/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083990370390343/1125899906842624), (44689605165569/2251799813685248)), (1995090964889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521598689971605/562949953421312), (86052234948439/2251799813685248)), (2057/2251799813685248), by norm_num⟩
  | 2 => ⟨((964925496603073/1125899906842624), (79731302481595/1125899906842624)), (1985/1125899906842624), by norm_num⟩
  | 3 => ⟨((1642640038922273/2251799813685248), (273327197823871/2251799813685248)), (921/281474976710656), by norm_num⟩
  | 4 => ⟨((36409188725055/70368744177664), (199386373576935/1125899906842624)), (12539/2251799813685248), by norm_num⟩
  | 5 => ⟨((266103676052249/1125899906842624), (825309155603343/4503599627370496)), (17417/2251799813685248), by norm_num⟩
  | 6 => ⟨((401317610444371/18014398509481984), (780239162827553/9007199254740992)), (116933/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-341131045863/68719476736)), (1/34359738368), by norm_num⟩, -1, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20990127117/8589934592), (-345287591075/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((240283350438451/9007199254740992), (1488917667308777/18014398509481984)), (110997/18014398509481984), by norm_num⟩
  | 1 => ⟨((-23891185065/274877906944), (-296083831619/1099511627776)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((77839787349/549755813888), (120583713345/274877906944)), (21/549755813888), by norm_num⟩
  | 3 => ⟨((-42268256947/274877906944), (-130957792997/274877906944)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((34428515407/274877906944), (213336565995/549755813888)), (21/549755813888), by norm_num⟩
  | 5 => ⟨((-89737141485/1099511627776), (-34753556355/137438953472)), (29/1099511627776), by norm_num⟩
  | 6 => ⟨((97457423335/2199023255552), (9435870137/68719476736)), (33/2199023255552), by norm_num⟩
  | 7 => ⟨((-90721626735/4398046511104), (-8783707379/137438953472)), (33/4398046511104), by norm_num⟩
  | 8 => ⟨((73894954497/8796093022208), (57236333205/2199023255552)), (7/2199023255552), by norm_num⟩
  | 9 => ⟨((-107003064633/35184372088832), (-331522665003/35184372088832)), (21/17592186044416), by norm_num⟩
  | 10 => ⟨((8715657861/8796093022208), (13501660589/4398046511104)), (29/70368744177664), by norm_num⟩
  | 11 => ⟨((-20651967057/70368744177664), (-127970075993/140737488355328)), (9/70368744177664), by norm_num⟩
  | 12 => ⟨((44857401581/562949953421312), (138979620521/562949953421312)), (41/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (1639453414319/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778198475379231/633825300114114700748351602688), (1939026470285/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889100333765745/39614081257132168796771975168), (2180941280977/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944417695597665/1237940039285380274899124224), (2316672515311/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770501729469625/154742504910672534362390528), (1158011490541/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387226905412699/2417851639229258349412352), (271322706233/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314555924925389/151115727451828646838272), (949284656689/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943437061508485/37778931862957161709568), (192742664979/4722366482869645213696)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296851166299985/4722366482869645213696), (2311781608889/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405125492639337/147573952589676412928), (1588431956293/295147905179352825856)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822292313470755/73786976294838206464), (3968328032969/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455331825710603/2305843009213693952), (4460588223385/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796288215800919/576460752303423488), (4455866688793/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193348213276643/144115188075855872), (243348611501/9007199254740992)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489789980563345/36028797018963968), (5829770915781/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((371737716044901/2251799813685248), (7268705615437/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111670920850289/2251799813685248), (3620506277755/1125899906842624)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104606454915045/1125899906842624), (21585054192025/2251799813685248)), (65/281474976710656), by norm_num⟩
  | 0 => ⟨((2167025775815835/2251799813685248), (5327632118547/281474976710656)), (523/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2167025775815835/2251799813685248), (5327632118547/281474976710656)), (1995090964889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2084636533863293/2251799813685248), (82032983960941/2251799813685248)), (1027/1125899906842624), by norm_num⟩
  | 2 => ⟨((1926894229891131/2251799813685248), (151886463714489/2251799813685248)), (1977/1125899906842624), by norm_num⟩
  | 3 => ⟨((819311701889101/1125899906842624), (259942423612729/2251799813685248)), (7301/2251799813685248), by norm_num⟩
  | 4 => ⟨((581205438402677/1125899906842624), (94579397417559/562949953421312)), (12313/2251799813685248), by norm_num⟩
  | 5 => ⟨((268246502313273/1125899906842624), (390585769167255/2251799813685248)), (8425/1125899906842624), by norm_num⟩
  | 6 => ⟨((240283350438451/9007199254740992), (1488917667308777/18014398509481984)), (110997/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-345287591075/68719476736)), (1/34359738368), by norm_num⟩, -1, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-169866138629/68719476736), (-87321811889/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((550556723345867/18014398509481984), (1417739224301233/18014398509481984)), (105193/18014398509481984), by norm_num⟩
  | 1 => ⟨((-55375523243/549755813888), (-285195141713/1099511627776)), (23/1099511627776), by norm_num⟩
  | 2 => ⟨((91254345489/549755813888), (58747291379/137438953472)), (21/549755813888), by norm_num⟩
  | 3 => ⟨((-100253145349/549755813888), (-64540496235/137438953472)), (25/549755813888), by norm_num⟩
  | 4 => ⟨((41302251547/274877906944), (212714946841/549755813888)), (23/549755813888), by norm_num⟩
  | 5 => ⟨((-54450193319/549755813888), (-280429505499/1099511627776)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((119639303001/2199023255552), (154041650423/1099511627776)), (37/2199023255552), by norm_num⟩
  | 7 => ⟨((-112660464415/4398046511104), (-145056042961/2199023255552)), (37/4398046511104), by norm_num⟩
  | 8 => ⟨((46413813995/4398046511104), (119520263507/4398046511104)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((-67987715225/17592186044416), (-350150480623/35184372088832)), (49/35184372088832), by norm_num⟩
  | 10 => ⟨((44815283655/35184372088832), (230807772537/70368744177664)), (17/35184372088832), by norm_num⟩
  | 11 => ⟨((-53710496011/140737488355328), (-69154978699/70368744177664)), (43/281474976710656), by norm_num⟩
  | 12 => ⟨((14751752737/140737488355328), (303898037685/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98797241905021/633825300114114700748351602688), (195454743579/1267650600228229401496703205376)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778155050419287/633825300114114700748351602688), (924635499093/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889051501337743/39614081257132168796771975168), (2079983242153/39614081257132168796771975168)), (51/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888783533171349/2475880078570760549798248448), (1104712496777/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885224950580195/77371252455336267181195264), (2208798402103/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548859064166373/9671406556917033397649408), (2070082980519/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258181243439677/604462909807314587353088), (1810657347503/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886805190684001/75557863725914323419136), (1470535690369/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162099939839627/590295810358705651712), (1102356565925/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810215519507851/295147905179352825856), (189356855545/36893488147419103232)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822203774742501/73786976294838206464), (3784482625703/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455306967350049/2305843009213693952), (4253895985961/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592477213630623/1152921504606846976), (2124670848085/576460752303423488)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193261639527103/144115188075855872), (464132059993/18014398509481984)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489660602817221/36028797018963968), (2779682436671/18014398509481984)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((371697496156373/2251799813685248), (6931355425719/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111511300433715/2251799813685248), (6904647436553/2251799813685248)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((276092538841567/281474976710656), (2572609667755/281474976710656)), (65/281474976710656), by norm_num⟩
  | 0 => ⟨((2166105425825843/2251799813685248), (20316167988919/1125899906842624)), (261/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166105425825843/2251799813685248), (20316167988919/1125899906842624)), (995638133811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((260367379271439/281474976710656), (39086033709867/1125899906842624)), (2047/2251799813685248), by norm_num⟩
  | 2 => ⟨((1924027225519731/2251799813685248), (144620005402675/2251799813685248)), (1965/1125899906842624), by norm_num⟩
  | 3 => ⟨((204334650232201/281474976710656), (247138156827693/2251799813685248)), (7221/2251799813685248), by norm_num⟩
  | 4 => ⟨((289889477501951/562949953421312), (179408093126261/1125899906842624)), (6035/1125899906842624), by norm_num⟩
  | 5 => ⟨((269967490839043/1125899906842624), (739085498594153/4503599627370496)), (8139/1125899906842624), by norm_num⟩
  | 6 => ⟨((550556723345867/18014398509481984), (1417739224301233/18014398509481984)), (105193/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-169866138629/68719476736), (-87321811889/17179869184)), (1/34359738368), by norm_num⟩, -1, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile003Terms3
