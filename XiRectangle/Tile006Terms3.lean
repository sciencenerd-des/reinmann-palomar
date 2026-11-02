/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile006Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

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
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4978472343/2147483648), (-38023082519/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-745625518383913/9007199254740992), (-479859540308275/9007199254740992)), (628721/9007199254740992), by norm_num⟩
  | 1 => ⟨((70335697377/274877906944), (45265692467/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((-54352656645/137438953472), (-17489772137/68719476736)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((7000265381/17179869184), (18020542725/68719476736)), (53/137438953472), by norm_num⟩
  | 4 => ⟨((-43276234955/137438953472), (-13925565649/68719476736)), (21/68719476736), by norm_num⟩
  | 5 => ⟨((53507471787/274877906944), (34435611687/274877906944)), (27/137438953472), by norm_num⟩
  | 6 => ⟨((-55131288955/549755813888), (-35480645877/549755813888)), (29/274877906944), by norm_num⟩
  | 7 => ⟨((24344736381/549755813888), (31334909337/1099511627776)), (53/1099511627776), by norm_num⟩
  | 8 => ⟨((-37625306835/2199023255552), (-48428767517/4398046511104)), (21/1099511627776), by norm_num⟩
  | 9 => ⟨((12922380083/2199023255552), (33265639191/8796093022208)), (59/8796093022208), by norm_num⟩
  | 10 => ⟨((-7988725087/4398046511104), (-41130201191/35184372088832)), (75/35184372088832), by norm_num⟩
  | 11 => ⟨((71835602595/140737488355328), (23115490545/70368744177664)), (87/140737488355328), by norm_num⟩
  | 12 => ⟨((-18503908107/140737488355328), (-23816987535/281474976710656)), (91/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-3347390808389/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((55574535530893/19807040628566084398385987584), (-3959869953473/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944654963417827/19807040628566084398385987584), (-4453936797993/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889057559105279/2475880078570760549798248448), (-4731186775885/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770723307554373/154742504910672534362390528), (-4729925773503/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48409835151013/302231454903657293676544), (-1108241470203/2417851639229258349412352)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258404289181081/604462909807314587353088), (-1938752966003/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887166408532883/75557863725914323419136), (-6298436789987/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297069355591489/4722366482869645213696), (-1180407928241/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620800317322513/590295810358705651712), (-3244338284725/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822662754919335/73786976294838206464), (-4052748689087/36893488147419103232)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227717578531383/1152921504606846976), (-1138916775065/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592985488410955/1152921504606846976), (-1137768959771/144115188075855872)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193701346696335/144115188075855872), (-7954059829383/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((745155062646347/18014398509481984), (-11910462596371/36028797018963968)), (277/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487584384180345/9007199254740992), (-14852022679077/9007199254740992)), (347/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112279571294887/2251799813685248), (-7399011636411/1125899906842624)), (697/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105457681820305/1125899906842624), (-22062330458449/1125899906842624)), (2105/1125899906842624), by norm_num⟩
  | 0 => ⟨((542485443898139/562949953421312), (-21793804789899/562949953421312)), (4263/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((542485443898139/562949953421312), (-21793804789899/562949953421312)), (16262058738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043842299403297/1125899906842624), (-42003100964215/562949953421312)), (8547/1125899906842624), by norm_num⟩
  | 2 => ⟨((1922994570799691/2251799813685248), (-155767358096721/1125899906842624)), (34249/2251799813685248), by norm_num⟩
  | 3 => ⟨((1599100514196365/2251799813685248), (-532089543852631/2251799813685248)), (67973/2251799813685248), by norm_num⟩
  | 4 => ⟨((504930135886323/1125899906842624), (-377859815957949/1125899906842624)), (128665/2251799813685248), by norm_num⟩
  | 5 => ⟨((199265318219953/2251799813685248), (-1355664439143057/4503599627370496)), (403533/4503599627370496), by norm_num⟩
  | 6 => ⟨((-745625518383913/9007199254740992), (-479859540308275/9007199254740992)), (628721/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-38023082519/4294967296)), (1/4294967296), by norm_num⟩, -1, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20200267671/8589934592), (-38569886085/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-96783732093663/1125899906842624), (-368801900596273/9007199254740992)), (300403/4503599627370496), by norm_num⟩
  | 1 => ⟨((74088093793/274877906944), (35289801823/274877906944)), (59/274877906944), by norm_num⟩
  | 2 => ⟨((-58075697389/137438953472), (-13831371187/68719476736)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((60698671083/137438953472), (3614015363/17179869184)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((-2973755189/8589934592), (-11331724267/68719476736)), (21/68719476736), by norm_num⟩
  | 5 => ⟨((29837415023/137438953472), (28424444717/274877906944)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((-62370028149/549755813888), (-14854113667/274877906944)), (59/549755813888), by norm_num⟩
  | 7 => ⟨((55874532145/1099511627776), (26614278563/1099511627776)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((-87597136179/4398046511104), (-5215557281/549755813888)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((30517812647/4398046511104), (29072621667/8796093022208)), (1/137438953472), by norm_num⟩
  | 10 => ⟨((-38275370015/17592186044416), (-2278925927/2199023255552)), (41/17592186044416), by norm_num⟩
  | 11 => ⟨((43640800471/70368744177664), (41574161819/140737488355328)), (3/4398046511104), by norm_num⟩
  | 12 => ⟨((-91223651637/562949953421312), (-10862961993/140737488355328)), (51/281474976710656), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633433/10141204801825835211973625643008), (-3513229718575/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444583227966101/158456325028528675187087900672), (-4155823994721/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472312784664477/9903520314283042199192993792), (-146072646539/1237940039285380274899124224)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888995048790179/2475880078570760549798248448), (-2482638160995/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885330371722667/77371252455336267181195264), (-2481966823509/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549056013879481/9671406556917033397649408), (-4652261493273/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157294107507349/75557863725914323419136), (-508662854131/75557863725914323419136)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943541364697107/37778931862957161709568), (-6609944098835/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297006502906509/4722366482869645213696), (-4955119890639/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810356871732671/295147905179352825856), (-3404745803229/295147905179352825856)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822554310907687/73786976294838206464), (-8506169427913/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56925572429425/288230376151711744), (-2390403396311/2305843009213693952)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199107848776107/144115188075855872), (-4775917691331/576460752303423488)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193593551061031/144115188075855872), (-521678946905/9007199254740992)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((745073783015775/18014398509481984), (-6249164145905/18014398509481984)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((371844919510957/2251799813685248), (-15584512307831/9007199254740992)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((17376134699033/35184372088832), (-3881750429549/562949953421312)), (1395/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105141701355335/1125899906842624), (-5786757311001/281474976710656)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084317045482715/1125899906842624), (-45721987209055/1125899906842624)), (267/70368744177664), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084317045482715/1125899906842624), (-45721987209055/1125899906842624)), (1018524438357331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1042413226857181/1125899906842624), (-22016668525691/281474976710656)), (67/8796093022208), by norm_num⟩
  | 2 => ⟨((479114346613975/562949953421312), (-163072872414535/1125899906842624)), (8611/562949953421312), by norm_num⟩
  | 3 => ⟨((1583816574438077/2251799813685248), (-555150966742375/2251799813685248)), (67/2199023255552), by norm_num⟩
  | 4 => ⟨((244280412075001/562949953421312), (-390468680696319/1125899906842624)), (65171/1125899906842624), by norm_num⟩
  | 5 => ⟨((153167946396247/2251799813685248), (-1355486037693919/4503599627370496)), (407051/4503599627370496), by norm_num⟩
  | 6 => ⟨((-96783732093663/1125899906842624), (-368801900596273/9007199254740992)), (300403/4503599627370496), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20200267671/8589934592), (-38569886085/4294967296)), (1/4294967296), by norm_num⟩, -1, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20474455899/8589934592), (-39093414233/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-787815706669473/9007199254740992), (-526756109239667/18014398509481984)), (1142717/18014398509481984), by norm_num⟩
  | 1 => ⟨((19101873201/68719476736), (25544117289/274877906944)), (29/137438953472), by norm_num⟩
  | 2 => ⟨((-60706781293/137438953472), (-5073786237/34359738368)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((1004840723/2147483648), (21499687713/137438953472)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((-25547503269/68719476736), (-8540895611/68719476736)), (85/274877906944), by norm_num⟩
  | 5 => ⟨((4059567031/17179869184), (21714740809/274877906944)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((-68808120279/549755813888), (-23003538401/549755813888)), (61/549755813888), by norm_num⟩
  | 7 => ⟨((62478831489/1099511627776), (20887566665/1099511627776)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((-3102517027/137438953472), (-33190905623/4398046511104)), (93/4398046511104), by norm_num⟩
  | 9 => ⟨((70115314641/8796093022208), (11720276083/4398046511104)), (67/8796093022208), by norm_num⟩
  | 10 => ⟨((-11141512213/4398046511104), (-29798134639/35184372088832)), (87/35184372088832), by norm_num⟩
  | 11 => ⟨((51503019003/70368744177664), (17218195623/70368744177664)), (13/17592186044416), by norm_num⟩
  | 12 => ⟨((-54559788939/281474976710656), (-18240117517/281474976710656)), (7/35184372088832), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646257/10141204801825835211973625643008), (-3672009475903/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778282873780019/633825300114114700748351602688), (-4343416754911/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889194810544279/39614081257132168796771975168), (-4885307300877/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888935151709717/2475880078570760549798248448), (-2594687165501/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885300395957941/77371252455336267181195264), (-5187951749187/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774499875762663/4835703278458516698824704), (-4862193569589/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258303572767425/604462909807314587353088), (-2126454256317/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471750632358687/18889465931478580854784), (-3454072090107/37778931862957161709568)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296946258475235/4722366482869645213696), (-1294657678207/1180591620717411303424)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101289422132869/36893488147419103232), (-7116592753277/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822450344807505/73786976294838206464), (-8889706562735/73786976294838206464)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910750520569381/4611686018427387904), (-4996313205523/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398186280315093/288230376151711744), (-9982265273207/1152921504606846976)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((4662070901659/562949953421312), (-8722833680735/144115188075855872)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489991589564689/36028797018963968), (-13060973289915/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487183182573945/9007199254740992), (-127230669441/70368744177664)), (695/4503599627370496), by norm_num⟩
  | 2 => ⟨((555936927260187/1125899906842624), (-2028072236267/281474976710656)), (349/562949953421312), by norm_num⟩
  | 1 => ⟨((1104837933018797/1125899906842624), (-24184807960283/1125899906842624)), (2109/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083687378520735/1125899906842624), (-47763248616733/1125899906842624)), (535/140737488355328), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1083687378520735/1125899906842624), (-47763248616733/1125899906842624)), (2040863573980287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((520515633460547/562949953421312), (-91944993277873/1125899906842624)), (8603/1125899906842624), by norm_num⟩
  | 2 => ⟨((955051341938491/1125899906842624), (-42507159054457/281474976710656)), (34629/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568902036915919/2251799813685248), (-72113904708985/281474976710656)), (8651/281474976710656), by norm_num⟩
  | 4 => ⟨((945300293725113/2251799813685248), (-803905578464189/2251799813685248)), (65951/1125899906842624), by norm_num⟩
  | 5 => ⟨((109835903141927/2251799813685248), (-1349910724445377/4503599627370496)), (409849/4503599627370496), by norm_num⟩
  | 6 => ⟨((-787815706669473/9007199254740992), (-526756109239667/18014398509481984)), (1142717/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20474455899/8589934592), (-39093414233/4294967296)), (1/4294967296), by norm_num⟩, -1, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20737449597/8589934592), (-79191135647/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1577283265406191/18014398509481984), (-329129047121911/18014398509481984)), (1081769/18014398509481984), by norm_num⟩
  | 1 => ⟨((77470077087/274877906944), (1010346921/17179869184)), (55/274877906944), by norm_num⟩
  | 2 => ⟨((-15585409893/34359738368), (-13008725115/137438953472)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((33444999417/68719476736), (13957823595/137438953472)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-107655300087/274877906944), (-22464250469/274877906944)), (21/68719476736), by norm_num⟩
  | 5 => ⟨((34652904287/137438953472), (1807740819/34359738368)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((-37181131957/274877906944), (-7758524293/274877906944)), (31/274877906944), by norm_num⟩
  | 7 => ⟨((34194699085/549755813888), (14270700733/1099511627776)), (59/1099511627776), by norm_num⟩
  | 8 => ⟨((-6879280639/274877906944), (-22967806797/4398046511104)), (97/4398046511104), by norm_num⟩
  | 9 => ⟨((78732622725/8796093022208), (16429004011/8796093022208)), (71/8796093022208), by norm_num⟩
  | 10 => ⟨((-3167881699/1099511627776), (-21153169535/35184372088832)), (47/17592186044416), by norm_num⟩
  | 11 => ⟨((59328103663/70368744177664), (12379895643/70368744177664)), (57/70368744177664), by norm_num⟩
  | 12 => ⟨((-63656599539/281474976710656), (-830194725/17592186044416)), (31/140737488355328), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241879/10141204801825835211973625643008), (-956076647095/2535301200456458802993406410752)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778234845563531/633825300114114700748351602688), (-2261665946989/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889140743288857/39614081257132168796771975168), (-5087653701747/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888877656361359/2475880078570760549798248448), (-5404297869799/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885271620818113/77371252455336267181195264), (-5402797069651/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774472869915817/4835703278458516698824704), (-5063527955581/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314564063573531/151115727451828646838272), (-1107248250999/151115727451828646838272)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886925527851619/75557863725914323419136), (-1798531421215/18889465931478580854784)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324222102998813/1180591620717411303424), (-5392980533701/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620551060624671/590295810358705651712), (-7411102279753/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911175248248729/36893488147419103232), (-9257511294979/73786976294838206464)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455347098576239/2305843009213693952), (-5202975029335/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199079009834155/144115188075855872), (-10395018175287/1152921504606846976)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596695397426543/72057594037927936), (-9083350520229/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((744920835986157/18014398509481984), (-6800232501241/18014398509481984)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((185874280964171/1125899906842624), (-16957644932275/9007199254740992)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((17370041090583/35184372088832), (-16893330697119/2251799813685248)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104545430399901/1125899906842624), (-12589763528725/562949953421312)), (33/17592186044416), by norm_num⟩
  | 0 => ⟨((541540032228399/562949953421312), (-49719083615617/1125899906842624)), (4287/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((541540032228399/562949953421312), (-49719083615617/1125899906842624)), (16353611472701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039693166003421/1125899906842624), (-95656368669835/1125899906842624)), (2157/281474976710656), by norm_num⟩
  | 2 => ⟨((475980028088293/562949953421312), (-88332250661277/562949953421312)), (8701/562949953421312), by norm_num⟩
  | 3 => ⟨((777171751423273/1125899906842624), (-597486677390531/2251799813685248)), (69777/2251799813685248), by norm_num⟩
  | 4 => ⟨((457188374976457/1125899906842624), (-206212721351871/562949953421312)), (133359/2251799813685248), by norm_num⟩
  | 5 => ⟨((34573645656831/1125899906842624), (-1339771798915519/4503599627370496)), (103003/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1577283265406191/18014398509481984), (-329129047121911/18014398509481984)), (1081769/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/8589934592), (-79191135647/8589934592)), (1/4294967296), by norm_num⟩, -1, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-20990127117/8589934592), (-10019505991/1073741824)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1557733906527911/18014398509481984), (-145894655382227/18014398509481984)), (127515/4503599627370496), by norm_num⟩
  | 1 => ⟨((77442130249/274877906944), (7253095575/274877906944)), (27/274877906944), by norm_num⟩
  | 2 => ⟨((-63078484115/137438953472), (-1476955349/34359738368)), (3/17179869184), by norm_num⟩
  | 3 => ⟨((68505263573/137438953472), (3208042073/68719476736)), (7/34359738368), by norm_num⟩
  | 4 => ⟨((-55799190521/137438953472), (-2613027693/68719476736)), (3/17179869184), by norm_num⟩
  | 5 => ⟨((9089957473/34359738368), (53209353/2147483648)), (33/274877906944), by norm_num⟩
  | 6 => ⟨((-19743972649/137438953472), (-7396744909/549755813888)), (37/549755813888), by norm_num⟩
  | 7 => ⟨((73517450211/1099511627776), (1721379213/274877906944)), (9/274877906944), by norm_num⟩
  | 8 => ⟨((-1871304297/68719476736), (-11216839309/4398046511104)), (61/4398046511104), by norm_num⟩
  | 9 => ⟨((86711325179/8796093022208), (8121232293/8796093022208)), (23/4398046511104), by norm_num⟩
  | 10 => ⟨((-113005547349/35184372088832), (-10583903527/35184372088832)), (31/17592186044416), by norm_num⟩
  | 11 => ⟨((8367795059/8796093022208), (6269705353/70368744177664)), (19/35184372088832), by norm_num⟩
  | 12 => ⟨((-36350778817/140737488355328), (-851137721/35184372088832)), (43/281474976710656), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (-1985314851217/5070602400912917605986812821504)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((444547167696967/158456325028528675187087900672), (-4696172534989/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944544380501813/19807040628566084398385987584), (-5282042359277/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888822375991531/2475880078570760549798248448), (-701345968097/309485009821345068724781056)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27663873531187/2417851639229258349412352), (-5609190341565/154742504910672534362390528)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548893804003135/9671406556917033397649408), (-1314235065213/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258210751844831/604462909807314587353088), (-2299073693955/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58964108644961/2361183241434822606848), (-7468848973693/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296832777710377/4722366482869645213696), (-2799444748497/2361183241434822606848)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810237203974909/295147905179352825856), (-7694010177619/590295810358705651712)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455563611953991/18446744073709551616), (-4805410403075/36893488147419103232)), (375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821280020135875/9223372036854775808), (-1350371991841/1152921504606846976)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199065413296825/144115188075855872), (-5395742484491/576460752303423488)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193295172738835/144115188075855872), (-4714815049507/72057594037927936)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489697349946327/36028797018963968), (-14118626900337/36028797018963968)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486812298334837/9007199254740992), (-8801573667949/4503599627370496)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111498377409107/2251799813685248), (-8767767199313/1125899906842624)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((276065838630703/281474976710656), (-6533647605425/281474976710656)), (529/562949953421312), by norm_num⟩
  | 0 => ⟨((541246741735449/562949953421312), (-51596270499375/1125899906842624)), (537/281474976710656), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((541246741735449/562949953421312), (-51596270499375/1125899906842624)), (2048493505382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((519198003091643/562949953421312), (-49607097618121/562949953421312)), (541/140737488355328), by norm_num⟩
  | 2 => ⟨((948950082176679/1125899906842624), (-45751679818019/281474976710656)), (8747/1125899906842624), by norm_num⟩
  | 3 => ⟨((96257979272307/140737488355328), (-616979325557029/2251799813685248)), (35177/2251799813685248), by norm_num⟩
  | 4 => ⟨((884328053751245/2251799813685248), (-421985526563947/1125899906842624)), (16849/562949953421312), by norm_num⟩
  | 5 => ⟨((61949528292667/4503599627370496), (-1325779093326281/4503599627370496)), (3233/70368744177664), by norm_num⟩
  | 6 => ⟨((-1557733906527911/18014398509481984), (-145894655382227/18014398509481984)), (127515/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-10019505991/1073741824)), (1/8589934592), by norm_num⟩, -1, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-21233267329/8589934592), (-20271134903/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-760361276800097/9007199254740992), (5590888308393/4503599627370496)), (241735/4503599627370496), by norm_num⟩
  | 1 => ⟨((38238933221/137438953472), (-140584227/34359738368)), (25/137438953472), by norm_num⟩
  | 2 => ⟨((-126029285827/274877906944), (1853370713/274877906944)), (85/274877906944), by norm_num⟩
  | 3 => ⟨((69228661071/137438953472), (-63629245/8589934592)), (3/8589934592), by norm_num⟩
  | 4 => ⟨((-114083186671/274877906944), (1677692891/274877906944)), (81/274877906944), by norm_num⟩
  | 5 => ⟨((75199914485/274877906944), (-34558763/8589934592)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((-5163471885/34359738368), (1214933815/549755813888)), (31/274877906944), by norm_num⟩
  | 7 => ⟨((77796393121/1099511627776), (-572031951/549755813888)), (15/274877906944), by norm_num⟩
  | 8 => ⟨((-64101055123/2199023255552), (1885323993/4398046511104)), (101/4398046511104), by norm_num⟩
  | 9 => ⟨((93896275833/8796093022208), (-690413369/4398046511104)), (19/2199023255552), by norm_num⟩
  | 10 => ⟨((-123786722989/35184372088832), (1820391867/35184372088832)), (51/17592186044416), by norm_num⟩
  | 11 => ⟨((37089167741/35184372088832), (-1090857205/70368744177664)), (63/70368744177664), by norm_num⟩
  | 12 => ⟨((-40746615457/140737488355328), (1198429131/281474976710656)), (71/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480279/10141204801825835211973625643008), (4073120530753/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778144445711637/633825300114114700748351602688), (4817166068543/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472259746261223/9903520314283042199192993792), (5418116015963/39614081257132168796771975168)), (409/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944384728442213/1237940039285380274899124224), (5755293078313/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770434950773311/154742504910672534362390528), (359603507533/9671406556917033397649408)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548844120153419/9671406556917033397649408), (2696156828877/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258167240197655/604462909807314587353088), (73695872591/9444732965739290427392)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943390349272669/37778931862957161709568), (3830555805489/37778931862957161709568)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20262181742775/73786976294838206464), (717872838491/590295810358705651712)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620401230430863/590295810358705651712), (7891969747515/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227770352995805/9223372036854775808), (616126088881/4611686018427387904)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910588367467435/4611686018427387904), (11080724539575/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796209880776457/576460752303423488), (11068799203251/1152921504606846976)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149150535012877/18014398509481984), (2417947886523/36028797018963968)), (185/36028797018963968), by norm_num⟩
  | 4 => ⟨((744780216022613/18014398509481984), (14480892457117/36028797018963968)), (139/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486640144281743/9007199254740992), (18054271124429/9007199254740992)), (697/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111324726270723/2251799813685248), (17984097815215/2251799813685248)), (175/281474976710656), by norm_num⟩
  | 1 => ⟨((1103999180209585/1125899906842624), (837532539965/35184372088832)), (529/281474976710656), by norm_num⟩
  | 0 => ⟨((135243826736667/140737488355328), (26451818103983/562949953421312)), (1075/281474976710656), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((135243826736667/140737488355328), (26451818103983/562949953421312)), (4100800634288699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((259307761081327/281474976710656), (25419276316007/281474976710656)), (8669/1125899906842624), by norm_num⟩
  | 2 => ⟨((946362992928315/1125899906842624), (93669649882761/562949953421312)), (17539/1125899906842624), by norm_num⟩
  | 3 => ⟨((764283659602329/1125899906842624), (629864091263223/2251799813685248)), (70643/2251799813685248), by norm_num⟩
  | 4 => ⟨((861439486800139/2251799813685248), (855129003558999/2251799813685248)), (33857/562949953421312), by norm_num⟩
  | 5 => ⟨((9621083210725/4503599627370496), (20445919678807/70368744177664)), (412953/4503599627370496), by norm_num⟩
  | 6 => ⟨((-760361276800097/9007199254740992), (5590888308393/4503599627370496)), (241735/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21233267329/8589934592), (-20271134903/2147483648)), (1/4294967296), by norm_num⟩, -2, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile006Terms3
