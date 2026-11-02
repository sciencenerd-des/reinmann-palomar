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
namespace Reinmann.XiRectangle.Tile008Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

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

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-70689085815/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-635411769976131/9007199254740992), (-403194533200685/2251799813685248)), (147533/1125899906842624), by norm_num⟩
  | 1 => ⟨((10651720869/68719476736), (27035795221/68719476736)), (21/68719476736), by norm_num⟩
  | 2 => ⟨((-5851055721/34359738368), (-59403713727/137438953472)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((8570722289/68719476736), (87015533191/274877906944)), (73/274877906944), by norm_num⟩
  | 4 => ⟨((-18831801659/274877906944), (-95596334069/549755813888)), (83/549755813888), by norm_num⟩
  | 5 => ⟨((33102157953/1099511627776), (656395671/8589934592)), (19/274877906944), by norm_num⟩
  | 6 => ⟨((-3030536459/274877906944), (-61535944567/2199023255552)), (29/1099511627776), by norm_num⟩
  | 7 => ⟨((30440087727/8796093022208), (77261879881/8796093022208)), (75/8796093022208), by norm_num⟩
  | 8 => ⟨((-33441854445/35184372088832), (-84880850683/35184372088832)), (85/35184372088832), by norm_num⟩
  | 9 => ⟨((4082181361/17592186044416), (82889907229/140737488355328)), (85/140737488355328), by norm_num⟩
  | 10 => ⟨((-14351150745/281474976710656), (-72851096551/562949953421312)), (77/562949953421312), by norm_num⟩
  | 11 => ⟨((22932873549/2251799813685248), (58207352665/2251799813685248)), (1/35184372088832), by norm_num⟩
  | 12 => ⟨((-33592448927/18014398509481984), (-85263083905/18014398509481984)), (3/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-2535022130349/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779422289877143/633825300114114700748351602688), (-3002179581163/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945238356241061/19807040628566084398385987584), (-3376952618531/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472574320215589/618970019642690137449562112), (-3587407925799/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885981521259541/77371252455336267181195264), (-3586728232071/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775138495088249/4835703278458516698824704), (-3361835641249/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314855321231503/151115727451828646838272), (-2940884220235/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944409525769043/37778931862957161709568), (-2388791703343/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298308859128671/4722366482869645213696), (-3582003520067/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405626167073689/147573952589676412928), (-4923331223781/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824793242340333/73786976294838206464), (-6151279376367/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228017186349941/1152921504606846976), (-1729056038399/2305843009213693952)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797691213530041/576460752303423488), (-863908700473/144115188075855872)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195798747933199/144115188075855872), (-6041789622865/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((746728186390947/18014398509481984), (-9051548347901/36028797018963968)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((372879354132655/2251799813685248), (-11294961863003/9007199254740992)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116212874607207/2251799813685248), (-5632890346481/1125899906842624)), (347/562949953421312), by norm_num⟩
  | 1 => ⟨((1111358092858475/1125899906842624), (-8412910200961/562949953421312)), (2091/1125899906842624), by norm_num⟩
  | 0 => ⟨((274193053507995/281474976710656), (-33360853015503/1125899906842624)), (4223/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((274193053507995/281474976710656), (-33360853015503/1125899906842624)), (16109470847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533704788345219/562949953421312), (-64995576252273/1125899906842624)), (8479/1125899906842624), by norm_num⟩
  | 2 => ⟨((1008205767297183/1125899906842624), (-123238131760299/1125899906842624)), (17057/1125899906842624), by norm_num⟩
  | 3 => ⟨((889325264178649/1125899906842624), (-27588907867507/140737488355328)), (68565/2251799813685248), by norm_num⟩
  | 4 => ⟨((82399194569519/140737488355328), (-174335303723233/562949953421312)), (135199/2251799813685248), by norm_num⟩
  | 5 => ⟨((555937433880269/2251799813685248), (-408280374467349/1125899906842624)), (242051/2251799813685248), by norm_num⟩
  | 6 => ⟨((-635411769976131/9007199254740992), (-403194533200685/2251799813685248)), (147533/1125899906842624), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-70689085815/8589934592)), (1/4294967296), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7417145753/4294967296), (-9259842901/1073741824)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-557464421844903/4503599627370496), (-574995240169215/4503599627370496)), (566117/4503599627370496), by norm_num⟩
  | 1 => ⟨((19586323053/68719476736), (40404524797/137438953472)), (21/68719476736), by norm_num⟩
  | 2 => ⟨((-704674617/2147483648), (-46517428243/137438953472)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((34614896395/137438953472), (8925861403/34359738368)), (41/137438953472), by norm_num⟩
  | 4 => ⟨((-39851872217/274877906944), (-41105110817/274877906944)), (49/274877906944), by norm_num⟩
  | 5 => ⟨((18352465379/274877906944), (37859206165/549755813888)), (47/549755813888), by norm_num⟩
  | 6 => ⟨((-56344150935/2199023255552), (-58116029165/2199023255552)), (37/1099511627776), by norm_num⟩
  | 7 => ⟨((18533886003/2199023255552), (19116728917/2199023255552)), (51/4398046511104), by norm_num⟩
  | 8 => ⟨((-21337924813/8796093022208), (-44017895031/17592186044416)), (61/17592186044416), by norm_num⟩
  | 9 => ⟨((43673233413/70368744177664), (22523321983/35184372088832)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((-5028066811/35184372088832), (-20744746177/140737488355328)), (61/281474976710656), by norm_num⟩
  | 11 => ⟨((16840075179/562949953421312), (69478608443/2251799813685248)), (105/2251799813685248), by norm_num⟩
  | 12 => ⟨((-51700941429/9007199254740992), (-26663401347/4503599627370496)), (83/9007199254740992), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-762260795471/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779298244456065/633825300114114700748351602688), (-3610454577249/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890337059257827/39614081257132168796771975168), (-2030564360535/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472537191538163/618970019642690137449562112), (-539273411885/309485009821345068724781056)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885907189057285/77371252455336267181195264), (-4313330110265/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775068729174795/4835703278458516698824704), (-4042836314411/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314824758936415/151115727451828646838272), (-3536571217747/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888620099056513/75557863725914323419136), (-179538161265/2361183241434822606848)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298159384645477/4722366482869645213696), (-1076855603107/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202787339830405/73786976294838206464), (-2960139686877/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824535172726871/73786976294838206464), (-3698355149073/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823846294039445/9223372036854775808), (-8316296785399/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595090146707593/1152921504606846976), (-8310045733501/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298885446570355/36028797018963968), (-908032511807/18014398509481984)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493068504356557/36028797018963968), (-10882336587225/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491028350736217/9007199254740992), (-3394585300397/2251799813685248)), (693/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115717493667197/2251799813685248), (-13541500365365/2251799813685248)), (1391/2251799813685248), by norm_num⟩
  | 1 => ⟨((555299669630487/562949953421312), (-20220248464841/1125899906842624)), (525/281474976710656), by norm_num⟩
  | 0 => ⟨((1095192610598709/1125899906842624), (-40073091737167/1125899906842624)), (531/140737488355328), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095192610598709/1125899906842624), (-40073091737167/1125899906842624)), (2025604784917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1063896527878541/1125899906842624), (-77960311902795/1125899906842624)), (1071/140737488355328), by norm_num⟩
  | 2 => ⟨((999909499022097/1125899906842624), (-2302094768861/17592186044416)), (4345/281474976710656), by norm_num⟩
  | 3 => ⟨((434368842878361/562949953421312), (-261694188683713/1125899906842624)), (8855/281474976710656), by norm_num⟩
  | 4 => ⟨((609486966019473/1125899906842624), (-403843365598305/1125899906842624)), (142251/2251799813685248), by norm_num⟩
  | 5 => ⟨((92541484613065/562949953421312), (-218613809406779/562949953421312)), (128029/1125899906842624), by norm_num⟩
  | 6 => ⟨((-557464421844903/4503599627370496), (-574995240169215/4503599627370496)), (566117/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-9259842901/1073741824)), (1/4294967296), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1931040333/1073741824), (-38572530651/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1346700395897053/9007199254740992), (-640446211158325/9007199254740992)), (1035439/9007199254740992), by norm_num⟩
  | 1 => ⟨((3079649461/8589934592), (11716636217/68719476736)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((-59077415075/137438953472), (-14047633299/68719476736)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((47220484779/137438953472), (22456502321/137438953472)), (41/137438953472), by norm_num⟩
  | 4 => ⟨((-56614888615/274877906944), (-26924170379/274877906944)), (51/274877906944), by norm_num⟩
  | 5 => ⟨((6787828689/68719476736), (12912268175/274877906944)), (51/549755813888), by norm_num⟩
  | 6 => ⟨((-86808012405/2199023255552), (-5160377803/274877906944)), (21/549755813888), by norm_num⟩
  | 7 => ⟨((7434161521/549755813888), (14141766331/2199023255552)), (15/1099511627776), by norm_num⟩
  | 8 => ⟨((-35652681537/8796093022208), (-16955237317/8796093022208)), (37/8796093022208), by norm_num⟩
  | 9 => ⟨((37996176231/35184372088832), (36139451921/70368744177664)), (81/70368744177664), by norm_num⟩
  | 10 => ⟨((-72888681095/281474976710656), (-34663448369/281474976710656)), (5/17592186044416), by norm_num⟩
  | 11 => ⟨((63556154123/1125899906842624), (30225206903/1125899906842624)), (9/140737488355328), by norm_num⟩
  | 12 => ⟨((-50800333843/4503599627370496), (-24158960251/4503599627370496)), (15/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-3514031783467/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889592852063041/316912650057057350374175801344), (-2080284779489/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945105170557633/19807040628566084398385987584), (-292492339575/2475880078570760549798248448)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945006991838605/1237940039285380274899124224), (-2485727394163/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885839716627147/77371252455336267181195264), (-4970425404669/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550010775126437/9671406556917033397649408), (-4658680174721/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629594007820263/302231454903657293676544), (-4075251598189/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888439368631465/75557863725914323419136), (-3310116809101/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298023554696605/4722366482869645213696), (-620422681245/590295810358705651712)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622111494526667/590295810358705651712), (-6821734978269/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912150228296683/36893488147419103232), (-8522797564755/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823581296646293/9223372036854775808), (-4791068960187/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594823974369859/1152921504606846976), (-1196828469259/144115188075855872)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((597653783371555/72057594037927936), (-2092338107601/36028797018963968)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((746357272616001/18014398509481984), (-12537140168227/36028797018963968)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((745290658443881/4503599627370496), (-3910470553375/2251799813685248)), (695/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115263616836371/2251799813685248), (-7798795782429/1125899906842624)), (1395/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109901536878147/1125899906842624), (-2910718118487/140737488355328)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093729777662699/1125899906842624), (-23064715841071/562949953421312)), (4271/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093729777662699/1125899906842624), (-23064715841071/562949953421312)), (16292576316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((265147215756385/281474976710656), (-89622767975711/1125899906842624)), (8649/1125899906842624), by norm_num⟩
  | 2 => ⟨((991932310365033/1125899906842624), (-84423943026267/562949953421312)), (2209/140737488355328), by norm_num⟩
  | 3 => ⟨((424291757160279/562949953421312), (-297514322000477/1125899906842624)), (4555/140737488355328), by norm_num⟩
  | 4 => ⟨((1121910047496799/2251799813685248), (-224234629907605/562949953421312)), (18547/281474976710656), by norm_num⟩
  | 5 => ⟨((403395935923943/4503599627370496), (-1787520064695999/4503599627370496)), (266053/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1346700395897053/9007199254740992), (-640446211158325/9007199254740992)), (1035439/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-38572530651/4294967296)), (1/4294967296), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2001111149/1073741824), (-79944390401/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-693652409086607/4503599627370496), (-41125657599479/2251799813685248)), (14199/140737488355328), by norm_num⟩
  | 1 => ⟨((105203947997/274877906944), (12182405/268435456)), (9/34359738368), by norm_num⟩
  | 2 => ⟨((-65355497491/137438953472), (-3874833817/68719476736)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((54134103439/137438953472), (6419066879/137438953472)), (79/274877906944), by norm_num⟩
  | 4 => ⟨((-8407387101/34359738368), (-7975390987/274877906944)), (51/274877906944), by norm_num⟩
  | 5 => ⟨((66853030767/549755813888), (7927240839/549755813888)), (13/137438953472), by norm_num⟩
  | 6 => ⟨((-110749027141/2199023255552), (-13132302317/2199023255552)), (89/2199023255552), by norm_num⟩
  | 7 => ⟨((78628855429/4398046511104), (9323584387/4398046511104)), (65/4398046511104), by norm_num⟩
  | 8 => ⟨((-97692682861/17592186044416), (-5792059211/8796093022208)), (83/17592186044416), by norm_num⟩
  | 9 => ⟨((107892087679/70368744177664), (6396767311/35184372088832)), (47/35184372088832), by norm_num⟩
  | 10 => ⟨((-53620353227/140737488355328), (-12716295703/281474976710656)), (3/8796093022208), by norm_num⟩
  | 11 => ⟨((12112870209/140737488355328), (11490475547/1125899906842624)), (89/1125899906842624), by norm_num⟩
  | 12 => ⟨((-20066234487/1125899906842624), (-9517586365/4503599627370496)), (19/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-984633279509/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779082691128443/633825300114114700748351602688), (-9106780893/1237940039285380274899124224)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890094336162821/39614081257132168796771975168), (-5244614578185/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889890576666797/2475880078570760549798248448), (-348208732813/154742504910672534362390528)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110722240978423/9671406556917033397649408), (-696267930527/19342813113834066795298816)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774947370002295/4835703278458516698824704), (-5220738479283/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259086303931153/604462909807314587353088), (-2283437612043/302231454903657293676544)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944136874038751/37778931862957161709568), (-7418789332825/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648949521470079/2361183241434822606848), (-695250884161/590295810358705651712)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405484952470719/147573952589676412928), (-3822185970279/295147905179352825856)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912042565163609/36893488147419103232), (-4775191817771/36893488147419103232)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823338065597509/9223372036854775808), (-5368597725365/4611686018427387904)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594579509523299/1152921504606846976), (-10728463737027/1152921504606846976)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597546137674343/72057594037927936), (-9377583925965/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492388847249295/36028797018963968), (-3511683894099/9007199254740992)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490169381770833/9007199254740992), (-17524056628769/9007199254740992)), (87/562949953421312), by norm_num⟩
  | 2 => ⟨((139355562570441/281474976710656), (-1092033003309/140737488355328)), (1399/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109255041705945/1125899906842624), (-26080026783187/1125899906842624)), (1057/562949953421312), by norm_num⟩
  | 0 => ⟨((1092366295580015/1125899906842624), (-51645339122557/1125899906842624)), (4293/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1092366295580015/1125899906842624), (-51645339122557/1125899906842624)), (16376499656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057462457746291/1125899906842624), (-50107143129169/562949953421312)), (8725/1125899906842624), by norm_num⟩
  | 2 => ⟨((984265066226227/1125899906842624), (-94122794401159/562949953421312)), (17943/1125899906842624), by norm_num⟩
  | 3 => ⟨((414486808826181/562949953421312), (-329129713579783/1125899906842624)), (9343/281474976710656), by norm_num⟩
  | 4 => ⟨((1028281265296255/2251799813685248), (-969321864883165/2251799813685248)), (153765/2251799813685248), by norm_num⟩
  | 5 => ⟨((104607418566163/4503599627370496), (-442639486709145/1125899906842624)), (545629/4503599627370496), by norm_num⟩
  | 6 => ⟨((-693652409086607/4503599627370496), (-41125657599479/2251799813685248)), (14199/140737488355328), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-79944390401/8589934592)), (1/4294967296), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16524560409/8589934592), (-10314940443/1073741824)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-323488369481755/2251799813685248), (59453049354999/2251799813685248)), (871453/9007199254740992), by norm_num⟩
  | 1 => ⟨((50642778653/137438953472), (-18614997649/274877906944)), (71/274877906944), by norm_num⟩
  | 2 => ⟨((-64948081283/137438953472), (11936631565/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((111059026237/274877906944), (-20411236975/274877906944)), (83/274877906944), by norm_num⟩
  | 4 => ⟨((-71215194497/274877906944), (13088447291/274877906944)), (55/274877906944), by norm_num⟩
  | 5 => ⟨((73065346947/549755813888), (-3357120447/137438953472)), (29/274877906944), by norm_num⟩
  | 6 => ⟨((-62469638235/1099511627776), (11481125245/1099511627776)), (51/1099511627776), by norm_num⟩
  | 7 => ⟨((91560833401/4398046511104), (-1051732315/274877906944)), (77/4398046511104), by norm_num⟩
  | 8 => ⟨((-3669514075/549755813888), (5395280251/4398046511104)), (51/8796093022208), by norm_num⟩
  | 9 => ⟨((33465307623/17592186044416), (-12300996101/35184372088832)), (15/8796093022208), by norm_num⟩
  | 10 => ⟨((-17167363857/35184372088832), (6310286409/70368744177664)), (63/140737488355328), by norm_num⟩
  | 11 => ⟨((64048609301/562949953421312), (-11771320051/562949953421312)), (15/140737488355328), by norm_num⟩
  | 12 => ⟨((-27380239879/1125899906842624), (5032139967/1125899906842624)), (105/4503599627370496), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (3855513892635/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778990604823257/633825300114114700748351602688), (4563936617795/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889990785973587/39614081257132168796771975168), (5133531920973/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889780611862383/2475880078570760549798248448), (2726651869767/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771445955279853/154742504910672534362390528), (5452095507783/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774895888422645/4835703278458516698824704), (39922311531/75557863725914323419136)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157374534949135/75557863725914323419136), (279375957663/37778931862957161709568)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944063793396857/37778931862957161709568), (907671050905/9444732965739290427392)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297789534175899/4722366482869645213696), (1360980206273/1180591620717411303424)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621789417591249/590295810358705651712), (7481970105399/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823897413240281/73786976294838206464), (9347331749157/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911563629725143/4611686018427387904), (5254347166371/4611686018427387904)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797184586286647/576460752303423488), (10499878601649/1152921504606846976)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194908757988987/144115188075855872), (9177478325783/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492114625211723/36028797018963968), (13746392240715/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((372457111650487/2251799813685248), (17148308936663/9007199254740992)), (87/562949953421312), by norm_num⟩
  | 2 => ⟨((1114506324691533/2251799813685248), (534259774317/70368744177664)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108754661107217/1125899906842624), (12757285246305/562949953421312)), (2113/1125899906842624), by norm_num⟩
  | 0 => ⟨((136424122041165/140737488355328), (6313763186859/140737488355328)), (4289/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((136424122041165/140737488355328), (6313763186859/140737488355328)), (16361240867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055677641325187/1125899906842624), (1530064252263/17592186044416)), (8701/1125899906842624), by norm_num⟩
  | 2 => ⟨((981318271668525/1125899906842624), (45908297491479/281474976710656)), (17831/1125899906842624), by norm_num⟩
  | 3 => ⟨((825352587921773/1125899906842624), (20006508072249/70368744177664)), (9225/281474976710656), by norm_num⟩
  | 4 => ⟨((1028049185134807/2251799813685248), (938622589086921/2251799813685248)), (150165/2251799813685248), by norm_num⟩
  | 5 => ⟨((78103196049331/2251799813685248), (1714095865885547/4503599627370496)), (131151/1125899906842624), by norm_num⟩
  | 6 => ⟨((-323488369481755/2251799813685248), (59453049354999/2251799813685248)), (871453/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-10314940443/1073741824)), (1/4294967296), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2125249673/1073741824), (-84903724439/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1115511759666891/9007199254740992), (137932390229873/2251799813685248)), (434235/4503599627370496), by norm_num⟩
  | 1 => ⟨((89840682545/274877906944), (-11108748945/68719476736)), (9/34359738368), by norm_num⟩
  | 2 => ⟨((-29636838971/68719476736), (14658312663/68719476736)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((52142211409/137438953472), (-25789418315/137438953472)), (45/137438953472), by norm_num⟩
  | 4 => ⟨((-68803142601/274877906944), (34029876715/274877906944)), (31/137438953472), by norm_num⟩
  | 5 => ⟨((72630175113/549755813888), (-8980679557/137438953472)), (17/137438953472), by norm_num⟩
  | 6 => ⟨((-63891731995/1099511627776), (3950088035/137438953472)), (31/549755813888), by norm_num⟩
  | 7 => ⟨((3010963279/137438953472), (-23827448643/2199023255552)), (3/137438953472), by norm_num⟩
  | 8 => ⟨((-63568837685/8796093022208), (15720500747/4398046511104)), (65/8796093022208), by norm_num⟩
  | 9 => ⟨((18640200781/8796093022208), (-36877602419/35184372088832)), (79/35184372088832), by norm_num⟩
  | 10 => ⟨((-78708093595/140737488355328), (38928842785/140737488355328)), (43/70368744177664), by norm_num⟩
  | 11 => ⟨((75532789565/562949953421312), (-18679172343/281474976710656)), (85/562949953421312), by norm_num⟩
  | 12 => ⟨((-66445120643/2251799813685248), (32863604455/2251799813685248)), (77/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (436745530069/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778906897360491/633825300114114700748351602688), (516946943189/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472474186576305/9903520314283042199192993792), (2325846745101/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944840430866645/1237940039285380274899124224), (4941423844387/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771346392962219/154742504910672534362390528), (1235074583335/38685626227668133590597632)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549698636624441/9671406556917033397649408), (2315166987651/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258914981241989/604462909807314587353088), (4050346677033/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887995850506457/75557863725914323419136), (6579572033475/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297691058568807/4722366482869645213696), (4932718215405/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621654543932733/590295810358705651712), (6779301873131/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911864807926857/36893488147419103232), (8469349957959/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822939578840971/9223372036854775808), (9521451632969/9223372036854775808)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199272856801521/144115188075855872), (2378311387265/288230376151711744)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((298686814947027/36028797018963968), (4157430902019/72057594037927936)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((372968857970319/9007199254740992), (6226923053787/18014398509481984)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((186191848121189/1125899906842624), (15535047531507/9007199254740992)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((69638789329685/140737488355328), (15486700414603/2251799813685248)), (1395/2251799813685248), by norm_num⟩
  | 1 => ⟨((34635810395253/35184372088832), (11554667063847/562949953421312)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090654173091563/1125899906842624), (45736715372131/1125899906842624)), (4271/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090654173091563/1125899906842624), (45736715372131/1125899906842624)), (16292576316451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527326927967757/562949953421312), (44304950360999/562949953421312)), (8623/1125899906842624), by norm_num⟩
  | 2 => ⟨((980942475100553/1125899906842624), (166005473315277/1125899906842624)), (17513/1125899906842624), by norm_num⟩
  | 3 => ⟨((103771471669597/140737488355328), (578530360947577/2251799813685248)), (35681/1125899906842624), by norm_num⟩
  | 4 => ⟨((1075603301792329/2251799813685248), (853147909098669/2251799813685248)), (70953/1125899906842624), by norm_num⟩
  | 5 => ⟨((23817676055145/281474976710656), (407517889630671/1125899906842624)), (486193/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1115511759666891/9007199254740992), (137932390229873/2251799813685248)), (434235/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-84903724439/8589934592)), (1/4294967296), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8723240287/4294967296), (-87123362369/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-890214834937725/9007199254740992), (388594599839887/4503599627370496)), (419739/4503599627370496), by norm_num⟩
  | 1 => ⟨((36785071759/137438953472), (-16057337711/68719476736)), (37/137438953472), by norm_num⟩
  | 2 => ⟨((-49807910487/137438953472), (43484076617/137438953472)), (13/34359738368), by norm_num⟩
  | 3 => ⟨((44960774003/137438953472), (-19626177071/68719476736)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((-15219504135/68719476736), (13287168191/68719476736)), (17/68719476736), by norm_num⟩
  | 5 => ⟨((65944289973/549755813888), (-57571709587/549755813888)), (19/137438953472), by norm_num⟩
  | 6 => ⟨((-59526815907/1099511627776), (51969026575/1099511627776)), (71/1099511627776), by norm_num⟩
  | 7 => ⟨((23028800827/1099511627776), (-10052480919/549755813888)), (57/2199023255552), by norm_num⟩
  | 8 => ⟨((-62363148711/8796093022208), (13611311487/2199023255552)), (5/549755813888), by norm_num⟩
  | 9 => ⟨((37529452757/17592186044416), (-32764546497/17592186044416)), (25/8796093022208), by norm_num⟩
  | 10 => ⟨((-20326328417/35184372088832), (8872803673/17592186044416)), (7/8796093022208), by norm_num⟩
  | 11 => ⟨((40032522005/281474976710656), (-8737453735/70368744177664)), (57/281474976710656), by norm_num⟩
  | 12 => ⟨((-72273386177/2251799813685248), (492947153/17592186044416)), (105/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (3157369567249/10141204801825835211973625643008)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778828798469307/633825300114114700748351602688), (1868425742597/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889808997077247/39614081257132168796771975168), (4203194688761/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944793885589345/1237940039285380274899124224), (1116241816141/618970019642690137449562112)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771253463200383/154742504910672534362390528), (2231962199577/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549611685728195/9671406556917033397649408), (4183821262559/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258839069865683/604462909807314587353088), (3659735948517/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887872814296241/75557863725914323419136), (5944994497597/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297599061008133/4722366482869645213696), (4456929443631/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621528501243389/590295810358705651712), (3062663553173/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823572742747163/73786976294838206464), (3826116999791/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113922751927665/576460752303423488), (8602681367437/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398502118141545/288230376151711744), (8595082515787/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194595985318411/144115188075855872), (7512153310591/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((372912783445243/9007199254740992), (175799284977/562949953421312)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((744629486681917/4503599627370496), (14034087426085/9007199254740992)), (1387/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113951633642657/2251799813685248), (6994679370985/1125899906842624)), (87/140737488355328), by norm_num⟩
  | 1 => ⟨((1107959389773809/1125899906842624), (10436203517707/562949953421312)), (2101/1125899906842624), by norm_num⟩
  | 0 => ⟨((68121772136803/70368744177664), (20649718063489/562949953421312)), (2127/562949953421312), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((68121772136803/70368744177664), (20649718063489/562949953421312)), (8113863231468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1053629869018533/1125899906842624), (39980687592169/562949953421312)), (8549/1125899906842624), by norm_num⟩
  | 2 => ⟨((980319895808393/1125899906842624), (149657518843355/1125899906842624)), (17215/1125899906842624), by norm_num⟩
  | 3 => ⟨((833670665986323/1125899906842624), (260613296773223/1125899906842624)), (34555/1125899906842624), by norm_num⟩
  | 4 => ⟨((139241393719807/281474976710656), (771882684652155/2251799813685248)), (33585/562949953421312), by norm_num⟩
  | 5 => ⟨((572910365847059/4503599627370496), (1527354538654213/4503599627370496)), (450023/4503599627370496), by norm_num⟩
  | 6 => ⟨((-890214834937725/9007199254740992), (388594599839887/4503599627370496)), (419739/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-87123362369/8589934592)), (1/4294967296), by norm_num⟩, -2, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile008Terms1
