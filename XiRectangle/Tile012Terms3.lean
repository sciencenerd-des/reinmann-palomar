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
namespace Reinmann.XiRectangle.Tile012Terms3
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2489236171/1073741824), (-9140164067/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-445401117742513/18014398509481984), (429134901255087/4503599627370496)), (2385017/4503599627370496), by norm_num⟩
  | 1 => ⟨((2625949409/34359738368), (-632512187/2147483648)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((-507307569/4294967296), (7820488089/17179869184)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((1045406155/8589934592), (-16115640459/34359738368)), (95/34359738368), by norm_num⟩
  | 4 => ⟨((-1615697403/17179869184), (12453532205/34359738368)), (149/68719476736), by norm_num⟩
  | 5 => ⟨((3995351411/68719476736), (-1924719837/8589934592)), (47/34359738368), by norm_num⟩
  | 6 => ⟨((-1029150069/34359738368), (7932520969/68719476736)), (99/137438953472), by norm_num⟩
  | 7 => ⟨((1817798031/137438953472), (-14011290901/274877906944)), (89/274877906944), by norm_num⟩
  | 8 => ⟨((-5618890885/1099511627776), (5413686875/274877906944)), (35/274877906944), by norm_num⟩
  | 9 => ⟨((1929803363/1099511627776), (-7437304871/1099511627776)), (49/1099511627776), by norm_num⟩
  | 10 => ⟨((-4772083297/8796093022208), (4597805019/2199023255552)), (123/8796093022208), by norm_num⟩
  | 11 => ⟨((5363895295/35184372088832), (-20672015281/35184372088832)), (35/8796093022208), by norm_num⟩
  | 12 => ⟨((-690834503/17592186044416), (21299358943/140737488355328)), (73/70368744177664), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986542947/2535301200456458802993406410752), (594210291669/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444597325509451/158456325028528675187087900672), (702934200013/158456325028528675187087900672)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889314844543219/39614081257132168796771975168), (3162560269975/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889063089846849/2475880078570760549798248448), (1679712560689/1237940039285380274899124224)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((885364590939377/77371252455336267181195264), (839632706523/38685626227668133590597632)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387280149201981/2417851639229258349412352), (3147672728823/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157301223957909/75557863725914323419136), (2753264018587/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887176032888883/75557863725914323419136), (4472274134881/75557863725914323419136)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648538585353309/2361183241434822606848), (3352648833141/4722366482869645213696)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101300751988715/36893488147419103232), (4607363597911/590295810358705651712)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822678849074377/73786976294838206464), (5755413775857/73786976294838206464)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821760726040433/9223372036854775808), (6469631666845/9223372036854775808)), (6701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593008071076375/1152921504606846976), (3231562871233/576460752303423488)), (3353/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193723895208671/144115188075855872), (2823961444119/72057594037927936)), (2937/72057594037927936), by norm_num⟩
  | 4 => ⟨((93146844276953/2251799813685248), (8457277619541/36028797018963968)), (8823/36028797018963968), by norm_num⟩
  | 3 => ⟨((46488853299625/281474976710656), (2636518689033/2251799813685248)), (11049/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224705910529289/4503599627370496), (21015740469199/4503599627370496)), (1385/281474976710656), by norm_num⟩
  | 1 => ⟨((2211207296662651/2251799813685248), (15666569782865/1125899906842624)), (16699/1125899906842624), by norm_num⟩
  | 0 => ⟨((2170809587531091/2251799813685248), (15476924454301/562949953421312)), (33715/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2170809587531091/2251799813685248), (15476924454301/562949953421312)), (128612522605514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2091030327674605/2251799813685248), (14920267683967/281474976710656)), (66859/1125899906842624), by norm_num⟩
  | 2 => ⟨((1935412057480267/2251799813685248), (221680325468287/2251799813685248)), (262519/2251799813685248), by norm_num⟩
  | 3 => ⟨((1641654663560155/2251799813685248), (381066533721139/2251799813685248)), (502957/2251799813685248), by norm_num⟩
  | 4 => ⟨((1132346807993373/2251799813685248), (555626346896441/2251799813685248)), (451791/1125899906842624), by norm_num⟩
  | 5 => ⟨((864631616266195/4503599627370496), (558807862512015/2251799813685248)), (2709339/4503599627370496), by norm_num⟩
  | 6 => ⟨((-445401117742513/18014398509481984), (429134901255087/4503599627370496)), (2385017/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2489236171/1073741824), (-9140164067/536870912)), (1/536870912), by norm_num⟩, -3, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2525033459/1073741824), (-144868863/8388608)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1893885881/2199023255552), (857582926720083/9007199254740992)), (542691/1125899906842624), by norm_num⟩
  | 1 => ⟨((92785441/34359738368), (-20515032245/68719476736)), (53/34359738368), by norm_num⟩
  | 2 => ⟨((-145464107/34359738368), (32162382471/68719476736)), (169/68719476736), by norm_num⟩
  | 3 => ⟨((304067911/68719476736), (-33614988069/68719476736)), (179/68719476736), by norm_num⟩
  | 4 => ⟨((-119175397/34359738368), (6587475041/17179869184)), (71/34359738368), by norm_num⟩
  | 5 => ⟨((149469507/68719476736), (-33047983821/137438953472)), (45/34359738368), by norm_num⟩
  | 6 => ⟨((-78110129/68719476736), (8635146843/68719476736)), (3/4294967296), by norm_num⟩
  | 7 => ⟨((17493847/34359738368), (-15471687417/274877906944)), (87/274877906944), by norm_num⟩
  | 8 => ⟨((-3428241/17179869184), (24255693203/1099511627776)), (69/549755813888), by norm_num⟩
  | 9 => ⟨((305755871/4398046511104), (-16900796831/2199023255552)), (195/4398046511104), by norm_num⟩
  | 10 => ⟨((-191739153/8796093022208), (21196940283/8796093022208)), (31/2199023255552), by norm_num⟩
  | 11 => ⟨((218617093/35184372088832), (-1510520083/2199023255552)), (143/35184372088832), by norm_num⟩
  | 12 => ⟨((-228490877/140737488355328), (6314969311/35184372088832)), (151/140737488355328), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (2057920185317/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778338990208625/633825300114114700748351602688), (1217164086957/316912650057057350374175801344)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889258314814845/39614081257132168796771975168), (2738056104353/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944501559742575/1237940039285380274899124224), (2908486494821/2475880078570760549798248448)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770669315467585/154742504910672534362390528), (363462672711/19342813113834066795298816)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549064582425319/9671406556917033397649408), (1362568058971/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258360889378083/604462909807314587353088), (148978778937/37778931862957161709568)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887096773320935/75557863725914323419136), (483985723381/9444732965739290427392)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648508953339655/2361183241434822606848), (2902547792999/4722366482869645213696)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620730837024641/590295810358705651712), (3988783719069/590295810358705651712)), (4757/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822577794900639/73786976294838206464), (4982652403787/73786976294838206464)), (1487/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910823821637931/4611686018427387904), (700114029957/1152921504606846976)), (6695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796447870481815/576460752303423488), (349700154027/72057594037927936)), (1675/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193626451274721/144115188075855872), (2444692673979/72057594037927936)), (1467/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490205027820061/36028797018963968), (7321261112371/36028797018963968)), (8811/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487465643885591/9007199254740992), (4564592175115/4503599627370496)), (1379/1125899906842624), by norm_num⟩
  | 2 => ⟨((2224359363621151/4503599627370496), (1136958911663/281474976710656)), (11059/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210709275555621/2251799813685248), (13559986361693/1125899906842624)), (16657/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169899893786163/2251799813685248), (53574918427289/2251799813685248)), (67177/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2169899893786163/2251799813685248), (53574918427289/2251799813685248)), (256259926802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089704088512039/2251799813685248), (1613323499863/35184372088832)), (132665/2251799813685248), by norm_num⟩
  | 2 => ⟨((1934542329290437/2251799813685248), (191640123930271/2251799813685248)), (129199/1125899906842624), by norm_num⟩
  | 3 => ⟨((1645673857949097/2251799813685248), (82319913493295/562949953421312)), (487967/2251799813685248), by norm_num⟩
  | 4 => ⟨((1154550835476605/2251799813685248), (240646133463945/1125899906842624)), (855949/2251799813685248), by norm_num⟩
  | 5 => ⟨((489095602016549/2251799813685248), (987079553898029/4503599627370496)), (2487253/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1893885881/2199023255552), (857582926720083/9007199254740992)), (542691/1125899906842624), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-144868863/8388608)), (1/536870912), by norm_num⟩, -3, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2559306987/1073741824), (-18794910689/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((185624518499879/9007199254740992), (1619339527022139/18014398509481984)), (3889007/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1125192093/17179869184), (-19631760355/68719476736)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((3575921041/34359738368), (7798848899/17179869184)), (39/17179869184), by norm_num⟩
  | 3 => ⟨((-3788156521/34359738368), (-16523441077/34359738368)), (85/34359738368), by norm_num⟩
  | 4 => ⟨((6019482671/68719476736), (26256192603/68719476736)), (137/68719476736), by norm_num⟩
  | 5 => ⟨((-478255999/8589934592), (-16688718695/68719476736)), (89/68719476736), by norm_num⟩
  | 6 => ⟨((4053128825/137438953472), (8839607729/68719476736)), (3/4294967296), by norm_num⟩
  | 7 => ⟨((-3680303311/274877906944), (-2006624943/34359738368)), (89/274877906944), by norm_num⟩
  | 8 => ⟨((5848101017/1099511627776), (25508648345/1099511627776)), (143/1099511627776), by norm_num⟩
  | 9 => ⟨((-4130128853/2199023255552), (-9007539731/1099511627776)), (103/2199023255552), by norm_num⟩
  | 10 => ⟨((5250308729/8796093022208), (5725289229/2199023255552)), (133/8796093022208), by norm_num⟩
  | 11 => ⟨((-6067550461/35184372088832), (-26465857985/35184372088832)), (39/8796093022208), by norm_num⟩
  | 12 => ⟨((50216151/1099511627776), (438072507/2199023255552)), (21/17592186044416), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455839/1267650600228229401496703205376), (1752574498147/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889145339857741/316912650057057350374175801344), (2073023364847/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944602012791771/19807040628566084398385987584), (2331666818451/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236118189425395/309485009821345068724781056), (1238396788621/1237940039285380274899124224)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221326474914629/19342813113834066795298816), (154757257075/9671406556917033397649408)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549010754401999/9671406556917033397649408), (2320639285301/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629156941579367/302231454903657293676544), (2029840067881/604462909807314587353088)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117938785188261/4722366482869645213696), (25758921649/590295810358705651712)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648480450877005/2361183241434822606848), (2471677417173/4722366482869645213696)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405163175824261/147573952589676412928), (1698320762545/295147905179352825856)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822480499343959/73786976294838206464), (4242931359007/73786976294838206464)), (743/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910769347987427/4611686018427387904), (4769353761039/9223372036854775808)), (3345/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592787430283819/1152921504606846976), (4764428212625/1152921504606846976)), (3347/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193532394078299/144115188075855872), (2081669795191/72057594037927936)), (2931/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490065367452489/36028797018963968), (779244318013/4503599627370496)), (8801/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487293554233887/9007199254740992), (7773131701089/9007199254740992)), (1377/1125899906842624), by norm_num⟩
  | 2 => ⟨((556005651767341/1125899906842624), (7744233360539/2251799813685248)), (11039/2251799813685248), by norm_num⟩
  | 1 => ⟨((2210222576645753/2251799813685248), (23088689544687/2251799813685248)), (33233/2251799813685248), by norm_num⟩
  | 0 => ⟨((135562469811243/140737488355328), (22802108052999/1125899906842624)), (66935/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((135562469811243/140737488355328), (22802108052999/1125899906842624)), (255336770064543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088320254559559/2251799813685248), (43927316320483/1125899906842624)), (32915/562949953421312), by norm_num⟩
  | 2 => ⟨((1933281556677367/2251799813685248), (162952859029469/2251799813685248)), (127239/1125899906842624), by norm_num⟩
  | 3 => ⟨((824012845318075/1125899906842624), (279806184417381/2251799813685248)), (118449/562949953421312), by norm_num⟩
  | 4 => ⟨((585686427391995/1125899906842624), (409563743203307/2251799813685248)), (405631/1125899906842624), by norm_num⟩
  | 5 => ⟨((1069697135472305/4503599627370496), (852210481902337/4503599627370496)), (1139137/2251799813685248), by norm_num⟩
  | 6 => ⟨((185624518499879/9007199254740992), (1619339527022139/18014398509481984)), (3889007/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2559306987/1073741824), (-18794910689/1073741824)), (1/536870912), by norm_num⟩, -3, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-162011325/67108864), (-4759082671/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((87642305756163/2251799813685248), (725353931995977/9007199254740992)), (6868669/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4304652393/34359738368), (-17813295259/68719476736)), (43/34359738368), by norm_num⟩
  | 2 => ⟨((6928070761/34359738368), (14334696367/34359738368)), (71/34359738368), by norm_num⟩
  | 3 => ⟨((-3716766581/17179869184), (-1922566983/4294967296)), (39/17179869184), by norm_num⟩
  | 4 => ⟨((5981905047/34359738368), (6188504383/17179869184)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-7702003817/68719476736), (-1992002715/8589934592)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((258247853/4294967296), (8549345843/68719476736)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-1900040619/68719476736), (-15725304373/274877906944)), (87/274877906944), by norm_num⟩
  | 8 => ⟨((6115994815/549755813888), (12654450521/549755813888)), (9/68719476736), by norm_num⟩
  | 9 => ⟨((-2187403095/549755813888), (-18103602159/2199023255552)), (105/2199023255552), by norm_num⟩
  | 10 => ⟨((5632783153/4398046511104), (5827324733/2199023255552)), (69/4398046511104), by norm_num⟩
  | 11 => ⟨((-3296587185/8796093022208), (-1705221337/2199023255552)), (41/8796093022208), by norm_num⟩
  | 12 => ⟨((1768550799/17592186044416), (3659263825/17592186044416)), (45/35184372088832), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (182461929527/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778244212719877/633825300114114700748351602688), (1726505647373/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944575900267863/19807040628566084398385987584), (121369454825/2475880078570760549798248448)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888890091847585/2475880078570760549798248448), (2062772671811/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442639112362781/38685626227668133590597632), (2062201336971/154742504910672534362390528)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387239735537021/2417851639229258349412352), (483176729555/2417851639229258349412352)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629134312812883/302231454903657293676544), (1690511952377/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943473583003295/37778931862957161709568), (2745945042921/75557863725914323419136)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296905982055429/4722366482869645213696), (1029232254767/2361183241434822606848)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202572174572319/73786976294838206464), (2828773939061/590295810358705651712)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227798334669499/9223372036854775808), (1766773455335/36893488147419103232)), (1485/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821433573793549/9223372036854775808), (3971914714455/9223372036854775808)), (6685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398170710399233/288230376151711744), (3967761729461/1152921504606846976)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193441477854775/144115188075855872), (866781212965/36028797018963968)), (183/4503599627370496), by norm_num⟩
  | 4 => ⟨((372482546904641/9007199254740992), (324460472245/2251799813685248)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((371781665628421/2251799813685248), (3236465245213/4503599627370496)), (11001/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223695043702315/4503599627370496), (6448573068031/2251799813685248)), (2755/562949953421312), by norm_num⟩
  | 1 => ⟨((276218335015629/281474976710656), (4806089546063/562949953421312)), (8289/562949953421312), by norm_num⟩
  | 0 => ⟨((542027227728013/562949953421312), (37965821072511/2251799813685248)), (4169/140737488355328), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((542027227728013/562949953421312), (37965821072511/2251799813685248)), (15903473437261537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((130430523215445/140737488355328), (73109549505371/2251799813685248)), (32675/562949953421312), by norm_num⟩
  | 2 => ⟨((965840311873375/1125899906842624), (135510685965287/2251799813685248)), (31343/281474976710656), by norm_num⟩
  | 3 => ⟨((1648915176021437/2251799813685248), (7265392909233/70368744177664)), (57547/281474976710656), by norm_num⟩
  | 4 => ⟨((1183439329275009/2251799813685248), (42561568945817/281474976710656)), (769301/2251799813685248), by norm_num⟩
  | 5 => ⟨((570474098361459/2251799813685248), (715787032932691/4503599627370496)), (2082535/4503599627370496), by norm_num⟩
  | 6 => ⟨((87642305756163/2251799813685248), (725353931995977/9007199254740992)), (6868669/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-4759082671/268435456)), (1/536870912), by norm_num⟩, -3, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1311882945/536870912), (-1204267547/67108864)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((241732077596841/4503599627370496), (1229987729563849/18014398509481984)), (5986319/18014398509481984), by norm_num⟩
  | 1 => ⟨((-12017615435/68719476736), (-15287089399/68719476736)), (19/17179869184), by norm_num⟩
  | 2 => ⟨((9788637811/34359738368), (6225851631/17179869184)), (63/34359738368), by norm_num⟩
  | 3 => ⟨((-10630775655/34359738368), (-6761475215/17179869184)), (35/17179869184), by norm_num⟩
  | 4 => ⟨((2164755835/8589934592), (11014769495/34359738368)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((-11284773587/68719476736), (-14354872943/68719476736)), (79/68719476736), by norm_num⟩
  | 6 => ⟨((3063906813/34359738368), (7794926973/68719476736)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((-5704288103/137438953472), (-7256178453/137438953472)), (21/68719476736), by norm_num⟩
  | 8 => ⟨((2323140165/137438953472), (2955166237/137438953472)), (35/274877906944), by norm_num⟩
  | 9 => ⟨((-3364006635/549755813888), (-4279207505/549755813888)), (13/274877906944), by norm_num⟩
  | 10 => ⟨((8768206697/4398046511104), (5576828463/2199023255552)), (69/4398046511104), by norm_num⟩
  | 11 => ⟨((-2597060353/4398046511104), (-13214433097/17592186044416)), (21/4398046511104), by norm_num⟩
  | 12 => ⟨((2820491115/17592186044416), (14351299575/70368744177664)), (93/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396370611537/5070602400912917605986812821504), (589152415859/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889099724768673/316912650057057350374175801344), (1393613407255/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889101483604633/39614081257132168796771975168), (1567482819239/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888836684359299/2475880078570760549798248448), (1665035466295/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442625775735641/38685626227668133590597632), (1664568760537/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548908994546071/9671406556917033397649408), (780018757471/4835703278458516698824704)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314556246544347/151115727451828646838272), (341134331619/151115727451828646838272)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886876373123335/75557863725914323419136), (554111129329/18889465931478580854784)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81053312085149/295147905179352825856), (207690156493/590295810358705651712)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405126177285377/147573952589676412928), (1141636395939/295147905179352825856)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822296075761171/73786976294838206464), (2852113979783/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821332000815665/9223372036854775808), (3205912086129/9223372036854775808)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592581710105537/1152921504606846976), (3202520278303/1152921504606846976)), (3341/576460752303423488), by norm_num⟩
  | 5 => ⟨((596676741697953/72057594037927936), (2798394086671/144115188075855872)), (2925/72057594037927936), by norm_num⟩
  | 4 => ⟨((372449796109211/9007199254740992), (4189980369209/36028797018963968)), (2195/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486964632393803/9007199254740992), (5224182584267/9007199254740992)), (5493/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223376130984179/4503599627370496), (10408590154435/4503599627370496)), (11001/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209281095976255/2251799813685248), (15513809464369/2251799813685248)), (16541/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083614190733755/1125899906842624), (30633479333333/2251799813685248)), (33241/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083614190733755/1125899906842624), (30633479333333/2251799813685248)), (126804356101607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042708241390459/1125899906842624), (58965939539399/2251799813685248)), (129781/2251799813685248), by norm_num⟩
  | 2 => ⟨((1929782966593661/2251799813685248), (109218005517887/2251799813685248)), (247181/2251799813685248), by norm_num⟩
  | 3 => ⟨((25758102077845/35184372088832), (93599371228659/1125899906842624)), (447645/2251799813685248), by norm_num⟩
  | 4 => ⟨((1191300384743149/2251799813685248), (4282693592703/35184372088832)), (729861/2251799813685248), by norm_num⟩
  | 5 => ⟨((596886970281039/2251799813685248), (18125854682879/140737488355328)), (1899873/4503599627370496), by norm_num⟩
  | 6 => ⟨((241732077596841/4503599627370496), (1229987729563849/18014398509481984)), (5986319/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1311882945/536870912), (-1204267547/67108864)), (1/536870912), by norm_num⟩, -3, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-4872868967/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((583230570939317/9007199254740992), (487971725248343/9007199254740992)), (5152197/18014398509481984), by norm_num⟩
  | 1 => ⟨((-14665472543/68719476736), (-3067541507/17179869184)), (67/68719476736), by norm_num⟩
  | 2 => ⟨((6041875633/17179869184), (10110116387/34359738368)), (57/34359738368), by norm_num⟩
  | 3 => ⟨((-6637678817/17179869184), (-11107098103/34359738368)), (1/536870912), by norm_num⟩
  | 4 => ⟨((10938353275/34359738368), (9151795851/34359738368)), (27/17179869184), by norm_num⟩
  | 5 => ⟨((-14420411191/68719476736), (-6032565231/34359738368)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((7921220471/68719476736), (6627450295/68719476736)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((-932394659/17179869184), (-6240855717/137438953472)), (79/274877906944), by norm_num⟩
  | 8 => ⟨((12292082763/549755813888), (5142210587/274877906944)), (67/549755813888), by norm_num⟩
  | 9 => ⟨((-4501411059/549755813888), (-15064788645/2199023255552)), (25/549755813888), by norm_num⟩
  | 10 => ⟨((5934366607/2199023255552), (9930217159/4398046511104)), (67/4398046511104), by norm_num⟩
  | 11 => ⟨((-7112256087/8796093022208), (-2975306891/4398046511104)), (41/8796093022208), by norm_num⟩
  | 12 => ⟨((15627223875/70368744177664), (3268708713/17592186044416)), (23/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (226883827891/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778156265933677/633825300114114700748351602688), (536658352713/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889052935958527/39614081257132168796771975168), (603611448067/19807040628566084398385987584)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888785146609829/2475880078570760549798248448), (80146938937/154742504910672534362390528)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770451614790341/154742504910672534362390528), (1281987470683/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548860777067287/9671406556917033397649408), (1201477121517/9671406556917033397649408)), (1617/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258182848510055/604462909807314587353088), (1050906508975/604462909807314587353088)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943403999004767/37778931862957161709568), (1706999718541/75557863725914323419136)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296801798218999/4722366482869645213696), (1279617189615/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620434455732921/590295810358705651712), (439611574481/147573952589676412928)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822208468611391/73786976294838206464), (1098258989015/36893488147419103232)), (1483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821233730566175/9223372036854775808), (617241794147/2305843009213693952)), (6675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398120949741955/288230376151711744), (308290680911/144115188075855872)), (6677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298317053571307/36028797018963968), (2155066538335/144115188075855872)), (1461/36028797018963968), by norm_num⟩
  | 4 => ⟨((744836042439861/18014398509481984), (3226672632647/36028797018963968)), (8771/36028797018963968), by norm_num⟩
  | 3 => ⟨((185850895035921/1125899906842624), (4022989083729/9007199254740992)), (2743/2251799813685248), by norm_num⟩
  | 2 => ⟨((555766343611057/1125899906842624), (8015006272917/4503599627370496)), (21967/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208825362882871/2251799813685248), (93323204747/17592186044416)), (33011/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166358119335637/2251799813685248), (23583920759819/2251799813685248)), (16567/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166358119335637/2251799813685248), (23583920759819/2251799813685248)), (63198091747093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2083911398950381/2251799813685248), (45378117462571/2251799813685248)), (1007/17592186044416), by norm_num⟩
  | 2 => ⟨((1927625856770593/2251799813685248), (83989682980211/2251799813685248)), (30471/281474976710656), by norm_num⟩
  | 3 => ⟨((823493978972733/1125899906842624), (143796694209381/2251799813685248)), (435535/2251799813685248), by norm_num⟩
  | 4 => ⟨((37357503817501/70368744177664), (210348559686239/2251799813685248)), (692735/2251799813685248), by norm_num⟩
  | 5 => ⟨((1229976626422695/4503599627370496), (223340553062727/2251799813685248)), (1729887/4503599627370496), by norm_num⟩
  | 6 => ⟨((583230570939317/9007199254740992), (487971725248343/9007199254740992)), (5152197/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-4872868967/268435456)), (1/536870912), by norm_num⟩, -3, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile012Terms3
