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
namespace Reinmann.XiRectangle.Tile009Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4978472343/2147483648), (-111144395055/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((103233759481169/1125899906842624), (-322740158497127/9007199254740992)), (298061/9007199254740992), by norm_num⟩
  | 1 => ⟨((-77905257123/274877906944), (30444443705/274877906944)), (15/137438953472), by norm_num⟩
  | 2 => ⟨((60202114277/137438953472), (-11763133495/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((-15507274251/34359738368), (6060057503/34359738368)), (27/137438953472), by norm_num⟩
  | 4 => ⟨((23966821523/68719476736), (-37463790023/274877906944)), (11/68719476736), by norm_num⟩
  | 5 => ⟨((-926030785/4294967296), (23160433085/274877906944)), (29/274877906944), by norm_num⟩
  | 6 => ⟨((61064543351/549755813888), (-1491455873/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-26964727985/549755813888), (10537493533/549755813888)), (15/549755813888), by norm_num⟩
  | 8 => ⟨((83349118945/4398046511104), (-32571839863/4398046511104)), (3/274877906944), by norm_num⟩
  | 9 => ⟨((-7156546253/1099511627776), (11186771089/4398046511104)), (35/8796093022208), by norm_num⟩
  | 10 => ⟨((8848475315/4398046511104), (-13831513741/17592186044416)), (45/35184372088832), by norm_num⟩
  | 11 => ⟨((-79566582825/140737488355328), (7773417485/35184372088832)), (53/140737488355328), by norm_num⟩
  | 12 => ⟨((20495307115/140737488355328), (-32037284605/562949953421312)), (57/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-485274820857/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889196680400981/316912650057057350374175801344), (-71758322089/79228162514264337593543950336)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889319636759215/39614081257132168796771975168), (-322847483385/19807040628566084398385987584)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889068479478383/2475880078570760549798248448), (-685888726083/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770734906329967/154742504910672534362390528), (-21428323637/4835703278458516698824704)), (431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549126318973973/9671406556917033397649408), (-642656009371/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258415153766975/604462909807314587353088), (-140532596265/151115727451828646838272)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887185411718721/75557863725914323419136), (-913098995037/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297084786459887/4722366482869645213696), (-684506888293/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((101301465468673/36893488147419103232), (-117585196175/73786976294838206464)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822694532722921/73786976294838206464), (-36721230989/2305843009213693952)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821780311251335/9223372036854775808), (-660451448503/4611686018427387904)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398257519464679/288230376151711744), (-41236794391/36028797018963968)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((298436467201281/36028797018963968), (-576570431505/72057594037927936)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((93149242979001/2251799813685248), (-107921061355/2251799813685248)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((743850362791451/4503599627370496), (-538306542419/2251799813685248)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224848940730193/4503599627370496), (-4290907048363/4503599627370496)), (685/1125899906842624), by norm_num⟩
  | 1 => ⟨((552872950627771/562949953421312), (-6397636575313/2251799813685248)), (2057/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085827682935259/1125899906842624), (-6320604858043/1125899906842624)), (8243/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1085827682935259/1125899906842624), (-6320604858043/1125899906842624)), (31444558150481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047146198181165/1125899906842624), (-12191292824607/1125899906842624)), (15993/2251799813685248), by norm_num⟩
  | 2 => ⟨((1947538188930289/2251799813685248), (-22677088530899/1125899906842624)), (1881/140737488355328), by norm_num⟩
  | 3 => ⟨((1683474691189753/2251799813685248), (-78451904399797/2251799813685248)), (6659/281474976710656), by norm_num⟩
  | 4 => ⟨((1255854235969735/2251799813685248), (-29325829660797/562949953421312)), (83367/2251799813685248), by norm_num⟩
  | 5 => ⟨((347146709919959/1125899906842624), (-130842776268163/2251799813685248)), (25419/562949953421312), by norm_num⟩
  | 6 => ⟨((103233759481169/1125899906842624), (-322740158497127/9007199254740992)), (298061/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-111144395055/8589934592)), (1/4294967296), by norm_num⟩, -2, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-20200267671/8589934592), (-112742743941/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((727252759927335/9007199254740992), (-14204562844301/281474976710656)), (330847/9007199254740992), by norm_num⟩
  | 1 => ⟨((-34794568211/137438953472), (43494457655/274877906944)), (17/137438953472), by norm_num⟩
  | 2 => ⟨((27274541843/68719476736), (-34094155101/137438953472)), (29/137438953472), by norm_num⟩
  | 3 => ⟨((-28506389397/68719476736), (35634008705/137438953472)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((698293899/2147483648), (-13966278523/68719476736)), (27/137438953472), by norm_num⟩
  | 5 => ⟨((-28025554961/137438953472), (17516474211/137438953472)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((14645660913/137438953472), (-36615202381/549755813888)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((-26240791475/549755813888), (1025060315/34359738368)), (37/1099511627776), by norm_num⟩
  | 8 => ⟨((82277849891/4398046511104), (-51425131019/4398046511104)), (61/4398046511104), by norm_num⟩
  | 9 => ⟨((-14332317913/2199023255552), (17915911207/4398046511104)), (11/2199023255552), by norm_num⟩
  | 10 => ⟨((17975559967/8796093022208), (-22470094385/17592186044416)), (29/17592186044416), by norm_num⟩
  | 11 => ⟨((-10247684419/17592186044416), (51239891619/140737488355328)), (69/140737488355328), by norm_num⟩
  | 12 => ⟨((21421036815/140737488355328), (-13388531983/140737488355328)), (37/281474976710656), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633433/10141204801825835211973625643008), (-727654766629/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778341768247145/633825300114114700748351602688), (-860747910403/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944630797298121/19807040628566084398385987584), (-968143812657/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889006808123469/2475880078570760549798248448), (-257101532845/618970019642690137449562112)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770673233235095/154742504910672534362390528), (-1028128747643/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549068498606655/9671406556917033397649408), (-30111752645/302231454903657293676544)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314591139778379/151115727451828646838272), (-210708643691/151115727451828646838272)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887103191990473/75557863725914323419136), (-10695736299/590295810358705651712)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297023118693079/4722366482869645213696), (-513153993767/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620738649527181/590295810358705651712), (-705194782655/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822588528131331/73786976294838206464), (-1761811894133/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821661046385371/9223372036854775808), (-1980423991387/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592910801015977/1152921504606846976), (-1978407984847/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193641488297961/144115188075855872), (-1728841699457/144115188075855872)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490231290872711/36028797018963968), (-2588738766077/36028797018963968)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((743752467590959/4503599627370496), (-3228022093977/9007199254740992)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224457231241445/4503599627370496), (-1608100251193/1125899906842624)), (343/562949953421312), by norm_num⟩
  | 1 => ⟨((552725983100547/562949953421312), (-9589706188851/2251799813685248)), (2061/1125899906842624), by norm_num⟩
  | 0 => ⟨((271309812070313/281474976710656), (-18945102654905/2251799813685248)), (4133/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((271309812070313/281474976710656), (-18945102654905/2251799813685248)), (15766148093795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045967309904055/1125899906842624), (-36521841486739/2251799813685248)), (16075/2251799813685248), by norm_num⟩
  | 2 => ⟨((485706653635245/562949953421312), (-33928994984779/1125899906842624)), (15195/1125899906842624), by norm_num⟩
  | 3 => ⟨((209275405192225/281474976710656), (-117094164517539/2251799813685248)), (54273/2251799813685248), by norm_num⟩
  | 4 => ⟨((1238673808239995/2251799813685248), (-87058995479527/1125899906842624)), (86349/2251799813685248), by norm_num⟩
  | 5 => ⟨((333954137331317/1125899906842624), (-11972389465617/140737488355328)), (1693/35184372088832), by norm_num⟩
  | 6 => ⟨((727252759927335/9007199254740992), (-14204562844301/281474976710656)), (330847/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20200267671/8589934592), (-112742743941/8589934592)), (1/4294967296), by norm_num⟩, -2, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-20474455899/8589934592), (-28568264247/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((76904614389749/1125899906842624), (-139531610577701/2251799813685248)), (360253/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7458709849/34359738368), (54130733575/274877906944)), (37/274877906944), by norm_num⟩
  | 2 => ⟨((23704181405/68719476736), (-21503798147/68719476736)), (31/137438953472), by norm_num⟩
  | 3 => ⟨((-50222109673/137438953472), (45560152045/137438953472)), (35/137438953472), by norm_num⟩
  | 4 => ⟨((9975535501/34359738368), (-36198153929/137438953472)), (15/68719476736), by norm_num⟩
  | 5 => ⟨((-25362231047/137438953472), (23007936349/137438953472)), (5/34359738368), by norm_num⟩
  | 6 => ⟨((53735023683/549755813888), (-48746973495/549755813888)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((-24396113977/549755813888), (44263001667/1099511627776)), (21/549755813888), by norm_num⟩
  | 8 => ⟨((38766081735/2199023255552), (-17583775249/1099511627776)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((-27377932121/4398046511104), (49673052695/8796093022208)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((69606833635/35184372088832), (-63145454153/35184372088832)), (67/35184372088832), by norm_num⟩
  | 11 => ⟨((-20110387659/35184372088832), (18243604767/35184372088832)), (41/70368744177664), by norm_num⟩
  | 12 => ⟨((21303964843/140737488355328), (-19326386003/140737488355328)), (45/281474976710656), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646257/10141204801825835211973625643008), (-479858744363/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889146145952793/316912650057057350374175801344), (-1135196694853/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236150741100169/4951760157141521099596496896), (-638416072709/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888947655868403/2475880078570760549798248448), (-678152201155/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885307036365889/77371252455336267181195264), (-338983397561/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549013026884001/9671406556917033397649408), (-1270793892027/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629158006310007/302231454903657293676544), (-555775481555/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887024287589223/75557863725914323419136), (-1805532474005/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1296963926117493/4722366482869645213696), (-1353504076643/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810328618298753/295147905179352825856), (-930010074741/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911243363681675/36893488147419103232), (-1161727170605/36893488147419103232)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227693309137871/1152921504606846976), (-2611727988093/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592796168707143/1152921504606846976), (-2609032954009/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((596770559480705/72057594037927936), (-2279875558751/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490080605579299/36028797018963968), (-1706882933983/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((371829087675957/2251799813685248), (-4256644664791/9007199254740992)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224079386249023/4503599627370496), (-8481682771985/4503599627370496)), (2747/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210335501118511/2251799813685248), (-1580474017685/281474976710656)), (4129/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169335135619899/2251799813685248), (-24974356833687/2251799813685248)), (4145/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169335135619899/2251799813685248), (-24974356833687/2251799813685248)), (15811924460982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2089613465432793/2251799813685248), (-48119508172585/2251799813685248)), (8079/1125899906842624), by norm_num⟩
  | 2 => ⟨((484520084925863/562949953421312), (-11163422655995/281474976710656)), (3835/281474976710656), by norm_num⟩
  | 3 => ⟨((832263057315359/1125899906842624), (-38432563750817/562949953421312)), (27623/1125899906842624), by norm_num⟩
  | 4 => ⟨((304979840824367/562949953421312), (-227274220831379/2251799813685248)), (22305/562949953421312), by norm_num⟩
  | 5 => ⟨((637956212964847/2251799813685248), (-492505987584735/4503599627370496)), (114681/2251799813685248), by norm_num⟩
  | 6 => ⟨((76904614389749/1125899906842624), (-139531610577701/2251799813685248)), (360253/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20474455899/8589934592), (-28568264247/2147483648)), (1/4294967296), by norm_num⟩, -2, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-20737449597/8589934592), (-115740890561/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((495949164120203/9007199254740992), (-317439574508267/4503599627370496)), (96461/2251799813685248), by norm_num⟩
  | 1 => ⟨((-48718224327/274877906944), (62365635513/274877906944)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((39204478629/137438953472), (-25093404557/68719476736)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-42064782829/137438953472), (26924184431/68719476736)), (39/137438953472), by norm_num⟩
  | 4 => ⟨((8462582033/34359738368), (-43332803185/137438953472)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((-43584001155/274877906944), (55793165039/274877906944)), (45/274877906944), by norm_num⟩
  | 6 => ⟨((46763829223/549755813888), (-59863756713/549755813888)), (25/274877906944), by norm_num⟩
  | 7 => ⟨((-10751925669/274877906944), (55055428363/1099511627776)), (3/68719476736), by norm_num⟩
  | 8 => ⟨((34609113607/2199023255552), (-44304146847/2199023255552)), (5/274877906944), by norm_num⟩
  | 9 => ⟨((-6189024395/1099511627776), (31691010495/4398046511104)), (59/8796093022208), by norm_num⟩
  | 10 => ⟨((31874721607/17592186044416), (-40803771019/17592186044416)), (5/2199023255552), by norm_num⟩
  | 11 => ⟨((-18654685601/35184372088832), (47760826217/70368744177664)), (3/4398046511104), by norm_num⟩
  | 12 => ⟨((40031411001/281474976710656), (-51245389629/281474976710656)), (53/281474976710656), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241879/10141204801825835211973625643008), (-591152788155/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889122381072853/316912650057057350374175801344), (-1398413123571/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889152449092929/39614081257132168796771975168), (-1572885127701/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888890821248763/2475880078570760549798248448), (-1670778992303/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770557224153521/154742504910672534362390528), (-52197384413/4835703278458516698824704)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1548959716528527/9671406556917033397649408), (-391357524009/2417851639229258349412352)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258269351265519/604462909807314587353088), (-684630046133/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471737108798175/18889465931478580854784), (-2224126984941/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324226753157197/1180591620717411303424), (-1667290069951/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810289470659369/295147905179352825856), (-2291216221101/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822388799555425/73786976294838206464), (-2862060192635/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821436223817863/9223372036854775808), (-1608562399991/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592685819131501/1152921504606846976), (-3213761948815/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((596722225358467/72057594037927936), (-2808263023265/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489935379631061/36028797018963968), (-4204848471069/36028797018963968)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487134429581347/9007199254740992), (-5242880363905/9007199254740992)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223714388228813/4503599627370496), (-326447544015/140737488355328)), (43/70368744177664), by norm_num⟩
  | 1 => ⟨((2209785150492229/2251799813685248), (-7785618848881/1125899906842624)), (4137/2251799813685248), by norm_num⟩
  | 0 => ⟨((542055808440395/562949953421312), (-30751614164997/2251799813685248)), (8311/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((542055808440395/562949953421312), (-30751614164997/2251799813685248)), (31703957564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087328678634823/2251799813685248), (-59220507882623/2251799813685248)), (16233/2251799813685248), by norm_num⟩
  | 2 => ⟨((1933313040368709/2251799813685248), (-27447525245243/562949953421312)), (15475/1125899906842624), by norm_num⟩
  | 3 => ⟨((827259471100359/1125899906842624), (-188523538051575/2251799813685248)), (14041/562949953421312), by norm_num⟩
  | 4 => ⟨((599940498547169/1125899906842624), (-138518425510727/1125899906842624)), (91939/2251799813685248), by norm_num⟩
  | 5 => ⟨((1210556091248289/4503599627370496), (-295240501411607/2251799813685248)), (120603/2251799813685248), by norm_num⟩
  | 6 => ⟨((495949164120203/9007199254740992), (-317439574508267/4503599627370496)), (96461/2251799813685248), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/8589934592), (-115740890561/8589934592)), (1/4294967296), by norm_num⟩, -2, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-5247531779/2147483648), (-29287786743/2147483648)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((748682775102557/18014398509481984), (-686894147021699/9007199254740992)), (1630477/18014398509481984), by norm_num⟩
  | 1 => ⟨((-37220470545/274877906944), (68297346265/274877906944)), (83/274877906944), by norm_num⟩
  | 2 => ⟨((30316971557/137438953472), (-55629836855/137438953472)), (35/68719476736), by norm_num⟩
  | 3 => ⟨((-32925206691/137438953472), (15103948239/34359738368)), (77/137438953472), by norm_num⟩
  | 4 => ⟨((26818375483/137438953472), (-12302530367/34359738368)), (1/2147483648), by norm_num⟩
  | 5 => ⟨((-34950742527/274877906944), (16033132639/68719476736)), (85/274877906944), by norm_num⟩
  | 6 => ⟨((9489407769/137438953472), (-34824995963/274877906944)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((-35334178971/1099511627776), (64836113591/1099511627776)), (45/549755813888), by norm_num⟩
  | 8 => ⟨((28780541545/2199023255552), (-52810579307/2199023255552)), (75/2199023255552), by norm_num⟩
  | 9 => ⟨((-41675459009/8796093022208), (19117996179/2199023255552)), (55/4398046511104), by norm_num⟩
  | 10 => ⟨((1697283359/1099511627776), (-12457655433/4398046511104)), (37/8796093022208), by norm_num⟩
  | 11 => ⟨((-16087019741/35184372088832), (29518722937/35184372088832)), (45/35184372088832), by norm_num⟩
  | 12 => ⟨((34942042217/281474976710656), (-64116566005/281474976710656)), (25/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (-698081217679/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444549757264555/158456325028528675187087900672), (-1651279563867/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236137623411975/4951760157141521099596496896), (-464323843201/9903520314283042199192993792)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888836126186371/2475880078570760549798248448), (-246610564827/309485009821345068724781056)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((27664101720399/2417851639229258349412352), (-986165729369/77371252455336267181195264)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548908401958319/9671406556917033397649408), (-1848473321979/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258224430891111/604462909807314587353088), (-808413483707/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886875401901559/75557863725914323419136), (-656560833329/18889465931478580854784)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1296852204740539/4722366482869645213696), (-984360031673/2361183241434822606848)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1620503527075895/590295810358705651712), (-2705427047677/590295810358705651712)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822294451828991/73786976294838206464), (-844860214915/18446744073709551616)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455332493252645/2305843009213693952), (-1899326012005/4611686018427387904)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592579431723137/1152921504606846976), (-948658065349/288230376151711744)), (209/144115188075855872), by norm_num⟩
  | 5 => ⟨((298337802157927/36028797018963968), (-3315786375279/144115188075855872)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489795211727511/36028797018963968), (-4964659288673/36028797018963968)), (1099/18014398509481984), by norm_num⟩
  | 3 => ⟨((743479344776725/4503599627370496), (-386879300631/562949953421312)), (1375/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223361330520347/4503599627370496), (-12332992213757/4503599627370496)), (5509/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209251664377461/2251799813685248), (-9191022773605/1125899906842624)), (4143/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083570464623839/1125899906842624), (-18148418265943/1125899906842624)), (2083/281474976710656), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083570464623839/1125899906842624), (-18148418265943/1125899906842624)), (7946015478038699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((521269954631783/562949953421312), (-69864434282663/2251799813685248)), (32613/2251799813685248), by norm_num⟩
  | 2 => ⟨((1928535913387597/2251799813685248), (-129383545615621/2251799813685248)), (31211/1125899906842624), by norm_num⟩
  | 3 => ⟨((411061259181185/562949953421312), (-221619002546045/2251799813685248)), (7131/140737488355328), by norm_num⟩
  | 4 => ⟨((1178802281789099/2251799813685248), (-323648614557667/2251799813685248)), (189083/2251799813685248), by norm_num⟩
  | 5 => ⟨((570577538037615/2251799813685248), (-677711620757397/4503599627370496)), (252321/2251799813685248), by norm_num⟩
  | 6 => ⟨((748682775102557/18014398509481984), (-686894147021699/9007199254740992)), (1630477/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-29287786743/2147483648)), (1/2147483648), by norm_num⟩, -2, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-165884901/67108864), (-59254086639/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((508629474278647/18014398509481984), (-1433315482360813/18014398509481984)), (425605/4503599627370496), by norm_num⟩
  | 1 => ⟨((-25579220161/274877906944), (18020530729/68719476736)), (87/274877906944), by norm_num⟩
  | 2 => ⟨((21076234203/137438953472), (-29696364761/68719476736)), (73/137438953472), by norm_num⟩
  | 3 => ⟨((-11577304947/68719476736), (65249582511/137438953472)), (41/68719476736), by norm_num⟩
  | 4 => ⟨((19078454227/137438953472), (-53762994883/137438953472)), (69/137438953472), by norm_num⟩
  | 5 => ⟨((-25151789115/274877906944), (70877624225/274877906944)), (93/274877906944), by norm_num⟩
  | 6 => ⟨((6908016151/137438953472), (-38933514483/274877906944)), (13/68719476736), by norm_num⟩
  | 7 => ⟨((-26020222059/1099511627776), (18331216051/274877906944)), (25/274877906944), by norm_num⟩
  | 8 => ⟨((21439601781/2199023255552), (-15104174415/549755813888)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((-15702539987/4398046511104), (44249684327/4398046511104)), (125/8796093022208), by norm_num⟩
  | 10 => ⟨((2587650509/2199023255552), (-29167948183/8796093022208)), (21/4398046511104), by norm_num⟩
  | 11 => ⟨((-24810106019/70368744177664), (8739345357/8796093022208)), (103/70368744177664), by norm_num⟩
  | 12 => ⟨((6814171839/70368744177664), (-76809217633/281474976710656)), (115/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-1601947270785/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((13891835621115/4951760157141521099596496896), (-1894578365201/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472262848508179/9903520314283042199192993792), (-2130942978347/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944391706245707/1237940039285380274899124224), (-1131778024583/1237940039285380274899124224)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770449772986461/154742504910672534362390528), (-2262914090131/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548858936046977/9671406556917033397649408), (-1035546931/4722366482869645213696)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314545280846415/151115727451828646838272), (-1855018521827/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471701245176311/18889465931478580854784), (-3013127703853/75557863725914323419136)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162099918527219/590295810358705651712), (-1129364311697/2361183241434822606848)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6329807747877/2305843009213693952), (-3103937540593/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822203423656651/73786976294838206464), (-1938601151929/36893488147419103232)), (743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455306857751131/2305843009213693952), (-2179058060369/4611686018427387904)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398119180267393/288230376151711744), (-4353450041677/1152921504606846976)), (1673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193261147757637/144115188075855872), (-1902012821283/72057594037927936)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489659743998929/36028797018963968), (-2847783822903/18014398509481984)), (275/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486788699947611/9007199254740992), (-7101170383607/9007199254740992)), (2753/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223019401564747/4503599627370496), (-7073806016553/2251799813685248)), (5515/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208733949177667/2251799813685248), (-10542540434045/1125899906842624)), (8299/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083043262768309/1125899906842624), (-41627712146413/2251799813685248)), (16705/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1083043262768309/1125899906842624), (-41627712146413/2251799813685248)), (63724526412200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082866310401223/2251799813685248), (-40043180491117/1125899906842624)), (32757/2251799813685248), by norm_num⟩
  | 2 => ⟨((961879074565581/1125899906842624), (-74078158368585/1125899906842624)), (31465/1125899906842624), by norm_num⟩
  | 3 => ⟨((1633757627921031/2251799813685248), (-31643234884403/281474976710656)), (115807/2251799813685248), by norm_num⟩
  | 4 => ⟨((578444214904247/1125899906842624), (-367331952336445/2251799813685248)), (194083/2251799813685248), by norm_num⟩
  | 5 => ⟨((133610686494363/562949953421312), (-754884307164969/4503599627370496)), (131373/1125899906842624), by norm_num⟩
  | 6 => ⟨((508629474278647/18014398509481984), (-1433315482360813/18014398509481984)), (425605/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-59254086639/4294967296)), (1/2147483648), by norm_num⟩, -2, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile009Terms3
