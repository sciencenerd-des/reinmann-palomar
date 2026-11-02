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
namespace Reinmann.XiRectangle.Tile007Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

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
  | 0 => ⟨((-4978472343/2147483648), (-21936393761/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-623998599993675/9007199254740992), (629958998107093/9007199254740992)), (632643/9007199254740992), by norm_num⟩
  | 1 => ⟨((14715623195/68719476736), (-59424743867/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((-45486616023/137438953472), (22960550759/68719476736)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((11716755099/34359738368), (-5914336429/17179869184)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((-36216987427/137438953472), (36562929971/137438953472)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((11194824567/68719476736), (-2825439219/17179869184)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((-23069118663/274877906944), (11644736767/137438953472)), (59/549755813888), by norm_num⟩
  | 7 => ⟨((40747214371/1099511627776), (-41136429377/1099511627776)), (27/549755813888), by norm_num⟩
  | 8 => ⟨((-62975684739/4398046511104), (7947153099/549755813888)), (43/2199023255552), by norm_num⟩
  | 9 => ⟨((43257892235/8796093022208), (-43671089089/8796093022208)), (61/8796093022208), by norm_num⟩
  | 10 => ⟨((-53484792537/35184372088832), (3374729759/2199023255552)), (39/17592186044416), by norm_num⟩
  | 11 => ⟨((7514716561/17592186044416), (-60691973549/140737488355328)), (45/70368744177664), by norm_num⟩
  | 12 => ⟨((-7742769305/70368744177664), (62533822273/562949953421312)), (95/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (3063014776661/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778386503658329/633825300114114700748351602688), (1811730520193/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944655770236891/19807040628566084398385987584), (4075557803879/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889059373894251/2475880078570760549798248448), (4329254698659/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770725235082039/154742504910672534362390528), (4328101284789/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549116651588949/9671406556917033397649408), (253523108733/604462909807314587353088)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629203047348123/302231454903657293676544), (443512328823/75557863725914323419136)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117948097909175/4722366482869645213696), (2881682144685/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297071919943109/4722366482869645213696), (4320514916445/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810402080582703/295147905179352825856), (5937445809023/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822668035843125/73786976294838206464), (7416916212571/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56929600714667/288230376151711744), (4168654604127/4611686018427387904)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398248224593777/288230376151711744), (4164456393205/576460752303423488)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298427186360763/36028797018963968), (7278360264931/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((745161523942937/18014398509481984), (10898682430147/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487603717707127/9007199254740992), (6795197037275/4503599627370496)), (693/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224607300425099/4503599627370496), (27082081185061/4503599627370496)), (2783/4503599627370496), by norm_num⟩
  | 1 => ⟨((34547049258159/35184372088832), (40376949134555/2251799813685248)), (2099/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085113258193451/1125899906842624), (39886388243579/1125899906842624)), (4249/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1085113258193451/1125899906842624), (39886388243579/1125899906842624)), (16208652976607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2088782230096501/2251799813685248), (153765884308253/2251799813685248)), (16983/2251799813685248), by norm_num⟩
  | 2 => ⟨((1927066176672293/2251799813685248), (71317051539433/562949953421312)), (33827/2251799813685248), by norm_num⟩
  | 3 => ⟨((806511768443023/1125899906842624), (488258954482163/2251799813685248)), (66469/2251799813685248), by norm_num⟩
  | 4 => ⟨((1049581809871627/2251799813685248), (699505507451105/2251799813685248)), (124053/2251799813685248), by norm_num⟩
  | 5 => ⟨((135961024807279/1125899906842624), (163022541360847/562949953421312)), (192717/2251799813685248), by norm_num⟩
  | 6 => ⟨((-623998599993675/9007199254740992), (629958998107093/9007199254740992)), (632643/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-21936393761/2147483648)), (1/4294967296), by norm_num⟩, -2, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-20200267671/8589934592), (-89007429427/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-507853327919221/9007199254740992), (691081507693091/9007199254740992)), (304225/4503599627370496), by norm_num⟩
  | 1 => ⟨((48595311653/274877906944), (-33063996431/137438953472)), (15/68719476736), by norm_num⟩
  | 2 => ⟨((-9523144913/34359738368), (51835984783/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((311039227/1073741824), (-846517867/2147483648)), (53/137438953472), by norm_num⟩
  | 4 => ⟨((-15604187155/68719476736), (42468030011/137438953472)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((39141470855/274877906944), (-53263304985/274877906944)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((-10227321289/137438953472), (27834464117/274877906944)), (15/137438953472), by norm_num⟩
  | 7 => ⟨((18324403855/549755813888), (-12467828749/274877906944)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((-28728031149/2199023255552), (610825077/34359738368)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((40034033557/8796093022208), (-27238947497/4398046511104)), (1/137438953472), by norm_num⟩
  | 10 => ⟨((-50210592263/35184372088832), (17081512465/8796093022208)), (41/17592186044416), by norm_num⟩
  | 11 => ⟨((57249098771/140737488355328), (-77903976049/140737488355328)), (3/4398046511104), by norm_num⟩
  | 12 => ⟨((-29917369677/281474976710656), (40711244383/281474976710656)), (13/70368744177664), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633433/10141204801825835211973625643008), (1435831093999/5070602400912917605986812821504)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889167991436425/316912650057057350374175801344), (1698454638835/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944627382161341/19807040628566084398385987584), (1910365357161/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888999126402331/2475880078570760549798248448), (4058551469305/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442666268586421/38685626227668133590597632), (1014363739213/38685626227668133590597632)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549060343022397/9671406556917033397649408), (3802699275405/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629178458381787/302231454903657293676544), (51971835221/9444732965739290427392)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887089824895471/75557863725914323419136), (2701444151101/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648506132251897/2361183241434822606848), (4050257197307/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620722379743407/590295810358705651712), (5566002807227/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822566175853635/73786976294838206464), (3476427291979/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821633134028437/9223372036854775808), (122118326975/144115188075855872)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398219859516177/288230376151711744), (243987281621/36028797018963968)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((74600635834703/9007199254740992), (6822674298417/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490176597593031/36028797018963968), (2554022952761/9007199254740992)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487423110629973/9007199254740992), (12738799345511/9007199254740992)), (1385/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224253421973753/4503599627370496), (25383828151815/4503599627370496)), (2779/4503599627370496), by norm_num⟩
  | 1 => ⟨((552624640879199/562949953421312), (18920965289707/1125899906842624)), (131/70368744177664), by norm_num⟩
  | 0 => ⟨((542318397862095/562949953421312), (37376150147787/1125899906842624)), (8479/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((542318397862095/562949953421312), (37376150147787/1125899906842624)), (32344826705168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043645172095403/1125899906842624), (144025405762711/2251799813685248)), (4225/562949953421312), by norm_num⟩
  | 2 => ⟨((1925587539840317/2251799813685248), (133503358930773/1125899906842624)), (16747/1125899906842624), by norm_num⟩
  | 3 => ⟨((1614972505150675/2251799813685248), (228326161963045/1125899906842624)), (16307/562949953421312), by norm_num⟩
  | 4 => ⟨((532819310327237/1125899906842624), (655014662557281/2251799813685248)), (120019/2251799813685248), by norm_num⟩
  | 5 => ⟨((627534878874539/4503599627370496), (1239912921697333/4503599627370496)), (366839/4503599627370496), by norm_num⟩
  | 6 => ⟨((-507853327919221/9007199254740992), (691081507693091/9007199254740992)), (304225/4503599627370496), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20200267671/8589934592), (-89007429427/8589934592)), (1/4294967296), by norm_num⟩, -2, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-20474455899/8589934592), (-90215571307/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-786414390199773/18014398509481984), (182929236498043/2251799813685248)), (1163473/18014398509481984), by norm_num⟩
  | 1 => ⟨((4766974001/34359738368), (-17741667503/68719476736)), (59/274877906944), by norm_num⟩
  | 2 => ⟨((-15149699983/68719476736), (56383974365/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((4012213505/17179869184), (-29865217617/68719476736)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((-25502060995/137438953472), (47456634621/137438953472)), (45/137438953472), by norm_num⟩
  | 5 => ⟨((32418769051/274877906944), (-60327895773/274877906944)), (59/274877906944), by norm_num⟩
  | 6 => ⟨((-17171432193/274877906944), (63908433413/549755813888)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((31183849059/1099511627776), (-58029840457/1099511627776)), (15/274877906944), by norm_num⟩
  | 8 => ⟨((-24775987737/2199023255552), (46105489185/2199023255552)), (49/2199023255552), by norm_num⟩
  | 9 => ⟨((17497649495/4398046511104), (-65122545113/8796093022208)), (71/8796093022208), by norm_num⟩
  | 10 => ⟨((-173776475/137438953472), (82785181575/35184372088832)), (23/8796093022208), by norm_num⟩
  | 11 => ⟨((25705704355/70368744177664), (-47835593345/70368744177664)), (55/70368744177664), by norm_num⟩
  | 12 => ⟨((-27231370729/281474976710656), (25337348443/140737488355328)), (15/70368744177664), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646257/10141204801825835211973625643008), (168028423481/633825300114114700748351602688)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778287563775447/633825300114114700748351602688), (3180024342041/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944600173581739/19807040628566084398385987584), (3576777930647/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236117672307161/309485009821345068724781056), (3799401714633/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885303702708381/77371252455336267181195264), (3798361561103/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549006362306211/9671406556917033397649408), (1779929551913/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629154883742711/302231454903657293676544), (778443049321/151115727451828646838272)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887013364415121/75557863725914323419136), (632226196637/9444732965739290427392)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296955056483847/4722366482869645213696), (3791546437949/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810321970835261/295147905179352825856), (1302608813781/147573952589676412928)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822468462303519/73786976294838206464), (6508634800103/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821523664956289/9223372036854775808), (3658077633353/4611686018427387904)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592770541381099/1152921504606846976), (1827146863085/288230376151711744)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193515531387719/144115188075855872), (6386508187671/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490035916640761/36028797018963968), (9562770501097/36028797018963968)), (1105/36028797018963968), by norm_num⟩
  | 3 => ⟨((743624747804403/4503599627370496), (11923772228335/9007199254740992)), (173/1125899906842624), by norm_num⟩
  | 2 => ⟨((2223912871176949/4503599627370496), (5939662626409/1125899906842624)), (347/562949953421312), by norm_num⟩
  | 1 => ⟨((1105002166631871/1125899906842624), (17708182952757/1125899906842624)), (2093/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084175451821461/1125899906842624), (69950037921277/2251799813685248)), (8461/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1084175451821461/1125899906842624), (69950037921277/2251799813685248)), (32276162154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085821574803809/2251799813685248), (134715552434679/2251799813685248)), (16821/2251799813685248), by norm_num⟩
  | 2 => ⟨((962008997318189/1125899906842624), (124785784252287/1125899906842624)), (4147/281474976710656), by norm_num⟩
  | 3 => ⟨((1616289003027463/2251799813685248), (426485681217437/2251799813685248)), (64049/2251799813685248), by norm_num⟩
  | 4 => ⟨((539679435590303/1125899906842624), (4783146909801/17592186044416)), (7263/140737488355328), by norm_num⟩
  | 5 => ⟨((87726972485261/562949953421312), (73366835085463/281474976710656)), (349193/4503599627370496), by norm_num⟩
  | 6 => ⟨((-786414390199773/18014398509481984), (182929236498043/2251799813685248)), (1163473/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20474455899/8589934592), (-90215571307/8589934592)), (1/4294967296), by norm_num⟩, -2, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-20737449597/8589934592), (-91374387285/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-564882322362993/18014398509481984), (1508991845859907/18014398509481984)), (1106859/18014398509481984), by norm_num⟩
  | 1 => ⟨((27744843313/274877906944), (-37057932835/137438953472)), (7/34359738368), by norm_num⟩
  | 2 => ⟨((-22326801351/137438953472), (59642442061/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((23955733705/137438953472), (-63993871629/137438953472)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((-19277633023/137438953472), (25748540791/68719476736)), (11/34359738368), by norm_num⟩
  | 5 => ⟨((24820922759/274877906944), (-33152542191/137438953472)), (59/274877906944), by norm_num⟩
  | 6 => ⟨((-6657955685/137438953472), (71142611061/549755813888)), (65/549755813888), by norm_num⟩
  | 7 => ⟨((24492722969/1099511627776), (-65428351675/1099511627776)), (31/549755813888), by norm_num⟩
  | 8 => ⟨((-19709758463/2199023255552), (52651434867/2199023255552)), (13/549755813888), by norm_num⟩
  | 9 => ⟨((3524625835/1099511627776), (-75323747039/8796093022208)), (77/8796093022208), by norm_num⟩
  | 10 => ⟨((-36305065255/35184372088832), (96983115353/35184372088832)), (51/17592186044416), by norm_num⟩
  | 11 => ⟨((21247544885/70368744177664), (-28379691403/35184372088832)), (31/35184372088832), by norm_num⟩
  | 12 => ⟨((-22797736189/281474976710656), (60900468383/281474976710656)), (17/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241879/10141204801825835211973625643008), (1256363669117/5070602400912917605986812821504)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778241076676925/633825300114114700748351602688), (1486007913753/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889148098665061/39614081257132168796771975168), (3342810294709/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888885928539623/2475880078570760549798248448), (887715169471/618970019642690137449562112)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442638006892899/38685626227668133590597632), (443734539043/19342813113834066795298816)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548954522107219/9671406556917033397649408), (3326963459365/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258264483790213/604462909807314587353088), (2910047786387/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886939921698041/75557863725914323419136), (2363434277667/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648450049856227/2361183241434822606848), (885859483615/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101285536216323/36893488147419103232), (4869444116753/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822374564207463/73786976294838206464), (1520658242381/18446744073709551616)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455354611981697/2305843009213693952), (3418614613799/4611686018427387904)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796332923191545/576460752303423488), (6830068965271/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193424509342311/144115188075855872), (5968263043019/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((372475138178355/9007199254740992), (4468159966191/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((371770582480851/2251799813685248), (5571157104453/4503599627370496)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((277948078805283/562949953421312), (22200550720915/4503599627370496)), (2773/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209527104376599/2251799813685248), (8272814756633/562949953421312)), (1045/562949953421312), by norm_num⟩
  | 0 => ⟨((2167456410456585/2251799813685248), (65348006610217/2251799813685248)), (8443/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2167456410456585/2251799813685248), (65348006610217/2251799813685248)), (32207497603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1042187875835191/1125899906842624), (125800663964059/2251799813685248)), (2093/281474976710656), by norm_num⟩
  | 2 => ⟨((480592950668787/562949953421312), (116447231195735/1125899906842624)), (16435/1125899906842624), by norm_num⟩
  | 3 => ⟨((101065642441275/140737488355328), (99411534004845/562949953421312)), (62923/2251799813685248), by norm_num⟩
  | 4 => ⟨((545503454744839/1125899906842624), (571110976481595/2251799813685248)), (28149/562949953421312), by norm_num⟩
  | 5 => ⟨((767500133755001/4503599627370496), (553411557848109/2251799813685248)), (332443/4503599627370496), by norm_num⟩
  | 6 => ⟨((-564882322362993/18014398509481984), (1508991845859907/18014398509481984)), (1106859/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/8589934592), (-91374387285/8589934592)), (1/4294967296), by norm_num⟩, -2, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-20990127117/8589934592), (-92487747609/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-44315515995359/2251799813685248), (1523854591720653/18014398509481984)), (1048675/18014398509481984), by norm_num⟩
  | 1 => ⟨((1101564249/17179869184), (-9469729175/34359738368)), (27/137438953472), by norm_num⟩
  | 2 => ⟨((-1794501333/17179869184), (30853291841/68719476736)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((3897772387/34359738368), (-16753833889/34359738368)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-198426855/2147483648), (109171216385/274877906944)), (85/274877906944), by norm_num⟩
  | 5 => ⟨((16550242543/274877906944), (-71138072431/274877906944)), (57/274877906944), by norm_num⟩
  | 6 => ⟨((-8987047989/274877906944), (19314558959/137438953472)), (1/8589934592), by norm_num⟩
  | 7 => ⟨((8365905697/549755813888), (-4494906977/68719476736)), (31/549755813888), by norm_num⟩
  | 8 => ⟨((-6814232097/1099511627776), (29289681721/1099511627776)), (13/549755813888), by norm_num⟩
  | 9 => ⟨((19734600893/8796093022208), (-42412715829/4398046511104)), (77/8796093022208), by norm_num⟩
  | 10 => ⟨((-25718893939/35184372088832), (13818472261/4398046511104)), (103/35184372088832), by norm_num⟩
  | 11 => ⟨((3808847241/17592186044416), (-65486424195/70368744177664)), (63/70368744177664), by norm_num⟩
  | 12 => ⟨((-2068265335/35184372088832), (35560181993/140737488355328)), (35/140737488355328), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (2343892975899/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444549092928175/158456325028528675187087900672), (1386093219877/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889097850721685/39614081257132168796771975168), (1559021697207/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118052037415613/154742504910672534362390528), (207005931437/154742504910672534362390528)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885249381750067/77371252455336267181195264), (1655582867459/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548904656929549/9671406556917033397649408), (3103230938383/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258220921601075/604462909807314587353088), (1357170236867/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((117929328999451/4722366482869645213696), (137779816365/2361183241434822606848)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296847220824647/4722366482869645213696), (3305098313557/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620496056687007/590295810358705651712), (4541883458827/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822284188950741/73786976294838206464), (709177076597/9223372036854775808)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821317157760983/9223372036854775808), (797147898865/1152921504606846976)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592565032902477/1152921504606846976), (1592606461357/288230376151711744)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193336832702013/144115188075855872), (2783264270029/72057594037927936)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((744885052639213/18014398509481984), (4167312246323/18014398509481984)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((743460566271933/4503599627370496), (10391780639445/9007199254740992)), (691/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223267796459203/4503599627370496), (10352119726449/2251799813685248)), (1385/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209065668205089/2251799813685248), (7714669253545/562949953421312)), (4175/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166588276470935/2251799813685248), (60930352077779/2251799813685248)), (4213/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2166588276470935/2251799813685248), (60930352077779/2251799813685248)), (16071323875045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082952589049547/2251799813685248), (58624654683187/1125899906842624)), (16671/2251799813685248), by norm_num⟩
  | 2 => ⟨((1920661002544097/2251799813685248), (108457577367531/1125899906842624)), (32579/2251799813685248), by norm_num⟩
  | 3 => ⟨((1617322499187761/2251799813685248), (92508329565633/562949953421312)), (30927/1125899906842624), by norm_num⟩
  | 4 => ⟨((1100811623968385/2251799813685248), (531542109061343/2251799813685248)), (109181/2251799813685248), by norm_num⟩
  | 5 => ⟨((825339101736351/4503599627370496), (259848912291093/1125899906842624)), (316587/4503599627370496), by norm_num⟩
  | 6 => ⟨((-44315515995359/2251799813685248), (1523854591720653/18014398509481984)), (1048675/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-92487747609/8589934592)), (1/4294967296), by norm_num⟩, -2, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-21233267329/8589934592), (-93559084167/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-78840313980169/9007199254740992), (1512690990621573/18014398509481984)), (990061/18014398509481984), by norm_num⟩
  | 1 => ⟨((991229299/34359738368), (-9509244411/34359738368)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((-6533860133/137438953472), (15670459149/34359738368)), (45/137438953472), by norm_num⟩
  | 3 => ⟨((7178179035/137438953472), (-68863035961/137438953472)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-11829053547/274877906944), (113480666313/274877906944)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((3898663077/137438953472), (-74802752723/274877906944)), (29/137438953472), by norm_num⟩
  | 6 => ⟨((-2141559583/137438953472), (10272402921/68719476736)), (65/549755813888), by norm_num⟩
  | 7 => ⟨((4033274871/549755813888), (-77385518285/1099511627776)), (63/1099511627776), by norm_num⟩
  | 8 => ⟨((-6646508005/2199023255552), (63762511015/2199023255552)), (53/2199023255552), by norm_num⟩
  | 9 => ⟨((2433978457/2199023255552), (-93400370877/8796093022208)), (79/8796093022208), by norm_num⟩
  | 10 => ⟨((-12835193487/35184372088832), (61566477127/17592186044416)), (107/35184372088832), by norm_num⟩
  | 11 => ⟨((7691400705/70368744177664), (-18446642275/17592186044416)), (33/35184372088832), by norm_num⟩
  | 12 => ⟨((-2112466833/70368744177664), (1266606743/4398046511104)), (37/140737488355328), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480279/10141204801825835211973625643008), (272678907953/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778153315863969/633825300114114700748351602688), (1289958962011/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889049454114659/39614081257132168796771975168), (2901781733189/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((118048826923553/154742504910672534362390528), (385295676611/309485009821345068724781056)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885223727895991/77371252455336267181195264), (3081490839077/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548856619838863/9671406556917033397649408), (1443984362513/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629089476494049/302231454903657293676544), (2526044033059/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886801184603547/75557863725914323419136), (4103081138427/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296796265847165/4722366482869645213696), (3075788702397/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810213081665985/295147905179352825856), (4226737304103/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822197076557149/73786976294838206464), (5279715721637/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821219505480445/9223372036854775808), (1483647088357/2305843009213693952)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592467816324771/1152921504606846976), (5928229244193/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193252257332283/144115188075855872), (2590027199195/72057594037927936)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((744822108962229/18014398509481984), (7755808718453/36028797018963968)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486765475053741/9007199254740992), (4834913594703/4503599627370496)), (1381/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111480781772301/2251799813685248), (19265028330277/4503599627370496)), (173/281474976710656), by norm_num⟩
  | 1 => ⟨((1104309471796953/1125899906842624), (28711589057431/2251799813685248)), (4169/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165744845798473/2251799813685248), (56683025767131/2251799813685248)), (4205/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2165744845798473/2251799813685248), (56683025767131/2251799813685248)), (16040806296920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1040775859205153/1125899906842624), (109033645134305/2251799813685248)), (8301/1125899906842624), by norm_num⟩
  | 2 => ⟨((479723951745739/562949953421312), (201580238185041/2251799813685248)), (16151/1125899906842624), by norm_num⟩
  | 3 => ⟨((1617162637415085/2251799813685248), (343557603542789/2251799813685248)), (30419/1125899906842624), by norm_num⟩
  | 4 => ⟨((1108972100327343/2251799813685248), (493461733918521/2251799813685248)), (26487/562949953421312), by norm_num⟩
  | 5 => ⟨((876023375140425/4503599627370496), (243021289978349/1125899906842624)), (301581/4503599627370496), by norm_num⟩
  | 6 => ⟨((-78840313980169/9007199254740992), (1512690990621573/18014398509481984)), (990061/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21233267329/8589934592), (-93559084167/8589934592)), (1/4294967296), by norm_num⟩, -2, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile007Terms3
