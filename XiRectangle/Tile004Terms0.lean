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
namespace Reinmann.XiRectangle.Tile004Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/640))
  have he : value ((3/4), (1269/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-142898134647/274877906944), (-188893471737/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((261298458657533/2251799813685248), (-328295958958985/562949953421312)), (12201/1125899906842624), by norm_num⟩
  | 1 => ⟨((-2763645781/34359738368), (444448082699/1099511627776)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((61299624997/2199023255552), (-77016983857/549755813888)), (5/1099511627776), by norm_num⟩
  | 3 => ⟨((-56652882981/8796093022208), (284715227817/8796093022208)), (11/8796093022208), by norm_num⟩
  | 4 => ⟨((39268786109/35184372088832), (-12334347339/2199023255552)), (17/70368744177664), by norm_num⟩
  | 5 => ⟨((-43550477401/281474976710656), (218867662901/281474976710656)), (11/281474976710656), by norm_num⟩
  | 6 => ⟨((80498374993/4503599627370496), (-101138335637/1125899906842624)), (23/4503599627370496), by norm_num⟩
  | 7 => ⟨((-63768253333/36028797018963968), (320474295741/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 8 => ⟨((44200785007/288230376151711744), (-222135854535/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 9 => ⟨((-54466932455/4611686018427387904), (273729495595/4611686018427387904)), (5/1152921504606846976), by norm_num⟩
  | 10 => ⟨((7550720133/9223372036854775808), (-303575724973/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-60901938867/1180591620717411303424), (306069320511/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 12 => ⟨((56285342955/18889465931478580854784), (-8839628607/590295810358705651712)), (13/9444732965739290427392), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395824647727665/2535301200456458802993406410752), (-27973196325/158456325028528675187087900672)), (11/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781166532184371/633825300114114700748351602688), (-1062072575561/316912650057057350374175801344)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946219463687773/19807040628566084398385987584), (-2389547843621/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236547760102285/309485009821345068724781056), (-2538759446775/2475880078570760549798248448)), (7/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774047782278373/154742504910672534362390528), (-634651849481/38685626227668133590597632)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552231369611227/9671406556917033397649408), (-148736429169/604462909807314587353088)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261131302694795/604462909807314587353088), (-2082148420461/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891597709656521/75557863725914323419136), (-3383188165451/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300392746744131/4722366482869645213696), (-2537125943063/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406342460243671/147573952589676412928), (-3488117176741/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828374447980995/73786976294838206464), (-4359499845909/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1828165987697925/9223372036854775808), (-2451774001005/4611686018427387904)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399852618040629/288230376151711744), (-2451218011831/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599661387856197/72057594037927936), (-4288380102051/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((749370691277697/18014398509481984), (-3215033104865/18014398509481984)), (9/9007199254740992), by norm_num⟩
  | 3 => ⟨((1498121853786557/9007199254740992), (-502074898551/562949953421312)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((280703634055695/562949953421312), (-2006654210015/562949953421312)), (11/562949953421312), by norm_num⟩
  | 1 => ⟨((560626756443255/562949953421312), (-12023454108709/1125899906842624)), (33/562949953421312), by norm_num⟩
  | 0 => ⟨((1116533967952505/1125899906842624), (-23980920123491/1125899906842624)), (33/281474976710656), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116533967952505/1125899906842624), (-23980920123491/1125899906842624)), (125886083507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1106735163124913/1125899906842624), (-47562863693133/1125899906842624)), (67/281474976710656), by norm_num⟩
  | 2 => ⟨((1085887375835203/1125899906842624), (-93506524670963/1125899906842624)), (551/1125899906842624), by norm_num⟩
  | 3 => ⟨((1039531059314511/1125899906842624), (-90183464872259/562949953421312)), (1155/1125899906842624), by norm_num⟩
  | 4 => ⟨((930893223779781/1125899906842624), (-333061623689845/1125899906842624)), (2503/1125899906842624), by norm_num⟩
  | 5 => ⟨((167784041972085/281474976710656), (-550750216266437/1125899906842624)), (5621/1125899906842624), by norm_num⟩
  | 6 => ⟨((261298458657533/2251799813685248), (-328295958958985/562949953421312)), (12201/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/274877906944), (-188893471737/137438953472)), (1/137438953472), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-28311023105/34359738368), (-149694534667/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-563915507819633/2251799813685248), (-811071628818223/2251799813685248)), (43025/2251799813685248), by norm_num⟩
  | 1 => ⟨((151251100259/549755813888), (27192787427/68719476736)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((-166166317419/1099511627776), (-238994643443/1099511627776)), (9/549755813888), by norm_num⟩
  | 3 => ⟨((60850786093/1099511627776), (21880204351/274877906944)), (15/2199023255552), by norm_num⟩
  | 4 => ⟨((-66851421377/4398046511104), (-192302891029/8796093022208)), (19/8796093022208), by norm_num⟩
  | 5 => ⟨((918047413/274877906944), (169013055385/35184372088832)), (19/35184372088832), by norm_num⟩
  | 6 => ⟨((-86065337131/140737488355328), (-61893273197/70368744177664)), (15/140737488355328), by norm_num⟩
  | 7 => ⟨((216119856001/2251799813685248), (310842105235/2251799813685248)), (5/281474976710656), by norm_num⟩
  | 8 => ⟨((-59357982407/4503599627370496), (-170747478323/9007199254740992)), (3/1125899906842624), by norm_num⟩
  | 9 => ⟨((115931393605/72057594037927936), (41685617321/18014398509481984)), (25/72057594037927936), by norm_num⟩
  | 10 => ⟨((-203781845851/1152921504606846976), (-293096521277/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 11 => ⟨((20352476369/1152921504606846976), (234181410939/9223372036854775808)), (39/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-59625281717/36893488147419103232), (-85758191945/36893488147419103232)), (31/73786976294838206464), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197862808528795/1267650600228229401496703205376), (-1418766950413/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1780693022957123/633825300114114700748351602688), (-3365005077133/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891906045289517/39614081257132168796771975168), (-59145905947/618970019642690137449562112)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29559619747205/38685626227668133590597632), (-4021581808917/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886740553427741/77371252455336267181195264), (-2010599724261/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775849918460737/4835703278458516698824704), (-3769468157919/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260665937219023/604462909807314587353088), (-1648939118799/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890840976541131/75557863725914323419136), (-1339572493667/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649912373599093/2361183241434822606848), (-251128151847/295147905179352825856)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812294055626911/295147905179352825856), (-1380933770487/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827396191069231/73786976294838206464), (-3451520969927/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1827063944606631/9223372036854775808), (-242615135195/288230376151711744)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598306550835035/1152921504606846976), (-242527679097/36028797018963968)), (27/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198354734073359/144115188075855872), (-6787624845173/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((187160638186039/4503599627370496), (-10175132563033/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496294146169707/9007199254740992), (-12707872673657/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((70060988453205/140737488355328), (-12691288599289/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((139808499757953/140737488355328), (-18995404651317/1125899906842624)), (33/281474976710656), by norm_num⟩
  | 0 => ⟨((555426902589109/562949953421312), (-18912145131949/562949953421312)), (133/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555426902589109/562949953421312), (-18912145131949/562949953421312)), (507356883811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1094738077562737/1125899906842624), (-74637641432347/1125899906842624)), (17/35184372088832), by norm_num⟩
  | 2 => ⟨((529745439047235/562949953421312), (-145143751409663/1125899906842624)), (1131/1125899906842624), by norm_num⟩
  | 3 => ⟨((244571965389211/281474976710656), (-136582727910683/562949953421312)), (2421/1125899906842624), by norm_num⟩
  | 4 => ⟨((783753305646833/1125899906842624), (-474703742317723/1125899906842624)), (5383/1125899906842624), by norm_num⟩
  | 5 => ⟨((690870651606245/2251799813685248), (-1321789352617621/2251799813685248)), (6017/562949953421312), by norm_num⟩
  | 6 => ⟨((-563915507819633/2251799813685248), (-811071628818223/2251799813685248)), (43025/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/34359738368), (-149694534667/68719476736)), (1/68719476736), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-142898134647/137438953472), (-188893471737/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-735489403693275/2251799813685248), (-609526495477151/4503599627370496)), (34125/2251799813685248), by norm_num⟩
  | 1 => ⟨((62231739075/137438953472), (103147356401/549755813888)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((-172543017925/549755813888), (-142992598543/1099511627776)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((318927217067/2199023255552), (33038305507/549755813888)), (11/1099511627776), by norm_num⟩
  | 4 => ⟨((-110531750657/2199023255552), (-91601633251/4398046511104)), (17/4398046511104), by norm_num⟩
  | 5 => ⟨((245167268257/17592186044416), (25397365529/4398046511104)), (21/17592186044416), by norm_num⟩
  | 6 => ⟨((-226582667677/70368744177664), (-93888598987/70368744177664)), (21/70368744177664), by norm_num⟩
  | 7 => ⟨((358983170889/562949953421312), (148751126113/562949953421312)), (9/140737488355328), by norm_num⟩
  | 8 => ⟨((-124414086385/1125899906842624), (-51553211835/1125899906842624)), (27/2251799813685248), by norm_num⟩
  | 9 => ⟨((306621415821/18014398509481984), (31763523051/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 10 => ⟨((-340054031801/144115188075855872), (-8806718579/9007199254740992)), (21/72057594037927936), by norm_num⟩
  | 11 => ⟨((85711815775/288230376151711744), (71032461417/576460752303423488)), (45/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-316858151707/9223372036854775808), (-131295867625/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715939/10141204801825835211973625643008), (-3580569129599/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890178104109641/316912650057057350374175801344), (-265290922693/39614081257132168796771975168)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891526951233395/39614081257132168796771975168), (-4774767439743/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891412650760651/2475880078570760549798248448), (-2536324501693/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886538920034405/77371252455336267181195264), (-158501241487/4835703278458516698824704)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((24239398513361/151115727451828646838272), (-4754389754603/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260334627353429/604462909807314587353088), (-4159443394069/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236287761671119/9444732965739290427392), (-1689470216775/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299420143569567/4722366482869645213696), (-5067347512453/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624031064817297/590295810358705651712), (-6965874630119/590295810358705651712)), (39/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913349404686789/36893488147419103232), (-8704749939075/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((228284739448651/1152921504606846976), (-2447319031205/2305843009213693952)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798759340522037/576460752303423488), (-2446203532595/288230376151711744)), (27/576460752303423488), by norm_num⟩
  | 5 => ⟨((598831640279283/72057594037927936), (-8556689123895/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((187030474859825/4503599627370496), (-12824978488161/36028797018963968)), (71/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494985311076377/9007199254740992), (-16013606965755/9007199254740992)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((559828107970263/1125899906842624), (-15987143815599/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((279115455863139/281474976710656), (-23914422316253/1125899906842624)), (133/1125899906842624), by norm_num⟩
  | 0 => ⟨((1106735163124913/1125899906842624), (-47562863693133/1125899906842624)), (67/281474976710656), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1106735163124913/1125899906842624), (-47562863693133/1125899906842624)), (255585790538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1085887375835203/1125899906842624), (-93506524670963/1125899906842624)), (551/1125899906842624), by norm_num⟩
  | 2 => ⟨((1039531059314511/1125899906842624), (-90183464872259/562949953421312)), (1155/1125899906842624), by norm_num⟩
  | 3 => ⟨((930893223779781/1125899906842624), (-333061623689845/1125899906842624)), (2503/1125899906842624), by norm_num⟩
  | 4 => ⟨((167784041972085/281474976710656), (-550750216266437/1125899906842624)), (5621/1125899906842624), by norm_num⟩
  | 5 => ⟨((261298458657533/2251799813685248), (-328295958958985/562949953421312)), (12201/1125899906842624), by norm_num⟩
  | 6 => ⟨((-735489403693275/2251799813685248), (-609526495477151/4503599627370496)), (34125/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/137438953472), (-188893471737/68719476736)), (1/68719476736), by norm_num⟩, 0, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-41474899193/34359738368), (-219298529483/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-168154074955181/562949953421312), (16701642361233/1125899906842624)), (106495/4503599627370496), by norm_num⟩
  | 1 => ⟨((132145284845/274877906944), (-13125125203/549755813888)), (23/549755813888), by norm_num⟩
  | 2 => ⟨((-212679631379/549755813888), (21124074107/1099511627776)), (39/1099511627776), by norm_num⟩
  | 3 => ⟨((14262277581/68719476736), (-22665257155/2199023255552)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((-45908500513/549755813888), (569973815/137438953472)), (37/4398046511104), by norm_num⟩
  | 5 => ⟨((472876039863/17592186044416), (-11741919577/8796093022208)), (49/17592186044416), by norm_num⟩
  | 6 => ⟨((-507376417625/70368744177664), (1574824211/4398046511104)), (55/70368744177664), by norm_num⟩
  | 7 => ⟨((233311669257/140737488355328), (-5793329807/70368744177664)), (53/281474976710656), by norm_num⟩
  | 8 => ⟨((-375500645915/1125899906842624), (18648009261/1125899906842624)), (45/1125899906842624), by norm_num⟩
  | 9 => ⟨((33574720871/562949953421312), (-13339028043/4503599627370496)), (17/2251799813685248), by norm_num⟩
  | 10 => ⟨((-345833143483/36028797018963968), (8587334979/18014398509481984)), (23/18014398509481984), by norm_num⟩
  | 11 => ⟨((101199449545/72057594037927936), (-20102956337/288230376151711744)), (7/36028797018963968), by norm_num⟩
  | 12 => ⟨((-217165641087/1152921504606846976), (10784820027/1152921504606846976)), (31/1152921504606846976), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (4027638355043/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780095259109145/633825300114114700748351602688), (4773325086849/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472808316736477/9903520314283042199192993792), (2684688662283/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945550229532943/1237940039285380274899124224), (1426064080367/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772765477317435/154742504910672534362390528), (712932569551/19342813113834066795298816)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775514241574147/4835703278458516698824704), (5346148589891/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260078051867661/604462909807314587353088), (2338517065231/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472471204548389/18889465931478580854784), (237456062295/2361183241434822606848)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649553444982719/2361183241434822606848), (2848778451387/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202949982332895/73786976294838206464), (3915941734721/295147905179352825856)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913079539475069/36893488147419103232), (2446616753755/18446744073709551616)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825669726638647/9223372036854775808), (11005115531297/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596909254109195/1152921504606846976), (5499643636899/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((598564321207533/72057594037927936), (9617814869187/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495439070404513/36028797018963968), (7206793793805/18014398509481984)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493974568537843/9007199254740992), (17993972455857/9007199254740992)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((559319130498169/1125899906842624), (17959402128973/2251799813685248)), (11/140737488355328), by norm_num⟩
  | 1 => ⟨((1114916984313521/1125899906842624), (13426247791209/562949953421312)), (265/1125899906842624), by norm_num⟩
  | 0 => ⟨((551787301826429/562949953421312), (53357479547649/1125899906842624)), (269/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((551787301826429/562949953421312), (53357479547649/1125899906842624)), (1026155711936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1079163323328811/1125899906842624), (104598923911169/1125899906842624)), (1107/1125899906842624), by norm_num⟩
  | 2 => ⟨((128081161624961/140737488355328), (100256978136843/562949953421312)), (291/140737488355328), by norm_num⟩
  | 3 => ⟨((896794040791557/1125899906842624), (91241007430477/281474976710656)), (1267/281474976710656), by norm_num⟩
  | 4 => ⟨((596003964944099/1125899906842624), (581397271584691/1125899906842624)), (355/35184372088832), by norm_num⟩
  | 5 => ⟨((30549676251759/2251799813685248), (1231068861330289/2251799813685248)), (47519/2251799813685248), by norm_num⟩
  | 6 => ⟨((-168154074955181/562949953421312), (16701642361233/1125899906842624)), (106495/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-219298529483/68719476736)), (1/34359738368), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-30517658817/8589934592)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-538429925386255/2251799813685248), (234742431351717/2251799813685248)), (50571/2251799813685248), by norm_num⟩
  | 1 => ⟨((235531473957/549755813888), (-102686028859/549755813888)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((-105503937191/274877906944), (91994332283/549755813888)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((63012559501/274877906944), (-3433994083/34359738368)), (29/1099511627776), by norm_num⟩
  | 4 => ⟨((-225806700333/2199023255552), (12305782831/274877906944)), (7/549755813888), by norm_num⟩
  | 5 => ⟨((161836517415/4398046511104), (-17639202331/1099511627776)), (21/4398046511104), by norm_num⟩
  | 6 => ⟨((-193314741697/17592186044416), (42140277075/8796093022208)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((98963862565/35184372088832), (-21572925853/17592186044416)), (7/17592186044416), by norm_num⟩
  | 8 => ⟨((-354638875725/562949953421312), (1207921693/4398046511104)), (13/140737488355328), by norm_num⟩
  | 9 => ⟨((141206125275/1125899906842624), (-123124914149/2251799813685248)), (43/2251799813685248), by norm_num⟩
  | 10 => ⟨((-50601482415/2251799813685248), (44122046165/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 11 => ⟨((131877360399/36028797018963968), (-3593458819/2251799813685248)), (11/18014398509481984), by norm_num⟩
  | 12 => ⟨((-315056679029/576460752303423488), (137357095813/576460752303423488)), (27/288230376151711744), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (3556731918251/10141204801825835211973625643008)), (19/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779886862129997/633825300114114700748351602688), (4214283984817/633825300114114700748351602688)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890999008924979/39614081257132168796771975168), (148139972579/1237940039285380274899124224)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890851790724953/2475880078570760549798248448), (5036065459723/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772517068619299/154742504910672534362390528), (5035285002253/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550795875802879/9671406556917033397649408), (589968798993/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259874796180611/604462909807314587353088), (4128952225929/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889555044568411/75557863725914323419136), (838499019617/9444732965739290427392)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649430005928955/2361183241434822606848), (5029633162139/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811630567835431/295147905179352825856), (864191721379/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912868388167793/36893488147419103232), (8638598995377/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825196149460029/9223372036854775808), (9713860545763/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596437567329083/1152921504606846976), (1213519404447/144115188075855872)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196718041555047/144115188075855872), (8488215777685/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((373706853796329/9007199254740992), (6359739818703/18014398509481984)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((746608710471611/4503599627370496), (3969215935875/2251799813685248)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((279473056772123/562949953421312), (15843117715655/2251799813685248)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((139228206595363/140737488355328), (5920062922401/281474976710656)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((550751212966187/562949953421312), (47022451474875/1125899906842624)), (535/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((550751212966187/562949953421312), (47022451474875/1125899906842624)), (2040867332076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075669760723661/1125899906842624), (92007014225825/1125899906842624)), (1093/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020161860293231/1125899906842624), (43951137386063/281474976710656)), (567/281474976710656), by norm_num⟩
  | 3 => ⟨((896902979935711/1125899906842624), (318587993872437/1125899906842624)), (4819/1125899906842624), by norm_num⟩
  | 4 => ⟨((624333159018681/1125899906842624), (63447585202587/140737488355328)), (5203/562949953421312), by norm_num⟩
  | 5 => ⟨((234752208953131/2251799813685248), (1125853012286997/2251799813685248)), (41847/2251799813685248), by norm_num⟩
  | 6 => ⟨((-538429925386255/2251799813685248), (234742431351717/2251799813685248)), (50571/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-30517658817/8589934592)), (1/34359738368), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-50145722707/34359738368), (-66286377203/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-788975541938493/4503599627370496), (343753099555347/2251799813685248)), (46197/2251799813685248), by norm_num⟩
  | 1 => ⟨((93705780909/274877906944), (-40827187817/137438953472)), (23/549755813888), by norm_num⟩
  | 2 => ⟨((-11396439381/34359738368), (158892078261/549755813888)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((118274384291/549755813888), (-206126471795/1099511627776)), (33/1099511627776), by norm_num⟩
  | 4 => ⟨((-230151324765/2199023255552), (200551796727/2199023255552)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((179141519471/4398046511104), (-156102310665/4398046511104)), (7/1099511627776), by norm_num⟩
  | 6 => ⟨((-14524720869/1099511627776), (202507380409/17592186044416)), (19/8796093022208), by norm_num⟩
  | 7 => ⟨((258411901725/70368744177664), (-112588904799/35184372088832)), (11/17592186044416), by norm_num⟩
  | 8 => ⟨((-251423171101/281474976710656), (219087892519/281474976710656)), (45/281474976710656), by norm_num⟩
  | 9 => ⟨((217443066823/1125899906842624), (-11842370933/70368744177664)), (41/1125899906842624), by norm_num⟩
  | 10 => ⟨((-169249868229/4503599627370496), (147482814639/4503599627370496)), (33/4503599627370496), by norm_num⟩
  | 11 => ⟨((239523662773/36028797018963968), (-208718767867/36028797018963968)), (3/2251799813685248), by norm_num⟩
  | 12 => ⟨((-77681921055/72057594037927936), (67691328115/72057594037927936)), (33/144115188075855872), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182021/10141204801825835211973625643008), (3158586199025/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889855221353223/316912650057057350374175801344), (3741817705667/633825300114114700748351602688)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890800681913171/39614081257132168796771975168), (1052245935663/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945320623423877/1237940039285380274899124224), (4471377261525/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772306725604253/154742504910672534362390528), (4470625752293/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775299446292113/4835703278458516698824704), (4190413180139/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259702649157013/604462909807314587353088), (3665813087807/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944637852720123/37778931862957161709568), (5955449221751/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298650857185081/4722366482869645213696), (4465277039459/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811487057977277/295147905179352825856), (6137627451787/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228172356646587/9223372036854775808), (479302607895/4611686018427387904)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228099331993637/1152921504606846976), (8623057342679/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399009383816183/288230376151711744), (8617570661317/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196369656094911/144115188075855872), (3767101127447/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494308118355023/36028797018963968), (1411120044827/4503599627370496)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((746287016825161/4503599627370496), (14089602731569/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((558628711556831/1125899906842624), (7028605710833/1125899906842624)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112894844415549/1125899906842624), (5251214451105/281474976710656)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((1099726034564063/1125899906842624), (20842998057221/562949953421312)), (533/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1099726034564063/1125899906842624), (20842998057221/562949953421312)), (2033237937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268154305166567/281474976710656), (81433837813073/1125899906842624)), (1081/1125899906842624), by norm_num⟩
  | 2 => ⟨((253991546046187/281474976710656), (38790009774579/281474976710656)), (2217/1125899906842624), by norm_num⟩
  | 3 => ⟨((447691950033547/562949953421312), (140010094949503/562949953421312)), (4613/1125899906842624), by norm_num⟩
  | 4 => ⟨((642420358463877/1125899906842624), (445378080601167/1125899906842624)), (301/35184372088832), by norm_num⟩
  | 5 => ⟨((380748379116505/2251799813685248), (127062780826639/281474976710656)), (37225/2251799813685248), by norm_num⟩
  | 6 => ⟨((-788975541938493/4503599627370496), (343753099555347/2251799813685248)), (46197/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50145722707/34359738368), (-66286377203/17179869184)), (1/34359738368), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-53586800493/34359738368), (-141670103803/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-131537540463847/1125899906842624), (787102498257523/4503599627370496)), (41503/2251799813685248), by norm_num⟩
  | 1 => ⟨((133556946255/549755813888), (-199796585991/549755813888)), (23/549755813888), by norm_num⟩
  | 2 => ⟨((-138861931111/549755813888), (103866330199/274877906944)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((96251756037/549755813888), (-287978615731/1099511627776)), (39/1099511627776), by norm_num⟩
  | 4 => ⟨((-200149899963/2199023255552), (149708674167/1099511627776)), (43/2199023255552), by norm_num⟩
  | 5 => ⟨((166480006619/4398046511104), (-124524174485/2199023255552)), (19/2199023255552), by norm_num⟩
  | 6 => ⟨((-14424393401/1099511627776), (10789197557/549755813888)), (7/2199023255552), by norm_num⟩
  | 7 => ⟨((137118550179/35184372088832), (-102562311321/17592186044416)), (35/35184372088832), by norm_num⟩
  | 8 => ⟨((-142565004689/140737488355328), (53318082693/35184372088832)), (39/140737488355328), by norm_num⟩
  | 9 => ⟨((32939510349/140737488355328), (-197105486355/562949953421312)), (19/281474976710656), by norm_num⟩
  | 10 => ⟨((-27398314473/562949953421312), (20493466821/281474976710656)), (33/2251799813685248), by norm_num⟩
  | 11 => ⟨((82870099327/9007199254740992), (-61985405441/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 12 => ⟨((-114882351403/72057594037927936), (171860036069/72057594037927936)), (19/36028797018963968), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521203/10141204801825835211973625643008), (2813696689477/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889778728308571/316912650057057350374175801344), (1666347069205/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945314343701053/19807040628566084398385987584), (1874376149171/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890458645115099/2475880078570760549798248448), (3982414130837/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443031071017951/38685626227668133590597632), (1990849783593/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550428023807089/9671406556917033397649408), (1866042093421/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259553309076793/604462909807314587353088), (3264814580787/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944516673309981/37778931862957161709568), (5303900572571/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298469366901659/4722366482869645213696), (3976680357365/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622725019678299/590295810358705651712), (683239068461/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825068161705601/73786976294838206464), (3414678395947/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824446060828471/9223372036854775808), (7678855639095/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49865315784441/36028797018963968), (1918410869341/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196066963881817/144115188075855872), (6708576121167/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493856694896101/36028797018963968), (5025572374619/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((746007161229819/4503599627370496), (12543431879411/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116704548367171/2251799813685248), (6256351629083/1125899906842624)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112082568224291/1125899906842624), (9346151750525/562949953421312)), (263/1125899906842624), by norm_num⟩
  | 0 => ⟨((549084647249881/562949953421312), (37078024780005/1125899906842624)), (531/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((549084647249881/562949953421312), (37078024780005/1125899906842624)), (2025608543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1069900629833603/1125899906842624), (36164802987051/562949953421312)), (67/70368744177664), by norm_num⟩
  | 2 => ⟨((506020019582985/562949953421312), (137464246185651/1125899906842624)), (17/8796093022208), by norm_num⟩
  | 3 => ⟨((111613898334325/140737488355328), (247125557517419/1125899906842624)), (1111/281474976710656), by norm_num⟩
  | 4 => ⟨((1307788270761895/2251799813685248), (391972987082491/1125899906842624)), (18001/2251799813685248), by norm_num⟩
  | 5 => ⟨((30412863081611/140737488355328), (910591912916177/2251799813685248)), (8361/562949953421312), by norm_num⟩
  | 6 => ⟨((-131537540463847/1125899906842624), (787102498257523/4503599627370496)), (41503/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53586800493/34359738368), (-141670103803/34359738368)), (1/34359738368), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile004Terms0
