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
namespace Reinmann.XiRectangle.Tile001Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-226488184839/137438953472), (-199592712889/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((205049202046189/9007199254740992), (-860632942592977/4503599627370496)), (65381/9007199254740992), by norm_num⟩
  | 1 => ⟨((-27498727191/549755813888), (230835431339/549755813888)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((30210439615/549755813888), (-253598641529/549755813888)), (13/549755813888), by norm_num⟩
  | 3 => ⟨((-44252746943/1099511627776), (185737722649/549755813888)), (21/1099511627776), by norm_num⟩
  | 4 => ⟨((48616611599/2199023255552), (-408107489143/2199023255552)), (25/2199023255552), by norm_num⟩
  | 5 => ⟨((-42728645549/4398046511104), (44835190267/549755813888)), (3/549755813888), by norm_num⟩
  | 6 => ⟨((7823702513/2199023255552), (-262701285291/8796093022208)), (19/8796093022208), by norm_num⟩
  | 7 => ⟨((-39292414737/35184372088832), (329836411737/35184372088832)), (13/17592186044416), by norm_num⟩
  | 8 => ⟨((21583564841/70368744177664), (-22647645949/8796093022208)), (31/140737488355328), by norm_num⟩
  | 9 => ⟨((-42154612565/562949953421312), (176931428615/281474976710656)), (33/562949953421312), by norm_num⟩
  | 10 => ⟨((18524630155/1125899906842624), (-311006466765/2251799813685248)), (31/2251799813685248), by norm_num⟩
  | 11 => ⟨((-14801008241/4503599627370496), (248491291813/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | 12 => ⟨((43361518769/72057594037927936), (-181997057875/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395457292338837/2535301200456458802993406410752), (-945844633607/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779424424897473/633825300114114700748351602688), (-1120146215677/316912650057057350374175801344)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945239618755567/19807040628566084398385987584), (-19687182361/309485009821345068724781056)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890300120896943/2475880078570760549798248448), (-2677006269337/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771966059293471/154742504910672534362390528), (-167281219549/9671406556917033397649408)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775140003046695/4835703278458516698824704), (-2508679965311/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259424111437203/604462909807314587353088), (-1097278377607/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236102999513915/9444732965739290427392), (-222821613519/4722366482869645213696)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298312874887377/4722366482869645213696), (-167061050393/295147905179352825856)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622510688946421/590295810358705651712), (-918477351819/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824801515885243/73786976294838206464), (-2295118498987/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((912073912728527/4611686018427387904), (-5161061986227/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398848510888397/288230376151711744), (-5157370617787/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597905175969479/72057594037927936), (-2254274575151/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((93342290732201/2251799813685248), (-3377265033051/18014398509481984)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((372886944707197/2251799813685248), (-8428663571127/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232501458836191/4503599627370496), (-1050868103175/281474976710656)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222867017520703/2251799813685248), (-12556224514545/1125899906842624)), (261/2251799813685248), by norm_num⟩
  | 0 => ⟨((2193993992796133/2251799813685248), (-49792605002605/2251799813685248)), (525/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2193993992796133/2251799813685248), (-49792605002605/2251799813685248)), (2002724654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1068285534902585/1125899906842624), (-48514381961245/1125899906842624)), (1047/2251799813685248), by norm_num⟩
  | 2 => ⟨((505764469782575/562949953421312), (-184127246725783/2251799813685248)), (1039/1125899906842624), by norm_num⟩
  | 3 => ⟨((1802496080982317/2251799813685248), (-330846529951113/2251799813685248)), (4075/2251799813685248), by norm_num⟩
  | 4 => ⟨((1394232594076747/2251799813685248), (-529664821907509/2251799813685248)), (3861/1125899906842624), by norm_num⟩
  | 5 => ⟨((369335607168711/1125899906842624), (-655898409930793/2251799813685248)), (3299/562949953421312), by norm_num⟩
  | 6 => ⟨((205049202046189/9007199254740992), (-860632942592977/4503599627370496)), (65381/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-226488184839/137438953472), (-199592712889/137438953472)), (1/68719476736), by norm_num⟩, 0, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-7417145753/4294967296), (-104581755117/68719476736)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((39171924929613/4503599627370496), (-1599814574427181/9007199254740992)), (92625/9007199254740992), by norm_num⟩
  | 1 => ⟨((-22020676369/1099511627776), (449671532059/1099511627776)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((6338060143/274877906944), (-517703483231/1099511627776)), (35/1099511627776), by norm_num⟩
  | 3 => ⟨((-9729281869/549755813888), (397352107693/1099511627776)), (15/549755813888), by norm_num⟩
  | 4 => ⟨((22402499397/2199023255552), (-457468519921/2199023255552)), (37/2199023255552), by norm_num⟩
  | 5 => ⟨((-20633464463/4398046511104), (421344077793/4398046511104)), (9/1099511627776), by norm_num⟩
  | 6 => ⟨((7918384615/4398046511104), (-323393530849/8796093022208)), (15/4398046511104), by norm_num⟩
  | 7 => ⟨((-5209358393/8796093022208), (106377303329/8796093022208)), (21/17592186044416), by norm_num⟩
  | 8 => ⟨((2998747745/17592186044416), (-122471396439/35184372088832)), (51/140737488355328), by norm_num⟩
  | 9 => ⟨((-24550655485/562949953421312), (501334776459/562949953421312)), (55/562949953421312), by norm_num⟩
  | 10 => ⟨((22611989337/2251799813685248), (-461746393149/2251799813685248)), (53/2251799813685248), by norm_num⟩
  | 11 => ⟨((-9466550831/4503599627370496), (386621949675/9007199254740992)), (47/9007199254740992), by norm_num⟩
  | 12 => ⟨((7265846275/18014398509481984), (-37092914081/4503599627370496)), (19/18014398509481984), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-61949964517/316912650057057350374175801344)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779302267892865/633825300114114700748351602688), (-2347412164233/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890341816732887/39614081257132168796771975168), (-660108328849/9903520314283042199192993792)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890154117078585/2475880078570760549798248448), (-2804965693385/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885910030983735/77371252455336267181195264), (-701102314251/38685626227668133590597632)), (21/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550143140508595/9671406556917033397649408), (-1314271290459/4835703278458516698824704)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259304360970323/604462909807314587353088), (-574845947845/151115727451828646838272)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118039338412605/4722366482869645213696), (-3735390875511/75557863725914323419136)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649083475076835/2361183241434822606848), (-350071765225/590295810358705651712)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622310061005807/590295810358705651712), (-3849215256045/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824550758891593/73786976294838206464), (-4809158738071/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823865762375303/9223372036854775808), (-5407059602589/9223372036854775808)), (79/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797556014417919/576460752303423488), (-5403006848051/1152921504606846976)), (79/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195563643736499/144115188075855872), (-590384336459/18014398509481984)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493106699426373/36028797018963968), (-3537753527831/18014398509481984)), (13/4503599627370496), by norm_num⟩
  | 3 => ⟨((1491085532482983/9007199254740992), (-4414233618753/4503599627370496)), (65/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115788777063559/2251799813685248), (-8804626620771/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | 1 => ⟨((2221482651101091/2251799813685248), (-6573729107345/562949953421312)), (391/2251799813685248), by norm_num⟩
  | 0 => ⟨((2191231345931683/2251799813685248), (-6514426984569/281474976710656)), (787/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2191231345931683/2251799813685248), (-6514426984569/281474976710656)), (3002175337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2131085883237555/2251799813685248), (-101427251375489/2251799813685248)), (1569/2251799813685248), by norm_num⟩
  | 2 => ⟨((503068648340133/562949953421312), (-23997491058957/281474976710656)), (389/281474976710656), by norm_num⟩
  | 3 => ⟨((1781860324245127/2251799813685248), (-343117829703031/2251799813685248)), (3047/1125899906842624), by norm_num⟩
  | 4 => ⟨((1357712329256891/2251799813685248), (-543021669664625/2251799813685248)), (11503/2251799813685248), by norm_num⟩
  | 5 => ⟨((687676686835033/2251799813685248), (-654824830765687/2251799813685248)), (4855/562949953421312), by norm_num⟩
  | 6 => ⟨((39171924929613/4503599627370496), (-1599814574427181/9007199254740992)), (92625/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-104581755117/68719476736)), (3/137438953472), by norm_num⟩, 0, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-123586581311/68719476736), (-27227668695/17179869184)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-20969880247789/9007199254740992), (-1491084695744449/9007199254740992)), (88017/9007199254740992), by norm_num⟩
  | 1 => ⟨((1534532981/274877906944), (218229061479/549755813888)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((-3679649381/549755813888), (-130822608727/274877906944)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((91910561/17179869184), (52283152507/137438953472)), (31/1099511627776), by norm_num⟩
  | 4 => ⟨((-881567599/274877906944), (-250739048487/1099511627776)), (5/274877906944), by norm_num⟩
  | 5 => ⟨((6764501691/4398046511104), (480996783259/4398046511104)), (41/4398046511104), by norm_num⟩
  | 6 => ⟨((-5406855543/8796093022208), (-48057496367/1099511627776)), (35/8796093022208), by norm_num⟩
  | 7 => ⟨((7408613341/35184372088832), (263398499111/17592186044416)), (51/35184372088832), by norm_num⟩
  | 8 => ⟨((-4441269727/70368744177664), (-78950251985/17592186044416)), (1/2199023255552), by norm_num⟩
  | 9 => ⟨((4733199859/281474976710656), (336558997371/281474976710656)), (9/70368744177664), by norm_num⟩
  | 10 => ⟨((-4539887027/1125899906842624), (-161406645763/562949953421312)), (37/1125899906842624), by norm_num⟩
  | 11 => ⟨((3958608597/4503599627370496), (281480896635/4503599627370496)), (17/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1582054807/9007199254740992), (-449974474283/36028797018963968)), (57/36028797018963968), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122365965/10141204801825835211973625643008), (-2064455676605/10141204801825835211973625643008)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222398970812239/79228162514264337593543950336), (-2444289628897/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890217508240311/39614081257132168796771975168), (-2749386772697/39614081257132168796771975168)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890022044752139/2475880078570760549798248448), (-2920687009457/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110730499736429/9671406556917033397649408), (-2920083638293/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775009667498149/4835703278458516698824704), (-2736937460189/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259196037694163/604462909807314587353088), (-2394179474443/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888453401577785/75557863725914323419136), (-1944670226653/37778931862957161709568)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298034951172161/4722366482869645213696), (-2915954609737/4722366482869645213696)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622128579979165/590295810358705651712), (-4007730739167/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912161967023179/36893488147419103232), (-5007104177951/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823610620904423/9223372036854775808), (-5629474906831/9223372036854775808)), (79/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594856933156149/1152921504606846976), (-5625080794413/1152921504606846976)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195340486794229/144115188075855872), (-4917005761133/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492772068222275/36028797018963968), (-7365637377251/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490667427312343/9007199254740992), (-2297447839797/2251799813685248)), (131/9007199254740992), by norm_num⟩
  | 2 => ⟨((557685475285293/1125899906842624), (-4581973498833/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220230585398271/2251799813685248), (-27362889790287/2251799813685248)), (49/281474976710656), by norm_num⟩
  | 0 => ⟨((1094366495603999/1125899906842624), (-54211597039045/2251799813685248)), (197/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1094366495603999/1125899906842624), (-54211597039045/2251799813685248)), (751497508811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2126127367296243/2251799813685248), (-105386553657489/2251799813685248)), (1571/2251799813685248), by norm_num⟩
  | 2 => ⟨((2002536472766825/2251799813685248), (-99504953555139/1125899906842624)), (1557/1125899906842624), by norm_num⟩
  | 3 => ⟨((55102414043181/70368744177664), (-353960947157245/2251799813685248)), (3045/1125899906842624), by norm_num⟩
  | 4 => ⟨((1325099277449377/2251799813685248), (-554339938656057/2251799813685248)), (11453/2251799813685248), by norm_num⟩
  | 5 => ⟨((643305554385369/2251799813685248), (-326208150347217/1125899906842624)), (1195/140737488355328), by norm_num⟩
  | 6 => ⟨((-20969880247789/9007199254740992), (-1491084695744449/9007199254740992)), (88017/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-123586581311/68719476736), (-27227668695/17179869184)), (3/137438953472), by norm_num⟩, 0, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-128071113533/68719476736), (-112862668801/68719476736)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-99901979998363/9007199254740992), (-1393447296634217/9007199254740992)), (20973/2251799813685248), by norm_num⟩
  | 1 => ⟨((15151800197/549755813888), (422679010441/1099511627776)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((-18825404533/549755813888), (-131289735471/274877906944)), (19/549755813888), by norm_num⟩
  | 3 => ⟨((15593124303/549755813888), (434990315627/1099511627776)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((-1210858071/68719476736), (-270227581973/1099511627776)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((1203547709/137438953472), (16787257885/137438953472)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((-31900839525/8796093022208), (-222478766667/4398046511104)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((5662186305/4398046511104), (315907980987/17592186044416)), (33/17592186044416), by norm_num⟩
  | 8 => ⟨((-28140008803/70368744177664), (-392500921337/70368744177664)), (43/70368744177664), by norm_num⟩
  | 9 => ⟨((31077908889/281474976710656), (433479177545/281474976710656)), (25/140737488355328), by norm_num⟩
  | 10 => ⟨((-3861285123/140737488355328), (-215431058165/562949953421312)), (13/281474976710656), by norm_num⟩
  | 11 => ⟨((27912532593/4503599627370496), (389328050185/4503599627370496)), (49/4503599627370496), by norm_num⟩
  | 12 => ⟨((-11560006309/9007199254740992), (-322481286951/18014398509481984)), (43/18014398509481984), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115840927/10141204801825835211973625643008), (-1069683838401/5070602400912917605986812821504)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222386361145497/79228162514264337593543950336), (-316588977239/79228162514264337593543950336)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945052013284369/19807040628566084398385987584), (-1424414922495/19807040628566084398385987584)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944950737823119/1237940039285380274899124224), (-1513152852365/1237940039285380274899124224)), (41/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771567432507437/154742504910672534362390528), (-3025657832309/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549906313130371/9671406556917033397649408), (-2835865999287/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629548574888709/302231454903657293676544), (-620173673749/151115727451828646838272)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888292720391643/75557863725914323419136), (-1007459781531/18889465931478580854784)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297914450524961/4722366482869645213696), (-1510625579589/2361183241434822606848)), (41/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405490727069371/147573952589676412928), (-4152387696235/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824116869529033/73786976294838206464), (-324233549535/4611686018427387904)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455844426993509/2305843009213693952), (-5832427486673/9223372036854775808)), (79/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594624063728445/1152921504606846976), (-1456927441775/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((74696048452733/9007199254740992), (-5093942442257/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((746233299969001/18014398509481984), (-7630316028745/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490285766724305/9007199254740992), (-9519370706525/9007199254740992)), (65/4503599627370496), by norm_num⟩
  | 2 => ⟨((139373694376531/281474976710656), (-18983254506353/4503599627370496)), (65/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109543871963513/1125899906842624), (-28336465582553/2251799813685248)), (49/281474976710656), by norm_num⟩
  | 0 => ⟨((8540831283775/8796093022208), (-56121071425525/2251799813685248)), (789/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((8540831283775/8796093022208), (-56121071425525/2251799813685248)), (3009804732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530400868756751/562949953421312), (-108984887108385/2251799813685248)), (393/562949953421312), by norm_num⟩
  | 2 => ⟨((996830085060159/1125899906842624), (-102683512899027/1125899906842624)), (3115/2251799813685248), by norm_num⟩
  | 3 => ⟨((873191576520113/1125899906842624), (-363648719660905/2251799813685248)), (6085/2251799813685248), by norm_num⟩
  | 4 => ⟨((1295680774187827/2251799813685248), (-564055466903259/2251799813685248)), (11405/2251799813685248), by norm_num⟩
  | 5 => ⟨((302120572749701/1125899906842624), (-649112607257943/2251799813685248)), (2355/281474976710656), by norm_num⟩
  | 6 => ⟨((-99901979998363/9007199254740992), (-1393447296634217/9007199254740992)), (20973/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-128071113533/68719476736), (-112862668801/68719476736)), (3/137438953472), by norm_num⟩, 0, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-66098241637/34359738368), (-232996301771/137438953472)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-40834941718061/2251799813685248), (-1305446423541919/9007199254740992)), (20061/2251799813685248), by norm_num⟩
  | 1 => ⟨((51142362071/1099511627776), (25546294901/68719476736)), (27/1099511627776), by norm_num⟩
  | 2 => ⟨((-32794392183/549755813888), (-262099810767/549755813888)), (19/549755813888), by norm_num⟩
  | 3 => ⟨((56077303439/1099511627776), (224090913739/549755813888)), (35/1099511627776), by norm_num⟩
  | 4 => ⟨((-4494857607/137438953472), (-71847730651/274877906944)), (3/137438953472), by norm_num⟩
  | 5 => ⟨((36893062819/2199023255552), (294857264909/2199023255552)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((-7885736481/1099511627776), (-252097984057/4398046511104)), (3/549755813888), by norm_num⟩
  | 7 => ⟨((23116016823/8796093022208), (369496321271/17592186044416)), (37/17592186044416), by norm_num⟩
  | 8 => ⟨((-59291412497/70368744177664), (-236934837957/35184372088832)), (25/35184372088832), by norm_num⟩
  | 9 => ⟨((4224429733/17592186044416), (135050191195/70368744177664)), (15/70368744177664), by norm_num⟩
  | 10 => ⟨((-17336717327/281474976710656), (-34639690113/70368744177664)), (33/562949953421312), by norm_num⟩
  | 11 => ⟨((32340219613/2251799813685248), (258469966249/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | 12 => ⟨((-27650341839/9007199254740992), (-220987457951/9007199254740992)), (59/18014398509481984), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418255/10141204801825835211973625643008), (-1104140018393/5070602400912917605986812821504)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778998093149833/633825300114114700748351602688), (-2614035483437/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944999818079063/19807040628566084398385987584), (-2940288680729/39614081257132168796771975168)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236223820719721/309485009821345068724781056), (-195215192423/154742504910672534362390528)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442864132042787/38685626227668133590597632), (-3122752876279/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387450586556009/2417851639229258349412352), (-731711910467/2417851639229258349412352)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629503092327139/302231454903657293676544), (-1280129343739/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118009057074353/4722366482869645213696), (-2079523188611/37778931862957161709568)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162225450609931/590295810358705651712), (-779520731291/1180591620717411303424)), (41/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621810511411947/590295810358705651712), (-2142705861043/295147905179352825856)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911963198684413/36893488147419103232), (-5353837460323/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823163459809719/9223372036854775808), (-1504761074219/2305843009213693952)), (79/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594409857019031/1152921504606846976), (-6014018803771/1152921504606846976)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((597474695631807/72057594037927936), (-5256616985893/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492185618382141/36028797018963968), (-7873637071299/36028797018963968)), (105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489934706424553/9007199254740992), (-9822315302475/9007199254740992)), (65/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229277495018633/4503599627370496), (-9792766075975/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | 1 => ⟨((1109018302554599/1125899906842624), (-29230883172521/2251799813685248)), (49/281474976710656), by norm_num⟩
  | 0 => ⟨((1092177891618605/1125899906842624), (-57874090801573/2251799813685248)), (395/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1092177891618605/1125899906842624), (-57874090801573/2251799813685248)), (1506809714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058722171570933/1125899906842624), (-56140694289835/1125899906842624)), (787/1125899906842624), by norm_num⟩
  | 2 => ⟨((1985506619598225/2251799813685248), (-52791014024253/562949953421312)), (1559/1125899906842624), by norm_num⟩
  | 3 => ⟨((216362831977403/281474976710656), (-372384462112255/2251799813685248)), (6085/2251799813685248), by norm_num⟩
  | 4 => ⟨((634459999271233/1125899906842624), (-572485396382585/2251799813685248)), (1421/281474976710656), by norm_num⟩
  | 5 => ⟨((284754094443881/1125899906842624), (-322603352184535/1125899906842624)), (9297/1125899906842624), by norm_num⟩
  | 6 => ⟨((-40834941718061/2251799813685248), (-1305446423541919/9007199254740992)), (20061/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66098241637/34359738368), (-232996301771/137438953472)), (3/137438953472), by norm_num⟩, 0, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-272031958151/137438953472), (-239728163121/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-107392065050187/4503599627370496), (-306455519982797/2251799813685248)), (12833/2251799813685248), by norm_num⟩
  | 1 => ⟨((69192826273/1099511627776), (197449630423/549755813888)), (19/1099511627776), by norm_num⟩
  | 2 => ⟨((-45650958833/549755813888), (-260540447199/549755813888)), (7/274877906944), by norm_num⟩
  | 3 => ⟨((80316998341/1099511627776), (114596862807/274877906944)), (27/1099511627776), by norm_num⟩
  | 4 => ⟨((-52990290791/1099511627776), (-151213845371/549755813888)), (5/274877906944), by norm_num⟩
  | 5 => ⟨((13984441531/549755813888), (319249605573/2199023255552)), (23/2199023255552), by norm_num⟩
  | 6 => ⟨((-49207657231/4398046511104), (-70209834297/1099511627776)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((2318961223/549755813888), (423514920715/17592186044416)), (9/4398046511104), by norm_num⟩
  | 8 => ⟨((-48958972901/35184372088832), (-279420038929/35184372088832)), (13/17592186044416), by norm_num⟩
  | 9 => ⟨((57424682793/140737488355328), (40966972321/17592186044416)), (33/140737488355328), by norm_num⟩
  | 10 => ⟨((-30309406005/281474976710656), (-345965403443/562949953421312)), (37/562949953421312), by norm_num⟩
  | 11 => ⟨((29086640027/1125899906842624), (332008194091/2251799813685248)), (19/1125899906842624), by norm_num⟩
  | 12 => ⟨((-25587103519/4503599627370496), (-73015721509/2251799813685248)), (35/9007199254740992), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987305/10141204801825835211973625643008), (-142005182285/633825300114114700748351602688)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444728044821571/158456325028528675187087900672), (-336164378775/79228162514264337593543950336)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889902987963749/39614081257132168796771975168), (-3024949318303/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889687881751705/2475880078570760549798248448), (-3213359099839/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221419231183383/19342813113834066795298816), (-3212628516253/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549706090581885/9671406556917033397649408), (-752765790935/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258921966621103/604462909807314587353088), (-329238049325/75557863725914323419136)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888008069509327/75557863725914323419136), (-2139320147881/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297700981437709/4722366482869645213696), (-3207708087155/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621669419364937/590295810358705651712), (-2204266091953/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911875027581481/36893488147419103232), (-5507566945813/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227870638296533/1152921504606846976), (-773969362369/1152921504606846976)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398552885798383/288230376151711744), (-6186435842533/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298693977869791/36028797018963968), (-5407152011399/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((745962744476555/18014398509481984), (-4049390390299/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((372402425991639/2251799813685248), (-10102594097411/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228627973645171/4503599627370496), (-20142645646751/4503599627370496)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((2217063551258325/2251799813685248), (-15028986327491/1125899906842624)), (131/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182414703702347/2251799813685248), (-59494123377851/2251799813685248)), (527/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182414703702347/2251799813685248), (-59494123377851/2251799813685248)), (2010354048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2113595693229311/2251799813685248), (-57660920324533/1125899906842624)), (1051/2251799813685248), by norm_num⟩
  | 2 => ⟨((1977967846181451/2251799813685248), (-54121983723819/562949953421312)), (1041/1125899906842624), by norm_num⟩
  | 3 => ⟨((214577787459173/281474976710656), (-190161741601837/1125899906842624)), (4059/2251799813685248), by norm_num⟩
  | 4 => ⟨((1244402877569223/2251799813685248), (-144966654759689/562949953421312)), (7561/2251799813685248), by norm_num⟩
  | 5 => ⟨((538366340764151/2251799813685248), (-160224653397859/562949953421312)), (3063/562949953421312), by norm_num⟩
  | 6 => ⟨((-107392065050187/4503599627370496), (-306455519982797/2251799813685248)), (12833/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272031958151/137438953472), (-239728163121/137438953472)), (1/68719476736), by norm_num⟩, 0, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-34892961149/17179869184), (-61498844025/34359738368)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-64200266675937/2251799813685248), (-576749234160591/4503599627370496)), (3075/562949953421312), by norm_num⟩
  | 1 => ⟨((84891379435/1099511627776), (1489511375/4294967296)), (19/1099511627776), by norm_num⟩
  | 2 => ⟨((-7184066161/68719476736), (-258154981031/549755813888)), (15/549755813888), by norm_num⟩
  | 3 => ⟨((51879498165/549755813888), (233032216099/549755813888)), (15/549755813888), by norm_num⟩
  | 4 => ⟨((-70246142719/1099511627776), (-315531469835/1099511627776)), (11/549755813888), by norm_num⟩
  | 5 => ⟨((76092032367/2199023255552), (42723753017/274877906944)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((-34343507259/2199023255552), (-308528181199/4398046511104)), (25/4398046511104), by norm_num⟩
  | 7 => ⟨((53145109565/8796093022208), (59679271653/2199023255552)), (21/8796093022208), by norm_num⟩
  | 8 => ⟨((-71959812323/35184372088832), (-323228927203/35184372088832)), (31/35184372088832), by norm_num⟩
  | 9 => ⟨((86609237437/140737488355328), (194515591403/70368744177664)), (5/17592186044416), by norm_num⟩
  | 10 => ⟨((-93816865143/562949953421312), (-421406389133/562949953421312)), (23/281474976710656), by norm_num⟩
  | 11 => ⟨((46192869185/1125899906842624), (51872257129/281474976710656)), (3/140737488355328), by norm_num⟩
  | 12 => ⟨((-83395072457/9007199254740992), (-374593803599/9007199254740992)), (23/4503599627370496), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (-582870494139/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889416098485533/316912650057057350374175801344), (-689846540073/158456325028528675187087900672)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889813012575967/39614081257132168796771975168), (-387968972575/4951760157141521099596496896)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889592287401667/2475880078570760549798248448), (-1648526186901/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885629130096409/77371252455336267181195264), (-1648141584283/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549616481039713/9671406556917033397649408), (-3089448378845/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258843563684727/604462909807314587353088), (-2702450452191/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887880674909621/75557863725914323419136), (-4389950787393/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297605444410805/4722366482869645213696), (-3291123744007/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202692258811835/73786976294838206464), (-4523119555753/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823585890961249/73786976294838206464), (-5650637536297/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911390225928995/4611686018427387904), (-794060563595/1152921504606846976)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199253365827953/144115188075855872), (-6346884715089/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149326801864109/18014398509481984), (-2773614657159/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491683330579217/36028797018963968), (-2077066683877/9007199254740992)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489307158701227/9007199254740992), (-10363351114523/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228023346677741/4503599627370496), (-20660866685525/4503599627370496)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((2216157788715451/2251799813685248), (-7706775172907/562949953421312)), (131/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180608003455263/2251799813685248), (-60999738948095/2251799813685248)), (527/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2180608003455263/2251799813685248), (-60999738948095/2251799813685248)), (2010354048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2110014517145503/2251799813685248), (-118142401602925/2251799813685248)), (525/1125899906842624), by norm_num⟩
  | 2 => ⟨((492739586411635/562949953421312), (-221407054887917/2251799813685248)), (2079/2251799813685248), by norm_num⟩
  | 3 => ⟨((1703373316317249/2251799813685248), (-387586924880489/2251799813685248)), (4049/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221803560726235/2251799813685248), (-146595008486657/562949953421312)), (235/70368744177664), by norm_num⟩
  | 5 => ⟨((510241802938819/2251799813685248), (-318163812369381/1125899906842624)), (6039/1125899906842624), by norm_num⟩
  | 6 => ⟨((-64200266675937/2251799813685248), (-576749234160591/4503599627370496)), (3075/562949953421312), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-61498844025/34359738368)), (1/68719476736), by norm_num⟩, 0, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile001Terms1
