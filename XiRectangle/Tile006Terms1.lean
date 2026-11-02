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
namespace Reinmann.XiRectangle.Tile006Terms1
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
  | 0 => ⟨((-28311023105/17179869184), (-54056359741/8589934592)), (3/17179869184), by norm_num⟩
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
  | 0 => ⟨((866676505656651/4503599627370496), (-16992965961849/9007199254740992)), (156883/4503599627370496), by norm_num⟩
  | 1 => ⟨((-116228205495/274877906944), (284861469/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((127689734847/274877906944), (-625904621/137438953472)), (29/274877906944), by norm_num⟩
  | 3 => ⟨((-93521007893/274877906944), (57302209/17179869184)), (23/274877906944), by norm_num⟩
  | 4 => ⟨((12842916065/68719476736), (-62952911/34359738368)), (7/137438953472), by norm_num⟩
  | 5 => ⟨((-90300066633/1099511627776), (885258773/1099511627776)), (27/1099511627776), by norm_num⟩
  | 6 => ⟨((132273017161/4398046511104), (-324185389/1099511627776)), (43/4398046511104), by norm_num⟩
  | 7 => ⟨((-41519074889/4398046511104), (814066405/8796093022208)), (29/8796093022208), by norm_num⟩
  | 8 => ⟨((45613365887/17592186044416), (-223585839/8796093022208)), (17/17592186044416), by norm_num⟩
  | 9 => ⟨((-44543470481/70368744177664), (218341467/35184372088832)), (35/140737488355328), by norm_num⟩
  | 10 => ⟨((78297606481/562949953421312), (-191898095/140737488355328)), (33/562949953421312), by norm_num⟩
  | 11 => ⟨((-15639765937/562949953421312), (1226598431/4503599627370496)), (55/4503599627370496), by norm_num⟩
  | 12 => ⟨((91637541601/18014398509481984), (-224592685/4503599627370496)), (43/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677669/5070602400912917605986812821504), (-3192443519/2535301200456458802993406410752)), (57/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779427107552893/633825300114114700748351602688), (-15123006039/633825300114114700748351602688)), (271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890482410212891/39614081257132168796771975168), (-2126364027/4951760157141521099596496896)), (305/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890303689413239/2475880078570760549798248448), (-18071055977/2475880078570760549798248448)), (81/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221496231235657/19342813113834066795298816), (-18067638919/154742504910672534362390528)), (81/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550283795609145/9671406556917033397649408), (-16934781777/9671406556917033397649408)), (19/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259427662965277/604462909807314587353088), (-14814305375/604462909807314587353088)), (265/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888830209000311/75557863725914323419136), (-24066444647/75557863725914323419136)), (27/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324579480179541/1180591620717411303424), (-9021942141/2361183241434822606848)), (81/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405629563486637/147573952589676412928), (-24800677531/590295810358705651712)), (445/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824811911676077/73786976294838206464), (-15493179523/36893488147419103232)), (139/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912080405537167/4611686018427387904), (-8709936187/2305843009213693952)), (625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595408639839815/1152921504606846976), (-34814875723/1152921504606846976)), (625/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195824932571445/144115188075855872), (-30435062579/144115188075855872)), (547/144115188075855872), by norm_num⟩
  | 4 => ⟨((373375533159067/9007199254740992), (-45596746387/36028797018963968)), (205/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491585929926477/9007199254740992), (-56898334463/9007199254740992)), (1025/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232596590981113/4503599627370496), (-113504410873/4503599627370496)), (2049/4503599627370496), by norm_num⟩
  | 1 => ⟨((2223056546587915/2251799813685248), (-169527849015/2251799813685248)), (1537/1125899906842624), by norm_num⟩
  | 0 => ⟨((274319864361709/281474976710656), (-168075934139/1125899906842624)), (3073/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((274319864361709/281474976710656), (-168075934139/1125899906842624)), (11722568992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1069386516659157/1125899906842624), (-327606865763/1125899906842624)), (11983/2251799813685248), by norm_num⟩
  | 2 => ⟨((507854831382447/562949953421312), (-622325950793/1125899906842624)), (22771/2251799813685248), by norm_num⟩
  | 3 => ⟨((458151619639751/562949953421312), (-2245679132819/2251799813685248)), (41111/2251799813685248), by norm_num⟩
  | 4 => ⟨((1491447615267945/2251799813685248), (-3655250437945/2251799813685248)), (33499/1125899906842624), by norm_num⟩
  | 5 => ⟨((1975666411120503/4503599627370496), (-9684012789677/4503599627370496)), (177937/4503599627370496), by norm_num⟩
  | 6 => ⟨((866676505656651/4503599627370496), (-16992965961849/9007199254740992)), (156883/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/17179869184), (-54056359741/8589934592)), (3/17179869184), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-442566021/67108864)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((762308812439333/4503599627370496), (-30687788266831/562949953421312)), (507981/9007199254740992), by norm_num⟩
  | 1 => ⟨((-26783461117/68719476736), (17251280225/137438953472)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((61671198307/137438953472), (-4965317585/34359738368)), (13/68719476736), by norm_num⟩
  | 3 => ⟨((-94668787925/274877906944), (30488176675/274877906944)), (43/274877906944), by norm_num⟩
  | 4 => ⟨((27247867481/137438953472), (-17550405281/274877906944)), (13/137438953472), by norm_num⟩
  | 5 => ⟨((-25096213391/274877906944), (32329041261/1099511627776)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((77048222459/2199023255552), (-24813456159/2199023255552)), (21/1099511627776), by norm_num⟩
  | 7 => ⟨((-50688596707/4398046511104), (16324312645/4398046511104)), (29/4398046511104), by norm_num⟩
  | 8 => ⟨((58357403581/17592186044416), (-18794059475/17592186044416)), (35/17592186044416), by norm_num⟩
  | 9 => ⟨((-14930320839/17592186044416), (150260143/549755813888)), (37/70368744177664), by norm_num⟩
  | 10 => ⟨((13751333679/70368744177664), (-17714522385/281474976710656)), (9/70368744177664), by norm_num⟩
  | 11 => ⟨((-46056168637/1125899906842624), (29664869217/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | 12 => ⟨((35349415781/4503599627370496), (-5692157137/2251799813685248)), (51/9007199254740992), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-405844695749/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889652545322023/316912650057057350374175801344), (-480571691515/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59073286077141/1237940039285380274899124224), (-67570127869/4951760157141521099596496896)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945078935590125/1237940039285380274899124224), (-143561227651/618970019642690137449562112)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885912024822835/77371252455336267181195264), (-143532780281/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387536781750131/2417851639229258349412352), (-8408235255/151115727451828646838272)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78706756065405/37778931862957161709568), (-470740340087/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472158987553941/18889465931478580854784), (-764726564029/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324543064494823/1180591620717411303424), (-286673410477/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811159009307321/295147905179352825856), (-788030104395/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824561693896585/73786976294838206464), (-492277608133/36893488147419103232)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823879421076839/9223372036854775808), (-553480850265/4611686018427387904)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595127381059631/1152921504606846976), (-1106133655597/1152921504606846976)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((597789489352835/72057594037927936), (-966936225571/144115188075855872)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((46660421776245/1125899906842624), (-181068119863/4503599627370496)), (1095/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491125651138721/9007199254740992), (-14120561947/70368744177664)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((278959697511693/562949953421312), (-3605134601503/4503599627370496)), (2739/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110840946411819/1125899906842624), (-5383443567273/2251799813685248)), (2055/1125899906842624), by norm_num⟩
  | 0 => ⟨((136989064542867/140737488355328), (-10670241662531/2251799813685248)), (4117/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((136989064542867/140737488355328), (-10670241662531/2251799813685248)), (15705112937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2133397067827797/2251799813685248), (-20772097624849/2251799813685248)), (4027/562949953421312), by norm_num⟩
  | 2 => ⟨((2021028486332679/2251799813685248), (-39359744055543/2251799813685248)), (7705/562949953421312), by norm_num⟩
  | 3 => ⟨((1813219331621615/2251799813685248), (-8831509296205/281474976710656)), (56401/2251799813685248), by norm_num⟩
  | 4 => ⟨((728921951454709/1125899906842624), (-113782500813463/2251799813685248)), (23593/562949953421312), by norm_num⟩
  | 5 => ⟨((1876154687393593/4503599627370496), (-294656965615823/4503599627370496)), (131733/2251799813685248), by norm_num⟩
  | 6 => ⟨((762308812439333/4503599627370496), (-30687788266831/562949953421312)), (507981/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-442566021/67108864)), (1/4294967296), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-14748320543/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((310909924760329/2251799813685248), (-411440641121127/4503599627370496)), (580567/9007199254740992), by norm_num⟩
  | 1 => ⟨((-45503505789/137438953472), (30108385265/137438953472)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((54556320713/137438953472), (-36098377349/137438953472)), (15/68719476736), by norm_num⟩
  | 3 => ⟨((-10901695295/34359738368), (14426688067/68719476736)), (13/68719476736), by norm_num⟩
  | 4 => ⟨((52282247227/274877906944), (-17296843559/137438953472)), (33/274877906944), by norm_num⟩
  | 5 => ⟨((-50146941391/549755813888), (33180815523/549755813888)), (17/274877906944), by norm_num⟩
  | 6 => ⟨((80164742471/2199023255552), (-53042747127/2199023255552)), (57/2199023255552), by norm_num⟩
  | 7 => ⟨((-54921902005/4398046511104), (36340272169/4398046511104)), (41/4398046511104), by norm_num⟩
  | 8 => ⟨((65848484595/17592186044416), (-43570083423/17592186044416)), (51/17592186044416), by norm_num⟩
  | 9 => ⟨((-17544196659/17592186044416), (11608499675/17592186044416)), (7/8796093022208), by norm_num⟩
  | 10 => ⟨((33655316987/140737488355328), (-5567193299/35184372088832)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((-14673077365/281474976710656), (38835044347/1125899906842624)), (51/1125899906842624), by norm_num⟩
  | 12 => ⟨((11728167617/1125899906842624), (-31040789753/4503599627370496)), (43/4503599627370496), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-190356053665/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444798631758903/158456325028528675187087900672), (-901516720449/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890220771834075/39614081257132168796771975168), (-1014045949799/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945012857714827/1237940039285380274899124224), (-1077226156013/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442922973700899/38685626227668133590597632), (-134625481141/19342813113834066795298816)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775011616404527/4835703278458516698824704), (-1009454970187/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629599845305275/302231454903657293676544), (-441518515541/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944229895808111/37778931862957161709568), (-179311587271/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298040140674439/4722366482869645213696), (-537741252869/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405534090006897/147573952589676412928), (-1478159822047/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912167312391713/36893488147419103232), (-1846757333573/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823623974087787/9223372036854775808), (-2076306937251/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594871941420455/1152921504606846976), (-2074689303873/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((149419434686269/18014398509481984), (-906767472855/72057594037927936)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492798262453435/36028797018963968), (-1358335065127/18014398509481984)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((745353319895489/4503599627370496), (-3389490377197/9007199254740992)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230839656772783/4503599627370496), (-6759975719911/4503599627370496)), (343/562949953421312), by norm_num⟩
  | 1 => ⟨((277553158982215/281474976710656), (-5046289816187/1125899906842624)), (4123/2251799813685248), by norm_num⟩
  | 0 => ⟨((547328234945957/562949953421312), (-624887293547/70368744177664)), (8269/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((547328234945957/562949953421312), (-624887293547/70368744177664)), (31543740279387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((532095622291635/562949953421312), (-9720749273391/562949953421312)), (16227/2251799813685248), by norm_num⟩
  | 2 => ⟨((2011058045748983/2251799813685248), (-9187971510311/281474976710656)), (31237/2251799813685248), by norm_num⟩
  | 3 => ⟨((1793654850806343/2251799813685248), (-131290846851495/2251799813685248)), (57835/2251799813685248), by norm_num⟩
  | 4 => ⟨((710533951088031/1125899906842624), (-104578774227829/1125899906842624)), (98881/2251799813685248), by norm_num⟩
  | 5 => ⟨((109672665533583/281474976710656), (-263990676970289/2251799813685248)), (71587/1125899906842624), by norm_num⟩
  | 6 => ⟨((310909924760329/2251799813685248), (-411440641121127/4503599627370496)), (580567/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-14748320543/2147483648)), (1/4294967296), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-61133945601/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((938952650104137/9007199254740992), (-1034429163740447/9007199254740992)), (318237/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4450244301/17179869184), (19611052763/68719476736)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((44233766627/137438953472), (-12182908855/34359738368)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-18319463473/68719476736), (40364521637/137438953472)), (15/68719476736), by norm_num⟩
  | 4 => ⟨((45522156605/274877906944), (-12537758529/68719476736)), (39/274877906944), by norm_num⟩
  | 5 => ⟨((-5655915483/68719476736), (12462063817/137438953472)), (41/549755813888), by norm_num⟩
  | 6 => ⟨((9369614663/274877906944), (-10322355083/274877906944)), (9/274877906944), by norm_num⟩
  | 7 => ⟨((-53217412073/4398046511104), (58628774371/4398046511104)), (53/4398046511104), by norm_num⟩
  | 8 => ⟨((16530037643/4398046511104), (-18210878913/4398046511104)), (35/8796093022208), by norm_num⟩
  | 9 => ⟨((-18255822427/17592186044416), (20112148493/17592186044416)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((36291211637/140737488355328), (-19990724613/70368744177664)), (43/140737488355328), by norm_num⟩
  | 11 => ⟨((-32792826591/562949953421312), (4515916775/70368744177664)), (41/562949953421312), by norm_num⟩
  | 12 => ⟨((13581185477/1125899906842624), (-59848701995/4503599627370496)), (35/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-543021441163/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779093436184147/633825300114114700748351602688), (-1285722726697/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890107037248465/39614081257132168796771975168), (-1446201065041/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59059526932317/77371252455336267181195264), (-384074117105/618970019642690137449562112)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442892757326293/38685626227668133590597632), (-23999498175/2417851639229258349412352)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774954954386615/4835703278458516698824704), (-359905215407/2417851639229258349412352)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314775129866483/151115727451828646838272), (-1259319329595/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888298614894091/75557863725914323419136), (-511434974889/18889465931478580854784)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297919237509959/4722366482869645213696), (-766866443505/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810985042367465/295147905179352825856), (-2107953574523/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824126730628937/73786976294838206464), (-2633548978269/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823390024561417/9223372036854775808), (-740207105367/2305843009213693952)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594637906441387/1152921504606846976), (-184902341843/72057594037927936)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195150601161763/144115188075855872), (-2585945399313/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((93280672346689/2251799813685248), (-1936774703345/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((745160963872595/4503599627370496), (-4832555213267/9007199254740992)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230069249162957/4503599627370496), (-4818510190517/2251799813685248)), (1375/2251799813685248), by norm_num⟩
  | 1 => ⟨((554816808450627/562949953421312), (-14385496181391/2251799813685248)), (4133/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093493674562067/1125899906842624), (-28491996422589/2251799813685248)), (8301/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1093493674562067/1125899906842624), (-28491996422589/2251799813685248)), (31665810591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((132729990092419/140737488355328), (-27671925074687/1125899906842624)), (16335/2251799813685248), by norm_num⟩
  | 2 => ⟨((1000744626578877/1125899906842624), (-26097483932129/562949953421312)), (31615/2251799813685248), by norm_num⟩
  | 3 => ⟨((1774163914369611/2251799813685248), (-185571855214353/2251799813685248)), (29567/1125899906842624), by norm_num⟩
  | 4 => ⟨((691273856291109/1125899906842624), (-292419323461181/2251799813685248)), (51465/1125899906842624), by norm_num⟩
  | 5 => ⟨((810875418736513/2251799813685248), (-359076028258883/2251799813685248)), (153127/2251799813685248), by norm_num⟩
  | 6 => ⟨((938952650104137/9007199254740992), (-1034429163740447/9007199254740992)), (318237/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-61133945601/8589934592)), (1/4294967296), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-16524560409/8589934592), (-63103165063/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((159934527352407/2251799813685248), (-1149610975787021/9007199254740992)), (338579/4503599627370496), by norm_num⟩
  | 1 => ⟨((-12519041845/68719476736), (5624187343/17179869184)), (7/34359738368), by norm_num⟩
  | 2 => ⟨((32110708337/137438953472), (-57703022847/137438953472)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((-6863528393/34359738368), (49335110459/137438953472)), (35/137438953472), by norm_num⟩
  | 4 => ⟨((35209205483/274877906944), (-3954439371/17179869184)), (47/274877906944), by norm_num⟩
  | 5 => ⟨((-4515491449/68719476736), (8114349379/68719476736)), (51/549755813888), by norm_num⟩
  | 6 => ⟨((30885351709/1099511627776), (-3468815871/68719476736)), (45/1099511627776), by norm_num⟩
  | 7 => ⟨((-45268207441/4398046511104), (2542096297/137438953472)), (17/1099511627776), by norm_num⟩
  | 8 => ⟨((29027664897/8796093022208), (-52162786109/8796093022208)), (23/4398046511104), by norm_num⟩
  | 9 => ⟨((-16545442317/17592186044416), (59464402095/35184372088832)), (27/17592186044416), by norm_num⟩
  | 10 => ⟨((1060955541/4398046511104), (-30504635989/70368744177664)), (29/70368744177664), by norm_num⟩
  | 11 => ⟨((-3958250521/70368744177664), (56903888349/562949953421312)), (7/70368744177664), by norm_num⟩
  | 12 => ⟨((27073899015/2251799813685248), (-48651863953/2251799813685248)), (25/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (-1384663108857/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779000311656321/633825300114114700748351602688), (-1639084916253/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236250282266419/4951760157141521099596496896), (-57614329413/1237940039285380274899124224)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472448378683675/618970019642690137449562112), (-979251347813/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771459660535907/154742504910672534362390528), (-979035127493/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387451369387631/2417851639229258349412352), (-917615758705/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629504559585027/302231454903657293676544), (-1605368367823/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472037511596861/18889465931478580854784), (-2607862869591/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((81112985846031/295147905179352825856), (-1955144305449/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810908380391719/295147905179352825856), (-2687100588249/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911967492192465/36893488147419103232), (-3357042439655/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911587092390439/4611686018427387904), (-1887076754613/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594421910522051/1152921504606846976), (-3771006782821/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194961429668285/144115188075855872), (-206005878283/9007199254740992)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492206651656317/36028797018963968), (-4937075269089/36028797018963968)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((744983094280481/4503599627370496), (-6158996800013/9007199254740992)), (43/281474976710656), by norm_num⟩
  | 2 => ⟨((2229355963566379/4503599627370496), (-12281023171005/4503599627370496)), (1377/2251799813685248), by norm_num⟩
  | 1 => ⟨((138637052093607/140737488355328), (-18329358273177/2251799813685248)), (2071/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184820936559743/2251799813685248), (-36291504825541/2251799813685248)), (8331/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184820936559743/2251799813685248), (-36291504825541/2251799813685248)), (31780251509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1059624710532623/1125899906842624), (-70424057307595/2251799813685248)), (4109/562949953421312), by norm_num⟩
  | 2 => ⟨((1992299019465501/2251799813685248), (-132557203150251/2251799813685248)), (15983/1125899906842624), by norm_num⟩
  | 3 => ⟨((1754900212194679/2251799813685248), (-234562223741483/2251799813685248)), (60329/2251799813685248), by norm_num⟩
  | 4 => ⟨((671608395109575/1125899906842624), (-365603810529777/2251799813685248)), (53301/1125899906842624), by norm_num⟩
  | 5 => ⟨((741879979339163/2251799813685248), (-436171256332061/2251799813685248)), (161795/2251799813685248), by norm_num⟩
  | 6 => ⟨((159934527352407/2251799813685248), (-1149610975787021/9007199254740992)), (338579/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-63103165063/8589934592)), (1/4294967296), by norm_num⟩, -1, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2125249673/1073741824), (-8115797189/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((45310921160959/1125899906842624), (-595267776184469/4503599627370496)), (176065/2251799813685248), by norm_num⟩
  | 1 => ⟨((-7298469153/68719476736), (23970730405/68719476736)), (59/274877906944), by norm_num⟩
  | 2 => ⟨((19261078513/137438953472), (-15815032943/34359738368)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((-16943696809/137438953472), (27824519071/68719476736)), (19/68719476736), by norm_num⟩
  | 4 => ⟨((22357693627/274877906944), (-36715250499/137438953472)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-1475080881/34359738368), (77514920751/549755813888)), (57/549755813888), by norm_num⟩
  | 6 => ⟨((5190430681/274877906944), (-34094386627/549755813888)), (13/274877906944), by norm_num⟩
  | 7 => ⟨((-31309358017/4398046511104), (102830903917/4398046511104)), (81/4398046511104), by norm_num⟩
  | 8 => ⟨((10328398845/4398046511104), (-67844162673/8796093022208)), (7/1099511627776), by norm_num⟩
  | 9 => ⟨((-12114327411/17592186044416), (79575393233/35184372088832)), (17/8796093022208), by norm_num⟩
  | 10 => ⟨((12788161819/70368744177664), (-21000402477/35184372088832)), (37/70368744177664), by norm_num⟩
  | 11 => ⟨((-6136125851/140737488355328), (80612750665/562949953421312)), (73/562949953421312), by norm_num⟩
  | 12 => ⟨((21591450537/2251799813685248), (-8864236271/281474976710656)), (33/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-1661142254549/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778913980780803/633825300114114700748351602688), (-122886548283/39614081257132168796771975168)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889905116792141/39614081257132168796771975168), (-2211572558063/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889690276063107/2475880078570760549798248448), (-2349321212987/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771356392651601/154742504910672534362390528), (-1174393702977/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549708632898981/9671406556917033397649408), (-2201421171263/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258924349122025/604462909807314587353088), (-962838334845/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944006118521951/37778931862957161709568), (-1564081044429/37778931862957161709568)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297704365833355/4722366482869645213696), (-586298058403/1180591620717411303424)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621674492938995/590295810358705651712), (-1611564909217/295147905179352825856)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911878513211715/36893488147419103232), (-4026649179343/73786976294838206464)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911486906548371/4611686018427387904), (-2263435228911/4611686018427387904)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594221328158413/1152921504606846976), (-4522985947471/1152921504606846976)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194785683830261/144115188075855872), (-3953246512917/144115188075855872)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((372985640554469/9007199254740992), (-1480286771817/9007199254740992)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((744817628621367/4503599627370496), (-7386190970257/9007199254740992)), (689/4503599627370496), by norm_num⟩
  | 2 => ⟨((557172914753599/1125899906842624), (-14726740391349/4503599627370496)), (2759/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217190329940191/2251799813685248), (-21976311165477/2251799813685248)), (519/281474976710656), by norm_num⟩
  | 0 => ⟨((2182792089300173/2251799813685248), (-10874811920425/562949953421312)), (4179/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182792089300173/2251799813685248), (-10874811920425/562949953421312)), (15941624168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528764712078027/562949953421312), (-42166187754821/1125899906842624)), (1033/140737488355328), by norm_num⟩
  | 2 => ⟨((991731581804043/1125899906842624), (-39605638107087/562949953421312)), (1009/70368744177664), by norm_num⟩
  | 3 => ⟨((216994667582975/281474976710656), (-139544063871355/1125899906842624)), (61425/2251799813685248), by norm_num⟩
  | 4 => ⟨((1303693910851323/2251799813685248), (-107577299079303/562949953421312)), (54967/1125899906842624), by norm_num⟩
  | 5 => ⟨((84068963388287/281474976710656), (-498260525303063/2251799813685248)), (169311/2251799813685248), by norm_num⟩
  | 6 => ⟨((45310921160959/1125899906842624), (-595267776184469/4503599627370496)), (176065/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-8115797189/1073741824)), (1/4294967296), by norm_num⟩, -1, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-8723240287/4294967296), (-33311873847/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((57787018397879/4503599627370496), (-73504574327811/562949953421312)), (359833/4503599627370496), by norm_num⟩
  | 1 => ⟨((-9551400561/274877906944), (97194373677/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((1616604513/34359738368), (-65801810795/137438953472)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-11674256471/274877906944), (118796404637/274877906944)), (41/137438953472), by norm_num⟩
  | 4 => ⟨((3951809073/137438953472), (-80426656867/274877906944)), (57/274877906944), by norm_num⟩
  | 5 => ⟨((-2140339471/137438953472), (87119769721/549755813888)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((3864097823/549755813888), (-78641569971/1099511627776)), (15/274877906944), by norm_num⟩
  | 7 => ⟨((-5979526221/2199023255552), (60847234107/2199023255552)), (95/4398046511104), by norm_num⟩
  | 8 => ⟨((8096428593/8796093022208), (-10298585285/1099511627776)), (33/4398046511104), by norm_num⟩
  | 9 => ⟨((-4872341129/17592186044416), (6052319/2147483648)), (41/17592186044416), by norm_num⟩
  | 10 => ⟨((10555635499/140737488355328), (-53706698539/70368744177664)), (91/140737488355328), by norm_num⟩
  | 11 => ⟨((-10394614849/562949953421312), (6610928899/35184372088832)), (23/140737488355328), by norm_num⟩
  | 12 => ⟨((9383046277/2251799813685248), (-47740606225/1125899906842624)), (85/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (-479634545307/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444708378175473/158456325028528675187087900672), (-283831687233/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889814567177317/39614081257132168796771975168), (-2554028196747/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944797017931591/1237940039285380274899124224), (-1356546208105/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771260117355115/154742504910672534362390528), (-2712459728029/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549618337551915/9671406556917033397649408), (-1271129468205/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258845303474417/604462909807314587353088), (-2223804704849/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471970929540271/18889465931478580854784), (-903105827951/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40550247367467/147573952589676412928), (-2708215979241/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621541775254033/590295810358705651712), (-3722007799229/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823590981330237/73786976294838206464), (-1162456835641/18446744073709551616)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822786809310067/9223372036854775808), (-5227369647385/9223372036854775808)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398508517796961/288230376151711744), (-5222765298439/1152921504606846976)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((298655387505991/36028797018963968), (-4564744267967/144115188075855872)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((745847897888837/18014398509481984), (-6836776969059/36028797018963968)), (551/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489325814065911/9007199254740992), (-8527902615739/9007199254740992)), (1379/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114034918419389/2251799813685248), (-17001700988775/4503599627370496)), (2763/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216250325343683/2251799813685248), (-12683822906655/1125899906842624)), (65/35184372088832), by norm_num⟩
  | 0 => ⟨((1090441701133959/1125899906842624), (-50197794830577/2251799813685248)), (131/35184372088832), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1090441701133959/1125899906842624), (-50197794830577/2251799813685248)), (499725476014603/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1055540676127417/1125899906842624), (-48616904980239/1125899906842624)), (8307/1125899906842624), by norm_num⟩
  | 2 => ⟨((30858718788875/35184372088832), (-45578759214905/562949953421312)), (32587/2251799813685248), by norm_num⟩
  | 3 => ⟨((1717390824629857/2251799813685248), (-159900777516509/1125899906842624)), (62439/2251799813685248), by norm_num⟩
  | 4 => ⟨((632196119881031/1125899906842624), (-487809132035779/2251799813685248)), (56489/1125899906842624), by norm_num⟩
  | 5 => ⟨((604285504600909/2251799813685248), (-273906267014781/1125899906842624)), (175825/2251799813685248), by norm_num⟩
  | 6 => ⟨((57787018397879/4503599627370496), (-73504574327811/562949953421312)), (359833/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-33311873847/4294967296)), (1/4294967296), by norm_num⟩, -1, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile006Terms1
