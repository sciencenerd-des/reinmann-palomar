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
namespace Reinmann.XiRectangle.Tile002Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-28311023105/17179869184), (-41581815185/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-650910274826611/4503599627370496), (-286145142281585/2251799813685248)), (306089/4503599627370496), by norm_num⟩
  | 1 => ⟨((10911529949/34359738368), (9593584279/34359738368)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((-47950163561/137438953472), (-42158518325/137438953472)), (7/34359738368), by norm_num⟩
  | 3 => ⟨((35119092621/137438953472), (61754488405/274877906944)), (11/68719476736), by norm_num⟩
  | 4 => ⟨((-1205695835/8589934592), (-33922119921/274877906944)), (13/137438953472), by norm_num⟩
  | 5 => ⟨((67819123749/1099511627776), (59627612485/1099511627776)), (3/68719476736), by norm_num⟩
  | 6 => ⟨((-24835640919/1099511627776), (-5458968985/274877906944)), (37/2199023255552), by norm_num⟩
  | 7 => ⟨((31182560355/4398046511104), (27416184733/4398046511104)), (49/8796093022208), by norm_num⟩
  | 8 => ⟨((-17128771999/8796093022208), (-1882484841/1099511627776)), (7/4398046511104), by norm_num⟩
  | 9 => ⟨((66908015673/140737488355328), (58826552307/140737488355328)), (29/70368744177664), by norm_num⟩
  | 10 => ⟨((-58804774583/562949953421312), (-12925514653/140737488355328)), (53/562949953421312), by norm_num⟩
  | 11 => ⟨((46984471265/2251799813685248), (20654733433/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 12 => ⟨((-4301476459/1125899906842624), (-15127695979/4503599627370496)), (67/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677669/5070602400912917605986812821504), (-3152815445341/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444854913878729/158456325028528675187087900672), (-466727589863/79228162514264337593543950336)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236309199611923/4951760157141521099596496896), (-2099960481915/19807040628566084398385987584)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890293776605479/2475880078570760549798248448), (-4461663801225/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221494915023491/19342813113834066795298816), (-2230408773505/77371252455336267181195264)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550273268904793/9671406556917033397649408), (-1045279342673/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629708898679647/302231454903657293676544), (-914394673307/151115727451828646838272)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888812950546987/75557863725914323419136), (-5941879896409/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298303904183017/4722366482869645213696), (-1113733820967/1180591620717411303424)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622497239567345/590295810358705651712), (-6123140022049/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824783033836717/73786976294838206464), (-7650331553489/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228015592395299/1152921504606846976), (-8601682810917/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595368093828801/1152921504606846976), (-4297754420431/576460752303423488)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195784430146489/144115188075855872), (-7514126261895/144115188075855872)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((373357837847193/9007199254740992), (-1407163227135/4503599627370496)), (277/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491479953866435/9007199254740992), (-7023672947053/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 2 => ⟨((69760385479841/140737488355328), (-7005468098627/1125899906842624)), (697/2251799813685248), by norm_num⟩
  | 1 => ⟨((555632521411349/562949953421312), (-10462725040659/562949953421312)), (1051/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096494880388767/1125899906842624), (-41487507343363/1125899906842624)), (2127/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096494880388767/1125899906842624), (-41487507343363/1125899906842624)), (8113865378951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533164538942015/562949953421312), (-80807963701959/1125899906842624)), (1075/281474976710656), by norm_num⟩
  | 2 => ⟨((502055186465777/562949953421312), (-9566556593565/70368744177664)), (8763/1125899906842624), by norm_num⟩
  | 3 => ⟨((437342951069087/562949953421312), (-273015493486223/1125899906842624)), (9007/562949953421312), by norm_num⟩
  | 4 => ⟨((613320920908707/1125899906842624), (-212099496381853/562949953421312)), (18363/562949953421312), by norm_num⟩
  | 5 => ⟨((5446137056957/35184372088832), (-462154966545793/1125899906842624)), (67687/1125899906842624), by norm_num⟩
  | 6 => ⟨((-650910274826611/4503599627370496), (-286145142281585/2251799813685248)), (306089/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/17179869184), (-41581815185/17179869184)), (1/8589934592), by norm_num⟩, 0, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-43575731299/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1286415884491/8796093022208), (-911203512413681/9007199254740992)), (282047/4503599627370496), by norm_num⟩
  | 1 => ⟨((46282531859/137438953472), (32014825811/137438953472)), (11/68719476736), by norm_num⟩
  | 2 => ⟨((-26642366981/68719476736), (-36858430333/137438953472)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((20448772351/68719476736), (28289890745/137438953472)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((-47085038385/274877906944), (-8142485089/68719476736)), (7/68719476736), by norm_num⟩
  | 5 => ⟨((43366922995/549755813888), (29998023657/549755813888)), (7/137438953472), by norm_num⟩
  | 6 => ⟨((-66570686945/2199023255552), (-46048668061/2199023255552)), (45/2199023255552), by norm_num⟩
  | 7 => ⟨((43795620397/4398046511104), (30294564751/4398046511104)), (31/4398046511104), by norm_num⟩
  | 8 => ⟨((-12605392833/4398046511104), (-34877906597/17592186044416)), (37/17592186044416), by norm_num⟩
  | 9 => ⟨((25799990781/35184372088832), (35693043469/70368744177664)), (5/8796093022208), by norm_num⟩
  | 10 => ⟨((-47525339337/281474976710656), (-16437253963/140737488355328)), (39/281474976710656), by norm_num⟩
  | 11 => ⟨((39793141053/1125899906842624), (55051892283/2251799813685248)), (17/562949953421312), by norm_num⟩
  | 12 => ⟨((-1908897779/281474976710656), (-42253888837/9007199254740992)), (27/4503599627370496), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-3303998107593/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779297030144391/633825300114114700748351602688), (-1956176803539/316912650057057350374175801344)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236291952925799/4951760157141521099596496896), (-2200354609241/19807040628566084398385987584)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890147151196841/2475880078570760549798248448), (-2337463751693/1237940039285380274899124224)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771812662679073/154742504910672534362390528), (-2336999099879/77371252455336267181195264)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387533935856507/2417851639229258349412352), (-4380886002621/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314824357137171/151115727451828646838272), (-958072006831/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944308643774693/37778931862957161709568), (-3112808588895/37778931862957161709568)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649078550657693/2361183241434822606848), (-4667593555545/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811147647715913/295147905179352825856), (-6415310070217/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824530468709135/73786976294838206464), (-4007595789631/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823840418363175/9223372036854775808), (-9011665733235/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99692721409107/72057594037927936), (-1125610774721/144115188075855872)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195535189584403/144115188075855872), (-3935825227231/72057594037927936)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493056976925723/36028797018963968), (-11792230785631/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491011093150291/9007199254740992), (-7356810654375/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115695980375675/2251799813685248), (-1834205433617/281474976710656)), (697/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110556488591033/1125899906842624), (-21910601409617/1125899906842624)), (263/281474976710656), by norm_num⟩
  | 0 => ⟨((1095064937030181/1125899906842624), (-43422237142695/1125899906842624)), (2131/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095064937030181/1125899906842624), (-43422237142695/1125899906842624)), (8129124168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531699895504917/562949953421312), (-42233034298511/562949953421312)), (2155/562949953421312), by norm_num⟩
  | 2 => ⟨((249508102795453/281474976710656), (-39888625599669/281474976710656)), (8789/1125899906842624), by norm_num⟩
  | 3 => ⟨((862075792559207/1125899906842624), (-282868066292723/1125899906842624)), (9037/562949953421312), by norm_num⟩
  | 4 => ⟨((1178009386372737/2251799813685248), (-433171209904141/1125899906842624)), (4595/140737488355328), by norm_num⟩
  | 5 => ⟨((141477257914025/1125899906842624), (-56652432875283/140737488355328)), (133495/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1286415884491/8796093022208), (-911203512413681/9007199254740992)), (282047/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-43575731299/17179869184)), (1/8589934592), by norm_num⟩, 0, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-45379447825/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-40892628178589/281474976710656), (-357572823841365/4503599627370496)), (260671/4503599627370496), by norm_num⟩
  | 1 => ⟨((47879023341/137438953472), (26166448485/137438953472)), (21/137438953472), by norm_num⟩
  | 2 => ⟨((-14351110467/34359738368), (-7843050391/34359738368)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((45883279931/137438953472), (6268937819/34359738368)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((-55011650023/274877906944), (-30064512723/274877906944)), (15/137438953472), by norm_num⟩
  | 5 => ⟨((52764870215/549755813888), (28836621175/549755813888)), (31/549755813888), by norm_num⟩
  | 6 => ⟨((-84349755239/2199023255552), (-46098131733/2199023255552)), (13/549755813888), by norm_num⟩
  | 7 => ⟨((57789108385/4398046511104), (31582426333/4398046511104)), (19/2199023255552), by norm_num⟩
  | 8 => ⟨((-17321528727/4398046511104), (-9466418851/4398046511104)), (3/1099511627776), by norm_num⟩
  | 9 => ⟨((36920188313/35184372088832), (2522164557/4398046511104)), (53/70368744177664), by norm_num⟩
  | 10 => ⟨((-70824596021/281474976710656), (-19353236699/140737488355328)), (53/281474976710656), by norm_num⟩
  | 11 => ⟨((3859771909/70368744177664), (33750570759/1125899906842624)), (3/70368744177664), by norm_num⟩
  | 12 => ⟨((-24680876839/2251799813685248), (-13488389013/2251799813685248)), (5/562949953421312), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-215047466313/633825300114114700748351602688)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889593043083175/316912650057057350374175801344), (-4073816048161/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945105396387593/19807040628566084398385987584), (-2291148317641/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945007245835345/1237940039285380274899124224), (-4867794385465/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221459996606029/19342813113834066795298816), (-4866786610853/154742504910672534362390528)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387502828638147/2417851639229258349412352), (-2280770886235/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78699282573393/37778931862957161709568), (-249392404465/37778931862957161709568)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236055031619885/9444732965739290427392), (-1620548845829/18889465931478580854784)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298024272878647/4722366482869645213696), (-4859890500375/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622112571215061/590295810358705651712), (-6679496261035/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824301936089981/73786976294838206464), (-8345091233057/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823583144592461/9223372036854775808), (-4691172489503/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199353256418867/144115188075855872), (-1171874162927/144115188075855872)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195309641276935/144115188075855872), (-2048712694437/36028797018963968)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((186589771270227/4503599627370496), (-12275745144291/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490586743278585/9007199254740992), (-7657882517427/4503599627370496)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((139408797572387/281474976710656), (-15272416382013/2251799813685248)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((554957503335303/562949953421312), (-1425021526245/70368744177664)), (527/562949953421312), by norm_num⟩
  | 0 => ⟨((1093769898889203/1125899906842624), (-22584061289533/562949953421312)), (1067/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093769898889203/1125899906842624), (-22584061289533/562949953421312)), (4070284129905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((530372382642765/562949953421312), (-87758303497623/1125899906842624)), (4319/1125899906842624), by norm_num⟩
  | 2 => ⟨((248129947088643/281474976710656), (-165359567897103/1125899906842624)), (2203/281474976710656), by norm_num⟩
  | 3 => ⟨((212663607519545/281474976710656), (-36442547497825/140737488355328)), (9063/562949953421312), by norm_num⟩
  | 4 => ⟨((1134411971028787/2251799813685248), (-220268350917929/562949953421312)), (36777/1125899906842624), by norm_num⟩
  | 5 => ⟨((226752029311219/2251799813685248), (-1775469045526765/4503599627370496)), (65835/1125899906842624), by norm_num⟩
  | 6 => ⟨((-40892628178589/281474976710656), (-357572823841365/4503599627370496)), (260671/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-45379447825/17179869184)), (1/8589934592), by norm_num⟩, 0, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-47026112001/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1284386053100767/9007199254740992), (-274785480208881/4503599627370496)), (241631/4503599627370496), by norm_num⟩
  | 1 => ⟨((12174909379/34359738368), (10418949387/68719476736)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((-60507026553/137438953472), (-3236264577/17179869184)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((25059052107/68719476736), (21444840981/137438953472)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((-31134702609/137438953472), (-26644213979/274877906944)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((30946731821/274877906944), (13241676899/274877906944)), (33/549755813888), by norm_num⟩
  | 6 => ⟨((-6408311641/137438953472), (-10968110327/549755813888)), (29/1099511627776), by norm_num⟩
  | 7 => ⟨((72795685535/4398046511104), (31148263185/4398046511104)), (11/1099511627776), by norm_num⟩
  | 8 => ⟨((-90445241531/17592186044416), (-38700263159/17592186044416)), (57/17592186044416), by norm_num⟩
  | 9 => ⟨((49943996027/35184372088832), (21370342505/35184372088832)), (33/35184372088832), by norm_num⟩
  | 10 => ⟨((-24821233569/70368744177664), (-1327582655/8796093022208)), (17/70368744177664), by norm_num⟩
  | 11 => ⟨((44857053347/562949953421312), (19193710357/562949953421312)), (1/17592186044416), by norm_num⟩
  | 12 => ⟨((-74310393435/4503599627370496), (-31796385667/4503599627370496)), (55/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-1782806397357/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779084789113581/633825300114114700748351602688), (-2110593181619/316912650057057350374175801344)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890096816065173/39614081257132168796771975168), (-593504179439/4951760157141521099596496896)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889893365849419/2475880078570760549798248448), (-5043823596379/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442889704578089/38685626227668133590597632), (-1260685352609/38685626227668133590597632)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387474425426753/2417851639229258349412352), (-4726420344775/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157386134939049/75557863725914323419136), (-1033617045201/151115727451828646838272)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888278603315293/75557863725914323419136), (-839544435201/9444732965739290427392)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297902985918519/4722366482869645213696), (-5035380940355/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621945721021711/590295810358705651712), (-6920585004901/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824093252734715/73786976294838206464), (-8646136322947/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227918526311949/1152921504606846976), (-4860293275141/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797295455691381/576460752303423488), (-9712692369437/1152921504606846976)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298775915818195/36028797018963968), (-8489727402169/144115188075855872)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((746204372385415/18014398509481984), (-12716840617797/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490199165384431/9007199254740992), (-15865001796151/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((557440810230771/1125899906842624), (-15818457255499/2251799813685248)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((277332238213131/281474976710656), (-23611426555771/1125899906842624)), (1055/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092586387247391/1125899906842624), (-46758434255027/1125899906842624)), (1069/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1092586387247391/1125899906842624), (-46758434255027/1125899906842624)), (4077913524436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1058316689772031/1125899906842624), (-90749858749541/1125899906842624)), (541/140737488355328), by norm_num⟩
  | 2 => ⟨((246868898431833/281474976710656), (-1332851747153/8796093022208)), (8835/1125899906842624), by norm_num⟩
  | 3 => ⟨((420109269202417/562949953421312), (-9351869112851/35184372088832)), (71/4398046511104), by norm_num⟩
  | 4 => ⟨((1094965464847003/2251799813685248), (-893307264658799/2251799813685248)), (36791/1125899906842624), by norm_num⟩
  | 5 => ⟨((356116469748915/4503599627370496), (-868763376170213/2251799813685248)), (64971/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1284386053100767/9007199254740992), (-274785480208881/4503599627370496)), (241631/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-47026112001/17179869184)), (1/8589934592), by norm_num⟩, 0, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-33049120819/17179869184), (-48540896203/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1250426148797821/9007199254740992), (-204514480222085/4503599627370496)), (224501/4503599627370496), by norm_num⟩
  | 1 => ⟨((48939205123/137438953472), (8004292063/68719476736)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((-7845411421/17179869184), (-2566325473/17179869184)), (13/68719476736), by norm_num⟩
  | 3 => ⟨((26830777311/68719476736), (17553319661/137438953472)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((-33603313/134217728), (-22511687993/274877906944)), (33/274877906944), by norm_num⟩
  | 5 => ⟨((17651875039/137438953472), (23096535861/549755813888)), (9/137438953472), by norm_num⟩
  | 6 => ⟨((-60368220719/1099511627776), (-1234196767/68719476736)), (33/1099511627776), by norm_num⟩
  | 7 => ⟨((22120204135/1099511627776), (14471552935/2199023255552)), (25/2199023255552), by norm_num⟩
  | 8 => ⟨((-56737203383/8796093022208), (-18559400201/8796093022208)), (17/4398046511104), by norm_num⟩
  | 9 => ⟨((16169783707/8796093022208), (10578649249/17592186044416)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((-4147467633/8796093022208), (-21706959675/140737488355328)), (11/35184372088832), by norm_num⟩
  | 11 => ⟨((7736759593/70368744177664), (20246273553/562949953421312)), (43/562949953421312), by norm_num⟩
  | 12 => ⟨((-6614798849/281474976710656), (-8655111057/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418217/10141204801825835211973625643008), (-1840233364015/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222373949223241/79228162514264337593543950336), (-136147681431/19807040628566084398385987584)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944995977396547/19807040628566084398385987584), (-4900463201377/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944890963220565/1237940039285380274899124224), (-2602858651861/1237940039285380274899124224)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885723675803417/77371252455336267181195264), (-5204564329095/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774896586353839/4835703278458516698824704), (-1219513531909/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258997587720487/604462909807314587353088), (-4267072548163/604462909807314587353088)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236016234378703/9444732965739290427392), (-3465848307609/37778931862957161709568)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324447848110583/1180591620717411303424), (-5196763470547/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202724025421495/73786976294838206464), (-3571142815979/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823901241058429/73786976294838206464), (-8922961654427/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227891505034783/1152921504606846976), (-2507900512369/2305843009213693952)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797187272791039/576460752303423488), (-5011595902907/576460752303423488)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((597457062110673/72057594037927936), (-8760834094667/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((746062000438375/18014398509481984), (-13122340672193/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489842479629779/9007199254740992), (-16369848350737/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1114523812684935/2251799813685248), (-4080065995515/562949953421312)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((554394738671755/562949953421312), (-24356547478951/1125899906842624)), (33/35184372088832), by norm_num⟩
  | 0 => ⟨((545748313580943/562949953421312), (-48218382699219/1125899906842624)), (2141/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((545748313580943/562949953421312), (-48218382699219/1125899906842624)), (8167271140670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056079556849849/1125899906842624), (-46745009714931/562949953421312)), (271/70368744177664), by norm_num⟩
  | 2 => ⟨((982825950990909/1125899906842624), (-21923107393767/140737488355328)), (8855/1125899906842624), by norm_num⟩
  | 3 => ⟨((830612912780701/1125899906842624), (-306195586190297/1125899906842624)), (18219/1125899906842624), by norm_num⟩
  | 4 => ⟨((264749144329999/562949953421312), (-225890424344503/562949953421312)), (73583/2251799813685248), by norm_num⟩
  | 5 => ⟨((67734708909935/1125899906842624), (-1699740339448327/4503599627370496)), (128263/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1250426148797821/9007199254740992), (-204514480222085/4503599627370496)), (224501/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-33049120819/17179869184), (-48540896203/17179869184)), (1/8589934592), by norm_num⟩, 0, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-34003994769/17179869184), (-49943367317/17179869184)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1210433853383521/9007199254740992), (-36146810187381/1125899906842624)), (209117/9007199254740992), by norm_num⟩
  | 1 => ⟨((97485483789/274877906944), (23289429777/274877906944)), (19/274877906944), by norm_num⟩
  | 2 => ⟨((-64317445131/137438953472), (-15365535089/137438953472)), (7/68719476736), by norm_num⟩
  | 3 => ⟨((56579141665/137438953472), (13516842667/137438953472)), (7/68719476736), by norm_num⟩
  | 4 => ⟨((-74657799257/274877906944), (-17835861357/274877906944)), (21/274877906944), by norm_num⟩
  | 5 => ⟨((78810484937/549755813888), (9413972129/274877906944)), (3/68719476736), by norm_num⟩
  | 6 => ⟨((-69328462641/1099511627776), (-16562674765/1099511627776)), (23/1099511627776), by norm_num⟩
  | 7 => ⟨((6534349553/274877906944), (24977056135/4398046511104)), (37/4398046511104), by norm_num⟩
  | 8 => ⟨((-68978092329/8796093022208), (-8239485383/4398046511104)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((20226348905/8796093022208), (19328421593/35184372088832)), (17/17592186044416), by norm_num⟩
  | 10 => ⟨((-85405590927/140737488355328), (-10201762535/70368744177664)), (19/70368744177664), by norm_num⟩
  | 11 => ⟨((81960091173/562949953421312), (19580389959/562949953421312)), (39/562949953421312), by norm_num⟩
  | 12 => ⟨((-72099126449/2251799813685248), (-8612295273/1125899906842624)), (9/562949953421312), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987295/10141204801825835211973625643008), (-1893402430471/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778905298930255/633825300114114700748351602688), (-4482191717011/633825300114114700748351602688)), (23/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944947428719077/19807040628566084398385987584), (-5041562664185/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889678737325167/2475880078570760549798248448), (-5355575455331/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221418017058113/19342813113834066795298816), (-669294368049/19342813113834066795298816)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387424095224811/2417851639229258349412352), (-2509205540797/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629456433659939/302231454903657293676544), (-548726643195/75557863725914323419136)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943996076391513/37778931862957161709568), (-7131015601023/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162211006963249/590295810358705651712), (-5346135058111/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405412510582135/147573952589676412928), (-3673740211551/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227965428814777/9223372036854775808), (-1147396063143/9223372036854775808)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822931853725193/9223372036854775808), (-2579860187585/2305843009213693952)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398543543166293/288230376151711744), (-10310538181689/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194738589297013/144115188075855872), (-9011708560399/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((372965070958863/9007199254740992), (-3374386444779/9007199254740992)), (139/18014398509481984), by norm_num⟩
  | 3 => ⟨((93094507093587/562949953421312), (-1052307477283/562949953421312)), (87/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114192378409803/2251799813685248), (-16784435520157/2251799813685248)), (351/2251799813685248), by norm_num⟩
  | 1 => ⟨((554144848032425/562949953421312), (-12522782835525/562949953421312)), (529/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090486787117591/1125899906842624), (-24783762501169/562949953421312)), (67/70368744177664), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090486787117591/1125899906842624), (-24783762501169/562949953421312)), (255584985232331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1054005321548591/1125899906842624), (-96016938551405/1125899906842624)), (543/281474976710656), by norm_num⟩
  | 2 => ⟨((489256619824003/562949953421312), (-179771511795907/1125899906842624)), (2219/562949953421312), by norm_num⟩
  | 3 => ⟨((821716351596047/1125899906842624), (-312476807813469/1125899906842624)), (2283/281474976710656), by norm_num⟩
  | 4 => ⟨((512990545206391/1125899906842624), (-912220707771151/2251799813685248)), (18399/1125899906842624), by norm_num⟩
  | 5 => ⟨((195834973302757/4503599627370496), (-1662530018464575/4503599627370496)), (63347/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1210433853383521/9007199254740992), (-36146810187381/1125899906842624)), (209117/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34003994769/17179869184), (-49943367317/17179869184)), (1/17179869184), by norm_num⟩, 0, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-34892961149/17179869184), (-51249036687/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-583462144301081/4503599627370496), (-46632344562103/2251799813685248)), (389925/9007199254740992), by norm_num⟩
  | 1 => ⟨((96438279859/274877906944), (15415372323/274877906944)), (17/137438953472), by norm_num⟩
  | 2 => ⟨((-65289925791/137438953472), (-5218200265/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((117872264445/274877906944), (4710382759/68719476736)), (47/274877906944), by norm_num⟩
  | 4 => ⟨((-39900501179/137438953472), (-6377976489/137438953472)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((86442048193/549755813888), (13817504411/549755813888)), (39/549755813888), by norm_num⟩
  | 6 => ⟨((-78029801997/1099511627776), (-6236415933/549755813888)), (37/1099511627776), by norm_num⟩
  | 7 => ⟨((60373891711/2199023255552), (4825293549/1099511627776)), (15/1099511627776), by norm_num⟩
  | 8 => ⟨((-40873882397/4398046511104), (-6533568583/4398046511104)), (43/8796093022208), by norm_num⟩
  | 9 => ⟨((98389800395/35184372088832), (1965914635/4398046511104)), (27/17592186044416), by norm_num⟩
  | 10 => ⟨((-53288903749/70368744177664), (-2129518209/17592186044416)), (61/140737488355328), by norm_num⟩
  | 11 => ⟨((104952019283/562949953421312), (16776268259/562949953421312)), (63/562949953421312), by norm_num⟩
  | 12 => ⟨((-47369222821/1125899906842624), (-15143658877/2251799813685248)), (59/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (-1942901647111/5070602400912917605986812821504)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778824952166353/633825300114114700748351602688), (-4598976933775/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472451113119793/9903520314283042199192993792), (-1293224632233/9903520314283042199192993792)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472395664974921/618970019642690137449562112), (-5495062394457/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885624017080127/77371252455336267181195264), (-2746888641857/77371252455336267181195264)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549606258593547/9671406556917033397649408), (-5149050896713/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258833983951175/604462909807314587353088), (-2252027183095/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887863917993523/75557863725914323419136), (-7316528948689/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297591836556039/4722366482869645213696), (-5485157534677/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621517671202855/590295810358705651712), (-3769226751027/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823557862224429/73786976294838206464), (-9417610687583/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822745446358277/9223372036854775808), (-5293655673209/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199248448405607/144115188075855872), (-10577937883681/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((597287563881623/72057594037927936), (-577822112019/9007199254740992)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491614695496585/36028797018963968), (-3461663809277/9007199254740992)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((744602220359777/4503599627370496), (-17271455692285/9007199254740992)), (697/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113883685998681/2251799813685248), (-4304049570261/562949953421312)), (175/562949953421312), by norm_num⟩
  | 1 => ⟨((1107824148136109/1125899906842624), (-25686286676793/1125899906842624)), (1057/1125899906842624), by norm_num⟩
  | 0 => ⟨((1089545891660501/1125899906842624), (-50821335942143/1125899906842624)), (1073/562949953421312), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1089545891660501/1125899906842624), (-50821335942143/1125899906842624)), (4093172313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1052071711391395/1125899906842624), (-12295093339989/140737488355328)), (1087/281474976710656), by norm_num⟩
  | 2 => ⟨((974491642415671/1125899906842624), (-91910975839363/562949953421312)), (8887/1125899906842624), by norm_num⟩
  | 3 => ⟨((406716194598207/562949953421312), (-79551012712045/281474976710656)), (18287/1125899906842624), by norm_num⟩
  | 4 => ⟨((497751558918931/1125899906842624), (-919575460519483/2251799813685248)), (73521/2251799813685248), by norm_num⟩
  | 5 => ⟨((32286935355349/1125899906842624), (-1626148527894481/4503599627370496)), (250109/4503599627370496), by norm_num⟩
  | 6 => ⟨((-583462144301081/4503599627370496), (-46632344562103/2251799813685248)), (389925/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-51249036687/17179869184)), (1/8589934592), by norm_num⟩, 0, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile002Terms1
