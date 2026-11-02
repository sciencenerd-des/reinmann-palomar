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
namespace Reinmann.XiRectangle.Tile015Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8931133415/4294967296), (-2541535427/134217728)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1121704141308639/9007199254740992), (-97110348934063/9007199254740992)), (294609/4503599627370496), by norm_num⟩
  | 1 => ⟨((-94910408077/274877906944), (1027096017/34359738368)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((16446720441/34359738368), (-5695429667/137438953472)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((-121599977633/274877906944), (10527389375/274877906944)), (73/274877906944), by norm_num⟩
  | 4 => ⟨((21071670413/68719476736), (-912128783/34359738368)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-93476921193/549755813888), (4046332763/274877906944)), (15/137438953472), by norm_num⟩
  | 6 => ⟨((86391019163/1099511627776), (-7479211057/1099511627776)), (57/1099511627776), by norm_num⟩
  | 7 => ⟨((-68436218695/2199023255552), (740599151/274877906944)), (47/2199023255552), by norm_num⟩
  | 8 => ⟨((94872744073/8796093022208), (-8213507415/8796093022208)), (67/8796093022208), by norm_num⟩
  | 9 => ⟨((-58454022281/17592186044416), (10121190235/35184372088832)), (85/35184372088832), by norm_num⟩
  | 10 => ⟨((32413792589/35184372088832), (-1403094895/17592186044416)), (49/70368744177664), by norm_num⟩
  | 11 => ⟨((-32680042101/140737488355328), (5658480119/281474976710656)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((30202772057/562949953421312), (-10459092109/2251799813685248)), (99/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326629/10141204801825835211973625643008), (-112491740973/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778761642161177/633825300114114700748351602688), (-133127067407/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889733883387745/39614081257132168796771975168), (-149740787013/39614081257132168796771975168)), (811/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889508530142525/2475880078570760549798248448), (-159065847607/2475880078570760549798248448)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885587429924797/77371252455336267181195264), (-79513953045/77371252455336267181195264)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774769336105887/4835703278458516698824704), (-74524180953/4835703278458516698824704)), (101/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314693964924013/151115727451828646838272), (-65188515513/302231454903657293676544)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887771365509507/75557863725914323419136), (-211787170453/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297524082696763/4722366482869645213696), (-79387170797/2361183241434822606848)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810713602578803/295147905179352825856), (-218207468133/590295810358705651712)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823448818024831/73786976294838206464), (-136299279057/36893488147419103232)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822628316401333/9223372036854775808), (-306452472279/9223372036854775808)), (833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593877376297041/1152921504606846976), (-306176584347/1152921504606846976)), (833/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194486460652773/144115188075855872), (-66898618161/36028797018963968)), (729/72057594037927936), by norm_num⟩
  | 4 => ⟨((745748594386847/18014398509481984), (-200386234409/18014398509481984)), (2187/36028797018963968), by norm_num⟩
  | 3 => ⟨((186135572450513/1125899906842624), (-31242737293/562949953421312)), (2733/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227608348817919/4503599627370496), (-996529735531/4503599627370496)), (5467/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215610224639803/2251799813685248), (-1486726183403/2251799813685248)), (8201/2251799813685248), by norm_num⟩
  | 0 => ⟨((272476226060915/281474976710656), (-367666943759/281474976710656)), (8205/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((272476226060915/281474976710656), (-367666943759/281474976710656)), (31299595359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2110117480623823/2251799813685248), (-711825274513/281474976710656)), (31815/2251799813685248), by norm_num⟩
  | 2 => ⟨((1977335341480949/2251799813685248), (-5336300130309/1125899906842624)), (59789/2251799813685248), by norm_num⟩
  | 3 => ⟨((434068464313737/562949953421312), (-292867253793/35184372088832)), (105571/2251799813685248), by norm_num⟩
  | 4 => ⟨((669308073061465/1125899906842624), (-28904750957215/2251799813685248)), (82281/1125899906842624), by norm_num⟩
  | 5 => ⟨((1590778799383503/4503599627370496), (-34365724782317/2251799813685248)), (99939/1125899906842624), by norm_num⟩
  | 6 => ⟨((1121704141308639/9007199254740992), (-97110348934063/9007199254740992)), (294609/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/4294967296), (-2541535427/134217728)), (1/2147483648), by norm_num⟩, -3, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9126418991/4294967296), (-83107452941/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((471970369405639/4503599627370496), (-516174705587709/9007199254740992)), (793727/9007199254740992), by norm_num⟩
  | 1 => ⟨((-81615768347/274877906944), (44629915275/274877906944)), (71/274877906944), by norm_num⟩
  | 2 => ⟨((57808720991/137438953472), (-31611517875/137438953472)), (13/34359738368), by norm_num⟩
  | 3 => ⟨((-27297406619/68719476736), (14927029045/68719476736)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((77339376691/274877906944), (-42291457877/274877906944)), (37/137438953472), by norm_num⟩
  | 5 => ⟨((-10955947703/68719476736), (23964144559/274877906944)), (87/549755813888), by norm_num⟩
  | 6 => ⟨((82774765943/1099511627776), (-45263689429/1099511627776)), (85/1099511627776), by norm_num⟩
  | 7 => ⟨((-8375663265/274877906944), (9160120635/549755813888)), (71/2199023255552), by norm_num⟩
  | 8 => ⟨((47460081855/4398046511104), (-1622036001/274877906944)), (13/1099511627776), by norm_num⟩
  | 9 => ⟨((-59762016543/17592186044416), (8169909409/4398046511104)), (67/17592186044416), by norm_num⟩
  | 10 => ⟨((67727417095/70368744177664), (-9258838543/17592186044416)), (39/35184372088832), by norm_num⟩
  | 11 => ⟨((-69776807953/281474976710656), (4769502711/35184372088832)), (41/140737488355328), by norm_num⟩
  | 12 => ⟨((65897527799/1125899906842624), (-36034716601/1125899906842624)), (79/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572619/10141204801825835211973625643008), (-162958619023/2535301200456458802993406410752)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778691243331369/633825300114114700748351602688), (-771348187231/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944827340881777/19807040628566084398385987584), (-867605897189/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889424373669063/2475880078570760549798248448), (-921631496361/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771090698049617/154742504910672534362390528), (-921406841037/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96841235304727/604462909807314587353088), (-863580293307/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314676702535095/151115727451828646838272), (-377697111065/302231454903657293676544)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887659149438737/75557863725914323419136), (-613534270339/37778931862957161709568)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648719955722217/2361183241434822606848), (-919910400857/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621311454785013/590295810358705651712), (-1264241759401/590295810358705651712)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911652053896141/36893488147419103232), (-394837558147/18446744073709551616)), (1483/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113904092931839/576460752303423488), (-1775461025325/9223372036854775808)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796857254454653/576460752303423488), (-443456873239/288230376151711744)), (1669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194343909336431/144115188075855872), (-775131662501/72057594037927936)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491283277795327/36028797018963968), (-1160864250251/18014398509481984)), (2191/36028797018963968), by norm_num⟩
  | 3 => ⟨((744408522722927/4503599627370496), (-1447877726379/4503599627370496)), (685/2251799813685248), by norm_num⟩
  | 2 => ⟨((2227072850460395/4503599627370496), (-1443085006293/1125899906842624)), (1371/1125899906842624), by norm_num⟩
  | 1 => ⟨((276850740479225/281474976710656), (-4305369357381/1125899906842624)), (8237/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089098562021467/1125899906842624), (-8515662281213/1125899906842624)), (16517/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1089098562021467/1125899906842624), (-8515662281213/1125899906842624)), (63007363326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106871408523751/2251799813685248), (-8237317978947/562949953421312)), (32205/2251799813685248), by norm_num⟩
  | 2 => ⟨((492697158353547/562949953421312), (-61657238364753/2251799813685248)), (7651/281474976710656), by norm_num⟩
  | 3 => ⟨((1723157715428323/2251799813685248), (-107925565850455/2251799813685248)), (27623/562949953421312), by norm_num⟩
  | 4 => ⟨((656724582376537/1125899906842624), (-165177002286735/2251799813685248)), (179697/2251799813685248), by norm_num⟩
  | 5 => ⟨((754003644545749/2251799813685248), (-385383450822603/4503599627370496)), (471987/4503599627370496), by norm_num⟩
  | 6 => ⟨((471970369405639/4503599627370496), (-516174705587709/9007199254740992)), (793727/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9126418991/4294967296), (-83107452941/4294967296)), (1/2147483648), by norm_num⟩, -3, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4655269565/2147483648), (-42392048477/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((648114748873515/9007199254740992), (-801439332333929/9007199254740992)), (121793/1125899906842624), by norm_num⟩
  | 1 => ⟨((-57168352235/274877906944), (70692676143/274877906944)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((41309447687/137438953472), (-25541014327/68719476736)), (33/68719476736), by norm_num⟩
  | 3 => ⟨((-310936617/1073741824), (24607675493/68719476736)), (65/137438953472), by norm_num⟩
  | 4 => ⟨((28759117321/137438953472), (-71125330273/274877906944)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((-33249816195/274877906944), (41115729179/274877906944)), (57/274877906944), by norm_num⟩
  | 6 => ⟨((16017388281/274877906944), (-39613247475/549755813888)), (7/68719476736), by norm_num⟩
  | 7 => ⟨((-13227487635/549755813888), (16356715963/549755813888)), (95/2199023255552), by norm_num⟩
  | 8 => ⟨((2389522293/274877906944), (-2954811867/274877906944)), (71/4398046511104), by norm_num⟩
  | 9 => ⟨((-49113655115/17592186044416), (60732478367/17592186044416)), (93/17592186044416), by norm_num⟩
  | 10 => ⟨((56782688669/70368744177664), (-8776972013/8796093022208)), (55/35184372088832), by norm_num⟩
  | 11 => ⟨((-59681119879/281474976710656), (73799889531/281474976710656)), (59/140737488355328), by norm_num⟩
  | 12 => ⟨((57500207793/1125899906842624), (-17775759703/281474976710656)), (29/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (-18130317703/158456325028528675187087900672)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444656118725111/158456325028528675187087900672), (-42905979081/19807040628566084398385987584)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889579542423111/39614081257132168796771975168), (-772161459179/19807040628566084398385987584)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236168063083173/309485009821345068724781056), (-1640480281477/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771010791453725/154742504910672534362390528), (-410018064799/38685626227668133590597632)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549384812534079/9671406556917033397649408), (-768567177493/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629320593485849/302231454903657293676544), (-1344559325245/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887552437114575/75557863725914323419136), (-2184096911449/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297359811941445/4722366482869645213696), (-818681257309/2361183241434822606848)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405300303018123/147573952589676412928), (-2250220040405/590295810358705651712)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911583072911201/36893488147419103232), (-2811045987025/73786976294838206464)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822310062076409/9223372036854775808), (-98751593695/288230376151711744)), (835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99597425793663/72057594037927936), (-1578541956247/576460752303423488)), (1671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597103685367749/72057594037927936), (-2759114004103/144115188075855872)), (1463/144115188075855872), by norm_num⟩
  | 4 => ⟨((372769465816215/9007199254740992), (-4132011038207/36028797018963968)), (2195/36028797018963968), by norm_num⟩
  | 3 => ⟨((744279610314741/4503599627370496), (-2576689393249/4503599627370496)), (2747/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226554050600213/4503599627370496), (-2567983034429/1125899906842624)), (5501/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214019917278589/2251799813685248), (-15321112619625/2251799813685248)), (4135/1125899906842624), by norm_num⟩
  | 0 => ⟨((2176594294622169/2251799813685248), (-15148373079971/1125899906842624)), (16617/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2176594294622169/2251799813685248), (-15148373079971/1125899906842624)), (63388833052825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((262936607517633/281474976710656), (-29284896657587/1125899906842624)), (8143/562949953421312), by norm_num⟩
  | 2 => ⟨((245428776855819/281474976710656), (-54712297829343/1125899906842624)), (62549/2251799813685248), by norm_num⟩
  | 3 => ⟨((1706672344087195/2251799813685248), (-95411481987831/1125899906842624)), (57579/1125899906842624), by norm_num⟩
  | 4 => ⟨((319335345554575/562949953421312), (-289255086757487/2251799813685248)), (194079/2251799813685248), by norm_num⟩
  | 5 => ⟨((1374840242995635/4503599627370496), (-656323870509259/4503599627370496)), (540091/4503599627370496), by norm_num⟩
  | 6 => ⟨((648114748873515/9007199254740992), (-801439332333929/9007199254740992)), (121793/1125899906842624), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-42392048477/2147483648)), (1/2147483648), by norm_num⟩, -3, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-592793865/268435456), (-86370066135/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75660472963171/2251799813685248), (-471171068497649/4503599627370496)), (1117197/9007199254740992), by norm_num⟩
  | 1 => ⟨((-13597268419/137438953472), (42338087767/137438953472)), (51/137438953472), by norm_num⟩
  | 2 => ⟨((5004540893/34359738368), (-31165478981/68719476736)), (77/137438953472), by norm_num⟩
  | 3 => ⟨((-19647420371/137438953472), (61176567411/137438953472)), (77/137438953472), by norm_num⟩
  | 4 => ⟨((14462657595/137438953472), (-90065334849/274877906944)), (29/68719476736), by norm_num⟩
  | 5 => ⟨((-8516882553/137438953472), (6629797065/34359738368)), (35/137438953472), by norm_num⟩
  | 6 => ⟨((4179573495/137438953472), (-52056087739/549755813888)), (35/274877906944), by norm_num⟩
  | 7 => ⟨((-14064570417/1099511627776), (87586270767/2199023255552)), (15/274877906944), by norm_num⟩
  | 8 => ⟨((20706134681/4398046511104), (-32236553711/2199023255552)), (45/2199023255552), by norm_num⟩
  | 9 => ⟨((-27096866695/17592186044416), (84372058045/17592186044416)), (15/2199023255552), by norm_num⟩
  | 10 => ⟨((7978507051/17592186044416), (-12421418823/8796093022208)), (9/4398046511104), by norm_num⟩
  | 11 => ⟨((-8542628057/70368744177664), (3324919069/8796093022208)), (79/140737488355328), by norm_num⟩
  | 12 => ⟨((16768831357/562949953421312), (-52213446983/562949953421312)), (79/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-1641345609693/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222320120607609/79228162514264337593543950336), (-485504638281/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472377012631367/9903520314283042199192993792), (-2184348827829/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889268487010727/2475880078570760549798248448), (-290043464495/309485009821345068724781056)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442733677291553/38685626227668133590597632), (-2319759639347/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((387328354192881/2417851639229258349412352), (-1087075009397/4835703278458516698824704)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629289323561341/302231454903657293676544), (-1901756835195/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887450681445995/75557863725914323419136), (-1544592249305/37778931862957161709568)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((648641691478879/2361183241434822606848), (-289483095005/590295810358705651712)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405273985021485/147573952589676412928), (-3182651515523/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823034283063827/73786976294838206464), (-3975822074769/73786976294838206464)), (743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822161342097673/9223372036854775808), (-4469375289567/9223372036854775808)), (1673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593409625785585/1152921504606846976), (-4465098198901/1152921504606846976)), (837/576460752303423488), by norm_num⟩
  | 5 => ⟨((597038154153163/72057594037927936), (-3902154129403/144115188075855872)), (733/72057594037927936), by norm_num⟩
  | 4 => ⟨((93180014087877/2251799813685248), (-5843629924021/36028797018963968)), (275/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488310353889043/9007199254740992), (-7287762868337/9007199254740992)), (2753/9007199254740992), by norm_num⟩
  | 2 => ⟨((69564090331791/140737488355328), (-14525312709489/4503599627370496)), (5517/4503599627370496), by norm_num⟩
  | 1 => ⟨((276656465221143/281474976710656), (-10831411406439/1125899906842624)), (8301/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175004742587871/2251799813685248), (-42827372739829/2251799813685248)), (2089/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2175004742587871/2251799813685248), (-42827372739829/2251799813685248)), (7968903661632449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2100014138772337/2251799813685248), (-82733587822143/2251799813685248)), (32921/2251799813685248), by norm_num⟩
  | 2 => ⟨((1955420064310063/2251799813685248), (-154313632252701/2251799813685248)), (3989/140737488355328), by norm_num⟩
  | 3 => ⟨((421868643441775/562949953421312), (-67001509385877/562949953421312)), (29899/562949953421312), by norm_num⟩
  | 4 => ⟨((1232677604856873/2251799813685248), (-200840843498691/1125899906842624)), (207717/2251799813685248), by norm_num⟩
  | 5 => ⟨((1206275879047971/4503599627370496), (-879552466135893/4503599627370496)), (301523/2251799813685248), by norm_num⟩
  | 6 => ⟨((75660472963171/2251799813685248), (-471171068497649/4503599627370496)), (1117197/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-86370066135/4294967296)), (1/2147483648), by norm_num⟩, -3, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9649929107/4294967296), (-87874666929/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18834901011619/4503599627370496), (-475825051458915/4503599627370496)), (151751/1125899906842624), by norm_num⟩
  | 1 => ⟨((1721933619/137438953472), (43501112769/137438953472)), (113/274877906944), by norm_num⟩
  | 2 => ⟨((-5158452115/274877906944), (-65158843729/137438953472)), (43/68719476736), by norm_num⟩
  | 3 => ⟨((1287778457/68719476736), (130132300711/274877906944)), (87/137438953472), by norm_num⟩
  | 4 => ⟨((-3857839485/274877906944), (-24365095817/68719476736)), (33/68719476736), by norm_num⟩
  | 5 => ⟨((4622821701/549755813888), (29196521555/137438953472)), (161/549755813888), by norm_num⟩
  | 6 => ⟨((-1154061347/274877906944), (-116619949197/1099511627776)), (163/1099511627776), by norm_num⟩
  | 7 => ⟨((987788235/549755813888), (99817755871/2199023255552)), (71/1099511627776), by norm_num⟩
  | 8 => ⟨((-2959149095/4398046511104), (-9344602273/549755813888)), (27/1099511627776), by norm_num⟩
  | 9 => ⟨((3939919309/17592186044416), (49766980645/8796093022208)), (73/8796093022208), by norm_num⟩
  | 10 => ⟨((-1180294343/17592186044416), (-119270840061/70368744177664)), (177/70368744177664), by norm_num⟩
  | 11 => ⟨((5143048517/281474976710656), (16241068403/35184372088832)), (195/281474976710656), by norm_num⟩
  | 12 => ⟨((-2567866071/562949953421312), (-64871857029/562949953421312)), (197/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (-1048836419219/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778500396412429/633825300114114700748351602688), (-620445330129/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944719926318435/19807040628566084398385987584), (-2791453770495/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889195948959143/2475880078570760549798248448), (-2965239530003/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770862083687177/154742504910672534362390528), (-2964474652785/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549245237566073/9671406556917033397649408), (-2778382536865/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629259448790503/302231454903657293676544), (-607568132623/151115727451828646838272)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117959588420819/4722366482869645213696), (-3947670561351/75557863725914323419136)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324302570275697/1180591620717411303424), (-184963841369/295147905179352825856)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620995178653183/590295810358705651712), (-4067041927463/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911453981134637/36893488147419103232), (-5080560351823/73786976294838206464)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822018724748553/9223372036854775808), (-2855587758581/4611686018427387904)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398316594188189/288230376151711744), (-5705611342163/1152921504606846976)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((596975128330253/72057594037927936), (-2493078152867/72057594037927936)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490689735199973/36028797018963968), (-1866685601341/9007199254740992)), (551/9007199254740992), by norm_num⟩
  | 3 => ⟨((744034889749345/4503599627370496), (-2327900261553/2251799813685248)), (345/1125899906842624), by norm_num⟩
  | 2 => ⟨((2225562399454199/4503599627370496), (-2319732198015/562949953421312)), (1383/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106250388680481/1125899906842624), (-13836950851389/1125899906842624)), (2083/562949953421312), by norm_num⟩
  | 0 => ⟨((2173430908776419/2251799813685248), (-54699118627133/2251799813685248)), (8401/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173430908776419/2251799813685248), (-54699118627133/2251799813685248)), (32047276023482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096460747956155/2251799813685248), (-52795436958703/1125899906842624)), (33251/2251799813685248), by norm_num⟩
  | 2 => ⟨((1946886312194635/2251799813685248), (-196613501044699/2251799813685248)), (32517/1125899906842624), by norm_num⟩
  | 3 => ⟨((416523420623013/562949953421312), (-339980607201609/2251799813685248)), (123813/2251799813685248), by norm_num⟩
  | 4 => ⟨((73837640045725/140737488355328), (-251549688558411/1125899906842624)), (220605/2251799813685248), by norm_num⟩
  | 5 => ⟨((1014834679536057/4503599627370496), (-131975037883977/562949953421312)), (41257/281474976710656), by norm_num⟩
  | 6 => ⟨((-18834901011619/4503599627370496), (-475825051458915/4503599627370496)), (151751/1125899906842624), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-87874666929/4294967296)), (1/2147483648), by norm_num⟩, -3, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4903546613/2147483648), (-44652921347/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-334408550176003/9007199254740992), (-855111462722651/9007199254740992)), (1261897/9007199254740992), by norm_num⟩
  | 1 => ⟨((7767595935/68719476736), (79449647065/274877906944)), (119/274877906944), by norm_num⟩
  | 2 => ⟨((-23648620111/137438953472), (-30235779145/68719476736)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((11999792425/68719476736), (61369005353/137438953472)), (95/137438953472), by norm_num⟩
  | 4 => ⟨((-18266818643/137438953472), (-93419656889/274877906944)), (147/274877906944), by norm_num⟩
  | 5 => ⟨((11122747845/137438953472), (56883648305/274877906944)), (91/274877906944), by norm_num⟩
  | 6 => ⟨((-11287818461/274877906944), (-14431961967/137438953472)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((19637723759/1099511627776), (25107675445/549755813888)), (21/274877906944), by norm_num⟩
  | 8 => ⟨((-29893745305/4398046511104), (-19110220313/1099511627776)), (65/2199023255552), by norm_num⟩
  | 9 => ⟨((10112464259/4398046511104), (51716884029/8796093022208)), (45/4398046511104), by norm_num⟩
  | 10 => ⟨((-12315049735/17592186044416), (-31490642767/17592186044416)), (111/35184372088832), by norm_num⟩
  | 11 => ⟨((27267960175/140737488355328), (69726522533/140737488355328)), (125/140737488355328), by norm_num⟩
  | 12 => ⟨((-27672638861/562949953421312), (-35380660393/281474976710656)), (129/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307151/10141204801825835211973625643008), (-2531731143667/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444610624369375/158456325028528675187087900672), (-2995139845987/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472343661273123/9903520314283042199192993792), (-1684427645799/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944563285482987/1237940039285380274899124224), (-3578574301525/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885396299477619/77371252455336267181195264), (-1788817901343/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96823748894331/604462909807314587353088), (-3353036675117/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258461686011289/604462909807314587353088), (-2932910498931/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943630116929139/37778931862957161709568), (-4764111584511/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297140210095279/4722366482869645213696), (-3571449842405/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620898530221653/590295810358705651712), (-2454044860331/295147905179352825856)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911393350617303/36893488147419103232), (-3065566754355/36893488147419103232)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910940843894195/4611686018427387904), (-6892057938291/9223372036854775808)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593128568622623/1152921504606846976), (-6885228923669/1152921504606846976)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193828809315005/144115188075855872), (-94014056567/2251799813685248)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((745252919772605/18014398509481984), (-9010015430023/36028797018963968)), (69/1125899906842624), by norm_num⟩
  | 3 => ⟨((371959226224973/2251799813685248), (-11235723858463/9007199254740992)), (2765/9007199254740992), by norm_num⟩
  | 2 => ⟨((278135960920837/562949953421312), (-22391217600697/4503599627370496)), (2773/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105883242055455/1125899906842624), (-33386797187329/2251799813685248)), (1045/281474976710656), by norm_num⟩
  | 0 => ⟨((2171874509661921/2251799813685248), (-8247093724593/281474976710656)), (16889/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2171874509661921/2251799813685248), (-8247093724593/281474976710656)), (64426430709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1046426490837297/1125899906842624), (-31817486670669/562949953421312)), (16785/1125899906842624), by norm_num⟩
  | 2 => ⟨((1937932464979587/2251799813685248), (-118286397295899/1125899906842624)), (16549/562949953421312), by norm_num⟩
  | 3 => ⟨((205369918386871/281474976710656), (-203598071277963/1125899906842624)), (127849/2251799813685248), by norm_num⟩
  | 4 => ⟨((562551498205343/1125899906842624), (-297098660568051/1125899906842624)), (116401/1125899906842624), by norm_num⟩
  | 5 => ⟨((202679272495617/1125899906842624), (-1187553498151017/4503599627370496)), (710999/4503599627370496), by norm_num⟩
  | 6 => ⟨((-334408550176003/9007199254740992), (-855111462722651/9007199254740992)), (1261897/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4903546613/2147483648), (-44652921347/2147483648)), (1/2147483648), by norm_num⟩, -3, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile015Terms2
