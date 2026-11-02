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
namespace Reinmann.XiRectangle.Tile005Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1551/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1551/640))
  have he : value ((3/4), (1551/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-39827778743/17179869184), (-8043344379/1073741824)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((314874586918945/9007199254740992), (-414450415217049/4503599627370496)), (15339/1125899906842624), by norm_num⟩
  | 1 => ⟨((-118809901813/1099511627776), (156382303253/549755813888)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((22952903149/137438953472), (-120846084577/274877906944)), (39/549755813888), by norm_num⟩
  | 3 => ⟨((-47298932041/274877906944), (62256729625/137438953472)), (21/274877906944), by norm_num⟩
  | 4 => ⟨((146203006937/1099511627776), (-96219097139/274877906944)), (67/1099511627776), by norm_num⟩
  | 5 => ⟨((-45191970125/549755813888), (1858858213/8589934592)), (43/1099511627776), by norm_num⟩
  | 6 => ⟨((93126865471/2199023255552), (-61288636279/549755813888)), (23/1099511627776), by norm_num⟩
  | 7 => ⟨((-41122727817/2199023255552), (216509459025/4398046511104)), (21/2199023255552), by norm_num⟩
  | 8 => ⟨((15889012185/2199023255552), (-83654991175/4398046511104)), (67/17592186044416), by norm_num⟩
  | 9 => ⟨((-21828271647/8796093022208), (28731236573/4398046511104)), (47/35184372088832), by norm_num⟩
  | 10 => ⟨((107955382951/140737488355328), (-284190310351/140737488355328)), (15/35184372088832), by norm_num⟩
  | 11 => ⟨((-121343517007/562949953421312), (159717148023/281474976710656)), (35/281474976710656), by norm_num⟩
  | 12 => ⟨((125025987503/2251799813685248), (-329128323379/2251799813685248)), (37/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085629/5070602400912917605986812821504), (-1573246009555/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778391681774797/633825300114114700748351602688), (-1861106144835/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889317654318137/39614081257132168796771975168), (-2093321196963/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944533124947909/1237940039285380274899124224), (-2223627772215/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442683134559721/38685626227668133590597632), (-555759061145/38685626227668133590597632)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96820246989237/604462909807314587353088), (-1041734091989/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258412935570939/604462909807314587353088), (-911203296913/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887181531881661/75557863725914323419136), (-185014598357/4722366482869645213696)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324270408992957/1180591620717411303424), (-1109572833069/2361183241434822606848)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810409362526871/295147905179352825856), (-381206654795/73786976294838206464)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455672011174613/18446744073709551616), (-3809560057043/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113860763076241/576460752303423488), (-267644451123/576460752303423488)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199127621757577/144115188075855872), (-2139005137759/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193736778723997/144115188075855872), (-3738425740945/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490372010838065/36028797018963968), (-2798992686217/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487676971858265/9007199254740992), (-1745154586675/2251799813685248)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112394885594827/2251799813685248), (-13910765592009/4503599627370496)), (691/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211374105631981/2251799813685248), (-10370193143981/1125899906842624)), (519/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171305471507083/2251799813685248), (-40980211191281/2251799813685248)), (261/281474976710656), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2171305471507083/2251799813685248), (-40980211191281/2251799813685248)), (995637060069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((261617842550039/281474976710656), (-39515305153845/1125899906842624)), (513/281474976710656), by norm_num⟩
  | 2 => ⟨((1942518802357523/2251799813685248), (-146910521181885/2251799813685248)), (3959/1125899906842624), by norm_num⟩
  | 3 => ⟨((833066192979753/1125899906842624), (-253465204078611/2251799813685248)), (14695/2251799813685248), by norm_num⟩
  | 4 => ⟨((602130016483683/1125899906842624), (-375083595497835/2251799813685248)), (25055/2251799813685248), by norm_num⟩
  | 5 => ⟨((1163118067096549/4503599627370496), (-200594289214591/1125899906842624)), (70293/4503599627370496), by norm_num⟩
  | 6 => ⟨((314874586918945/9007199254740992), (-414450415217049/4503599627370496)), (15339/1125899906842624), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39827778743/17179869184), (-8043344379/1073741824)), (1/17179869184), by norm_num⟩, -1, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-80801070685/34359738368), (-65272114913/8589934592)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((433170554745111/18014398509481984), (-829818938405611/9007199254740992)), (248211/18014398509481984), by norm_num⟩
  | 1 => ⟨((-82898179255/1099511627776), (317613828325/1099511627776)), (49/1099511627776), by norm_num⟩
  | 2 => ⟨((64981690391/549755813888), (-248969080403/549755813888)), (5/68719476736), by norm_num⟩
  | 3 => ⟨((-33958285727/274877906944), (130106851925/274877906944)), (43/549755813888), by norm_num⟩
  | 4 => ⟨((3327375265/34359738368), (-3187103763/8589934592)), (69/1099511627776), by norm_num⟩
  | 5 => ⟨((-66770981745/1099511627776), (127912261305/549755813888)), (45/1099511627776), by norm_num⟩
  | 6 => ⟨((17446668921/549755813888), (-33422346289/274877906944)), (49/2199023255552), by norm_num⟩
  | 7 => ⟨((-62518776559/4398046511104), (239532739365/4398046511104)), (23/2199023255552), by norm_num⟩
  | 8 => ⟨((12251703893/2199023255552), (-187763379701/8796093022208)), (37/8796093022208), by norm_num⟩
  | 9 => ⟨((-68293594119/35184372088832), (261658218229/35184372088832)), (53/35184372088832), by norm_num⟩
  | 10 => ⟨((42826833869/70368744177664), (-328171131923/140737488355328)), (17/35184372088832), by norm_num⟩
  | 11 => ⟨((-24415143615/140737488355328), (374174067629/562949953421312)), (79/562949953421312), by norm_num⟩
  | 12 => ⟨((102071388781/2251799813685248), (-391073541601/2251799813685248)), (85/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395228129658349/2535301200456458802993406410752), (-856785620631/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778339963845527/633825300114114700748351602688), (-506748850171/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889259464300773/39614081257132168796771975168), (-2279902206549/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472251103066113/618970019642690137449562112), (-1210907469029/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442667672137755/38685626227668133590597632), (-1210580690197/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24204155546135/151115727451828646838272), (-141821538311/604462909807314587353088)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258362175531823/604462909807314587353088), (-992403803539/302231454903657293676544)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471774755727323/18889465931478580854784), (-3224011779131/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648509866681775/2361183241434822606848), (-604217839893/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620733575116161/590295810358705651712), (-3321350725175/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822581556634587/73786976294838206464), (-4148919068155/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910826170367171/4611686018427387904), (-291483059901/576460752303423488)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199112627391989/144115188075855872), (-2329488492069/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((298407930342703/36028797018963968), (-1017816188143/36028797018963968)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490214232342731/36028797018963968), (-6096231552999/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((92967463402711/562949953421312), (-1900414396237/2251799813685248)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112196831757391/2251799813685248), (-15147551000309/4503599627370496)), (691/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210777497001891/2251799813685248), (-22582375046019/2251799813685248)), (1039/2251799813685248), by norm_num⟩
  | 0 => ⟨((542525668632683/562949953421312), (-44611690677591/2251799813685248)), (523/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((542525668632683/562949953421312), (-44611690677591/2251799813685248)), (1995088817405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((130655359172347/140737488355328), (-85986284097197/2251799813685248)), (1029/562949953421312), by norm_num⟩
  | 2 => ⟨((1937444434371665/2251799813685248), (-159652825468225/2251799813685248)), (7957/2251799813685248), by norm_num⟩
  | 3 => ⟨((1655654241082939/2251799813685248), (-137364998547051/1125899906842624)), (7411/1125899906842624), by norm_num⟩
  | 4 => ⟨((1183814999233855/2251799813685248), (-403994957346713/2251799813685248)), (12707/1125899906842624), by norm_num⟩
  | 5 => ⟨((549873936095171/2251799813685248), (-849552055587353/4503599627370496)), (35841/2251799813685248), by norm_num⟩
  | 6 => ⟨((433170554745111/18014398509481984), (-829818938405611/9007199254740992)), (248211/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-80801070685/34359738368), (-65272114913/8589934592)), (1/17179869184), by norm_num⟩, -1, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-40948911799/17179869184), (-66158085625/8589934592)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((251827969568971/18014398509481984), (-1642153775607861/18014398509481984)), (249827/18014398509481984), by norm_num⟩
  | 1 => ⟨((-24423914895/549755813888), (79633378549/274877906944)), (25/549755813888), by norm_num⟩
  | 2 => ⟨((19405129071/274877906944), (-253079163721/549755813888)), (41/549755813888), by norm_num⟩
  | 3 => ⟨((-41113696515/549755813888), (268099735215/549755813888)), (45/549755813888), by norm_num⟩
  | 4 => ⟨((65330770345/1099511627776), (-53252211901/137438953472)), (37/549755813888), by norm_num⟩
  | 5 => ⟨((-41524940987/1099511627776), (270781433611/1099511627776)), (49/1099511627776), by norm_num⟩
  | 6 => ⟨((43989499253/2199023255552), (-286852657425/2199023255552)), (53/2199023255552), by norm_num⟩
  | 7 => ⟨((-39943141885/4398046511104), (65116656191/1099511627776)), (25/2199023255552), by norm_num⟩
  | 8 => ⟨((15867681883/4398046511104), (-413888477255/17592186044416)), (81/17592186044416), by norm_num⟩
  | 9 => ⟨((-11206299375/8796093022208), (292302191217/35184372088832)), (59/35184372088832), by norm_num⟩
  | 10 => ⟨((14245689061/35184372088832), (-371580839367/140737488355328)), (77/140737488355328), by norm_num⟩
  | 11 => ⟨((-65852460635/562949953421312), (53677450447/70368744177664)), (91/562949953421312), by norm_num⟩
  | 12 => ⟨((69760888253/2251799813685248), (-113726551331/562949953421312)), (49/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646181/10141204801825835211973625643008), (-7218450561/39614081257132168796771975168)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889145211170899/316912650057057350374175801344), (-1092903118187/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236150465218697/4951760157141521099596496896), (-2458520834923/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472236293423723/618970019642690137449562112), (-2611543153967/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885305718192263/77371252455336267181195264), (-20397099845/1208925819614629174706176)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193626298952313/1208925819614629174706176), (-152930825219/604462909807314587353088)), (103/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629156771603729/302231454903657293676544), (-2140273049975/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943509984206889/37778931862957161709568), (-3476522096663/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648480209469601/2361183241434822606848), (-651537061915/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202581497449147/73786976294838206464), (-55959914551/9223372036854775808)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822479505092811/73786976294838206464), (-4473766112971/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910768727211161/4611686018427387904), (-5028827788239/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99549127204367/72057594037927936), (-2511816791771/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((298382750306879/36028797018963968), (-548730287815/18014398509481984)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490062934823489/36028797018963968), (-3286552632371/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((743644957496051/4503599627370496), (-256125489217/281474976710656)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224013542840145/4503599627370496), (-8165538466525/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((2210204549491351/2251799813685248), (-6086182595091/562949953421312)), (65/140737488355328), by norm_num⟩
  | 0 => ⟨((2168945939794209/2251799813685248), (-48084918383181/2251799813685248)), (2095/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2168945939794209/2251799813685248), (-48084918383181/2251799813685248)), (7991799361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1044056914339701/1125899906842624), (-23157828653039/562949953421312)), (2063/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932515836722437/2251799813685248), (-85897835071689/1125899906842624)), (999/281474976710656), by norm_num⟩
  | 3 => ⟨((1645396577611095/2251799813685248), (-294873328627807/2251799813685248)), (7469/1125899906842624), by norm_num⟩
  | 4 => ⟨((290920578480487/562949953421312), (-215464786347479/1125899906842624)), (1609/140737488355328), by norm_num⟩
  | 5 => ⟨((32431175276173/140737488355328), (-55673812481401/281474976710656)), (18231/1125899906842624), by norm_num⟩
  | 6 => ⟨((251827969568971/18014398509481984), (-1642153775607861/18014398509481984)), (249827/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40948911799/17179869184), (-66158085625/8589934592)), (1/17179869184), by norm_num⟩, -1, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-41474899193/17179869184), (-268031536035/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((85738370366681/18014398509481984), (-1608974008845099/18014398509481984)), (250531/18014398509481984), by norm_num⟩
  | 1 => ⟨((-16844553689/1099511627776), (316106417231/1099511627776)), (51/1099511627776), by norm_num⟩
  | 2 => ⟨((27110263325/1099511627776), (-508753652255/1099511627776)), (21/274877906944), by norm_num⟩
  | 3 => ⟨((-3636023801/137438953472), (272935805343/549755813888)), (47/549755813888), by norm_num⟩
  | 4 => ⟨((23407818223/1099511627776), (-109818308195/274877906944)), (39/549755813888), by norm_num⟩
  | 5 => ⟨((-7534686019/549755813888), (282793197901/1099511627776)), (13/274877906944), by norm_num⟩
  | 6 => ⟨((8084406225/1099511627776), (-303425396053/2199023255552)), (29/1099511627776), by norm_num⟩
  | 7 => ⟨((-7435057073/2199023255552), (279053906287/4398046511104)), (55/4398046511104), by norm_num⟩
  | 8 => ⟨((23932525469/17592186044416), (-449119936391/17592186044416)), (45/8796093022208), by norm_num⟩
  | 9 => ⟨((-17119072813/35184372088832), (321258067937/35184372088832)), (33/17592186044416), by norm_num⟩
  | 10 => ⟨((22041667849/140737488355328), (-206817965685/70368744177664)), (87/140737488355328), by norm_num⟩
  | 11 => ⟨((-25799778829/562949953421312), (484160981739/562949953421312)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((27682094787/2251799813685248), (-259742346577/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (-1976790131071/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778242880519701/633825300114114700748351602688), (-2338117418395/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889150227970267/39614081257132168796771975168), (-657457040533/9903520314283042199192993792)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888888323260387/2475880078570760549798248448), (-1396752077195/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885277285510811/77371252455336267181195264), (-1396365067727/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774478532249679/4835703278458516698824704), (-2617362370861/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629133433079649/302231454903657293676544), (-2289370240347/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471736022149471/18889465931478580854784), (-1859343166181/37778931862957161709568)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296903483213999/4722366482869645213696), (-696916902549/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620573651032669/590295810358705651712), (-3830855044875/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822381531641065/73786976294838206464), (-1196322248647/18446744073709551616)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227678393532521/1152921504606846976), (-2689471867681/4611686018427387904)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592675621951719/1152921504606846976), (-5373315788427/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193434269545421/144115188075855872), (-4695326788739/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489917598544549/36028797018963968), (-3515179199841/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487107829741607/9007199254740992), (-8765881187965/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223648139277963/4503599627370496), (-17465716950893/4503599627370496)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209653402074743/2251799813685248), (-13017001687605/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167831718747469/2251799813685248), (-51412959438487/2251799813685248)), (1049/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2167831718747469/2251799813685248), (-51412959438487/2251799813685248)), (4001621726607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2085820879753345/2251799813685248), (-98991609776381/2251799813685248)), (517/281474976710656), by norm_num⟩
  | 2 => ⟨((1927724381726791/2251799813685248), (-22923748076661/281474976710656)), (8027/2251799813685248), by norm_num⟩
  | 3 => ⟨((1635353810346397/2251799813685248), (-313993581982729/2251799813685248)), (3763/562949953421312), by norm_num⟩
  | 4 => ⟨((1143880597126727/2251799813685248), (-456071270278153/2251799813685248)), (26061/2251799813685248), by norm_num⟩
  | 5 => ⟨((122175804685417/562949953421312), (-926709512644163/4503599627370496)), (74069/4503599627370496), by norm_num⟩
  | 6 => ⟨((85738370366681/18014398509481984), (-1608974008845099/18014398509481984)), (250531/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-268031536035/34359738368)), (1/17179869184), by norm_num⟩, -1, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-20990127117/8589934592), (-271297392987/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-65397474875007/18014398509481984), (-781591860291539/9007199254740992)), (62595/4503599627370496), by norm_num⟩
  | 1 => ⟨((13004839263/1099511627776), (310852262471/1099511627776)), (51/1099511627776), by norm_num⟩
  | 2 => ⟨((-10592755445/549755813888), (-7912395939/17179869184)), (85/1099511627776), by norm_num⟩
  | 3 => ⟨((11504073281/549755813888), (137489865687/274877906944)), (3/34359738368), by norm_num⟩
  | 4 => ⟨((-18740690665/1099511627776), (-447955255407/1099511627776)), (5/68719476736), by norm_num⟩
  | 5 => ⟨((12211795875/1099511627776), (145948146683/549755813888)), (27/549755813888), by norm_num⟩
  | 6 => ⟨((-1657800411/274877906944), (-317008767625/2199023255552)), (61/2199023255552), by norm_num⟩
  | 7 => ⟨((192902635/68719476736), (2305457965/34359738368)), (59/4398046511104), by norm_num⟩
  | 8 => ⟨((-20111853033/17592186044416), (-120182473829/4398046511104)), (49/8796093022208), by norm_num⟩
  | 9 => ⟨((14561413053/35184372088832), (43507344657/4398046511104)), (73/35184372088832), by norm_num⟩
  | 10 => ⟨((-18976995783/140737488355328), (-453603612817/140737488355328)), (97/140737488355328), by norm_num⟩
  | 11 => ⟨((1405201915/35184372088832), (268706247373/281474976710656)), (59/281474976710656), by norm_num⟩
  | 12 => ⟨((-12208755985/1125899906842624), (-291823631437/1125899906842624)), (33/562949953421312), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (-525150499211/2535301200456458802993406410752)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889098591181465/316912650057057350374175801344), (-310554941653/79228162514264337593543950336)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889098807565467/39614081257132168796771975168), (-2794398566899/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118052104672471/154742504910672534362390528), (-1484154089639/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770499906438843/154742504910672534362390528), (-2967475644103/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548905799387131/9671406556917033397649408), (-2781124130755/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258221992144073/604462909807314587353088), (-1216299823595/302231454903657293676544)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943435568209987/37778931862957161709568), (-3951317664461/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296848741215879/4722366482869645213696), (-2962039257463/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620498335599891/590295810358705651712), (-508806329489/73786976294838206464)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911143659868839/36893488147419103232), (-5084535496571/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910660533585291/4611686018427387904), (-2857627655243/4611686018427387904)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592569425391861/1152921504606846976), (-5709201802337/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149167652275503/18014398509481984), (-2494374396953/72057594037927936)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489777764207735/36028797018963968), (-933692017667/4503599627370496)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486932589595297/9007199254740992), (-9313184455789/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223296329640083/4503599627370496), (-2319415997203/562949953421312)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209122407226783/2251799813685248), (-13827985188821/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166756863842101/2251799813685248), (-27303665224477/1125899906842624)), (2101/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2166756863842101/2251799813685248), (-27303665224477/1125899906842624)), (8014687545012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083601445365389/2251799813685248), (-52544994163013/1125899906842624)), (2073/1125899906842624), by norm_num⟩
  | 2 => ⟨((1923062188372515/2251799813685248), (-97240283189821/1125899906842624)), (2015/562949953421312), by norm_num⟩
  | 3 => ⟨((812759968138175/1125899906842624), (-332177151188127/2251799813685248)), (1895/281474976710656), by norm_num⟩
  | 4 => ⟨((1124422068104107/2251799813685248), (-239790668047039/1125899906842624)), (26361/2251799813685248), by norm_num⟩
  | 5 => ⟨((918666679891921/4503599627370496), (-957903690155309/4503599627370496)), (75111/4503599627370496), by norm_num⟩
  | 6 => ⟨((-65397474875007/18014398509481984), (-781591860291539/9007199254740992)), (62595/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-271297392987/34359738368)), (1/17179869184), by norm_num⟩, -1, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-84933069315/34359738368), (-274439980223/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-101046853072943/9007199254740992), (-1507400194909267/18014398509481984)), (249549/18014398509481984), by norm_num⟩
  | 1 => ⟨((20326778781/549755813888), (303231514539/1099511627776)), (13/274877906944), by norm_num⟩
  | 2 => ⟨((-33496873437/549755813888), (-124925200569/274877906944)), (11/137438953472), by norm_num⟩
  | 3 => ⟨((18400038395/274877906944), (274488721019/549755813888)), (25/274877906944), by norm_num⟩
  | 4 => ⟨((-30321762439/549755813888), (-226167511509/549755813888)), (21/274877906944), by norm_num⟩
  | 5 => ⟨((39974232995/1099511627776), (298164488929/1099511627776)), (29/549755813888), by norm_num⟩
  | 6 => ⟨((-21958091799/1099511627776), (-163783585791/1099511627776)), (33/1099511627776), by norm_num⟩
  | 7 => ⟨((10338612637/1099511627776), (154229708599/2199023255552)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-266206099/68719476736), (-254157979717/8796093022208)), (27/4398046511104), by norm_num⟩
  | 9 => ⟨((49912711113/35184372088832), (23268423315/2199023255552)), (81/35184372088832), by norm_num⟩
  | 10 => ⟨((-16450415337/35184372088832), (-245404567601/70368744177664)), (55/70368744177664), by norm_num⟩
  | 11 => ⟨((19715594665/140737488355328), (294113971267/281474976710656)), (67/281474976710656), by norm_num⟩
  | 12 => ⟨((-43319589155/1125899906842624), (-323117223103/1125899906842624)), (75/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480317/10141204801825835211973625643008), (-2219740585815/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778153189460869/633825300114114700748351602688), (-2625225291081/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889049304926365/39614081257132168796771975168), (-2952741318453/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944390531496747/1237940039285380274899124224), (-3136496290723/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770447277589647/154742504910672534362390528), (-3135606327183/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548856441712405/9671406556917033397649408), (-1469342823439/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157272348259391/75557863725914323419136), (-642601248795/151115727451828646838272)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886800892666941/75557863725914323419136), (-2087568531953/37778931862957161709568)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296796028799615/4722366482869645213696), (-195612740391/295147905179352825856)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620425808024631/590295810358705651712), (-134405143483/18446744073709551616)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455549147109557/18446744073709551616), (-5372434553831/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227652361996783/1152921504606846976), (-6038807326347/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398116782878211/288230376151711744), (-3016168069695/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193251573622205/144115188075855872), (-5271021932189/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((23275672248553/562949953421312), (-7892008240217/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486763688970301/9007199254740992), (-9839636474203/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222957115593191/4503599627370496), (-19603328533489/4503599627370496)), (693/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104305049650707/1125899906842624), (-14607875204897/1125899906842624)), (261/562949953421312), by norm_num⟩
  | 0 => ⟨((2165718569846197/2251799813685248), (-57678234546329/2251799813685248)), (263/281474976710656), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2165718569846197/2251799813685248), (-57678234546329/2251799813685248)), (1003266454601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2081450631868387/2251799813685248), (-110946650651415/2251799813685248)), (1039/562949953421312), by norm_num⟩
  | 2 => ⟨((1918522040617949/2251799813685248), (-205107021235723/2251799813685248)), (4047/1125899906842624), by norm_num⟩
  | 3 => ⟨((1615888725126821/2251799813685248), (-349500287312157/2251799813685248)), (3817/562949953421312), by norm_num⟩
  | 4 => ⟨((1105314027487793/2251799813685248), (-501601936605577/2251799813685248)), (26653/2251799813685248), by norm_num⟩
  | 5 => ⟨((861634849296085/4503599627370496), (-984861360011967/4503599627370496)), (76081/4503599627370496), by norm_num⟩
  | 6 => ⟨((-101046853072943/9007199254740992), (-1507400194909267/18014398509481984)), (249549/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84933069315/34359738368), (-274439980223/34359738368)), (1/17179869184), by norm_num⟩, -1, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile005Terms3
