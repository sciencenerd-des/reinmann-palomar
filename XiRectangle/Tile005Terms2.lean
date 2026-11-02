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
namespace Reinmann.XiRectangle.Tile005Terms2
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
  | 0 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-17862266831/8589934592), (-115434899395/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((127570635240067/1125899906842624), (-475497122776123/9007199254740992)), (99013/9007199254740992), by norm_num⟩
  | 1 => ⟨((-345411039605/1099511627776), (40233092043/274877906944)), (9/274877906944), by norm_num⟩
  | 2 => ⟨((239420688237/549755813888), (-111549817259/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((-110635850013/274877906944), (103093921767/549755813888)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((153373855011/549755813888), (-142918522411/1099511627776)), (5/137438953472), by norm_num⟩
  | 5 => ⟨((-42524262069/274877906944), (79250856687/1099511627776)), (47/2199023255552), by norm_num⟩
  | 6 => ⟨((157203052579/2199023255552), (-36621671913/1099511627776)), (23/2199023255552), by norm_num⟩
  | 7 => ⟨((-124531260195/4398046511104), (29010524153/2199023255552)), (19/4398046511104), by norm_num⟩
  | 8 => ⟨((345273967583/35184372088832), (-80434252093/17592186044416)), (55/35184372088832), by norm_num⟩
  | 9 => ⟨((-212733935245/70368744177664), (99116044549/70368744177664)), (9/17592186044416), by norm_num⟩
  | 10 => ⟨((235929483879/281474976710656), (-27480802731/70368744177664)), (21/140737488355328), by norm_num⟩
  | 11 => ⟨((-118933713863/562949953421312), (55413064531/562949953421312)), (11/281474976710656), by norm_num⟩
  | 12 => ⟨((54959045625/1125899906842624), (-6401568241/281474976710656)), (43/4503599627370496), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (-567951932925/10141204801825835211973625643008)), (19/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778761409819015/633825300114114700748351602688), (-168034058777/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889733608896893/39614081257132168796771975168), (-756016019995/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944754110711545/1237940039285380274899124224), (-401548334589/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885587265969783/77371252455336267181195264), (-802905094285/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549538344419101/9671406556917033397649408), (-376260020669/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258775552515057/604462909807314587353088), (-329125811685/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471942707047979/18889465931478580854784), (-66829852587/4722366482869645213696)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648761823179835/2361183241434822606848), (-200406198157/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621426551060249/590295810358705651712), (-68855783621/36893488147419103232)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823447919303949/73786976294838206464), (-172037980481/9223372036854775808)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911313596996937/4611686018427387904), (-24175412045/144115188075855872)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593876114953565/1152921504606846976), (-1545833269339/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((149310650126679/18014398509481984), (-337759635211/36028797018963968)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((186436873529205/4503599627370496), (-1011715420171/18014398509481984)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((372270321609467/2251799813685248), (-1261912858921/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113800071297067/2251799813685248), (-5031300338525/4503599627370496)), (343/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107796946010899/1125899906842624), (-1876550843163/562949953421312)), (515/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179761208066107/2251799813685248), (-14850199501763/2251799813685248)), (2063/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179761208066107/2251799813685248), (-14850199501763/2251799813685248)), (7869729048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2109929296063383/2251799813685248), (-28750236685569/2251799813685248)), (2011/1125899906842624), by norm_num⟩
  | 2 => ⟨((988314998346295/1125899906842624), (-26938880749067/1125899906842624)), (7641/2251799813685248), by norm_num⟩
  | 3 => ⟨((1733796808629905/2251799813685248), (-94587803839961/2251799813685248)), (13781/2251799813685248), by norm_num⟩
  | 4 => ⟨((83186361160003/140737488355328), (-18207217115433/281474976710656)), (5595/562949953421312), by norm_num⟩
  | 5 => ⟨((194321927275221/562949953421312), (-344378381369779/4503599627370496)), (58705/4503599627370496), by norm_num⟩
  | 6 => ⟨((127570635240067/1125899906842624), (-475497122776123/9007199254740992)), (99013/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-115434899395/17179869184)), (1/17179869184), by norm_num⟩, -1, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-117958965465/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((449089843991947/4503599627370496), (-148056934340277/2251799813685248)), (105213/9007199254740992), by norm_num⟩
  | 1 => ⟨((-155318278647/549755813888), (204822696315/1099511627776)), (39/1099511627776), by norm_num⟩
  | 2 => ⟨((220024909819/549755813888), (-145076599091/549755813888)), (15/274877906944), by norm_num⟩
  | 3 => ⟨((-51948125877/137438953472), (137010985485/549755813888)), (15/274877906944), by norm_num⟩
  | 4 => ⟨((294360246867/1099511627776), (-194090676179/1099511627776)), (45/1099511627776), by norm_num⟩
  | 5 => ⟨((-166797075877/1099511627776), (109980058741/1099511627776)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((157523900375/2199023255552), (-207731313337/4398046511104)), (55/4398046511104), by norm_num⟩
  | 7 => ⟨((-63756973793/2199023255552), (84078161275/4398046511104)), (47/8796093022208), by norm_num⟩
  | 8 => ⟨((180637108927/17592186044416), (-59552842117/8796093022208)), (35/17592186044416), by norm_num⟩
  | 9 => ⟨((-14216207429/4398046511104), (149978583967/70368744177664)), (23/35184372088832), by norm_num⟩
  | 10 => ⟨((128888155487/140737488355328), (-169968530167/281474976710656)), (27/140737488355328), by norm_num⟩
  | 11 => ⟨((-265576466921/1125899906842624), (175111675541/1125899906842624)), (29/562949953421312), by norm_num⟩
  | 12 => ⟨((250811596649/4503599627370496), (-165376245281/4503599627370496)), (57/4503599627370496), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-759331613085/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889345564802549/316912650057057350374175801344), (-449277450597/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59051704606925/1237940039285380274899124224), (-1010686865143/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236178027821969/309485009821345068724781056), (-1073622072331/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771090537565183/154742504910672534362390528), (-67085022407/9671406556917033397649408)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549459604449901/9671406556917033397649408), (-1005997353257/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258706659803599/604462909807314587353088), (-439984900183/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943829443236997/37778931862957161709568), (-1429430104127/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297439697902349/4722366482869645213696), (-1071617069745/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405327783669025/147573952589676412928), (-736366832095/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455825916993533/18446744073709551616), (-114988003743/4611686018427387904)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822464937633721/9223372036854775808), (-2068260284403/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398428472914203/288230376151711744), (-2066357234351/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18661613952129/2251799813685248), (-451480988677/36028797018963968)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491282201009947/36028797018963968), (-2704614439667/36028797018963968)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((744407717045347/4503599627370496), (-3373305875965/9007199254740992)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((2227068835421545/4503599627370496), (-3362138446469/2251799813685248)), (687/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214797933679197/2251799813685248), (-10030758602187/2251799813685248)), (1031/2251799813685248), by norm_num⟩
  | 0 => ⟨((544543338082429/562949953421312), (-9919984736983/1125899906842624)), (517/562949953421312), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((544543338082429/562949953421312), (-9919984736983/1125899906842624)), (1972200633811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1053389715102281/1125899906842624), (-9595633802923/562949953421312)), (2019/1125899906842624), by norm_num⟩
  | 2 => ⟨((61576387718251/70368744177664), (-17955311829153/562949953421312)), (7695/2251799813685248), by norm_num⟩
  | 3 => ⟨((860976372296327/1125899906842624), (-125694810184771/2251799813685248)), (13959/2251799813685248), by norm_num⟩
  | 4 => ⟨((1309762107350027/2251799813685248), (-192237802013579/2251799813685248)), (5727/562949953421312), by norm_num⟩
  | 5 => ⟨((1490826489216143/4503599627370496), (-111815351945329/1125899906842624)), (61121/4503599627370496), by norm_num⟩
  | 6 => ⟨((449089843991947/4503599627370496), (-148056934340277/2251799813685248)), (105213/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-117958965465/17179869184)), (1/17179869184), by norm_num⟩, -1, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-74484313041/34359738368), (-240677436513/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((386952721001469/4503599627370496), (-680755534605227/9007199254740992)), (27603/2251799813685248), by norm_num⟩
  | 1 => ⟨((-273055961041/1099511627776), (240190011139/1099511627776)), (41/1099511627776), by norm_num⟩
  | 2 => ⟨((197308309529/549755813888), (-173559606181/549755813888)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((-47524530455/137438953472), (167217261339/549755813888)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((274727121269/1099511627776), (-241660024803/1099511627776)), (49/1099511627776), by norm_num⟩
  | 5 => ⟨((-158812702489/1099511627776), (139697462141/1099511627776)), (15/549755813888), by norm_num⟩
  | 6 => ⟨((153009250023/2199023255552), (-67296266537/1099511627776)), (15/1099511627776), by norm_num⟩
  | 7 => ⟨((-252716351407/8796093022208), (111149273263/4398046511104)), (13/2199023255552), by norm_num⟩
  | 8 => ⟨((11413190701/1099511627776), (-160631360175/17592186044416)), (39/17592186044416), by norm_num⟩
  | 9 => ⟨((-234583922273/70368744177664), (103174299307/35184372088832)), (13/17592186044416), by norm_num⟩
  | 10 => ⟨((135606948759/140737488355328), (-119284832343/140737488355328)), (31/140737488355328), by norm_num⟩
  | 11 => ⟨((-285057814449/1125899906842624), (15671705025/70368744177664)), (17/281474976710656), by norm_num⟩
  | 12 => ⟨((137320509375/2251799813685248), (-241584285879/4503599627370496)), (67/4503599627370496), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290153/2535301200456458802993406410752), (-939769175123/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889312411088591/316912650057057350374175801344), (-555998483167/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889579952608715/39614081257132168796771975168), (-625380036247/19807040628566084398385987584)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889344965995249/2475880078570760549798248448), (-332159688805/618970019642690137449562112)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771011281454103/154742504910672534362390528), (-1328308330561/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193673162793953/1208925819614629174706176), (-311234523947/2417851639229258349412352)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258641645981467/604462909807314587353088), (-68060624739/37778931862957161709568)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943776619996749/37778931862957161709568), (-1768918689885/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324340115979213/1180591620717411303424), (-1326113926029/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810601094699743/295147905179352825856), (-911236313307/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823167488614061/73786976294838206464), (-2276690628421/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56947241844307/288230376151711744), (-2559353169293/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593560697131061/1152921504606846976), (-1278475285413/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1166219973157/140737488355328), (-2234631760603/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((186385143801185/4503599627370496), (-3346554990843/36028797018963968)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((372141034859145/2251799813685248), (-2086886532665/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113283153014793/2251799813685248), (-8319349854205/4503599627370496)), (43/281474976710656), by norm_num⟩
  | 1 => ⟨((553511075938899/562949953421312), (-12408763677871/2251799813685248)), (1033/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176666834821123/2251799813685248), (-6134464092039/562949953421312)), (2073/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2176666834821123/2251799813685248), (-6134464092039/562949953421312)), (7907876021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2103773334833941/2251799813685248), (-47438265008787/2251799813685248)), (2027/1125899906842624), by norm_num⟩
  | 2 => ⟨((61389946672975/70368744177664), (-44319817583137/1125899906842624)), (3873/1125899906842624), by norm_num⟩
  | 3 => ⟨((213791094874547/281474976710656), (-9666192248349/140737488355328)), (7063/1125899906842624), by norm_num⟩
  | 4 => ⟨((1288438260113747/2251799813685248), (-234939059742191/2251799813685248)), (2925/281474976710656), by norm_num⟩
  | 5 => ⟨((1425416929674479/4503599627370496), (-537711161582501/4503599627370496)), (63323/4503599627370496), by norm_num⟩
  | 6 => ⟨((386952721001469/4503599627370496), (-680755534605227/9007199254740992)), (27603/2251799813685248), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74484313041/34359738368), (-240677436513/34359738368)), (1/17179869184), by norm_num⟩, -1, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-18969403681/8589934592), (-15323721411/2147483648)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((162842979250897/2251799813685248), (-372597451471425/4503599627370496)), (114651/9007199254740992), by norm_num⟩
  | 1 => ⟨((-58530421825/274877906944), (267844350501/1099511627776)), (43/1099511627776), by norm_num⟩
  | 2 => ⟨((172339255489/549755813888), (-197162836491/549755813888)), (17/274877906944), by norm_num⟩
  | 3 => ⟨((-84573736917/274877906944), (193511313669/549755813888)), (35/549755813888), by norm_num⟩
  | 4 => ⟨((31127775949/137438953472), (-142445563719/549755813888)), (27/549755813888), by norm_num⟩
  | 5 => ⟨((-73323069471/549755813888), (83884454045/549755813888)), (17/549755813888), by norm_num⟩
  | 6 => ⟨((35982550637/549755813888), (-20582721353/274877906944)), (35/2199023255552), by norm_num⟩
  | 7 => ⟨((-242167827807/8796093022208), (277049449367/8796093022208)), (61/8796093022208), by norm_num⟩
  | 8 => ⟨((44565524481/4398046511104), (-50984699867/4398046511104)), (47/17592186044416), by norm_num⟩
  | 9 => ⟨((-233280830949/70368744177664), (33360297251/8796093022208)), (1/1099511627776), by norm_num⟩
  | 10 => ⟨((34344058587/35184372088832), (-39290943833/35184372088832)), (39/140737488355328), by norm_num⟩
  | 11 => ⟨((-73544716223/281474976710656), (42069013291/140737488355328)), (43/562949953421312), by norm_num⟩
  | 12 => ⟨((72182643053/1125899906842624), (-165159523399/2251799813685248)), (11/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (-555224233443/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778562060106009/633825300114114700748351602688), (-328467007839/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889509344043155/39614081257132168796771975168), (-738908456953/19807040628566084398385987584)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472317485450853/618970019642690137449562112), (-1569826801177/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442734063590245/38685626227668133590597632), (-1569429073253/154742504910672534362390528)), (27/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387328740344705/2417851639229258349412352), (-183864663237/1208925819614629174706176)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258580094568091/604462909807314587353088), (-1286630345003/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887453213228179/75557863725914323419136), (-2089982826713/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162160679857759/590295810358705651712), (-783397447825/2361183241434822606848)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621099021898399/590295810358705651712), (-1076609362081/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823038517236753/73786976294838206464), (-2689838081259/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822166629839067/9223372036854775808), (-755938061431/2305843009213693952)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796707783830463/576460752303423488), (-1510430168077/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((597041120824681/72057594037927936), (-1320001473491/72057594037927936)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((186361323698217/4503599627370496), (-1976756796991/18014398509481984)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488325861885011/9007199254740992), (-4930552971319/9007199254740992)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226089526953581/4503599627370496), (-307099013851/140737488355328)), (43/281474976710656), by norm_num⟩
  | 1 => ⟨((2213328594694151/2251799813685248), (-14656186776283/2251799813685248)), (517/1125899906842624), by norm_num⟩
  | 0 => ⟨((271904171387315/281474976710656), (-28975772253343/2251799813685248)), (2077/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((271904171387315/281474976710656), (-28975772253343/2251799813685248)), (7923134810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050448755393719/1125899906842624), (-1749408028407/70368744177664)), (4067/2251799813685248), by norm_num⟩
  | 2 => ⟨((979358032915423/1125899906842624), (-104459075266499/2251799813685248)), (487/140737488355328), by norm_num⟩
  | 3 => ⟨((1698932962374371/2251799813685248), (-90863169853217/1125899906842624)), (14279/2251799813685248), by norm_num⟩
  | 4 => ⟨((158392673871247/281474976710656), (-274216976822309/2251799813685248)), (5963/562949953421312), by norm_num⟩
  | 5 => ⟨((679657376748359/2251799813685248), (-38577106113791/281474976710656)), (16327/1125899906842624), by norm_num⟩
  | 6 => ⟨((162842979250897/2251799813685248), (-372597451471425/4503599627370496)), (114651/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-15323721411/2147483648)), (1/17179869184), by norm_num⟩, -1, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-77199432855/34359738368), (-249450667413/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((133261546166167/2251799813685248), (-394625993009605/4503599627370496)), (59051/4503599627370496), by norm_num⟩
  | 1 => ⟨((-194929645837/1099511627776), (144310769439/549755813888)), (45/1099511627776), by norm_num⟩
  | 2 => ⟨((145989257777/549755813888), (-216158214715/549755813888)), (35/549755813888), by norm_num⟩
  | 3 => ⟨((-72890788519/274877906944), (215850713339/549755813888)), (37/549755813888), by norm_num⟩
  | 4 => ⟨((218361287611/1099511627776), (-161657737055/549755813888)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((-65415195659/549755813888), (96856660033/549755813888)), (37/1099511627776), by norm_num⟩
  | 6 => ⟨((130644275211/2199023255552), (-193437748247/2199023255552)), (39/2199023255552), by norm_num⟩
  | 7 => ⟨((-111821506173/4398046511104), (82783957907/2199023255552)), (35/4398046511104), by norm_num⟩
  | 8 => ⟨((41873411865/4398046511104), (-247998574435/17592186044416)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((-111503583403/35184372088832), (82548592581/17592186044416)), (19/17592186044416), by norm_num⟩
  | 10 => ⟨((133613953367/140737488355328), (-197834786345/140737488355328)), (47/140737488355328), by norm_num⟩
  | 11 => ⟨((-36388330209/140737488355328), (215512747013/562949953421312)), (53/562949953421312), by norm_num⟩
  | 12 => ⟨((145346260251/2251799813685248), (-215206163863/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197631132535527/1267650600228229401496703205376), (-1272371032017/10141204801825835211973625643008)), (19/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778502481543907/633825300114114700748351602688), (-188169635069/79228162514264337593543950336)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236180289375661/4951760157141521099596496896), (-846597482209/19807040628566084398385987584)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118074919894935/154742504910672534362390528), (-1798607356571/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770865025119815/154742504910672534362390528), (-1798143702297/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774624088930287/4835703278458516698824704), (-421316811721/2417851639229258349412352)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258521652898319/604462909807314587353088), (-368529136377/151115727451828646838272)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887358234121941/75557863725914323419136), (-1197258355765/37778931862957161709568)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648607097295979/2361183241434822606848), (-1795080572091/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202625130615853/73786976294838206464), (-1233462592181/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822916021964731/73786976294838206464), (-3081691819305/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911014394864673/4611686018427387904), (-3464203904941/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398319421653907/288230376151711744), (-216302043051/72057594037927936)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193961549991393/144115188075855872), (-189027508637/9007199254740992)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490709461383343/36028797018963968), (-1132273412705/9007199254740992)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488099294610425/9007199254740992), (-1412037224123/2251799813685248)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((2225635928237273/4503599627370496), (-5628368180837/2251799813685248)), (689/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212647060235583/2251799813685248), (-16786526001467/2251799813685248)), (1035/2251799813685248), by norm_num⟩
  | 0 => ⟨((135866618749125/140737488355328), (-33180682416661/2251799813685248)), (2081/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((135866618749125/140737488355328), (-33180682416661/2251799813685248)), (7938393599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1049070162614531/1125899906842624), (-1001009747923/35184372088832)), (4081/2251799813685248), by norm_num⟩
  | 2 => ⟨((1953143668274519/2251799813685248), (-119385897395695/2251799813685248)), (3919/1125899906842624), by norm_num⟩
  | 3 => ⟨((1687768678781451/2251799813685248), (-207103498421611/2251799813685248)), (14429/2251799813685248), by norm_num⟩
  | 4 => ⟨((1245968330295539/2251799813685248), (-310456369858211/2251799813685248)), (24285/2251799813685248), by norm_num⟩
  | 5 => ⟨((646617835948289/2251799813685248), (-687128229482869/4503599627370496)), (8393/562949953421312), by norm_num⟩
  | 6 => ⟨((133261546166167/2251799813685248), (-394625993009605/4503599627370496)), (59051/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77199432855/34359738368), (-249450667413/34359738368)), (1/17179869184), by norm_num⟩, -1, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-19614186453/8589934592), (-7922292497/1073741824)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((52568328775215/1125899906842624), (-204050426325855/2251799813685248)), (120683/9007199254740992), by norm_num⟩
  | 1 => ⟨((-39073597771/274877906944), (303337940125/1099511627776)), (47/1099511627776), by norm_num⟩
  | 2 => ⟨((7435027821/34359738368), (-230879791231/549755813888)), (19/274877906944), by norm_num⟩
  | 3 => ⟨((-60362957403/274877906944), (58576558735/137438953472)), (5/68719476736), by norm_num⟩
  | 4 => ⟨((183776378221/1099511627776), (-356675294787/1099511627776)), (63/1099511627776), by norm_num⟩
  | 5 => ⟨((-27975565351/274877906944), (27147648449/137438953472)), (5/137438953472), by norm_num⟩
  | 6 => ⟨((28390745473/549755813888), (-55101083223/549755813888)), (21/1099511627776), by norm_num⟩
  | 7 => ⟨((-49392149495/2199023255552), (95860848123/2199023255552)), (19/2199023255552), by norm_num⟩
  | 8 => ⟨((150375507385/17592186044416), (-145925251505/8796093022208)), (15/4398046511104), by norm_num⟩
  | 9 => ⟨((-101738134737/35184372088832), (197454534417/35184372088832)), (21/17592186044416), by norm_num⟩
  | 10 => ⟨((15487201699/17592186044416), (-240461904185/140737488355328)), (53/140737488355328), by norm_num⟩
  | 11 => ⟨((-17145866571/70368744177664), (66553787519/140737488355328)), (15/140737488355328), by norm_num⟩
  | 12 => ⟨((69601300653/1125899906842624), (-270165999223/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (-89149482553/633825300114114700748351602688)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444611444362103/158456325028528675187087900672), (-421869704627/158456325028528675187087900672)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944689259058093/19807040628566084398385987584), (-949017866423/19807040628566084398385987584)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889130926828569/2475880078570760549798248448), (-2016193241791/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55337413295027/4835703278458516698824704), (-2015665001141/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774592303487531/4835703278458516698824704), (-472281215981/2417851639229258349412352)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258466019702601/604462909807314587353088), (-1652423384987/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887267813954089/75557863725914323419136), (-1342068400135/37778931862957161709568)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297146365302451/4722366482869645213696), (-503045808103/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620907756699851/590295810358705651712), (-1382629391223/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227849922169813/9223372036854775808), (-3454335152513/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821897517529699/9223372036854775808), (-3883051651111/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593146355907231/1152921504606846976), (-3879210857377/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193846570160569/144115188075855872), (-3389993347549/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490536861616543/36028797018963968), (-5076369553927/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487883319388525/9007199254740992), (-6330402724539/9007199254740992)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225203309315923/4503599627370496), (-394241688119/140737488355328)), (345/2251799813685248), by norm_num⟩
  | 1 => ⟨((2211996488754675/2251799813685248), (-9405646725523/1125899906842624)), (1037/2251799813685248), by norm_num⟩
  | 0 => ⟨((543139588051899/562949953421312), (-37175576240211/2251799813685248)), (521/562949953421312), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((543139588051899/562949953421312), (-37175576240211/2251799813685248)), (1987459422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1047745839039703/1125899906842624), (-35867357376951/1125899906842624)), (4091/2251799813685248), by norm_num⟩
  | 2 => ⟨((973874204301777/1125899906842624), (-133510534002747/2251799813685248)), (7875/2251799813685248), by norm_num⟩
  | 3 => ⟨((1676835914800269/2251799813685248), (-230966295098921/2251799813685248)), (7279/1125899906842624), by norm_num⟩
  | 4 => ⟨((38280951404517/70368744177664), (-42998113817275/281474976710656)), (24669/2251799813685248), by norm_num⟩
  | 5 => ⟨((1227707687980713/4503599627370496), (-374259049186775/2251799813685248)), (68755/4503599627370496), by norm_num⟩
  | 6 => ⟨((52568328775215/1125899906842624), (-204050426325855/2251799813685248)), (120683/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-7922292497/1073741824)), (1/17179869184), by norm_num⟩, -1, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile005Terms2
