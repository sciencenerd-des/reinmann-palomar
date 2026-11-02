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
namespace Reinmann.XiRectangle.Tile010Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4978472343/2147483648), (-61421902531/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-289067869822777/18014398509481984), (-1749665720929775/18014398509481984)), (1168873/9007199254740992), by norm_num⟩
  | 1 => ⟨((3408512335/68719476736), (41261985951/137438953472)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((-5267928165/68719476736), (-31885637571/68719476736)), (11/17179869184), by norm_num⟩
  | 3 => ⟨((5427796533/68719476736), (65706572923/137438953472)), (23/34359738368), by norm_num⟩
  | 4 => ⟨((-2097193689/34359738368), (-101550903185/274877906944)), (9/17179869184), by norm_num⟩
  | 5 => ⟨((10372023561/274877906944), (7847453823/34359738368)), (91/274877906944), by norm_num⟩
  | 6 => ⟨((-10686788385/549755813888), (-64684834447/549755813888)), (95/549755813888), by norm_num⟩
  | 7 => ⟨((4719045227/549755813888), (7140841763/137438953472)), (85/1099511627776), by norm_num⟩
  | 8 => ⟨((-911673071/274877906944), (-88290580169/4398046511104)), (133/4398046511104), by norm_num⟩
  | 9 => ⟨((10019627257/8796093022208), (15161662863/2199023255552)), (93/8796093022208), by norm_num⟩
  | 10 => ⟨((-12388437287/35184372088832), (-74984549717/35184372088832)), (117/35184372088832), by norm_num⟩
  | 11 => ⟨((6962397379/70368744177664), (42141895731/70368744177664)), (67/70368744177664), by norm_num⟩
  | 12 => ⟨((-7173688625/281474976710656), (-86841592513/562949953421312)), (35/140737488355328), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-2259419619843/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444597427542293/158456325028528675187087900672), (-2672830385529/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59041103950853/1237940039285380274899124224), (-3006323041803/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944531815901661/1237940039285380274899124224), (-1596731214823/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770729757503069/154742504910672534362390528), (-24942284501/1208925819614629174706176)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774560586101169/4835703278458516698824704), (-93505351933/302231454903657293676544)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258410330851351/604462909807314587353088), (-2617247269513/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887176975979851/75557863725914323419136), (-531416886333/9444732965739290427392)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297077936510581/4722366482869645213696), (-3187021684661/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620813179725275/590295810358705651712), (-4379751581233/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822680426145529/73786976294838206464), (-1367771667189/18446744073709551616)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821762695431739/9223372036854775808), (-1537505490823/2305843009213693952)), (419/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796505141982959/576460752303423488), (-6143838769415/1152921504606846976)), (1677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193726104757117/144115188075855872), (-2684454836725/72057594037927936)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((372588341908303/9007199254740992), (-2009870776651/9007199254740992)), (1103/18014398509481984), by norm_num⟩
  | 3 => ⟨((371912269849875/2251799813685248), (-5012549929585/4503599627370496)), (1381/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224720292696971/4503599627370496), (-19977591205495/4503599627370496)), (5537/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211235904351037/2251799813685248), (-14892701111127/1125899906842624)), (8343/2251799813685248), by norm_num⟩
  | 0 => ⟨((271361828801739/281474976710656), (-58850080181271/2251799813685248)), (16835/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((271361828801739/281474976710656), (-58850080181271/2251799813685248)), (64220437056731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2091358270749405/2251799813685248), (-113471297304945/2251799813685248)), (33341/2251799813685248), by norm_num⟩
  | 2 => ⟨((484157567517393/562949953421312), (-210772853491791/2251799813685248)), (16323/562949953421312), by norm_num⟩
  | 3 => ⟨((822922087624505/1125899906842624), (-362544739279561/2251799813685248)), (124531/2251799813685248), by norm_num⟩
  | 4 => ⟨((1144579702670705/2251799813685248), (-132492272133619/562949953421312)), (222141/2251799813685248), by norm_num⟩
  | 5 => ⟨((457054599040639/2251799813685248), (-538761801198233/2251799813685248)), (660781/4503599627370496), by norm_num⟩
  | 6 => ⟨((-289067869822777/18014398509481984), (-1749665720929775/18014398509481984)), (1168873/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-61421902531/4294967296)), (1/2147483648), by norm_num⟩, -2, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-2525033459/1073741824), (-62305200599/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-619285037471653/18014398509481984), (-1599537637411085/18014398509481984)), (1179233/9007199254740992), by norm_num⟩
  | 1 => ⟨((29628977249/274877906944), (9566003819/34359738368)), (115/274877906944), by norm_num⟩
  | 2 => ⟨((-23225371697/137438953472), (-7498537411/17179869184)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((6068584885/34359738368), (62697655147/137438953472)), (49/68719476736), by norm_num⟩
  | 4 => ⟨((-9514006403/68719476736), (-98294067533/274877906944)), (39/68719476736), by norm_num⟩
  | 5 => ⟨((11932444819/137438953472), (30820048021/137438953472)), (25/68719476736), by norm_num⟩
  | 6 => ⟨((-24942741141/549755813888), (-32212027435/274877906944)), (53/274877906944), by norm_num⟩
  | 7 => ⟨((22345091593/1099511627776), (57714643261/1099511627776)), (97/1099511627776), by norm_num⟩
  | 8 => ⟨((-17515726361/2199023255552), (-22620491265/1099511627776)), (77/2199023255552), by norm_num⟩
  | 9 => ⟨((1525568297/549755813888), (63045706243/8796093022208)), (109/8796093022208), by norm_num⟩
  | 10 => ⟨((-3826728457/4398046511104), (-39535889453/17592186044416)), (69/17592186044416), by norm_num⟩
  | 11 => ⟨((4363158161/17592186044416), (90156038329/140737488355328)), (5/4398046511104), by norm_num⟩
  | 12 => ⟨((-4560219059/70368744177664), (-94227912237/562949953421312)), (85/281474976710656), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (-1263656621971/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778337376655763/633825300114114700748351602688), (-373697063055/79228162514264337593543950336)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889256409837415/39614081257132168796771975168), (-3362578982915/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889000977038903/2475880078570760549798248448), (-446485308155/309485009821345068724781056)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885333519969207/77371252455336267181195264), (-3570917826189/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48408197119319/302231454903657293676544), (-836677704755/2417851639229258349412352)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258358757913221/604462909807314587353088), (-731836911291/151115727451828646838272)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943546522607589/37778931862957161709568), (-594377500473/9444732965739290427392)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324253719856965/1180591620717411303424), (-1782292878097/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202590787419497/73786976294838206464), (-612322239911/73786976294838206464)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227821445102079/9223372036854775808), (-3059566697897/36893488147419103232)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821639858480475/9223372036854775808), (-1719601582329/2305843009213693952)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592886993797327/1152921504606846976), (-214730886215/36028797018963968)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193617717504477/144115188075855872), (-6004577095435/144115188075855872)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490189773823211/36028797018963968), (-8991108940837/36028797018963968)), (69/1125899906842624), by norm_num⟩
  | 3 => ⟨((743721411496213/4503599627370496), (-5605677035709/4503599627370496)), (2765/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224302521295923/4503599627370496), (-11170140090737/2251799813685248)), (2773/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105298109415951/1125899906842624), (-33304938948277/2251799813685248)), (1045/281474976710656), by norm_num⟩
  | 0 => ⟨((1084781925348445/1125899906842624), (-4111967427035/140737488355328)), (2111/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084781925348445/1125899906842624), (-4111967427035/140737488355328)), (8052827001476199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((522102226292869/562949953421312), (-126777534389621/2251799813685248)), (16765/1125899906842624), by norm_num⟩
  | 2 => ⟨((1929736020744249/2251799813685248), (-117578538814097/1125899906842624)), (32985/1125899906842624), by norm_num⟩
  | 3 => ⟨((407294449122821/562949953421312), (-403047447179075/2251799813685248)), (126849/2251799813685248), by norm_num⟩
  | 4 => ⟨((138321190496095/281474976710656), (-145802470514021/562949953421312)), (228961/2251799813685248), by norm_num⟩
  | 5 => ⟨((392735774944953/2251799813685248), (-286598425685315/1125899906842624)), (343631/2251799813685248), by norm_num⟩
  | 6 => ⟨((-619285037471653/18014398509481984), (-1599537637411085/18014398509481984)), (1179233/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-62305200599/4294967296)), (1/2147483648), by norm_num⟩, -2, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-5118613975/2147483648), (-63150899915/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-445666824160557/9007199254740992), (-701001190450067/9007199254740992)), (1172543/9007199254740992), by norm_num⟩
  | 1 => ⟨((43223668139/274877906944), (67987656201/274877906944)), (29/68719476736), by norm_num⟩
  | 2 => ⟨((-34341786023/137438953472), (-54017107801/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((18190007435/68719476736), (57223092117/137438953472)), (101/137438953472), by norm_num⟩
  | 4 => ⟨((-28904411401/137438953472), (-11366129193/34359738368)), (41/68719476736), by norm_num⟩
  | 5 => ⟨((36743910147/274877906944), (57795472669/274877906944)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((-1216397129/17179869184), (-15306426941/137438953472)), (57/274877906944), by norm_num⟩
  | 7 => ⟨((17672116823/549755813888), (55593884307/1099511627776)), (105/1099511627776), by norm_num⟩
  | 8 => ⟨((-877545915/68719476736), (-44170089241/2199023255552)), (85/2199023255552), by norm_num⟩
  | 9 => ⟨((19832093557/4398046511104), (62388853911/8796093022208)), (61/4398046511104), by norm_num⟩
  | 10 => ⟨((-25210984357/17592186044416), (-79310054457/35184372088832)), (157/35184372088832), by norm_num⟩
  | 11 => ⟨((29135223783/70368744177664), (11456891925/17592186044416)), (93/70368744177664), by norm_num⟩
  | 12 => ⟨((-15432218257/140737488355328), (-48547492355/281474976710656)), (25/70368744177664), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790435469823053/5070602400912917605986812821504), (-2783803621165/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444571793150961/158456325028528675187087900672), (-3292807213569/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889199885378773/39614081257132168796771975168), (-462953908071/4951760157141521099596496896)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944470429555403/1237940039285380274899124224), (-1967075243591/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55331464181647/4835703278458516698824704), (-983268330933/38685626227668133590597632)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549005810928845/9671406556917033397649408), (-1843056030823/4835703278458516698824704)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157288656351239/75557863725914323419136), (-3224204219521/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117938278794645/4722366482869645213696), (-654648487509/9444732965739290427392)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648477161338997/2361183241434822606848), (-981503923941/1180591620717411303424)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620642841750655/590295810358705651712), (-674403213475/73786976294838206464)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822466951194895/73786976294838206464), (-842433215935/9223372036854775808)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910760888995463/4611686018427387904), (-3787812019145/4611686018427387904)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592768421183407/1152921504606846976), (-3783893131321/576460752303423488)), (1679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193513414484613/144115188075855872), (-6613003531347/144115188075855872)), (1471/144115188075855872), by norm_num⟩
  | 4 => ⟨((745016109731987/18014398509481984), (-9901906515341/36028797018963968)), (1105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487243964628025/9007199254740992), (-12346630514583/9007199254740992)), (2769/9007199254740992), by norm_num⟩
  | 2 => ⟨((277987386920935/562949953421312), (-12300591994267/2251799813685248)), (2777/2251799813685248), by norm_num⟩
  | 1 => ⟨((276247117020145/281474976710656), (-18336107937009/1125899906842624)), (4189/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084134741021681/1125899906842624), (-36214991221007/1125899906842624)), (16939/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1084134741021681/1125899906842624), (-36214991221007/1125899906842624)), (64617165572356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085507963835571/2251799813685248), (-17435799527949/281474976710656)), (2107/140737488355328), by norm_num⟩
  | 2 => ⟨((480714025529199/562949953421312), (-258371093560883/2251799813685248)), (33311/1125899906842624), by norm_num⟩
  | 3 => ⟨((806159576307575/1125899906842624), (-110314076509995/562949953421312)), (129069/2251799813685248), by norm_num⟩
  | 4 => ⟨((1067975007216043/2251799813685248), (-78986372269493/281474976710656)), (235415/2251799813685248), by norm_num⟩
  | 5 => ⟨((329196406917745/2251799813685248), (-1198763349840431/4503599627370496)), (710853/4503599627370496), by norm_num⟩
  | 6 => ⟨((-445666824160557/9007199254740992), (-701001190450067/9007199254740992)), (1172543/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5118613975/2147483648), (-63150899915/4294967296)), (1/2147483648), by norm_num⟩, -2, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-5184362399/2147483648), (-15990517775/1073741824)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-69022972305877/1125899906842624), (-293313050433559/4503599627370496)), (1150725/9007199254740992), by norm_num⟩
  | 1 => ⟨((54242279521/274877906944), (57625627879/274877906944)), (115/274877906944), by norm_num⟩
  | 2 => ⟨((-43649790559/137438953472), (-23186217559/68719476736)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((23417209265/68719476736), (49755703447/137438953472)), (103/137438953472), by norm_num⟩
  | 4 => ⟨((-37688544395/137438953472), (-2502459859/8589934592)), (85/137438953472), by norm_num⟩
  | 5 => ⟨((48525897771/274877906944), (25776344137/137438953472)), (111/274877906944), by norm_num⟩
  | 6 => ⟨((-52066279739/549755813888), (-6914237583/68719476736)), (121/549755813888), by norm_num⟩
  | 7 => ⟨((47884254041/1099511627776), (50871022179/1099511627776)), (113/1099511627776), by norm_num⟩
  | 8 => ⟨((-38533366931/2199023255552), (-20468437935/1099511627776)), (93/2199023255552), by norm_num⟩
  | 9 => ⟨((55126277007/8796093022208), (29282382241/4398046511104)), (135/8796093022208), by norm_num⟩
  | 10 => ⟨((-35488928075/17592186044416), (-9425635229/4398046511104)), (89/17592186044416), by norm_num⟩
  | 11 => ⟨((41539800957/70368744177664), (44130835451/70368744177664)), (53/35184372088832), by norm_num⟩
  | 12 => ⟨((-2785655439/17592186044416), (-11837639947/70368744177664)), (29/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058242031/10141204801825835211973625643008), (-3029822033733/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778238928031753/633825300114114700748351602688), (-1791813799645/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889145562345685/39614081257132168796771975168), (-1007680764637/9903520314283042199192993792)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888883076077167/2475880078570760549798248448), (-4281587305429/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27664828092993/2417851639229258349412352), (-2140199825521/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774475746874093/4835703278458516698824704), (-1002903278433/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258261646042955/604462909807314587353088), (-1754450139597/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235866869789739/9444732965739290427392), (-1424899746373/18889465931478580854784)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296896069475157/4722366482869645213696), (-4272631539927/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620562538493737/590295810358705651712), (-733938725681/73786976294838206464)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822366265004201/73786976294838206464), (-916793993729/9223372036854775808)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910704042302739/4611686018427387904), (-8244226516989/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592654202322965/1152921504606846976), (-4117791706929/576460752303423488)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193412883608941/144115188075855872), (-7196420492569/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489880248863855/36028797018963968), (-10775221987425/36028797018963968)), (553/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487051956388363/9007199254740992), (-13435109944403/9007199254740992)), (2771/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223508983864919/4503599627370496), (-13384329160305/2251799813685248)), (2781/2251799813685248), by norm_num⟩
  | 1 => ⟨((2209376670695069/2251799813685248), (-19949876008093/1125899906842624)), (4197/1125899906842624), by norm_num⟩
  | 0 => ⟨((8464880432189/8796093022208), (-78790571077827/2251799813685248)), (16989/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((8464880432189/8796093022208), (-78790571077827/2251799813685248)), (64807900435637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1041327412084145/1125899906842624), (-151647501151659/2251799813685248)), (1059/70368744177664), by norm_num⟩
  | 2 => ⟨((479000633826877/562949953421312), (-280512857250565/2251799813685248)), (67251/2251799813685248), by norm_num⟩
  | 3 => ⟨((1595336419511783/2251799813685248), (-477363345011415/2251799813685248)), (131201/2251799813685248), by norm_num⟩
  | 4 => ⟨((1029053521621831/2251799813685248), (-676396831555229/2251799813685248)), (241533/2251799813685248), by norm_num⟩
  | 5 => ⟨((33386542232191/281474976710656), (-1236430587293847/4503599627370496)), (731723/4503599627370496), by norm_num⟩
  | 6 => ⟨((-69022972305877/1125899906842624), (-293313050433559/4503599627370496)), (1150725/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/2147483648), (-15990517775/1073741824)), (1/2147483648), by norm_num⟩, -2, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-5247531779/2147483648), (-32370711663/2147483648)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1260340103319419/18014398509481984), (-927018337764001/18014398509481984)), (278883/2251799813685248), by norm_num⟩
  | 1 => ⟨((62657313955/274877906944), (46086353103/274877906944)), (113/274877906944), by norm_num⟩
  | 2 => ⟨((-12758973605/34359738368), (-18769223437/68719476736)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((55426623641/137438953472), (10191990317/34359738368)), (13/17179869184), by norm_num⟩
  | 4 => ⟨((-22573161325/68719476736), (-33206488367/137438953472)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((14709107753/68719476736), (43275977915/274877906944)), (115/274877906944), by norm_num⟩
  | 6 => ⟨((-63898257397/549755813888), (-1468722019/17179869184)), (127/549755813888), by norm_num⟩
  | 7 => ⟨((29740955887/549755813888), (43750748575/1099511627776)), (15/137438953472), by norm_num⟩
  | 8 => ⟨((-24224726353/1099511627776), (-35636040617/2199023255552)), (99/2199023255552), by norm_num⟩
  | 9 => ⟨((8769610785/1099511627776), (25801257903/4398046511104)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((-45715581661/17592186044416), (-8406298905/4398046511104)), (3/549755813888), by norm_num⟩
  | 11 => ⟨((1692565663/2199023255552), (39837866705/70368744177664)), (29/17592186044416), by norm_num⟩
  | 12 => ⟨((-58821784821/281474976710656), (-21632602599/140737488355328)), (1/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (-3266190140759/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778192492663979/633825300114114700748351602688), (-3863012565409/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889093272121055/39614081257132168796771975168), (-543118885691/4951760157141521099596496896)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888827449362397/2475880078570760549798248448), (-4615358125769/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885246647215613/77371252455336267181195264), (-288378871655/9671406556917033397649408)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548899190164871/9671406556917033397649408), (-4324306220899/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629107899478267/302231454903657293676544), (-3782391467561/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886860304255935/75557863725914323419136), (-6143806046507/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648419972812229/2361183241434822606848), (-4605597761371/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620485151905699/590295810358705651712), (-6329031172003/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822269207899221/73786976294838206464), (-7905792977675/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821298450966651/9223372036854775808), (-4443232201735/4611686018427387904)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((1592544014576043/1152921504606846976), (-8877029962595/1152921504606846976)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193315847862715/144115188075855872), (-3878398156337/72057594037927936)), (737/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489733457061271/36028797018963968), (-11614006765135/36028797018963968)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486866310485379/9007199254740992), (-3620119929129/2251799813685248)), (2775/9007199254740992), by norm_num⟩
  | 2 => ⟨((555782816546741/1125899906842624), (-1803129512777/281474976710656)), (1393/1125899906842624), by norm_num⟩
  | 1 => ⟨((552198544510033/562949953421312), (-42998586804949/2251799813685248)), (8409/2251799813685248), by norm_num⟩
  | 0 => ⟨((541445407051343/562949953421312), (-84895267776233/2251799813685248)), (17035/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((541445407051343/562949953421312), (-84895267776233/2251799813685248)), (64983376509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079848673100455/2251799813685248), (-163304579877757/2251799813685248)), (17027/1125899906842624), by norm_num⟩
  | 2 => ⟨((1909184862287049/2251799813685248), (-301668746667243/2251799813685248)), (67847/2251799813685248), by norm_num⟩
  | 3 => ⟨((789142707995401/1125899906842624), (-127884681635983/562949953421312)), (33307/562949953421312), by norm_num⟩
  | 4 => ⟨((990013842272517/2251799813685248), (-717074499173615/2251799813685248)), (247291/2251799813685248), by norm_num⟩
  | 5 => ⟨((206915182999135/2251799813685248), (-1261060021069425/4503599627370496)), (374943/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1260340103319419/18014398509481984), (-927018337764001/18014398509481984)), (278883/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-32370711663/2147483648)), (1/2147483648), by norm_num⟩, -2, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-165884901/67108864), (-65491358917/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1363086124473433/18014398509481984), (-337303065264797/9007199254740992)), (1069259/9007199254740992), by norm_num⟩
  | 1 => ⟨((68550254831/274877906944), (33926265793/274877906944)), (55/137438953472), by norm_num⟩
  | 2 => ⟨((-28241307131/68719476736), (-13976929691/68719476736)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((62052494125/137438953472), (30710453433/137438953472)), (103/137438953472), by norm_num⟩
  | 4 => ⟨((-51128724441/137438953472), (-25304161149/137438953472)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((33702386985/137438953472), (33359354871/274877906944)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-74051712999/549755813888), (-36648997203/549755813888)), (131/549755813888), by norm_num⟩
  | 7 => ⟨((17433026121/274877906944), (4313897003/137438953472)), (125/1099511627776), by norm_num⟩
  | 8 => ⟨((-897756409/34359738368), (-28435801557/2199023255552)), (105/2199023255552), by norm_num⟩
  | 9 => ⟨((84163091043/8796093022208), (20826614019/4398046511104)), (39/2199023255552), by norm_num⟩
  | 10 => ⟨((-13869390911/4398046511104), (-27456448911/17592186044416)), (105/17592186044416), by norm_num⟩
  | 11 => ⟨((66489090725/70368744177664), (8226543321/17592186044416)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-73045732133/281474976710656), (-36151126343/281474976710656)), (71/140737488355328), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-3493636538065/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((55567116655905/19807040628566084398385987584), (-2065913254951/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889042864880803/39614081257132168796771975168), (-4647287750797/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888773820273673/2475880078570760549798248448), (-4936496069773/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55326237034857/4835703278458516698824704), (-2467546632619/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774424376258507/4835703278458516698824704), (-289072487621/604462909807314587353088)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258171580936929/604462909807314587353088), (-2022762540347/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943394145318589/37778931862957161709568), (-3285592903737/37778931862957161709568)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324196449043583/1180591620717411303424), (-2462973394129/2361183241434822606848)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405102617624355/147573952589676412928), (-6769209209481/590295810358705651712)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822175517869267/73786976294838206464), (-8455562784067/73786976294838206464)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910596292769725/4611686018427387904), (-9504333034137/9223372036854775808)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592437570433645/1152921504606846976), (-2373530191901/288230376151711744)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74576378762133/9007199254740992), (-8295875957719/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((744795741244511/18014398509481984), (-6210438615937/18014398509481984)), (277/4503599627370496), by norm_num⟩
  | 3 => ⟨((1486686590668767/9007199254740992), (-7743004228269/4503599627370496)), (1389/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111382558360707/2251799813685248), (-15425978687813/2251799813685248)), (2789/2251799813685248), by norm_num⟩
  | 1 => ⟨((552057084042991/562949953421312), (-22989252106747/1125899906842624)), (4213/1125899906842624), by norm_num⟩
  | 0 => ⟨((270573051417603/281474976710656), (-22690896729387/562949953421312)), (8541/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270573051417603/281474976710656), (-22690896729387/562949953421312)), (32581333640670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077088565637181/2251799813685248), (-174496368784729/2251799813685248)), (34219/2251799813685248), by norm_num⟩
  | 2 => ⟨((1902410640922299/2251799813685248), (-40239413173545/281474976710656)), (4277/140737488355328), by norm_num⟩
  | 3 => ⟨((1561211952095181/2251799813685248), (-543933877891483/2251799813685248)), (135195/2251799813685248), by norm_num⟩
  | 4 => ⟨((951025345517733/2251799813685248), (-754237624634925/2251799813685248)), (252781/2251799813685248), by norm_num⟩
  | 5 => ⟨((298050307458721/4503599627370496), (-637089578932851/2251799813685248)), (382857/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1363086124473433/18014398509481984), (-337303065264797/9007199254740992)), (1069259/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-65491358917/4294967296)), (1/2147483648), by norm_num⟩, -2, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile010Terms3
