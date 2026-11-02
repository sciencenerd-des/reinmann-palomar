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
namespace Reinmann.XiRectangle.Tile004Terms1
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
  | 0 => ⟨((-28311023105/17179869184), (-149694534667/34359738368)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-603670868163419/9007199254740992), (1624925507723937/9007199254740992)), (147653/9007199254740992), by norm_num⟩
  | 1 => ⟨((5059816239/34359738368), (-217915421259/549755813888)), (11/274877906944), by norm_num⟩
  | 2 => ⟨((-88940420777/549755813888), (239404559685/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((130281385633/1099511627776), (-87670930411/274877906944)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((-143128731241/2199023255552), (192632723017/1099511627776)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((62897193201/2199023255552), (-169302941365/2199023255552)), (43/4398046511104), by norm_num⟩
  | 6 => ⟨((-23033209791/2199023255552), (123998861261/4398046511104)), (17/4398046511104), by norm_num⟩
  | 7 => ⟨((28919505513/8796093022208), (-77843813007/8796093022208)), (45/35184372088832), by norm_num⟩
  | 8 => ⟨((-127085296555/140737488355328), (342080678265/140737488355328)), (13/35184372088832), by norm_num⟩
  | 9 => ⟨((1939131507/8796093022208), (-334056921651/562949953421312)), (53/562949953421312), by norm_num⟩
  | 10 => ⟨((-54537054795/1125899906842624), (9174975981/70368744177664)), (49/2251799813685248), by norm_num⟩
  | 11 => ⟨((87149205215/9007199254740992), (-234583071673/9007199254740992)), (41/9007199254740992), by norm_num⟩
  | 12 => ⟨((-127657583729/72057594037927936), (343621127005/72057594037927936)), (63/72057594037927936), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677669/5070602400912917605986812821504), (1254741291117/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889711193231821/316912650057057350374175801344), (2971933569129/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945238413356143/19807040628566084398385987584), (3342931068107/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945148704671481/1237940039285380274899124224), (1775633068729/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771963178995227/154742504910672534362390528), (3550593318187/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550277126613835/9671406556917033397649408), (3327966464259/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259421412794789/604462909807314587353088), (363906999487/75557863725914323419136)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236102409403251/9444732965739290427392), (4729451241591/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298309040797839/4722366482869645213696), (443239548107/590295810358705651712)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811252470331661/295147905179352825856), (4873730897323/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824793616627499/73786976294838206464), (6089308200143/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456034489582295/2305843009213693952), (3423273391245/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595382952578333/1152921504606846976), (6841642497817/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195799272885973/144115188075855872), (5980922470435/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((746728645088855/18014398509481984), (8960360792019/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((745759395041619/4503599627370496), (5590587782215/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116214587105499/2251799813685248), (2788072949825/562949953421312)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111361504545513/1125899906842624), (8328165606093/562949953421312)), (263/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096782382671061/1125899906842624), (33024854984273/1125899906842624)), (529/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096782382671061/1125899906842624), (33024854984273/1125899906842624)), (2017979148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067449199157691/1125899906842624), (32170780827749/562949953421312)), (1063/1125899906842624), by norm_num⟩
  | 2 => ⟨((1008356026433901/1125899906842624), (61001291539601/562949953421312)), (1069/562949953421312), by norm_num⟩
  | 3 => ⟨((889863512447747/1125899906842624), (109265520976379/562949953421312)), (8587/2251799813685248), by norm_num⟩
  | 4 => ⟨((1321789352617635/2251799813685248), (345435325803129/1125899906842624)), (4227/562949953421312), by norm_num⟩
  | 5 => ⟨((281957753909821/1125899906842624), (811071628818247/2251799813685248)), (15113/1125899906842624), by norm_num⟩
  | 6 => ⟨((-603670868163419/9007199254740992), (1624925507723937/9007199254740992)), (147653/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/17179869184), (-149694534667/34359738368)), (1/34359738368), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-39218158169/8589934592)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-234281836318117/9007199254740992), (396126278203353/2251799813685248)), (130463/9007199254740992), by norm_num⟩
  | 1 => ⟨((65851301741/1099511627776), (-222684195101/549755813888)), (39/1099511627776), by norm_num⟩
  | 2 => ⟨((-9476764109/137438953472), (128187327021/274877906944)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((29094741023/549755813888), (-393549637745/1099511627776)), (39/1099511627776), by norm_num⟩
  | 4 => ⟨((-16748279241/549755813888), (113272691153/549755813888)), (47/2199023255552), by norm_num⟩
  | 5 => ⟨((30851470491/2199023255552), (-417312016147/4398046511104)), (23/2199023255552), by norm_num⟩
  | 6 => ⟨((-23679378683/4398046511104), (320298809169/8796093022208)), (37/8796093022208), by norm_num⟩
  | 7 => ⟨((62312896419/35184372088832), (-1646239427/137438953472)), (51/35184372088832), by norm_num⟩
  | 8 => ⟨((-35870186599/70368744177664), (242598807303/70368744177664)), (31/70368744177664), by norm_num⟩
  | 9 => ⟨((18354257099/140737488355328), (-124134310505/140737488355328)), (17/140737488355328), by norm_num⟩
  | 10 => ⟨((-67619582063/2251799813685248), (114331925159/562949953421312)), (65/2251799813685248), by norm_num⟩
  | 11 => ⟨((56618124237/9007199254740992), (-382922162217/9007199254740992)), (57/9007199254740992), by norm_num⟩
  | 12 => ⟨((-43456016287/36028797018963968), (9184488151/1125899906842624)), (23/18014398509481984), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (1118676895117/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222412682666885/79228162514264337593543950336), (331163899255/79228162514264337593543950336)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890340863026209/39614081257132168796771975168), (2980016236791/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890153044403903/2475880078570760549798248448), (3165708763823/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885909461276137/77371252455336267181195264), (1582540282707/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193767750179085/1208925819614629174706176), (741648922005/2417851639229258349412352)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259303293447049/604462909807314587353088), (648776004623/151115727451828646838272)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888627547156539/75557863725914323419136), (4215793297815/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649082716764915/2361183241434822606848), (3160750866403/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811153893625729/295147905179352825856), (1086063762379/147573952589676412928)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824547634398347/73786976294838206464), (5427653655235/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455965464908953/2305843009213693952), (3051223642309/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797553821103791/576460752303423488), (6097870707003/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((597779631023447/72057594037927936), (2665245669505/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493099042572073/36028797018963968), (3992726874775/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((745537034691457/4503599627370496), (4981919516863/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2231548973905443/4503599627370496), (19873813804385/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221425722818051/2251799813685248), (29676305721087/2251799813685248)), (261/1125899906842624), by norm_num⟩
  | 0 => ⟨((2191061718909095/2251799813685248), (3676026587421/140737488355328)), (1053/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2191061718909095/2251799813685248), (3676026587421/140737488355328)), (4016884810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2130425651079989/2251799813685248), (57229962162283/1125899906842624)), (2105/2251799813685248), by norm_num⟩
  | 2 => ⟨((2009775626145331/2251799813685248), (216580849966989/2251799813685248)), (2099/1125899906842624), by norm_num⟩
  | 3 => ⟨((110808329258789/140737488355328), (386605337391093/2251799813685248)), (8303/2251799813685248), by norm_num⟩
  | 4 => ⟨((1329527015761173/2251799813685248), (608780105705441/2251799813685248)), (7963/1125899906842624), by norm_num⟩
  | 5 => ⟨((155101361591479/562949953421312), (359441186678445/1125899906842624)), (27419/2251799813685248), by norm_num⟩
  | 6 => ⟨((-234281836318117/9007199254740992), (396126278203353/2251799813685248)), (130463/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-39218158169/8589934592)), (1/34359738368), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-123586581311/68719476736), (-326732024341/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((31446527083325/4503599627370496), (744952644383951/4503599627370496)), (14423/1125899906842624), by norm_num⟩
  | 1 => ⟨((-18409540683/1099511627776), (-436112896589/1099511627776)), (9/274877906944), by norm_num⟩
  | 2 => ⟨((22072075289/1099511627776), (522876526569/1099511627776)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((-17642174999/1099511627776), (-417934383773/1099511627776)), (39/1099511627776), by norm_num⟩
  | 4 => ⟨((1322002751/137438953472), (501081441595/2199023255552)), (49/2199023255552), by norm_num⟩
  | 5 => ⟨((-10144077271/2199023255552), (-480616328035/4398046511104)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((16216289957/8796093022208), (384155873675/8796093022208)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((-22219980017/35184372088832), (-4112346221/274877906944)), (15/8796093022208), by norm_num⟩
  | 8 => ⟨((13320296261/70368744177664), (157775609015/35184372088832)), (19/35184372088832), by norm_num⟩
  | 9 => ⟨((-7097927875/140737488355328), (-168146394231/140737488355328)), (43/281474976710656), by norm_num⟩
  | 10 => ⟨((13616070159/1125899906842624), (80639488773/281474976710656)), (43/1125899906842624), by norm_num⟩
  | 11 => ⟨((-11872694643/4503599627370496), (-281258252989/4503599627370496)), (39/4503599627370496), by norm_num⟩
  | 12 => ⟨((1186228265/2251799813685248), (112404639213/9007199254740992)), (1/562949953421312), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122365965/10141204801825835211973625643008), (497795838513/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889595994641043/316912650057057350374175801344), (2357536117967/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945108885811355/19807040628566084398385987584), (2651804988721/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890022340987067/2475880078570760549798248448), (2817025442595/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771688310445741/154742504910672534362390528), (2816443535411/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550019649561625/9671406556917033397649408), (2639797667583/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259196332495539/604462909807314587353088), (2309204957931/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888453917273021/75557863725914323419136), (3751299613865/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298035369980385/4722366482869645213696), (703115345603/1180591620717411303424)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811064603925933/295147905179352825856), (3865488322933/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228040599602459/9223372036854775808), (2414696150905/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823611698544039/9223372036854775808), (1357418587107/2305843009213693952)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594858144364285/1152921504606846976), (2712718416149/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195341696582917/144115188075855872), (4742493421577/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492774182161727/36028797018963968), (1776055253293/9007199254740992)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((372667647961881/2251799813685248), (8863636910875/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230749790203903/4503599627370496), (17677432122415/4503599627370496)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((555061574208263/562949953421312), (26391811020457/2251799813685248)), (521/2251799813685248), by norm_num⟩
  | 0 => ⟨((273597474125373/281474976710656), (13071968572223/562949953421312)), (525/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((273597474125373/281474976710656), (13071968572223/562949953421312)), (2002720359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531577333313719/562949953421312), (101649038220059/2251799813685248)), (2091/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003223744091779/2251799813685248), (5999015136973/70368744177664)), (4139/2251799813685248), by norm_num⟩
  | 3 => ⟨((1765722443768037/2251799813685248), (21347136615813/140737488355328)), (8071/2251799813685248), by norm_num⟩
  | 4 => ⟨((1332763449181077/2251799813685248), (535651426968165/2251799813685248)), (15107/2251799813685248), by norm_num⟩
  | 5 => ⟨((5167172107759/17592186044416), (634067592533023/2251799813685248)), (12535/1125899906842624), by norm_num⟩
  | 6 => ⟨((31446527083325/4503599627370496), (744952644383951/4503599627370496)), (14423/1125899906842624), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-123586581311/68719476736), (-326732024341/68719476736)), (1/34359738368), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-128071113533/68719476736), (-84647001601/17179869184)), (3/68719476736), by norm_num⟩
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
  | 0 => ⟨((74415610044559/2251799813685248), (1364944264727287/9007199254740992)), (38219/2251799813685248), by norm_num⟩
  | 1 => ⟨((-45145469787/549755813888), (-414033090821/1099511627776)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((56091139041/549755813888), (257208395153/549755813888)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((-46460414799/549755813888), (-26630785479/68719476736)), (55/1099511627776), by norm_num⟩
  | 4 => ⟨((57724896843/1099511627776), (264700063703/1099511627776)), (9/274877906944), by norm_num⟩
  | 5 => ⟨((-57376392009/2199023255552), (-131550989699/1099511627776)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((95049985363/8796093022208), (108963976363/2199023255552)), (33/4398046511104), by norm_num⟩
  | 7 => ⟨((-67482954483/17592186044416), (-38680758493/2199023255552)), (49/17592186044416), by norm_num⟩
  | 8 => ⟨((83844421171/70368744177664), (48059036999/8796093022208)), (63/70368744177664), by norm_num⟩
  | 9 => ⟨((-23149506635/70368744177664), (-212306169993/140737488355328)), (9/35184372088832), by norm_num⟩
  | 10 => ⟨((46019490381/562949953421312), (422048810885/1125899906842624)), (37/562949953421312), by norm_num⟩
  | 11 => ⟨((-10395830697/562949953421312), (-381364326073/4503599627370496)), (69/4503599627370496), by norm_num⟩
  | 12 => ⟨((68887116877/18014398509481984), (39485614577/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115840927/10141204801825835211973625643008), (1766447353461/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779091981139263/633825300114114700748351602688), (261403295489/79228162514264337593543950336)), (69/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945052658663603/19807040628566084398385987584), (588060562059/9903520314283042199192993792)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29529733240529/38685626227668133590597632), (2498781958869/2475880078570760549798248448)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771568974548875/154742504910672534362390528), (312280903997/19342813113834066795298816)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774953927338253/4835703278458516698824704), (1170769383147/4835703278458516698824704)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9836707769147/4722366482869645213696), (2048278557139/604462909807314587353088)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944147623759119/37778931862957161709568), (3327388230887/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297916502829583/4722366482869645213696), (2494610121031/4722366482869645213696)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101372874063133/36893488147419103232), (107143017349/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824121097235855/73786976294838206464), (4283453199073/73786976294838206464)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823382988409179/9223372036854775808), (4815768744215/9223372036854775808)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797314999224599/576460752303423488), (2405938081643/576460752303423488)), (79/576460752303423488), by norm_num⟩
  | 5 => ⟨((298785675689873/36028797018963968), (525751999225/18014398509481984)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492476956895831/36028797018963968), (787535181049/4503599627370496)), (207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490301269812673/9007199254740992), (7860072047429/9007199254740992)), (259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115008877355557/2251799813685248), (15674383476261/4503599627370496)), (519/4503599627370496), by norm_num⟩
  | 1 => ⟨((277395586867087/281474976710656), (5849362171243/562949953421312)), (195/562949953421312), by norm_num⟩
  | 0 => ⟨((2186681975026907/2251799813685248), (23170019357477/1125899906842624)), (785/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2186681975026907/2251799813685248), (23170019357477/1125899906842624)), (2994541648482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2122493585652073/2251799813685248), (89999942947151/2251799813685248)), (3115/2251799813685248), by norm_num⟩
  | 2 => ⟨((998507727923693/1125899906842624), (169663662332181/2251799813685248)), (6123/2251799813685248), by norm_num⟩
  | 3 => ⟨((1758275735043113/2251799813685248), (150466730618709/1125899906842624)), (1473/281474976710656), by norm_num⟩
  | 4 => ⟨((1332699556199775/2251799813685248), (234978260296743/1125899906842624)), (21553/2251799813685248), by norm_num⟩
  | 5 => ⟨((345330203509851/1125899906842624), (34767236113849/140737488355328)), (34509/2251799813685248), by norm_num⟩
  | 6 => ⟨((74415610044559/2251799813685248), (1364944264727287/9007199254740992)), (38219/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-128071113533/68719476736), (-84647001601/17179869184)), (3/68719476736), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-66098241637/34359738368), (-21843403291/4294967296)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((119987082818081/2251799813685248), (9569977173619/70368744177664)), (90193/9007199254740992), by norm_num⟩
  | 1 => ⟨((-18784227965/137438953472), (-383539168787/1099511627776)), (31/1099511627776), by norm_num⟩
  | 2 => ⟨((48180593449/274877906944), (245939636135/549755813888)), (11/274877906944), by norm_num⟩
  | 3 => ⟨((-82387188139/549755813888), (-105137118613/274877906944)), (21/549755813888), by norm_num⟩
  | 4 => ⟨((6603717665/68719476736), (1053403847/4294967296)), (29/1099511627776), by norm_num⟩
  | 5 => ⟨((-108404488843/2199023255552), (-69169344525/549755813888)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((92684008001/4398046511104), (236554487727/4398046511104)), (29/4398046511104), by norm_num⟩
  | 7 => ⟨((-135845592439/17592186044416), (-346714446457/17592186044416)), (45/17592186044416), by norm_num⟩
  | 8 => ⟨((21777316565/8796093022208), (111163124583/17592186044416)), (31/35184372088832), by norm_num⟩
  | 9 => ⟨((-99302602899/140737488355328), (-253446919975/140737488355328)), (37/140737488355328), by norm_num⟩
  | 10 => ⟨((12735307375/70368744177664), (32503925727/70368744177664)), (5/70368744177664), by norm_num⟩
  | 11 => ⟨((-95026671909/2251799813685248), (-121266797685/1125899906842624)), (39/2251799813685248), by norm_num⟩
  | 12 => ⟨((2538943761/281474976710656), (207362129869/9007199254740992)), (35/9007199254740992), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418255/10141204801825835211973625643008), (1559710273537/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222374990657487/79228162514264337593543950336), (1846295728345/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945000900731641/19807040628566084398385987584), (259591351465/4951760157141521099596496896)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236224125138999/309485009821345068724781056), (275761665181/309485009821345068724781056)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221432389371565/19342813113834066795298816), (2205606145825/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549804932167897/9671406556917033397649408), (2067238270417/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157376076008229/75557863725914323419136), (1808316144713/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888149152338885/75557863725914323419136), (183596502279/4722366482869645213696)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297807047481723/4722366482869645213696), (1101154929131/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621815672330399/590295810358705651712), (3026798375021/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823933488783723/73786976294838206464), (3781432488905/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823172316810905/9223372036854775808), (4251273204835/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594419811159993/1152921504606846976), (1061931951609/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194959332933883/144115188075855872), (464097092273/18014398509481984)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((373050747069085/9007199254740992), (5561203617551/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489960705283983/9007199254740992), (6937591460617/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229342296570889/4503599627370496), (3458380456983/1125899906842624)), (173/2251799813685248), by norm_num⟩
  | 1 => ⟨((554541405696041/562949953421312), (2580800363965/281474976710656)), (519/2251799813685248), by norm_num⟩
  | 0 => ⟨((2184739918616793/2251799813685248), (20439460305027/1125899906842624)), (1045/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184739918616793/2251799813685248), (20439460305027/1125899906842624)), (3986367232512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1059467497254711/1125899906842624), (39661522815649/1125899906842624)), (1033/1125899906842624), by norm_num⟩
  | 2 => ⟨((995557717462163/1125899906842624), (149285363856699/2251799813685248)), (4035/2251799813685248), by norm_num⟩
  | 3 => ⟨((1750712710505225/2251799813685248), (66001513628537/562949953421312)), (959/281474976710656), by norm_num⟩
  | 4 => ⟨((1330178544158589/2251799813685248), (410514960059287/2251799813685248)), (6865/1125899906842624), by norm_num⟩
  | 5 => ⟨((44432580584491/140737488355328), (15156159436563/70368744177664)), (5307/562949953421312), by norm_num⟩
  | 6 => ⟨((119987082818081/2251799813685248), (9569977173619/70368744177664)), (90193/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66098241637/34359738368), (-21843403291/4294967296)), (1/34359738368), by norm_num⟩, -1, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-34003994769/17179869184), (-359592244681/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((618761872573649/9007199254740992), (1079771151316975/9007199254740992)), (39879/4503599627370496), by norm_num⟩
  | 1 => ⟨((-199334479383/1099511627776), (-86962218359/274877906944)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((131513779715/549755813888), (14343642485/34359738368)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-57845400717/274877906944), (-201886372445/549755813888)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((152657328747/1099511627776), (266394855475/1099511627776)), (27/1099511627776), by norm_num⟩
  | 5 => ⟨((-40287144235/549755813888), (-281212518365/2199023255552)), (31/2199023255552), by norm_num⟩
  | 6 => ⟨((35440027761/1099511627776), (123689326295/2199023255552)), (15/2199023255552), by norm_num⟩
  | 7 => ⟨((-53444722871/4398046511104), (-23315944511/1099511627776)), (3/1099511627776), by norm_num⟩
  | 8 => ⟨((70521843811/17592186044416), (246128457035/35184372088832)), (17/17592186044416), by norm_num⟩
  | 9 => ⟨((-165432167829/140737488355328), (-288687603807/140737488355328)), (21/70368744177664), by norm_num⟩
  | 10 => ⟨((174633990025/562949953421312), (152372627359/281474976710656)), (47/562949953421312), by norm_num⟩
  | 11 => ⟨((-167588767773/2251799813685248), (-146225490569/1125899906842624)), (47/2251799813685248), by norm_num⟩
  | 12 => ⟨((73712727659/4503599627370496), (128632484221/4503599627370496)), (11/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987295/10141204801825835211973625643008), (171037704277/1267650600228229401496703205376)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889457322934513/316912650057057350374175801344), (1619568601095/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889905902727757/39614081257132168796771975168), (1821697973439/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944845580006409/1237940039285380274899124224), (483790804683/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442839332890889/38685626227668133590597632), (1934723616157/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549709571490877/9671406556917033397649408), (906668220317/4835703278458516698824704)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629462614355993/302231454903657293676544), (396550645073/151115727451828646838272)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944006887823361/37778931862957161709568), (644176059885/18889465931478580854784)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324426403827825/1180591620717411303424), (1931762901723/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621676366042009/590295810358705651712), (2654930987351/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227969950016383/9223372036854775808), (1658400117327/36893488147419103232)), (93/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822977027519669/9223372036854775808), (1864419791569/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594224940658817/1152921504606846976), (3725641177061/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((597394645839277/72057594037927936), (1628170591221/72057594037927936)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((186493608187231/4503599627370496), (2438665234787/18014398509481984)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489644691285367/9007199254740992), (6084114663705/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228715171193081/4503599627370496), (12130659390335/4503599627370496)), (345/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217237136084037/2251799813685248), (18102327444901/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | 0 => ⟨((272866427580955/281474976710656), (17915791922865/1125899906842624)), (521/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((272866427580955/281474976710656), (17915791922865/1125899906842624)), (1987461570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115599111385183/2251799813685248), (69471442135351/2251799813685248)), (1027/1125899906842624), by norm_num⟩
  | 2 => ⟨((992746622423859/1125899906842624), (130538887475669/2251799813685248)), (3987/2251799813685248), by norm_num⟩
  | 3 => ⟨((435778416040537/562949953421312), (14387606621251/140737488355328)), (3747/1125899906842624), by norm_num⟩
  | 4 => ⟨((1325807206585193/2251799813685248), (44549668302971/281474976710656)), (13135/2251799813685248), by norm_num⟩
  | 5 => ⟨((724196560717573/2251799813685248), (104919222264959/562949953421312)), (9813/1125899906842624), by norm_num⟩
  | 6 => ⟨((618761872573649/9007199254740992), (1079771151316975/9007199254740992)), (39879/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34003994769/17179869184), (-359592244681/68719476736)), (1/34359738368), by norm_num⟩, -1, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-34892961149/17179869184), (-184496532075/34359738368)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((721895821038915/9007199254740992), (935613129368149/9007199254740992)), (70683/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1864366649/8589934592), (-309288003313/1099511627776)), (13/549755813888), by norm_num⟩
  | 2 => ⟨((20195193915/68719476736), (52347964973/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-72919465257/274877906944), (-189014556097/549755813888)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((197469572553/1099511627776), (255930453325/1099511627776)), (29/1099511627776), by norm_num⟩
  | 5 => ⟨((-213903006265/2199023255552), (-138614503119/1099511627776)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((48271673261/1099511627776), (250250022031/4398046511104)), (33/4398046511104), by norm_num⟩
  | 7 => ⟨((-149396702265/8796093022208), (-193625606425/8796093022208)), (27/8796093022208), by norm_num⟩
  | 8 => ⟨((101143442403/17592186044416), (262173931209/35184372088832)), (39/35184372088832), by norm_num⟩
  | 9 => ⟨((-30433502171/17592186044416), (-78886685237/35184372088832)), (25/70368744177664), by norm_num⟩
  | 10 => ⟨((131864722679/281474976710656), (10681455191/17592186044416)), (29/281474976710656), by norm_num⟩
  | 11 => ⟨((-32463298979/281474976710656), (-84148121827/562949953421312)), (15/562949953421312), by norm_num⟩
  | 12 => ⟨((58608162219/2251799813685248), (303836450981/9007199254740992)), (7/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (595052227109/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889417605171547/316912650057057350374175801344), (1408528049237/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944908286512383/19807040628566084398385987584), (99019505737/2475880078570760549798248448)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889596291845433/2475880078570760549798248448), (1682982819199/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771262513590861/154742504910672534362390528), (420647643435/38685626227668133590597632)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549620732949443/9671406556917033397649408), (788506011429/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258847548269317/604462909807314587353088), (1379469015863/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471971911193081/18889465931478580854784), (2240856494173/75557863725914323419136)), (9/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297611104462755/4722366482869645213696), (839979792319/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621546555392611/590295810358705651712), (2308835442405/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455899387320833/18446744073709551616), (2884381769145/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822795012150339/9223372036854775808), (3242645042315/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594043289627391/1152921504606846976), (404973973109/144115188075855872)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597315378140589/72057594037927936), (707902765127/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((745855939675763/18014398509481984), (4241010988867/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((744674942379507/4503599627370496), (5290071687705/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((557032455654033/1125899906842624), (10546638142927/4503599627370496)), (345/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216369725555665/2251799813685248), (7868220923065/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 0 => ⟨((545309689208287/562949953421312), (31140304652753/2251799813685248)), (65/140737488355328), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((545309689208287/562949953421312), (31140304652753/2251799813685248)), (247955859136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((66014316176493/70368744177664), (60329021252571/2251799813685248)), (2045/2251799813685248), by norm_num⟩
  | 2 => ⟨((247515325347319/281474976710656), (56595852748637/1125899906842624)), (3947/2251799813685248), by norm_num⟩
  | 3 => ⟨((1735533121590083/2251799813685248), (199070497421699/2251799813685248)), (7339/2251799813685248), by norm_num⟩
  | 4 => ⟨((1320031263493113/2251799813685248), (38357477395087/281474976710656)), (12611/2251799813685248), by norm_num⟩
  | 5 => ⟨((366000471704073/1125899906842624), (359769596160541/2251799813685248)), (18223/2251799813685248), by norm_num⟩
  | 6 => ⟨((721895821038915/9007199254740992), (935613129368149/9007199254740992)), (70683/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-184496532075/34359738368)), (1/34359738368), by norm_num⟩, -1, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile004Terms1
